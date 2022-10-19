var factory = require('./zeos_updater.js');

const fetch = require("node-fetch");
global.fetch = fetch;

// Convert a hex string to a byte array
function hex2Bytes(hex)
{
  for(var bytes = [], c = 0; c < hex.length; c += 2)
      bytes.push(parseInt(hex.substr(c, 2), 16));
  return bytes;
}

// merkle tree helper functions
function MT_ARR_LEAF_ROW_OFFSET(d) {return ((1n<<(d)) - 1n);}
function MT_ARR_FULL_TREE_OFFSET(d) {return ((1n<<((d)+1n)) - 1n);}
function MT_NUM_LEAVES(d) {return (1n<<(d));}

var endpoint = 'https://kylin-dsp-1.liquidapps.io'; 

factory().then(async (instance) => {
  
  // read leaf_count, tree_depth and note_commitments from uri 'address'
  var leaf_count = 7n;
  var tree_depth = 5n;
  var note_commitments = [249, 255, 255, 255, 132, 169, 195, 207, 62, 48, 229, 190, 27, 209, 17, 16, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 63,
                          249, 255, 255, 255, 132, 169, 195, 207, 62, 48, 229, 190, 27, 209, 17, 16, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 63,
                          249, 255, 255, 255, 132, 169, 195, 207, 62, 48, 229, 190, 27, 209, 17, 16, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 63,
                          249, 255, 255, 255, 132, 169, 195, 207, 62, 48, 229, 190, 27, 209, 17, 16, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 63,
                          249, 255, 255, 255, 132, 169, 195, 207, 62, 48, 229, 190, 27, 209, 17, 16, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 63];
  var note_commitments_ptr = instance.allocate(note_commitments, instance.ALLOC_NORMAL);

  // calculate indices of nodes to fetch
  var indices = [];
  var idx = MT_ARR_LEAF_ROW_OFFSET(tree_depth-1n) + leaf_count % MT_NUM_LEAVES(tree_depth-1n);
  var tos = leaf_count / MT_NUM_LEAVES(tree_depth-1n) /*=tree_idx*/ * MT_ARR_FULL_TREE_OFFSET(tree_depth-1n);
  for(var d = 0n; d < tree_depth-1n; d++)
  {
    // if array index of node is uneven it is always the left child
    var is_left_child = 1n == idx % 2n;
    // determine sister node
    var sis_idx = is_left_child ? idx + 1n : idx - 1n;
    // if idx is a right child add its sister node index to list
    if(!is_left_child)
    {
      indices.push(tos + sis_idx);
    }
    // set idx to parent node index:
    // left child's array index divided by two (integer division) equals array index of parent node
    idx = is_left_child ? idx / 2n : sis_idx / 2n;
  }
  //console.log(indices);
  /*
  // fetch final nodes from EOS RAM
  var final_nodes = "";
  for(const i of indices)
  {
    res = await fetch(endpoint + '/v1/chain/get_table_rows', {
      method: 'POST',
      mode: 'cors',
      body: JSON.stringify({ code: 'thezavitoken', table: 'mteosram', scope: 'thezavitoken', index_position: 'primary', key_type: 'uint64_t', lower_bound: i.toString(), upper_bound: i.toString() })
    });
    var resJson = await res.json();
    final_nodes += resJson.rows[0];
    //console.log(resJson.rows[0]);
  };
  */
  var final_nodes = "0300000000000000328D17093AFCECC9BF941920F29F4C0B2ABD416E0A9CCB220AF1EA9EB77E3B1C"
  final_nodes +=    "09000000000000002910580A9E00A907FC78E3811FB9E7090AEA2BF264A2821A9F9C30501F03820C"
  final_nodes +=    "1500000000000000F9FFFFFF84A9C3CF3E30E5BE1BD11110FFFFFFFFFFFFFFFFFFFFFFFFFFFFFF3F"
  var final_nodes = hex2Bytes(final_nodes);
  var final_nodes_ptr = instance.allocate(final_nodes, instance.ALLOC_NORMAL);
  //console.log(final_nodes);
  
  console.dir(instance.update_merkle_tree(Number(leaf_count), Number(leaf_count >> 32n), Number(tree_depth), final_nodes_ptr, indices.length, note_commitments_ptr, note_commitments.length/32), {'maxArrayLength': null});

  
});
