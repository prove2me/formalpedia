-- Prove2me | solution 1 for AaronsonAmbainis.sensitivity_of_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:14:42.964494+00:00
-- url     : https://prove2.me/submissions/100b54f4-b208-4b2f-8614-5a1dc7f4005d

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Row_DisjointBlocks
import Theorems.Thm_AaronsonAmbainis_Row_disjoint_blocks_of_block

set_option autoImplicit true
open AaronsonAmbainis
open Finset
namespace AaronsonAmbainis
theorem _root_.solution : BlockInequality → SensitivityBound := by
  intro hBlock ι _ _ d f hf hdeg x
  exact Row.disjoint_blocks_of_block hBlock ι d f hf hdeg x ι (fun j => {j})
    (fun b b' hne => Finset.disjoint_singleton.mpr hne)
end AaronsonAmbainis
