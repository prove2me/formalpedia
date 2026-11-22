-- Prove2me | solution 1 for Autoconvolutions.Blocks.peak_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:03.97081+00:00
-- url     : https://prove2.me/submissions/5819cffc-b8d5-4d66-ac84-5ff8c6781a4c

module
public import Definitions.Def_Autoconvolutions_BlockKeys
public import Definitions.Def_Autoconvolutions_Occupancy
public import Definitions.Def_Autoconvolutions_Estimate
public import Definitions.Def_Autoconvolutions_GoodBlocks
public import Theorems.Thm_Autoconvolutions_Blocks_peak_mem
public import Theorems.Thm_Autoconvolutions_Blocks_goodVectors_spec
public import Theorems.Thm_Autoconvolutions_Blocks_mem_rows


set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open Autoconvolutions Autoconvolutions.Blocks
namespace Autoconvolutions.Blocks
theorem _root_.solution {m n K D h : ℕ} {I J : Finset (Fin m)} {x : Peak m}
    (hx : x ∈ peakSet I J n K) (hh : h < D) :
    (x.2,h) ∈ rows I J (2*n-x.1) (2*n+x.1) D :=
  mem_rows.mpr ⟨(goodVectors_spec (peak_mem hx).2.1).1,
    (goodVectors_spec (peak_mem hx).2.2).1, hh⟩
end Autoconvolutions.Blocks
