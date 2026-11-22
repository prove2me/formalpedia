-- Prove2me | solution 1 for Autoconvolutions.Blocks.peak_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:49:42.06807+00:00
-- url     : https://prove2.me/submissions/e05fe841-b699-440c-852a-254766bade25

module
public import Definitions.Def_Autoconvolutions_BlockKeys
public import Definitions.Def_Autoconvolutions_Occupancy
public import Definitions.Def_Autoconvolutions_Estimate
public import Definitions.Def_Autoconvolutions_GoodBlocks
public import Theorems.Thm_Autoconvolutions_Construction_card_evenAlphabet
public import Theorems.Thm_Autoconvolutions_Construction_card_oddAlphabet
attribute [local simp] Autoconvolutions.Construction.card_evenAlphabet
attribute [local simp] Autoconvolutions.Construction.card_oddAlphabet



set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open Autoconvolutions Autoconvolutions.Blocks
namespace Autoconvolutions.Blocks
theorem _root_.solution {m n K : ℕ} {I J : Finset (Fin m)} {x : Peak m} (hx : x ∈ peakSet I J n K) :
    x.1 ≤ K ∧ x.2.1 ∈ goodVectors I (2*n-x.1) ∧ x.2.2 ∈ goodVectors J (2*n+x.1) := by
  simpa only [peakSet, Finset.mem_sigma, Finset.mem_range, Nat.lt_succ_iff,
    Finset.mem_product] using hx
end Autoconvolutions.Blocks
