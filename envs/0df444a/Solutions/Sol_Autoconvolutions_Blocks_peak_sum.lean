-- Prove2me | solution 1 for Autoconvolutions.Blocks.peak_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:41.213084+00:00
-- url     : https://prove2.me/submissions/ab11ad2b-176d-4065-bf07-9afcdb3cffe7

module
public import Definitions.Def_Autoconvolutions_BlockKeys
public import Definitions.Def_Autoconvolutions_Occupancy
public import Definitions.Def_Autoconvolutions_Estimate
public import Definitions.Def_Autoconvolutions_GoodBlocks
public import Theorems.Thm_Autoconvolutions_Blocks_peak_rowKey
public import Theorems.Thm_Autoconvolutions_Blocks_card_goodPairs
public import Theorems.Thm_Autoconvolutions_Construction_card_evenAlphabet
public import Theorems.Thm_Autoconvolutions_Construction_card_oddAlphabet
attribute [local simp] Autoconvolutions.Construction.card_evenAlphabet
attribute [local simp] Autoconvolutions.Construction.card_oddAlphabet


attribute [local simp] Autoconvolutions.Blocks.peak_rowKey

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open Autoconvolutions Autoconvolutions.Blocks
namespace Autoconvolutions.Blocks
theorem _root_.solution {m : ℕ} (I J : Finset (Fin m)) (n K : ℕ) :
    (∑ x ∈ peakSet I J n K, (x.1:ℝ) * (Estimate.height n x.1)^2) =
      ∑ s ∈ range (K+1), (s:ℝ)*Estimate.count n I.card J.card s*(Estimate.height n s)^2 := by
  rw [peakSet, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Finset.sum_const, card_goodPairs, nsmul_eq_mul, Nat.cast_mul, Estimate.count]
  ring
end Autoconvolutions.Blocks
