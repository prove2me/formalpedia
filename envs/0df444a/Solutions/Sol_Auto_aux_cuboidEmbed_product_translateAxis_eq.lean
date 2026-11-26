-- Prove2me | solution 1 for Auto.aux_cuboidEmbed_product_translateAxis_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:45:14.732535+00:00
-- url     : https://prove2.me/submissions/bbc260a6-11b3-4e26-9f0e-a665cc04291d

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_cuboidEmbed_translateAxis_eq

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace Auto
theorem _root_.solution {n : ℕ} {ε δ : ℝ}
    (hε : ε < 1) (hεδ : ε + δ < 1)
    (a : Fin n → aux_ZVector n → ℝ) (k : aux_ZVector n)
    (u : aux_RVector n) (m : ℤ) (s : ℝ)
    (hu : ∀ j, 0 ≤ u j ∧ u j < ε)
    (hs : ∀ i, ε - u i ≤ s - m ∧ s - m < ε + δ - u i) :
    (∏ i, aux_cuboidEmbed ε δ i (a i)
        (aux_translateAxis (fun j ↦ (k j : ℝ) + u j) i s)) =
      ∏ i, a i (aux_translateAxisInt k i m) := by
  apply Finset.prod_congr rfl
  intro i _
  exact aux_cuboidEmbed_translateAxis_eq hε hεδ i (a i) k u m s hu (hs i)
end Auto
