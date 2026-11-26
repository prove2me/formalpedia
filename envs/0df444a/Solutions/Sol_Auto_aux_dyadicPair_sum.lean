-- Prove2me | solution 1 for Auto.aux_dyadicPair_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:41:58.839393+00:00
-- url     : https://prove2.me/submissions/b0230c1b-13d3-44b4-a45a-03d2bc2ddb01

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
public import Theorems.Thm_Auto_aux_dyadicPairChain_zero
public import Theorems.Thm_Auto_aux_dyadicPairChain_succ

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {B : Type*} [SeminormedAddCommGroup B]
    {M : ℕ} {k : ℤ} (a : ℝ → B) (r : ℝ) (hr : 0 < r)
    (x : aux_dyadicInterval k) :
    (∑ j : Fin (M + 1),
      (‖a (aux_dyadicPairChain (M + 1) k x j.succ) -
        a (aux_dyadicPairChain (M + 1) k x j.castSucc)‖₊ : ℝ≥0∞) ^ r) =
      (‖a x - a ((2 : ℝ) ^ k)‖₊ : ℝ≥0∞) ^ r := by
  rw [Fin.sum_univ_succ]
  rw [aux_dyadicPairChain_succ x 0]
  simp only [Fin.castSucc_zero]
  rw [aux_dyadicPairChain_zero x]
  simp [aux_dyadicPairChain, aux_dyadicLowerPoint, ENNReal.zero_rpow_of_pos hr]
end Auto
