-- Prove2me | solution 1 for Auto.aux_dyadicPair_le_variation_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:55:38.512523+00:00
-- url     : https://prove2.me/submissions/08112d32-75ea-45c7-8172-23965db77c79

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
public import Theorems.Thm_Auto_aux_chainVariation_le
public import Theorems.Thm_Auto_aux_dyadicPairChain_mono
public import Theorems.Thm_Auto_aux_dyadicPair_sum

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {B : Type*} [SeminormedAddCommGroup B]
    {J : ℕ} (hJ : 0 < J) {k : ℤ} (a : ℝ → B) (r : ℝ) (hr : 1 ≤ r)
    (x : aux_dyadicInterval k) :
    (‖a x - a ((2 : ℝ) ^ k)‖₊ : ℝ≥0∞) ^ r ≤
      (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hJ.ne'
  let c : {u : Fin (M + 1 + 1) → aux_dyadicInterval k // Monotone u} :=
    ⟨aux_dyadicPairChain (M + 1) k x, aux_dyadicPairChain_mono x⟩
  have hc := aux_chainVariation_le (fun s : aux_dyadicInterval k ↦ a s) r (M + 1) c.1 c.2
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hpos : 0 ≤ r := hrpos.le
  have hne : r ≠ 0 := ne_of_gt hrpos
  have hp := ENNReal.rpow_le_rpow hc hpos
  rw [show (∑ j : Fin (M + 1),
      (‖(fun s : aux_dyadicInterval k ↦ a s) (c.1 j.succ) -
        (fun s : aux_dyadicInterval k ↦ a s) (c.1 j.castSucc)‖₊ : ℝ≥0∞) ^ r) =
      (‖a x - a ((2 : ℝ) ^ k)‖₊ : ℝ≥0∞) ^ r by
        simpa [c] using aux_dyadicPair_sum (M := M) (k := k) a r hrpos x] at hp
  simpa [ENNReal.rpow_inv_rpow hne] using hp
end Auto
