-- Prove2me | solution 1 for Auto.aux_dyadicLocal_sum_le_variation_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:42:04.340153+00:00
-- url     : https://prove2.me/submissions/0423a248-9415-4159-bd49-bfe4e356f60f

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
public import Theorems.Thm_Auto_aux_chainVariation_le
public import Theorems.Thm_Auto_aux_dyadicLocalChain_mono

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {B : Type*} [SeminormedAddCommGroup B]
    {J : ℕ} {k : ℤ} {t : Fin (J + 1) → ℝ} (ht : Monotone t)
    (a : ℝ → B) (r : ℝ) (hr : 1 ≤ r) :
    (∑ j : Fin J,
      (‖a (aux_dyadicLocalChain J k t j.succ) -
        a (aux_dyadicLocalChain J k t j.castSucc)‖₊ : ℝ≥0∞) ^ r) ≤
      (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r := by
  let c : {u : Fin (J + 1) → aux_dyadicInterval k // Monotone u} :=
    ⟨aux_dyadicLocalChain J k t, aux_dyadicLocalChain_mono ht⟩
  have hc := aux_chainVariation_le (fun s : aux_dyadicInterval k ↦ a s) r J c.1 c.2
  have hpos : 0 ≤ r := le_trans zero_le_one hr
  have hne : r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr)
  have hp := ENNReal.rpow_le_rpow hc hpos
  simpa [c, ENNReal.rpow_inv_rpow hne] using hp
end Auto
