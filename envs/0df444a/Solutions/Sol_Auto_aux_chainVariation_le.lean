-- Prove2me | solution 1 for Auto.aux_chainVariation_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:38:19.541944+00:00
-- url     : https://prove2.me/submissions/04b66bab-3d9c-4803-b1fc-f77b5f9d6b03

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {B : Type*} [SeminormedAddCommGroup B]
    {I : Set ℝ} (a : I → B) (r : ℝ) (J : ℕ)
    (t : Fin (J + 1) → I) (ht : Monotone t) :
    (∑ j : Fin J,
      (‖a (t j.succ) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ r) ^ r⁻¹ ≤
        finiteVariationSeminorm a r J := by
  exact le_iSup (fun t : {u : Fin (J + 1) → I // Monotone u} ↦
    (∑ j : Fin J,
      (‖a (t.1 j.succ) - a (t.1 j.castSucc)‖₊ : ℝ≥0∞) ^ r) ^ r⁻¹) ⟨t, ht⟩
end Auto
