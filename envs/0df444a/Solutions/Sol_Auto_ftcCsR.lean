-- Prove2me | solution 1 for Auto.ftcCsR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:03:43.280204+00:00
-- url     : https://prove2.me/submissions/3fa67a60-a6ee-4b7e-9437-8d09f5017932

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
public import Theorems.Thm_Auto_aux_chain_first_ftc
public import Theorems.Thm_Auto_aux_second_ftcCsR

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution (J : ℕ) {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ 1 a (Set.Icc α β)) :
    finiteVariationSeminorm (fun t : Set.Icc α β ↦ a t) 2 J ≤
      (ENNReal.ofReal ((β - α) / α)) ^ ((2 : ℝ)⁻¹) *
        aux_logarithmicL2 α β (fun t ↦ t * deriv a t) ∧
    (finiteVariationSeminorm (fun t : Set.Icc α β ↦ a t) 2 J) ^ (2 : ℝ) ≤
      8 * aux_logarithmicL2 α β a *
        aux_logarithmicL2 α β (fun t ↦ t * deriv a t) := by
  constructor
  · unfold finiteVariationSeminorm
    apply iSup_le
    intro t
    exact aux_chain_first_ftc hα hαβ a ha t.1 t.2
  · exact aux_second_ftcCsR hα a ha
end Auto
