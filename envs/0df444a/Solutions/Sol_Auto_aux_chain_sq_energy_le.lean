-- Prove2me | solution 1 for Auto.aux_chain_sq_energy_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:00:32.431983+00:00
-- url     : https://prove2.me/submissions/f63ea8a4-3bf2-410c-9472-50af45cd4c3f

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
public import Theorems.Thm_Auto_aux_sum_lintegral_Ioc_le
public import Theorems.Thm_Auto_aux_pair_sq_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {J : ℕ} {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ 1 a (Set.Icc α β))
    (t : Fin (J + 1) → Set.Icc α β) (ht : Monotone t) :
    (∑ j : Fin J, ‖a (t j.succ) - a (t j.castSucc)‖ₑ ^ (2 : ℝ)) ≤
      ENNReal.ofReal ((β - α) / α) *
        ∫⁻ x in Set.Icc α β, ‖x * deriv a x‖ₑ ^ (2 : ℝ)
          ∂aux_logarithmicMeasure α β := by
  let : NullSingletonClass (aux_logarithmicMeasure α β) := by
    unfold aux_logarithmicMeasure
    infer_instance
  have ht' : Monotone (fun j ↦ (t j : ℝ)) := fun i j hij ↦ ht hij
  calc
    (∑ j : Fin J, ‖a (t j.succ) - a (t j.castSucc)‖ₑ ^ (2 : ℝ)) ≤
        ∑ j : Fin J, ENNReal.ofReal ((β - α) / α) *
          ∫⁻ x in Set.Icc (t j.castSucc : ℝ) (t j.succ : ℝ),
            ‖x * deriv a x‖ₑ ^ (2 : ℝ) ∂aux_logarithmicMeasure α β := by
      apply Finset.sum_le_sum
      intro j _
      exact aux_pair_sq_le hα hαβ (t j.castSucc).2 (t j.succ).2
        (ht (Fin.castSucc_le_succ j)) a ha
    _ = ENNReal.ofReal ((β - α) / α) *
        ∑ j : Fin J, ∫⁻ x in Set.Icc (t j.castSucc : ℝ) (t j.succ : ℝ),
          ‖x * deriv a x‖ₑ ^ (2 : ℝ) ∂aux_logarithmicMeasure α β := by
      rw [Finset.mul_sum]
    _ = ENNReal.ofReal ((β - α) / α) *
        ∑ j : Fin J, ∫⁻ x in Set.Ioc (t j.castSucc : ℝ) (t j.succ : ℝ),
          ‖x * deriv a x‖ₑ ^ (2 : ℝ) ∂aux_logarithmicMeasure α β := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [← restrict_Ioc_eq_restrict_Icc]
    _ ≤ ENNReal.ofReal ((β - α) / α) *
        ∫⁻ x in Set.Icc α β, ‖x * deriv a x‖ₑ ^ (2 : ℝ)
          ∂aux_logarithmicMeasure α β := by
      gcongr
      exact aux_sum_lintegral_Ioc_le (fun j ↦ (t j : ℝ)) ht'
        (fun x ↦ ‖x * deriv a x‖ₑ ^ (2 : ℝ)) (t 0).2.1 (t (Fin.last J)).2.2
end Auto
