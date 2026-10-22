-- Prove2me | solution 1 for AddLogReg.Multiclass.two_class_reduces
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:19:59.234899+00:00
-- url     : https://prove2.me/submissions/e435aad5-fb94-4d2f-b676-c6ff7b5331f2

import Mathlib
import Definitions.Def_AddLogReg_Multiclass_Setting
set_option autoImplicit false
open MeasureTheory ProbabilityTheory ENNReal
open AddLogReg.Multiclass

theorem solution {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Fin 2)) [IsProbabilityMeasure ν] (F : X → Fin 2 → ℝ) (x : X)
    (hF : F x 0 + F x 1 = 0) :
    softmax (F x) 0 = Real.exp (F x 0) / (Real.exp (F x 0) + Real.exp (-F x 0)) ∧
      logitBoostJStep ν F x 0 =
        F x 0 + (1 / 2) * wCondExpBy ν (fun x' _ => classWeight F x' 0)
          (fun x' y => workingResponse F x' y 0) x ∧
      logitBoostJStep ν F x 1 = -logitBoostJStep ν F x 0 := by
  have hF1 : F x 1 = -F x 0 := by linarith
  have hsm0 : softmax (F x) 0 = Real.exp (F x 0) / (Real.exp (F x 0) + Real.exp (-F x 0)) := by
    unfold softmax
    rw [Fin.sum_univ_two, hF1]
  have hsm1 : softmax (F x) 1 = 1 - softmax (F x) 0 := by
    unfold softmax
    rw [Fin.sum_univ_two]
    have : 0 < Real.exp (F x 0) + Real.exp (F x 1) := by positivity
    field_simp
    ring
  have hys : ∀ y : Fin 2, ystar y 1 = 1 - ystar y 0 := by
    intro y; fin_cases y <;> simp [ystar]
  have hw : classWeight F x 1 = classWeight F x 0 := by
    unfold classWeight; rw [hsm1]; ring
  have hz : ∀ y : Fin 2, workingResponse F x y 1 = - workingResponse F x y 0 := by
    intro y
    unfold workingResponse
    rw [hys, hsm1]
    have : (1 - softmax (F x) 0) * (1 - (1 - softmax (F x) 0)) = softmax (F x) 0 * (1 - softmax (F x) 0) := by ring
    rw [this, ← neg_div]
    congr 1; ring
  have hu : wCondExpBy ν (fun x' _ => classWeight F x' 1) (fun x' y => workingResponse F x' y 1) x
      = - wCondExpBy ν (fun x' _ => classWeight F x' 0) (fun x' y => workingResponse F x' y 0) x := by
    unfold wCondExpBy
    simp only [hw, hz, mul_neg, integral_neg, neg_div]
  refine ⟨hsm0, ?_, ?_⟩
  · unfold logitBoostJStep
    simp only [Fin.sum_univ_two, hu]
    push_cast
    ring
  · unfold logitBoostJStep
    simp only [Fin.sum_univ_two, hu, hF1]
    push_cast
    ring
