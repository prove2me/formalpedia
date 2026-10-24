-- Prove2me | solution 1 for ArapostathisAC.RossReduction.modified_exists
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T19:35:50.908847+00:00
-- url     : https://prove2.me/submissions/b88ebafe-ef6d-450d-b341-bc7bf76d2d57

import Init
import Mathlib
import Definitions.Def_ArapostathisAC_RossReduction_CMP

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section
namespace RossResidual
lemma atom_le (μ : Measure ℕ) (a : ℝ≥0∞) (ha : a ≤ μ {0}) :
    a • Measure.dirac 0 ≤ μ := by
  intro s
  by_cases h : 0 ∈ s
  · simpa [Measure.smul_apply, Measure.dirac_apply_of_mem h] using
      ha.trans (measure_mono (singleton_subset_iff.mpr h))
  · simp [Measure.smul_apply, Measure.dirac_apply, h]

def residual {X : Type*} [MeasurableSpace X] (P : Kernel X ℕ) (a : ℝ≥0∞) : X → Measure ℕ :=
  fun x => if a ≤ P x {0} then (1-a)⁻¹ • (P x - a • Measure.dirac 0) else P x

lemma residual_apply {X : Type*} [MeasurableSpace X] (P : Kernel X ℕ) (a : ℝ≥0∞)
    (ha : a ≠ ∞) (x : X) (s : Set ℕ) :
    residual P a x s = if a ≤ P x {0} then (1-a)⁻¹ * (P x s - a * Measure.dirac 0 s) else P x s := by
  classical
  letI : IsFiniteMeasure (a • Measure.dirac (0 : ℕ)) := ⟨by simp [ha.lt_top]⟩
  by_cases h : a ≤ P x {0}
  · simp [residual, h, Measure.smul_apply, Measure.sub_apply ((Set.to_countable s).measurableSet) (atom_le _ _ h)]
  · simp [residual, h]

def kernel {X : Type*} [MeasurableSpace X] (P : Kernel X ℕ) (a : ℝ≥0∞)
    (ha : a ≠ ∞) : Kernel X ℕ where
  toFun := residual P a
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [residual_apply P a ha]
    exact Measurable.ite (measurableSet_le measurable_const (P.measurable_coe (measurableSet_singleton 0)))
      (measurable_const.mul ((P.measurable_coe hs).sub measurable_const)) (P.measurable_coe hs)

lemma markov {X : Type*} [MeasurableSpace X] (P : Kernel X ℕ) [IsMarkovKernel P]
    (a : ℝ≥0∞) (ha : a < 1) : IsMarkovKernel (kernel P a (ha.trans_le le_top).ne) := by
  constructor
  intro x
  constructor
  change residual P a x univ = 1
  rw [residual_apply P a (ha.trans_le le_top).ne]
  split_ifs
  · simp only [measure_univ, Measure.dirac_apply_of_mem (mem_univ _), mul_one]
    exact ENNReal.inv_mul_cancel (tsub_pos_iff_lt.mpr ha).ne' (by finiteness)
  · exact measure_univ
end RossResidual

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section
namespace RossResidual
open ArapostathisAC.RossReduction
lemma probability {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hP : ∀ i, ∀ a ∈ M.U i, α ≤ prob M i a 0)
    (i : ℕ) (a : A) (ha : a ∈ M.U i) (j : ℕ) :
    ((kernel M.P (ENNReal.ofReal α) ENNReal.ofReal_ne_top) (i,a) {j}).toReal =
      (prob M i a j - if j = 0 then α else 0) / (1-α) := by
  have h : ENNReal.ofReal α ≤ M.P (i,a) {0} :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr (hP i a ha)
  change (residual M.P (ENNReal.ofReal α) (i,a) {j}).toReal = _
  rw [residual_apply M.P _ ENNReal.ofReal_ne_top, if_pos h]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_sub_of_le (ENNReal.ofReal_lt_one.mpr hα1).le ENNReal.one_ne_top]
  simp only [ENNReal.toReal_one, ENNReal.toReal_ofReal hα.le]
  by_cases hj : j = 0
  · subst j
    simp only [Measure.dirac_apply_of_mem (mem_singleton 0), mul_one, if_true]
    rw [ENNReal.toReal_sub_of_le h (measure_ne_top _ _), ENNReal.toReal_ofReal hα.le]
    simp [prob, div_eq_mul_inv, mul_comm]
  · simp [Measure.dirac_apply, hj, Ne.symm hj, prob, div_eq_mul_inv, mul_comm]
end RossResidual

open ArapostathisAC.RossReduction
 theorem solution {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hP : ∀ i, ∀ a ∈ M.U i, α ≤ prob M i a 0) :
    ∃ M' : CMP A, ModifiedLaw M M' α := by
  let K := RossResidual.kernel M.P (ENNReal.ofReal α) ENNReal.ofReal_ne_top
  letI : IsMarkovKernel K := RossResidual.markov M.P _ (ENNReal.ofReal_lt_one.mpr hα1)
  have hp := RossResidual.probability M α hα hα1 hP
  let M' : CMP A := {
    U := M.U
    U_nonempty := M.U_nonempty
    U_compact := M.U_compact
    c := M.c
    c_meas := M.c_meas
    c_nonneg := M.c_nonneg
    P := K
    c_cont := M.c_cont
    P_cont := by
      intro i j
      apply ContinuousOn.congr ((M.P_cont i j).sub continuousOn_const |>.div_const (1-α))
      intro a ha
      exact hp i a ha j
  }
  exact ⟨M', rfl, fun _ _ _ => rfl, hp⟩
