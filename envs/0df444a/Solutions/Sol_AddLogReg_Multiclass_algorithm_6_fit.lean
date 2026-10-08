-- Prove2me | solution 1 for AddLogReg.Multiclass.algorithm_6_fit
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:15:43.573869+00:00
-- url     : https://prove2.me/submissions/da4206e3-f516-448a-bea7-54fba4b4e77e

import Mathlib
import Definitions.Def_AddLogReg_Multiclass_Setting

open MeasureTheory ProbabilityTheory ENNReal

open AddLogReg.Multiclass

theorem AddLogReg.Multiclass.algorithm_6_fit {J : ℕ} [NeZero J] (hJ : 2 ≤ J) {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Fin J)) [IsProbabilityMeasure ν] (F : X → Fin J → ℝ) (x : X) (j : Fin J) :
    wCondExpBy ν (fun x' _ => classWeight F x' j) (fun x' y => workingResponse F x' y j) x =
      (∫ y, (ystar y j - softmax (F x) j) ∂(ν.condKernel x)) /
        (softmax (F x) j * (1 - softmax (F x) j)) := by
  classical
  have hZ : 0 < ∑ k, Real.exp (F x k) :=
    Finset.sum_pos (fun k _ => Real.exp_pos _) Finset.univ_nonempty
  have hcard : 1 < Fintype.card (Fin J) := by simpa using (show 1 < J by omega)
  obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card hcard j
  have hlt : Real.exp (F x j) < ∑ k, Real.exp (F x k) :=
    Finset.single_lt_sum hk (Finset.mem_univ j) (Finset.mem_univ k)
      (Real.exp_pos _) (fun i _ _ => le_of_lt (Real.exp_pos _))
  have hp : 0 < softmax (F x) j := div_pos (Real.exp_pos _) hZ
  have hp1 : softmax (F x) j < 1 := (div_lt_one hZ).2 hlt
  have hw : softmax (F x) j * (1 - softmax (F x) j) ≠ 0 :=
    ne_of_gt (mul_pos hp (sub_pos.mpr hp1))
  unfold wCondExpBy classWeight workingResponse
  have he (y : Fin J) :
      softmax (F x) j * (1 - softmax (F x) j) *
        ((ystar y j - softmax (F x) j) /
          (softmax (F x) j * (1 - softmax (F x) j))) =
        ystar y j - softmax (F x) j := by
    exact mul_div_cancel₀ _ hw
  simp_rw [he]
  simp

theorem solution {J : ℕ} [NeZero J] (hJ : 2 ≤ J) {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Fin J)) [IsProbabilityMeasure ν] (F : X → Fin J → ℝ) (x : X) (j : Fin J) :
    wCondExpBy ν (fun x' _ => classWeight F x' j) (fun x' y => workingResponse F x' y j) x =
      (∫ y, (ystar y j - softmax (F x) j) ∂(ν.condKernel x)) /
        (softmax (F x) j * (1 - softmax (F x) j)) := AddLogReg.Multiclass.algorithm_6_fit hJ ν F x j

#print axioms solution
