-- Prove2me | solution 1 for AddLogReg.Multiclass.result_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T15:33:43.089993+00:00
-- url     : https://prove2.me/submissions/6443293e-ec60-4fba-b028-dde9ee220069

import Mathlib
import Definitions.Def_AddLogReg_Multiclass_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ENNReal

namespace AddLogReg.Multiclass.P99

variable {J : ℕ} [NeZero J] {X : Type*} [MeasurableSpace X]

lemma integ (μ : Measure (Fin J)) [IsFiniteMeasure μ] (f : Fin J → ℝ) : Integrable f μ :=
  Integrable.of_finite

lemma baseLogLik_eq (ν : Measure (X × Fin J)) [IsFiniteMeasure ν] (F : X → Fin J → ℝ) (x : X)
    (b : Fin J) (g : Fin J → ℝ) :
    baseLogLik ν F x b g =
      ∑ i ∈ Finset.univ.erase b, (∫ y, ystar y i ∂(ν.condKernel x)) * (F x i - F x b + g i) -
        Real.log (1 + ∑ k ∈ Finset.univ.erase b, Real.exp (F x k - F x b + g k)) := by
  unfold baseLogLik logLik
  rw [integral_sub (integ _ _) (integ _ _), integral_finsetSum _ (fun i _ => integ _ _)]
  simp [integral_mul_const]

lemma hasDerivAt_upd (c : Fin J → ℝ) (j i : Fin J) (t0 : ℝ) :
    HasDerivAt (fun t : ℝ => Function.update c j (c j + t) i) (if i = j then 1 else 0) t0 := by
  by_cases h : i = j
  · subst h; simp only [Function.update_self, if_true]; exact (hasDerivAt_id' t0).const_add _
  · simp only [Function.update_of_ne h, if_neg h]; exact hasDerivAt_const _ _

lemma sumExp_pos (F : X → Fin J → ℝ) (x : X) : 0 < ∑ k, Real.exp (F x k) :=
  Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

lemma hS (F : X → Fin J → ℝ) (x : X) (b : Fin J) :
    1 + ∑ k ∈ Finset.univ.erase b, Real.exp (F x k - F x b) =
      (∑ k, Real.exp (F x k)) / Real.exp (F x b) := by
  have h := Finset.add_sum_erase Finset.univ (fun k => Real.exp (F x k - F x b)) (Finset.mem_univ b)
  simp only [sub_self, Real.exp_zero] at h
  rw [h, Finset.sum_div]
  simp [Real.exp_sub]

lemma part1b (ν : Measure (X × Fin J)) [IsFiniteMeasure ν] (F : X → Fin J → ℝ) (x : X)
    (b j : Fin J) (hj : j ≠ b) (g : Fin J → ℝ) :
    HasDerivAt (fun t : ℝ => baseLogLik ν F x b (Function.update g j (g j + t)))
      (gradBase ν F x b g j) 0 := by
  simp only [baseLogLik_eq]
  have hjm : j ∈ Finset.univ.erase b := Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩
  have h1 : HasDerivAt (fun t : ℝ => ∑ i ∈ Finset.univ.erase b,
      (∫ y, ystar y i ∂(ν.condKernel x)) * (F x i - F x b + Function.update g j (g j + t) i))
      (∑ i ∈ Finset.univ.erase b, (∫ y, ystar y i ∂(ν.condKernel x)) * (if i = j then 1 else 0)) 0 :=
    HasDerivAt.fun_sum (fun i _ =>
      ((hasDerivAt_upd g j i 0).const_add (F x i - F x b)).const_mul _)
  have h2 : HasDerivAt (fun t : ℝ => 1 + ∑ k ∈ Finset.univ.erase b,
      Real.exp (F x k - F x b + Function.update g j (g j + t) k))
      (∑ k ∈ Finset.univ.erase b, Real.exp (F x k - F x b + Function.update g j (g j + 0) k) *
        (if k = j then 1 else 0)) 0 :=
    (HasDerivAt.fun_sum (fun k _ => ((hasDerivAt_upd g j k 0).const_add (F x k - F x b)).exp)).const_add 1
  have hpos : (1 + ∑ k ∈ Finset.univ.erase b,
      Real.exp (F x k - F x b + Function.update g j (g j + 0) k)) ≠ 0 := by positivity
  refine (h1.sub (h2.log hpos)).congr_deriv ?_
  simp [gradBase, Finset.sum_ite_eq', hjm]

lemma gradBase_zero (ν : Measure (X × Fin J)) [IsFiniteMeasure ν] (F : X → Fin J → ℝ) (x : X)
    (b j : Fin J) : gradBase ν F x b 0 j = score ν F x j := by
  unfold gradBase score
  rw [integral_sub (integ _ _) (integ _ _), integral_const]
  simp only [Pi.zero_apply, add_zero]
  rw [hS]
  unfold softmax
  rw [Real.exp_sub, div_div_div_cancel_right₀ (Real.exp_pos (F x b)).ne']
  simp

lemma part1c (ν : Measure (X × Fin J)) [IsFiniteMeasure ν] (F : X → Fin J → ℝ) (x : X)
    (b j k : Fin J) (hk : k ≠ b) :
    HasDerivAt (fun t : ℝ => gradBase ν F x b (Function.update 0 k t) j) (hess F x j k) 0 := by
  have hkm : k ∈ Finset.univ.erase b := Finset.mem_erase.2 ⟨hk, Finset.mem_univ _⟩
  have hN : HasDerivAt (fun t : ℝ => Real.exp (F x j - F x b +
      Function.update (0 : Fin J → ℝ) k ((0 : Fin J → ℝ) k + t) j))
      (Real.exp (F x j - F x b + Function.update (0 : Fin J → ℝ) k ((0 : Fin J → ℝ) k + 0) j) *
        (if j = k then 1 else 0)) 0 :=
    ((hasDerivAt_upd 0 k j 0).const_add _).exp
  have hD : HasDerivAt (fun t : ℝ => 1 + ∑ i ∈ Finset.univ.erase b,
      Real.exp (F x i - F x b + Function.update (0 : Fin J → ℝ) k ((0 : Fin J → ℝ) k + t) i))
      (∑ i ∈ Finset.univ.erase b,
        Real.exp (F x i - F x b + Function.update (0 : Fin J → ℝ) k ((0 : Fin J → ℝ) k + 0) i) *
        (if i = k then 1 else 0)) 0 :=
    (HasDerivAt.fun_sum (fun i _ => ((hasDerivAt_upd 0 k i 0).const_add (F x i - F x b)).exp)).const_add 1
  have hpos : (1 + ∑ i ∈ Finset.univ.erase b,
      Real.exp (F x i - F x b + Function.update (0 : Fin J → ℝ) k ((0 : Fin J → ℝ) k + 0) i)) ≠ 0 := by
    positivity
  have h := (hasDerivAt_const (0 : ℝ) (∫ y, ystar y j ∂(ν.condKernel x))).sub (hN.div hD hpos)
  have key : HasDerivAt (fun t : ℝ => gradBase ν F x b
      (Function.update (0 : Fin J → ℝ) k ((0 : Fin J → ℝ) k + t)) j) (hess F x j k) 0 := by
    refine h.congr_deriv ?_
    have hz : Function.update (0 : Fin J → ℝ) k ((0 : Fin J → ℝ) k + 0) = 0 := by
      ext i; simp [Function.update_apply]
    rw [hz]
    simp only [Pi.zero_apply, add_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', hkm, if_true]
    rw [hS]
    have hE := Real.exp_pos (F x b)
    have hT := sumExp_pos F x
    unfold hess softmax
    simp only [Real.exp_sub]
    split_ifs with hjk
    · subst hjk; field_simp; ring
    · field_simp; ring
  simp only [Pi.zero_apply, zero_add] at key
  exact key

lemma softmax_pos (F : X → Fin J → ℝ) (x : X) (j : Fin J) : 0 < softmax (F x) j :=
  div_pos (Real.exp_pos _) (sumExp_pos F x)

lemma softmax_lt_one (hJ : 2 ≤ J) (F : X → Fin J → ℝ) (x : X) (j : Fin J) : softmax (F x) j < 1 := by
  unfold softmax
  rw [div_lt_one (sumExp_pos F x)]
  have hne : (Finset.univ.erase j).Nonempty := Finset.card_pos.1 (by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]; omega)
  have h := Finset.add_sum_erase Finset.univ (fun k => Real.exp (F x k)) (Finset.mem_univ j)
  have hp : 0 < ∑ k ∈ Finset.univ.erase j, Real.exp (F x k) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) hne
  linarith

lemma hess_ne (hJ : 2 ≤ J) (F : X → Fin J → ℝ) (x : X) (j : Fin J) : hess F x j j ≠ 0 := by
  unfold hess
  rw [if_pos rfl, neg_ne_zero]
  exact mul_ne_zero (softmax_pos F x j).ne' (sub_ne_zero.2 (softmax_lt_one hJ F x j).ne')

lemma part3 (ν : Measure (X × Fin J)) [IsFiniteMeasure ν] (F : X → Fin J → ℝ) (x : X)
    (b j : Fin J) (hj : j ≠ b) : diagStep ν F x b j =
      (∫ y, (ystar y j - softmax (F x) j) ∂(ν.condKernel x)) /
        (softmax (F x) j * (1 - softmax (F x) j)) := by
  rw [diagStep, if_neg hj, hess, if_pos rfl, neg_div_neg_eq]
  rfl

lemma part4 (hJ : 2 ≤ J) (ν : Measure (X × Fin J)) [IsFiniteMeasure ν] (F : X → Fin J → ℝ)
    (x : X) (j : Fin J) :
    logitBoostJStep ν F x j = F x j + (1 / (J : ℝ)) * ∑ b, symmetrize (diagStep ν F x b) j := by
  set d : Fin J → ℝ := fun i => (∫ y, (ystar y i - softmax (F x) i) ∂(ν.condKernel x)) /
        (softmax (F x) i * (1 - softmax (F x) i)) with hd
  have hu : ∀ i, wCondExpBy ν (fun x' _ => classWeight F x' i)
      (fun x' y => workingResponse F x' y i) x = d i := by
    intro i
    have hw : classWeight F x i ≠ 0 :=
      mul_ne_zero (softmax_pos F x i).ne' (sub_ne_zero.2 (softmax_lt_one hJ F x i).ne')
    unfold wCondExpBy workingResponse
    rw [integral_const_mul, integral_const, integral_div]
    simp only [probReal_univ, one_smul, hd]
    rw [mul_div_cancel_left₀ _ hw]
  have hD : ∀ b i, diagStep ν F x b i = d i - if i = b then d i else 0 := by
    intro b i
    by_cases h : i = b
    · subst h; simp [diagStep]
    · rw [part3 ν F x b i h, if_neg h, sub_zero]
  have hJ0 : (J : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ J := by exact_mod_cast hJ
    linarith
  simp only [logitBoostJStep, hu, symmetrize, hD]
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  field_simp

end AddLogReg.Multiclass.P99

open MeasureTheory ProbabilityTheory ENNReal AddLogReg.Multiclass in
theorem solution {J : ℕ} [NeZero J] (hJ : 2 ≤ J) {X : Type*} [MeasurableSpace X]
    (ν : Measure (X × Fin J)) [IsProbabilityMeasure ν] (F : X → Fin J → ℝ) (x : X) :
    (∀ b j, j ≠ b →
        HasDerivAt (fun t : ℝ => baseLogLik ν F x b (Function.update 0 j t)) (score ν F x j) 0 ∧
          (∀ g : Fin J → ℝ,
            HasDerivAt (fun t : ℝ => baseLogLik ν F x b (Function.update g j (g j + t)))
              (gradBase ν F x b g j) 0) ∧
          ∀ k, k ≠ b →
            HasDerivAt (fun t : ℝ => gradBase ν F x b (Function.update 0 k t) j) (hess F x j k) 0) ∧
      (∀ j, hess F x j j ≠ 0) ∧
      (∀ b j, j ≠ b → diagStep ν F x b j =
        (∫ y, (ystar y j - softmax (F x) j) ∂(ν.condKernel x)) /
          (softmax (F x) j * (1 - softmax (F x) j))) ∧
      ∀ j, logitBoostJStep ν F x j = F x j + (1 / (J : ℝ)) * ∑ b, symmetrize (diagStep ν F x b) j := by
  refine ⟨fun b j hj => ⟨?_, fun g => AddLogReg.Multiclass.P99.part1b ν F x b j hj g,
    fun k hk => AddLogReg.Multiclass.P99.part1c ν F x b j k hk⟩,
    fun j => AddLogReg.Multiclass.P99.hess_ne hJ F x j,
    fun b j hj => AddLogReg.Multiclass.P99.part3 ν F x b j hj,
    fun j => AddLogReg.Multiclass.P99.part4 hJ ν F x j⟩
  have h := AddLogReg.Multiclass.P99.part1b ν F x b j hj 0
  simp only [Pi.zero_apply, zero_add] at h
  rw [AddLogReg.Multiclass.P99.gradBase_zero] at h
  exact h
