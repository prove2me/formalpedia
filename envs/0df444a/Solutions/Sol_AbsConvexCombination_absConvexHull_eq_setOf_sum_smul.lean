-- Prove2me | solution 1 for AbsConvexCombination.absConvexHull_eq_setOf_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:47:26.239048+00:00
-- url     : https://prove2.me/submissions/506f9d79-ebec-4336-b761-059c203a12b9

import Mathlib

open scoped ComplexOrder

set_option autoImplicit false

namespace Sol_AbsConvexCombination_absConvexHull_eq_setOf_sum_smul

/-- The set of finite absolutely convex combinations of points of `s` (with at least one term). -/
def T (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] (s : Set E) : Set E :=
  {y : E | ∃ (n : ℕ) (c : Fin n → 𝕜) (x : Fin n → E), 0 < n ∧ (∀ i, x i ∈ s) ∧
    ∑ i, ‖c i‖ ≤ 1 ∧ y = ∑ i, c i • x i}

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]

lemma subset_T (s : Set E) : s ⊆ T 𝕜 E s := by
  intro y hy
  refine ⟨1, fun _ => 1, fun _ => y, Nat.one_pos, fun _ => hy, ?_, ?_⟩
  · simp
  · simp

lemma balanced_T (s : Set E) : Balanced 𝕜 (T 𝕜 E s) := by
  rw [balanced_iff_smul_mem]
  rintro a ha y ⟨n, c, x, hn, hx, hc, rfl⟩
  refine ⟨n, fun i => a * c i, x, hn, hx, ?_, ?_⟩
  · calc ∑ i, ‖a * c i‖ = ‖a‖ * ∑ i, ‖c i‖ := by
          simp only [norm_mul, Finset.mul_sum]
      _ ≤ 1 := mul_le_one₀ ha (Finset.sum_nonneg fun i _ => norm_nonneg _) hc
  · simp only [Finset.smul_sum, smul_smul]

lemma convex_T (s : Set E) : Convex 𝕜 (T 𝕜 E s) := by
  rintro y ⟨n, c, x, hn, hx, hc, rfl⟩ z ⟨m, d, w, hm, hw, hd, rfl⟩ a b ha hb hab
  have hab' : ‖a‖ + ‖b‖ = 1 := by
    have h1 : ((‖a‖ + ‖b‖ : ℝ) : 𝕜) = 1 := by
      rw [RCLike.ofReal_add, RCLike.norm_of_nonneg' ha, RCLike.norm_of_nonneg' hb, hab]
    exact_mod_cast h1
  refine ⟨n + m, Fin.append (fun i => a * c i) (fun j => b * d j), Fin.append x w,
    Nat.add_pos_left hn m, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact hx i
    · rw [Fin.append_right]; exact hw j
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, norm_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    calc ‖a‖ * ∑ i, ‖c i‖ + ‖b‖ * ∑ j, ‖d j‖ ≤ ‖a‖ * 1 + ‖b‖ * 1 := by
          gcongr
      _ = 1 := by rw [mul_one, mul_one, hab']
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Finset.smul_sum, smul_smul]

lemma T_subset (s : Set E) : T 𝕜 E s ⊆ absConvexHull 𝕜 s := by
  rintro y ⟨n, c, x, hn, hx, hc, rfl⟩
  set D := absConvexHull 𝕜 s
  have hDb : Balanced 𝕜 D := balanced_absConvexHull
  have hDc : Convex 𝕜 D := convex_absConvexHull
  have hsD : s ⊆ D := subset_absConvexHull
  have hD0 : (0 : E) ∈ D := hDb.zero_mem ⟨x ⟨0, hn⟩, hsD (hx _)⟩
  set S : ℝ := ∑ i, ‖c i‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => norm_nonneg _
  rcases hS0.eq_or_lt with hS0' | hSpos
  · -- all coefficients vanish
    have hci : ∀ i, c i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => norm_nonneg (c i))).1 hS0'.symm i
        (Finset.mem_univ i)
      exact norm_eq_zero.1 this
    simp only [hci, zero_smul, Finset.sum_const_zero]
    exact hD0
  · -- normalize: z i = (c i / ‖c i‖) • x i ∈ D, weights ‖c i‖ / S
    set z : Fin n → E := fun i => (c i / (‖c i‖ : 𝕜)) • x i with hz
    have hzD : ∀ i, z i ∈ D := by
      intro i
      refine hDb.smul_mem ?_ (hsD (hx i))
      by_cases hci : c i = 0
      · simp [hci]
      · rw [norm_div, RCLike.norm_ofReal, abs_norm, div_self (norm_ne_zero_iff.2 hci)]
    have hcz : ∀ i, (‖c i‖ : 𝕜) • z i = c i • x i := by
      intro i
      simp only [hz, smul_smul]
      by_cases hci : c i = 0
      · simp [hci]
      · rw [mul_div_cancel₀ _ (RCLike.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hci))]
    have hmem : ∑ i, ((‖c i‖ / S : ℝ) : 𝕜) • z i ∈ D := by
      -- view `E` as a real vector space by restriction of scalars, where `D` is convex
      let _ : Module ℝ E := Module.compHom E (algebraMap ℝ 𝕜)
      have hDR : Convex ℝ D := by
        intro p hp q hq a b ha hb hab
        have hab' : (a : 𝕜) + (b : 𝕜) = 1 := by
          rw [← RCLike.ofReal_add, hab, RCLike.ofReal_one]
        exact hDc hp hq (RCLike.ofReal_nonneg.2 ha) (RCLike.ofReal_nonneg.2 hb) hab'
      have h1 : ∑ i, ‖c i‖ / S = 1 := by
        rw [← Finset.sum_div, ← hS, div_self hSpos.ne']
      exact hDR.sum_mem (t := Finset.univ) (w := fun i => ‖c i‖ / S)
        (fun i _ => div_nonneg (norm_nonneg _) hS0) h1 (fun i _ => hzD i)
    have hnorm : ‖((S : ℝ) : 𝕜)‖ ≤ 1 := by
      rw [RCLike.norm_of_nonneg hS0]; exact hc
    have key := hDb.smul_mem hnorm hmem
    have heq : ((S : ℝ) : 𝕜) • ∑ i, ((‖c i‖ / S : ℝ) : 𝕜) • z i = ∑ i, c i • x i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← RCLike.ofReal_mul, mul_div_cancel₀ _ hSpos.ne', hcz i]
    rw [← heq]
    exact key

end Sol_AbsConvexCombination_absConvexHull_eq_setOf_sum_smul

open Sol_AbsConvexCombination_absConvexHull_eq_setOf_sum_smul in
theorem solution (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (s : Set E) :
    absConvexHull 𝕜 s =
      {y : E | ∃ (n : ℕ) (c : Fin n → 𝕜) (x : Fin n → E), 0 < n ∧ (∀ i, x i ∈ s) ∧
        ∑ i, ‖c i‖ ≤ 1 ∧ y = ∑ i, c i • x i} := by
  apply Set.Subset.antisymm
  · exact absConvexHull_min (subset_T s) ⟨balanced_T s, convex_T s⟩
  · exact T_subset s
