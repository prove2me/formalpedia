-- Prove2me | solution 1 for AdaOGD.individual_convexity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:05:28.066026+00:00
-- url     : https://prove2.me/submissions/2e65eee0-cf0e-4c58-bd37-868c9d83b7e7

import Mathlib
import Definitions.Def_AdaOGD_ContinuousGame

open scoped InnerProductSpace

namespace AdaOGD.Aux_AO

open AdaOGD

variable {N : ℕ} {d : Fin N → ℕ}

theorem update_self' (x : Joint d) (i : Fin N) (y : EuclideanSpace ℝ (Fin (d i))) :
    (update x i y) i = y := by
  simp [update]

theorem update_ne' (x : Joint d) {i j : Fin N} (h : j ≠ i) (y : EuclideanSpace ℝ (Fin (d i))) :
    (update x i y) j = x j := by
  simp [update, Function.update_of_ne h]

theorem update_update' (x : Joint d) (i : Fin N) (y y' : EuclideanSpace ℝ (Fin (d i))) :
    update (update x i y) i y' = update x i y' := by
  simp [update]

theorem update_mem (X : ∀ i, Set (EuclideanSpace ℝ (Fin (d i)))) {x : Joint d}
    (hx : x ∈ jointSet X) (i : Fin N) {y : EuclideanSpace ℝ (Fin (d i))} (hy : y ∈ X i) :
    update x i y ∈ jointSet X := by
  intro j
  by_cases h : j = i
  · subst h; rw [update_self']; exact hy
  · rw [update_ne' x h]; exact hx j

end AdaOGD.Aux_AO

open AdaOGD AdaOGD.Aux_AO in
theorem solution {N : ℕ} {d : Fin N → ℕ} (G : ContinuousGame d) {β : ℝ}
    (hβ : 0 < β) (hmono : IsStronglyMonotone G β) :
    ∀ i : Fin N, ∀ x ∈ jointSet G.X, ConvexOn ℝ (G.X i) (fun y => G.u i (update x i y)) := by
  intro i x hx
  set f : EuclideanSpace ℝ (Fin (d i)) → ℝ := fun y => G.u i (update x i y) with hf
  -- monotonicity of the partial gradient
  have hL5 : ∀ y ∈ G.X i, ∀ y' ∈ G.X i,
      0 ≤ ⟪y' - y, G.v (update x i y') i - G.v (update x i y) i⟫_ℝ := by
    intro y hy y' hy'
    have h := hmono (update x i y) (update_mem G.X hx i hy) (update x i y')
      (update_mem G.X hx i hy')
    rw [PiLp.inner_apply] at h
    rw [Finset.sum_eq_single i] at h
    · simp only [PiLp.sub_apply, update_self'] at h
      have : 0 ≤ β * ‖update x i y' - update x i y‖ ^ 2 := by positivity
      linarith
    · intro j _ hj
      simp [PiLp.sub_apply, update_ne' x hj]
    · intro h; exact absurd (Finset.mem_univ i) h
  -- the partial gradient
  have hL6 : ∀ y ∈ G.X i, HasGradientWithinAt f (G.v (update x i y) i) (G.X i) y := by
    intro y hy
    have h := G.hasGradient (update x i y) (update_mem G.X hx i hy) i
    simp only [update_update', update_self'] at h
    exact h
  refine ⟨G.convex i, ?_⟩
  intro y0 hy0 y1 hy1 a b ha hb hab
  set L : ℝ → EuclideanSpace ℝ (Fin (d i)) := fun t => y0 + t • (y1 - y0) with hLdef
  have hLmaps : Set.MapsTo L (Set.Icc 0 1) (G.X i) := fun t ht =>
    (G.convex i).add_smul_sub_mem hy0 hy1 ht
  set g : ℝ → ℝ := fun t => ⟪G.v (update x i (L t)) i, y1 - y0⟫_ℝ with hg
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (f ∘ L) (g t) (Set.Icc 0 1) t := by
    intro t ht
    have h1 := (hL6 (L t) (hLmaps ht)).hasFDerivWithinAt
    have hL : HasDerivWithinAt L (y1 - y0) (Set.Icc 0 1) t := by
      have := ((hasDerivAt_id' t).smul_const (y1 - y0)).const_add y0
      rw [one_smul] at this
      exact this.hasDerivWithinAt
    have h2 := h1.comp_hasDerivWithinAt t hL hLmaps
    simpa [hg] using h2
  have hderivAt : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (f ∘ L) (g t) t := by
    intro t ht
    exact (hderiv t (Set.Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (f ∘ L) := by
    apply MonotoneOn.convexOn_of_deriv (convex_Icc 0 1)
    · exact fun t ht => (hderiv t ht).continuousWithinAt
    · rw [interior_Icc]
      exact fun t ht => (hderivAt t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs t ht hst
      rw [(hderivAt s hs).deriv, (hderivAt t ht).deriv]
      rcases hst.lt_or_eq with hlt | heq
      · have hm := hL5 (L s) (hLmaps (Set.Ioo_subset_Icc_self hs)) (L t)
          (hLmaps (Set.Ioo_subset_Icc_self ht))
        have hdiff : L t - L s = (t - s) • (y1 - y0) := by
          simp only [hLdef, sub_smul]; abel
        rw [hdiff, real_inner_smul_left] at hm
        have hts : 0 < t - s := by linarith
        have hm' : 0 ≤ ⟪y1 - y0, G.v (update x i (L t)) i - G.v (update x i (L s)) i⟫_ℝ := by
          by_contra hneg
          push_neg at hneg
          have := mul_neg_of_pos_of_neg hts hneg
          linarith
        rw [inner_sub_right, real_inner_comm _ (y1 - y0), real_inner_comm _ (y1 - y0)] at hm'
        simp only [hg]
        linarith
      · subst heq
        exact le_refl _
  have hab' : a = 1 - b := by linarith
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  have key := hconv.2 h0 h1 ha hb hab
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Function.comp_apply] at key
  have hL0 : L 0 = y0 := by simp [hLdef]
  have hL1 : L 1 = y1 := by simp [hLdef]
  have hLb : L b = a • y0 + b • y1 := by
    simp only [hLdef, hab', sub_smul, one_smul, smul_sub]
    abel
  rw [hL0, hL1, hLb] at key
  simpa [smul_eq_mul] using key
