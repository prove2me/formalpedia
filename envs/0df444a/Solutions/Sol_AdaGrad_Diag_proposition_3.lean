-- Prove2me | solution 1 for AdaGrad.Diag.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T08:43:22.449849+00:00
-- url     : https://prove2.me/submissions/b6de04a5-f9cd-4fc3-a01e-5e08c319a186

import Definitions.Def_AdaGrad_Diag_Setup

set_option autoImplicit false
open Filter Topology
open AdaGrad.Diag ShorNonsmooth.AlmostDiff

private lemma bregman_segment {d : ℕ} (h : Fin d → ℝ)
    (y u z : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    bregman h ((1-t) • y + t • u) z =
      (1-t) * bregman h y z + t * bregman h u z - t*(1-t)*bregman h u y := by
  simp only [bregman, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private lemma min_gap {d : ℕ} (η : ℝ) (hη : 0 ≤ η)
    (X : Set (EuclideanSpace ℝ (Fin d))) (hX : Convex ℝ X)
    (ϕ : EuclideanSpace ℝ (Fin d) → ℝ) (hϕ : ConvexOn ℝ Set.univ ϕ)
    (h : Fin d → ℝ) (g z y u : EuclideanSpace ℝ (Fin d))
    (hy : y ∈ X) (hu : u ∈ X)
    (hm : IsMinOn (fun v => η * inner ℝ g v + η * ϕ v + bregman h v z) X y) :
    bregman h u y ≤ (η * inner ℝ g u + η * ϕ u + bregman h u z) -
      (η * inner ℝ g y + η * ϕ y + bregman h y z) := by
  have hs : ∀ t : ℝ, 0 < t → t < 1 →
      (1-t)*bregman h u y ≤ (η * inner ℝ g u + η * ϕ u + bregman h u z) -
        (η * inner ℝ g y + η * ϕ y + bregman h y z) := by
    intro t ht ht1
    have ha : 0 ≤ 1-t := by linarith
    have hab : 1-t+t=1 := by ring
    have hv := hX hy hu ha ht.le hab
    have hmin := hm hv
    have hc := hϕ.2 (Set.mem_univ y) (Set.mem_univ u) ha ht.le hab
    have hcη := mul_le_mul_of_nonneg_left hc hη
    change η * inner ℝ g y + η * ϕ y + bregman h y z ≤
      η * inner ℝ g ((1-t) • y + t • u) + η * ϕ ((1-t) • y + t • u) +
        bregman h ((1-t) • y + t • u) z at hmin
    rw [bregman_segment] at hmin
    simp only [inner_add_right, inner_smul_right, smul_eq_mul] at hmin hcη
    nlinarith
  have hl : Tendsto (fun t : ℝ => (1-t)*bregman h u y) (𝓝[>] 0) (𝓝 (bregman h u y)) := by
    have hc : ContinuousAt (fun t : ℝ => (1-t)*bregman h u y) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin, (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    (Iio_mem_nhds (show (0:ℝ)<1 by norm_num))] with t ht ht1
  exact hs t ht ht1

private lemma coordinate_young (a b c η : ℝ) (ha : 0 ≤ a) (hz : a = 0 → b = 0) :
    η*b*c - a*c^2/2 ≤ η^2/2*(b^2/a) := by
  by_cases h0 : a = 0
  · simp [h0, hz h0]
  · have hp : 0 < a := lt_of_le_of_ne ha (Ne.symm h0)
    apply (mul_le_mul_iff_left₀ hp).mp
    field_simp
    nlinarith [sq_nonneg (a*c-η*b)]

private lemma weighted_young {d : ℕ} (h : Fin d → ℝ) (hh : ∀ i, 0 ≤ h i)
    (g y z : EuclideanSpace ℝ (Fin d)) (η : ℝ)
    (hz : ∀ i, h i = 0 → g i = 0) :
    η * inner ℝ g (z-y) - bregman h y z ≤ η^2/2 * dualNormSq h g := by
  simp only [PiLp.inner_apply, PiLp.sub_apply, RCLike.inner_apply, conj_trivial,
    bregman, dualNormSq]
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i hi
  convert coordinate_young (h i) (g i) (z i-y i) η (hh i) (hz i) using 1 <;> first | rfl | ring

private theorem one_step {d : ℕ} (η : ℝ) (hη : 0 < η) (X : Set (EuclideanSpace ℝ (Fin d)))
    (hXc : Convex ℝ X) (ϕ : EuclideanSpace ℝ (Fin d) → ℝ) (hϕ : ConvexOn ℝ Set.univ ϕ)
    (ft : EuclideanSpace ℝ (Fin d) → ℝ) (hft : ConvexOn ℝ Set.univ ft)
    (h : Fin d → ℝ) (hh : ∀ i, 0 ≤ h i)
    (xt xnext gt : EuclideanSpace ℝ (Fin d))
    (hhg : ∀ i, h i = 0 → gt i = 0)
    (hsub : IsSubgradient ft xt gt) (hmem : xnext ∈ X)
    (hmin : IsMinOn (fun y => η * inner ℝ gt y + η * ϕ y + bregman h y xt) X xnext)
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : xstar ∈ X) :
    η * (ft xt - ft xstar) + η * (ϕ xnext - ϕ xstar)
      ≤ bregman h xstar xt - bregman h xstar xnext + η ^ 2 / 2 * dualNormSq h gt := by
  have hm := min_gap η hη.le X hXc ϕ hϕ h gt xt xnext xstar hmem hxstar hmin
  have hy := weighted_young h hh gt xnext xt η hhg
  have hg := mul_le_mul_of_nonneg_left (hsub xstar) hη.le
  simp only [inner_sub_right] at hg hy
  linarith


private lemma diagonal_nonneg {d : ℕ} (h : Fin d → ℝ) (hh : ∀ i, 0 ≤ h i)
    (u v : EuclideanSpace ℝ (Fin d)) : 0 ≤ bregman h u v := by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => mul_nonneg (hh i) (sq_nonneg _)))

private lemma potential_telescope (B : ℕ → ℕ → ℝ) (T : ℕ) (hT : 1 ≤ T) :
    (∑ t ∈ Finset.Icc 1 T, (B t t - B t (t+1))) =
      B 1 1 - B T (T+1) + ∑ t ∈ Finset.Ico 1 T, (B (t+1) (t+1) - B t (t+1)) := by
  induction T, hT using Nat.le_induction with
  | base => simp
  | succ T hT ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ T+1), Finset.sum_Ico_succ_top hT, ih]
    ring

private lemma shift_telescope (a : ℕ → ℝ) (T : ℕ) :
    (∑ t ∈ Finset.Icc 1 T, (a (t+1)-a t)) = a (T+1)-a 1 := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ T+1), ih]
    ring

theorem solution {d : ℕ} (η : ℝ) (hη : 0 < η) (X : Set (EuclideanSpace ℝ (Fin d)))
    (hXc : Convex ℝ X) (hXcl : IsClosed X)
    (ϕ : EuclideanSpace ℝ (Fin d) → ℝ) (hϕ : ConvexOn ℝ Set.univ ϕ)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (hf : ∀ t, ConvexOn ℝ Set.univ (f t))
    (h : ℕ → Fin d → ℝ) (x g : ℕ → EuclideanSpace ℝ (Fin d))
    (hh : ∀ t, 1 ≤ t → ∀ i, 0 ≤ h t i)
    (hhg : ∀ t, 1 ≤ t → ∀ i, h t i = 0 → g t i = 0)
    (hrun : IsCompositeMDRun η X ϕ f h x g)
    (hx1 : x 1 ∈ X) (hϕx1 : ∀ y ∈ X, ϕ (x 1) ≤ ϕ y)
    (T : ℕ) (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : xstar ∈ X) :
    regret f ϕ x xstar T
      ≤ 1 / η * bregman (h 1) xstar (x 1)
        + 1 / η * ∑ t ∈ Finset.Ico 1 T,
            (bregman (h (t + 1)) xstar (x (t + 1)) - bregman (h t) xstar (x (t + 1)))
        + η / 2 * ∑ t ∈ Finset.Icc 1 T, dualNormSq (h t) (g t)  := by
  by_cases hT : T=0
  · subst T
    simpa [regret] using mul_nonneg (one_div_nonneg.mpr hη.le)
      (diagonal_nonneg (h 1) (hh 1 le_rfl) xstar (x 1))
  have hT1 : 1 ≤ T := by omega
  have hs := Finset.sum_le_sum (fun t (ht : t ∈ Finset.Icc 1 T) =>
    one_step η hη X hXc ϕ hϕ (f t) (hf t) (h t) (hh t (Finset.mem_Icc.mp ht).1)
      (x t) (x (t+1)) (g t) (hhg t (Finset.mem_Icc.mp ht).1)
      (hrun t (Finset.mem_Icc.mp ht).1).1 (hrun t (Finset.mem_Icc.mp ht).1).2.1
      (hrun t (Finset.mem_Icc.mp ht).1).2.2 xstar hxstar)
  have heq : (∑ t ∈ Finset.Icc 1 T,
      (η * (f t (x t)-f t xstar) + η * (ϕ (x (t+1))-ϕ xstar))) =
      η * regret f ϕ x xstar T + η * (ϕ (x (T+1))-ϕ (x 1)) := by
    rw [← shift_telescope (fun t => ϕ (x t)) T]
    simp only [regret, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [heq, Finset.sum_add_distrib, ← Finset.mul_sum,
    potential_telescope (fun t k => bregman (h t) xstar (x k)) T hT1] at hs
  have hb := diagonal_nonneg (h T) (hh T hT1) xstar (x (T+1))
  have hp := mul_nonneg hη.le (sub_nonneg.mpr (hϕx1 _ (hrun T hT1).2.1))
  apply (mul_le_mul_iff_right₀ hη).mp
  have hhη : η ≠ 0 := ne_of_gt hη
  field_simp
  nlinarith


