-- Prove2me | solution 1 for AdaGrad.Diag.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T10:40:55.554971+00:00
-- url     : https://prove2.me/submissions/4c5122a6-67ae-4288-86b5-b17287b5590e

/-
SPDX-License-Identifier: Apache-2.0
The quadratic-minimum and FTRL helpers below are extracted and adapted from
sometik179's accepted AdaGrad.Diag.theorem_5 proof, Prove2Me submission
7bc3e949-6b41-4a3d-a0dc-19d6fa9b66b2. This file exposes the native open
Proposition 2 milestone with positive, monotone diagonal weights.
Mathematical source: Duchi, Hazan and Singer, JMLR 12 (2011), Proposition 2,
Eq. (10), p. 2129, and Appendix F. The native definitions are unchanged.
-/
import Mathlib
import Definitions.Def_AdaGrad_Diag_Setup

open AdaGrad.Diag ShorNonsmooth.AlmostDiff
open scoped BigOperators

namespace P2MAdaGradDual
variable {d : ℕ}

lemma bregman_nonneg (h : Fin d → ℝ) (hh : ∀ i, 0 ≤ h i)
    (u v : EuclideanSpace ℝ (Fin d)) : 0 ≤ bregman h u v := by
  unfold bregman
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => mul_nonneg (hh i) (sq_nonneg _)))

lemma bregman_symm (h : Fin d → ℝ) (u v : EuclideanSpace ℝ (Fin d)) :
    bregman h u v = bregman h v u := by
  unfold bregman
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma bregman_zero (h : Fin d → ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    bregman h u 0 = prox h u := by simp [bregman, prox]

lemma bregman_self (h : Fin d → ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    bregman h u u = 0 := by simp [bregman]

lemma quadratic_interpolation (h : Fin d → ℝ) (u v z : EuclideanSpace ℝ (Fin d))
    (a b : ℝ) (hab : a + b = 1) :
    bregman h (a • u + b • v) z =
      a * bregman h u z + b * bregman h v z - a*b*bregman h u v := by
  unfold bregman
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hb : b = 1-a := by linarith
  rw [hb]
  ring

lemma quadratic_min_gap {X : Set (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ConvexOn ℝ X f)
    (h : Fin d → ℝ) (hh : ∀ i, 0 ≤ h i) (z a u : EuclideanSpace ℝ (Fin d))
    (ha : a ∈ X) (hu : u ∈ X)
    (hm : IsMinOn (fun y => f y + bregman h y z) X a) :
    f a + bregman h a z + bregman h a u ≤ f u + bregman h u z := by
  let B := bregman h a u
  let D := (f u + bregman h u z) - (f a + bregman h a z)
  have hD : 0 ≤ D := sub_nonneg.mpr (hm hu)
  have hB : 0 ≤ B := bregman_nonneg h hh a u
  suffices B ≤ D by dsimp [B,D] at this; linarith
  by_contra hn
  have hDB : D < B := lt_of_not_ge hn
  have hBp : 0 < B := lt_of_le_of_lt hD hDB
  let t := (B-D)/(2*B)
  have ht : 0 < t := div_pos (sub_pos.mpr hDB) (by positivity)
  have htB : t*(2*B) = B-D := div_mul_cancel₀ _ (ne_of_gt (by positivity : 0 < 2*B))
  have ht1 : t < 1 := by nlinarith
  have hmem := hf.1 ha hu (show 0 ≤ 1-t by linarith) ht.le (by ring : (1-t)+t=1)
  have hlow := hm hmem
  change f a + bregman h a z ≤ f ((1-t) • a+t • u) + bregman h ((1-t) • a+t • u) z at hlow
  have hconv := hf.2 ha hu (show 0 ≤ 1-t by linarith) ht.le (by ring : (1-t)+t=1)
  simp only [smul_eq_mul] at hconv
  rw [quadratic_interpolation h a u z (1-t) t (by ring)] at hlow
  have hineq : (1-t)*B ≤ D := by
    dsimp [B,D]
    nlinarith
  nlinarith

lemma objective_convex {X : Set (EuclideanSpace ℝ (Fin d))} (hX : Convex ℝ X)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ConvexOn ℝ Set.univ φ)
    (v : EuclideanSpace ℝ (Fin d)) (c : ℝ) (hc : 0 ≤ c) :
    ConvexOn ℝ X (fun y => inner ℝ v y + c * φ y) := by
  refine ⟨hX, ?_⟩
  intro x hx y hy a b ha hb hab
  have hp := hφ.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  simp only [smul_eq_mul] at hp ⊢
  simp only [inner_add_right, inner_smul_right]
  nlinarith [mul_le_mul_of_nonneg_left hp hc]

lemma weighted_young (h : Fin d → ℝ) (hh : ∀ i, 0 ≤ h i)
    (v a b : EuclideanSpace ℝ (Fin d)) (hz : ∀ i, h i = 0 → v i = 0) (η : ℝ) :
    η * inner ℝ v (a-b) ≤ bregman h a b + (η^2/2)*dualNormSq h v := by
  have hi (i : Fin d) : η * (v i * (a i-b i)) ≤
      (1/2)*(h i*(a i-b i)^2) + (η^2/2)*((v i)^2/h i) := by
    by_cases he : h i = 0
    · simp [he, hz i he]
    · have hp : 0 < h i := lt_of_le_of_ne (hh i) (Ne.symm he)
      have hd : ((v i)^2/h i)*h i = (v i)^2 := div_mul_cancel₀ _ he
      have hs := sq_nonneg (h i*(a i-b i)-η*v i)
      apply (mul_le_mul_iff_left₀ hp).mp
      nlinarith
  have hh' := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, bregman, dualNormSq,
    Finset.mul_sum, Finset.sum_add_distrib, mul_comm] using hh'

lemma sum_increment (a : ℕ → ℝ) (T : ℕ) :
    (∑ t ∈ Finset.Icc 1 T, (a t - a (t-1))) = a T - a 0 := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ T+1)]
    simp only [Nat.add_sub_cancel, ih]
    ring

lemma sum_forward_increment (a : ℕ → ℝ) (T : ℕ) :
    (∑ t ∈ Finset.Icc 1 T, (a (t+1) - a t)) = a (T+1) - a 1 := by
  have h := sum_increment (fun n => a (n+1)) T
  have he : (∑ t ∈ Finset.Icc 1 T, (a (t+1)-a (t-1+1))) =
      ∑ t ∈ Finset.Icc 1 T, (a (t+1)-a t) := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [Nat.sub_add_cancel (Finset.mem_Icc.mp ht).1]
  simpa only [he, Nat.zero_add] using h

lemma shifted_loss_bound {X : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} {f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ}
    {x g : ℕ → EuclideanSpace ℝ (Fin d)} {xstar : EuclideanSpace ℝ (Fin d)}
    {η : ℝ} (hη : 0 ≤ η) (T : ℕ) (hx1 : x 1 = 0)
    (hφ0 : ∀ y ∈ X, φ 0 ≤ φ y) (hxend : x (T+1) ∈ X)
    (hg : ∀ t ∈ Finset.Icc 1 T, IsSubgradient (f t) (x t) (g t)) :
    η * regret f φ x xstar T ≤
      ∑ t ∈ Finset.Icc 1 T,
        η * (inner ℝ (g t) (x t-xstar) + φ (x (t+1))-φ xstar) := by
  have hstep : ∀ t ∈ Finset.Icc 1 T,
      f t (x t) + φ (x t)-f t xstar-φ xstar ≤
      inner ℝ (g t) (x t-xstar)+φ (x (t+1))-φ xstar
        -(φ (x (t+1))-φ (x t)) := by
    intro t ht
    have h := hg t ht xstar
    rw [inner_sub_right] at h ⊢
    linarith
  have hs := Finset.sum_le_sum hstep
  conv_rhs at hs => rw [Finset.sum_sub_distrib]
  rw [sum_forward_increment (fun t => φ (x t)) T, hx1] at hs
  have hp := hφ0 (x (T+1)) hxend
  have hh : regret f φ x xstar T ≤ ∑ t ∈ Finset.Icc 1 T,
      (inner ℝ (g t) (x t-xstar)+φ (x (t+1))-φ xstar) := by
    unfold regret
    linarith
  simpa only [Finset.mul_sum] using mul_le_mul_of_nonneg_left hh hη

noncomputable def ftrlObj (η : ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (h : ℕ → Fin d → ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d))
    (t : ℕ) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  η * inner ℝ (∑ r ∈ Finset.Icc 1 t, g r) y + η*(t:ℝ)*φ y + prox (h t) y

lemma prox_mono {h k : Fin d → ℝ} (hh : ∀ i, h i ≤ k i)
    (u : EuclideanSpace ℝ (Fin d)) : prox h u ≤ prox k u := by
  unfold prox
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hh i) (sq_nonneg _))

lemma ftrl_min {X : Set (EuclideanSpace ℝ (Fin d))} (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ X)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} {f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ}
    {η : ℝ} {h : ℕ → Fin d → ℝ} (hh : ∀ t i, 0 ≤ h t i)
    {x g : ℕ → EuclideanSpace ℝ (Fin d)} (hx1 : x 1=0)
    (hrun : IsDualAveragingRun η X φ f h x g) (t : ℕ) :
    x (t+1) ∈ X ∧ IsMinOn (ftrlObj η φ h g t) X (x (t+1)) := by
  by_cases ht : t=0
  · subst t
    simp only [zero_add, hx1]
    refine ⟨h0, ?_⟩
    intro y hy
    change ftrlObj η φ h g 0 0 ≤ ftrlObj η φ h g 0 y
    simp only [ftrlObj, Finset.Icc_eq_empty_of_lt (by omega : 0 < 1), Finset.sum_empty, inner_zero_left, mul_zero, Nat.cast_zero, zero_mul, zero_add, prox]
    simp only [PiLp.zero_apply, zero_pow (by omega : 2 ≠ 0), mul_zero, Finset.sum_const_zero]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => mul_nonneg (hh 0 i) (sq_nonneg _)))
  · have ht1 : 1 ≤ t := by omega
    refine ⟨(hrun t ht1).2.1, ?_⟩
    intro y hy
    have hm := (hrun t ht1).2.2 hy
    change η * inner ℝ ((1/(t:ℝ)) • ∑ r ∈ Finset.Icc 1 t, g r) (x (t+1)) +
        η*φ (x (t+1))+(1/(t:ℝ))*prox (h t) (x (t+1)) ≤
      η * inner ℝ ((1/(t:ℝ)) • ∑ r ∈ Finset.Icc 1 t, g r) y +
        η*φ y+(1/(t:ℝ))*prox (h t) y at hm
    have htpos : (0:ℝ)<t := Nat.cast_pos.mpr (by omega)
    have hs := mul_le_mul_of_nonneg_left hm htpos.le
    change ftrlObj η φ h g t (x (t+1)) ≤ ftrlObj η φ h g t y
    unfold ftrlObj
    simp only [inner_smul_left, conj_trivial] at hs
    field_simp at hs
    nlinarith

lemma ftrl_increment (η : ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (h : ℕ → Fin d → ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d))
    (t : ℕ) (y : EuclideanSpace ℝ (Fin d)) :
    ftrlObj η φ h g (t+1) y = ftrlObj η φ h g t y +
      η*inner ℝ (g (t+1)) y + η*φ y + prox (h (t+1)) y-prox (h t) y := by
  unfold ftrlObj
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ t+1)]
  simp only [inner_add_left, Nat.cast_add, Nat.cast_one]
  ring

lemma ftrl_step {X : Set (EuclideanSpace ℝ (Fin d))} (hX : Convex ℝ X)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ X)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ConvexOn ℝ Set.univ φ)
    {f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ} {η : ℝ} (hη : 0 ≤ η)
    {h : ℕ → Fin d → ℝ} (hh : ∀ t i, 0 ≤ h t i)
    (hmono : ∀ t i, h t i ≤ h (t+1) i)
    {x g : ℕ → EuclideanSpace ℝ (Fin d)} (hx1 : x 1=0)
    (hrun : IsDualAveragingRun η X φ f h x g) (t : ℕ)
    (hz : ∀ i, h t i=0 → g (t+1) i=0) :
    η * (inner ℝ (g (t+1)) (x (t+1)) + φ (x (t+2))) ≤
      ftrlObj η φ h g (t+1) (x (t+2))-ftrlObj η φ h g t (x (t+1)) +
      (η^2/2)*dualNormSq (h t) (g (t+1)) := by
  obtain ⟨hxt, hm⟩ := ftrl_min h0 hh hx1 hrun t
  have hxnext : x (t+2) ∈ X := (hrun (t+1) (by omega)).2.1
  have hc := objective_convex hX hφ (η • ∑ r ∈ Finset.Icc 1 t, g r)
    (η*(t:ℝ)) (mul_nonneg hη (Nat.cast_nonneg _))
  simp only [inner_smul_left, conj_trivial] at hc
  have hgap := quadratic_min_gap hc (h t) (hh t) 0 (x (t+1)) (x (t+2))
    hxt hxnext (by
      intro y hy
      have hm' := hm hy
      change ftrlObj η φ h g t (x (t+1)) ≤ ftrlObj η φ h g t y at hm'
      change (η * inner ℝ (∑ r ∈ Finset.Icc 1 t, g r) (x (t+1)) + η*(t:ℝ)*φ (x (t+1))) + bregman (h t) (x (t+1)) 0 ≤
        (η * inner ℝ (∑ r ∈ Finset.Icc 1 t, g r) y + η*(t:ℝ)*φ y) + bregman (h t) y 0
      simpa only [ftrlObj, bregman_zero] using hm')
  simp only [bregman_zero] at hgap
  have hp := prox_mono (hmono t) (x (t+2))
  have hy := weighted_young (h t) (hh t) (g (t+1)) (x (t+1)) (x (t+2)) hz η
  have he := ftrl_increment η φ h g t (x (t+2))
  simp only [inner_sub_right] at hy
  unfold ftrlObj at he ⊢
  nlinarith

lemma primal_dual_regret_bound {X : Set (EuclideanSpace ℝ (Fin d))}
    (hX : Convex ℝ X) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ X)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ConvexOn ℝ Set.univ φ)
    (hφ0 : ∀ y ∈ X, φ 0 ≤ φ y)
    {f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ} {η : ℝ} (hη : 0 < η)
    {h : ℕ → Fin d → ℝ} (hh : ∀ t i, 0 ≤ h t i)
    (hmono : ∀ t i, h t i ≤ h (t+1) i)
    {x g : ℕ → EuclideanSpace ℝ (Fin d)} (hx1 : x 1=0)
    (hrun : IsDualAveragingRun η X φ f h x g) (T : ℕ)
    (hz : ∀ t ∈ Finset.Icc 1 T, ∀ i, h (t-1) i=0 → g t i=0)
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : xstar ∈ X) :
    η * regret f φ x xstar T ≤ prox (h T) xstar +
      (η^2/2)*(∑ t ∈ Finset.Icc 1 T, dualNormSq (h (t-1)) (g t)) := by
  have hxend := (ftrl_min h0 hh hx1 hrun T).1
  have hl := shifted_loss_bound hη.le T hx1 hφ0 hxend
    (fun t ht => (hrun t (Finset.mem_Icc.mp ht).1).1) (xstar := xstar)
  have hstep : ∀ t ∈ Finset.Icc 1 T,
      η*(inner ℝ (g t) (x t)+φ (x (t+1))) ≤
        (ftrlObj η φ h g t (x (t+1))-ftrlObj η φ h g (t-1) (x t)) +
        (η^2/2)*dualNormSq (h (t-1)) (g t) := by
    intro t ht
    have ht1 := (Finset.mem_Icc.mp ht).1
    have hz' : ∀ i, h (t-1) i=0 → g (t-1+1) i=0 := by
      simpa only [Nat.sub_add_cancel ht1] using hz t ht
    simpa only [Nat.sub_add_cancel ht1, show t-1+2=t+1 by omega] using
      ftrl_step hX h0 hφ hη.le hh hmono hx1 hrun (t-1) hz'
  have hs := Finset.sum_le_sum hstep
  have htel : (∑ t ∈ Finset.Icc 1 T,
      (ftrlObj η φ h g t (x (t+1))-ftrlObj η φ h g (t-1) (x t))) =
      ftrlObj η φ h g T (x (T+1)) := by
    have he := sum_increment (fun t => ftrlObj η φ h g t (x (t+1))) T
    have hsame : (∑ t ∈ Finset.Icc 1 T,
        (ftrlObj η φ h g t (x (t+1))-ftrlObj η φ h g (t-1) (x t))) =
        ∑ t ∈ Finset.Icc 1 T,
        (ftrlObj η φ h g t (x (t+1))-ftrlObj η φ h g (t-1) (x (t-1+1))) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Nat.sub_add_cancel (Finset.mem_Icc.mp ht).1]
    rw [hsame, he]
    simp [ftrlObj, hx1, prox]
  rw [Finset.sum_add_distrib, htel, ← Finset.mul_sum] at hs
  have hm := (ftrl_min h0 hh hx1 hrun T).2 hxstar
  change ftrlObj η φ h g T (x (T+1)) ≤ ftrlObj η φ h g T xstar at hm
  have hsum : (∑ t ∈ Finset.Icc 1 T,
      η*(inner ℝ (g t) (x t-xstar)+φ (x (t+1))-φ xstar)) =
      (∑ t ∈ Finset.Icc 1 T, η*(inner ℝ (g t) (x t)+φ (x (t+1)))) -
      η*inner ℝ (∑ t ∈ Finset.Icc 1 T, g t) xstar - η*(T:ℝ)*φ xstar := by
    simp only [inner_sub_right, sum_inner, Finset.mul_sum]
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp
    ring
  rw [hsum] at hl
  unfold ftrlObj at hm hs
  simp only [Finset.mul_sum] at hs ⊢
  linarith

end P2MAdaGradDual

theorem solution {d : ℕ} (η : ℝ) (hη : 0 < η) (X : Set (EuclideanSpace ℝ (Fin d)))
    (hXc : Convex ℝ X) (hXcl : IsClosed X) (hX0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ X)
    (ϕ : EuclideanSpace ℝ (Fin d) → ℝ) (hϕ : ConvexOn ℝ Set.univ ϕ)
    (hϕ0 : ∀ y ∈ X, ϕ 0 ≤ ϕ y)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (hf : ∀ t, ConvexOn ℝ Set.univ (f t))
    (h : ℕ → Fin d → ℝ) (hpos : ∀ t i, 0 < h t i) (hmono : ∀ t i, h t i ≤ h (t + 1) i)
    (x g : ℕ → EuclideanSpace ℝ (Fin d)) (hx1 : x 1 = 0)
    (hrun : IsDualAveragingRun η X ϕ f h x g)
    (T : ℕ) (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : xstar ∈ X) :
    regret f ϕ x xstar T
      ≤ 1 / η * prox (h T) xstar
        + η / 2 * ∑ t ∈ Finset.Icc 1 T, dualNormSq (h (t - 1)) (g t) := by
  have hb := P2MAdaGradDual.primal_dual_regret_bound hXc hX0 hϕ hϕ0 hη
    (fun t i => (hpos t i).le) hmono hx1 hrun T
    (fun t _ i hz => False.elim ((ne_of_gt (hpos (t-1) i)) hz)) xstar hxstar
  apply (mul_le_mul_iff_right₀ hη).mp
  have he : η * (1 / η * prox (h T) xstar +
      η / 2 * ∑ t ∈ Finset.Icc 1 T, dualNormSq (h (t-1)) (g t)) =
      prox (h T) xstar +
      η^2 / 2 * ∑ t ∈ Finset.Icc 1 T, dualNormSq (h (t-1)) (g t) := by
    field_simp
    <;> ring
  rw [he]
  exact hb
