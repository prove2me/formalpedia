-- Prove2me | solution 1 for AdaGrad.Diag.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-20T09:51:52.541407+00:00
-- url     : https://prove2.me/submissions/7bc3e949-6b41-4a3d-a0dc-19d6fa9b66b2

/-
SPDX-License-Identifier: Apache-2.0
Original Lean proof of both clauses of the diagonal AdaGrad regret guarantee.
Mathematical source: Duchi, Hazan and Singer, JMLR 12 (2011), Theorem 5;
Appendix C and Appendix F, Propositions 2/3 and Lemma 16.
Native Prove2Me definitions are imported unchanged. No accepted proof source is copied.
The proof derives both regret templates from native argmin predicates,
including semidefinite weights, zero gradients and changing quadratic potentials.
-/
import Mathlib
import Definitions.Def_AdaGrad_Diag_Setup

-- BEGIN Foundation

-- END Foundation

-- BEGIN Quadratic
open AdaGrad.Diag
open scoped BigOperators

namespace AdaGradProof
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

end AdaGradProof
-- END Quadratic

-- BEGIN RegretBasic
open AdaGrad.Diag ShorNonsmooth.AlmostDiff
open scoped BigOperators

namespace AdaGradProof
variable {d : ℕ}

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

lemma mirror_step {X : Set (EuclideanSpace ℝ (Fin d))} (hX : Convex ℝ X)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ConvexOn ℝ Set.univ φ)
    (η : ℝ) (hη : 0 ≤ η) (h : Fin d → ℝ) (hh : ∀ i, 0 ≤ h i)
    (g x y u : EuclideanSpace ℝ (Fin d)) (hz : ∀ i, h i=0 → g i=0)
    (hy : y ∈ X) (hu : u ∈ X)
    (hm : IsMinOn (fun z => η*inner ℝ g z+η*φ z+bregman h z x) X y) :
    η * (inner ℝ g (x-u)+φ y-φ u) ≤
      bregman h u x-bregman h u y+(η^2/2)*dualNormSq h g := by
  have hc := objective_convex hX hφ (η • g) η hη
  simp only [inner_smul_left, conj_trivial] at hc
  have hgap := quadratic_min_gap hc h hh x y u hy hu hm
  have hyoung := weighted_young h hh g x y hz η
  rw [bregman_symm h y u] at hgap
  rw [bregman_symm h y x] at hgap
  simp only [inner_sub_right] at hyoung ⊢
  linarith

lemma mirror_descent_regret_bound {X : Set (EuclideanSpace ℝ (Fin d))}
    (hX : Convex ℝ X) {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) (hφ0 : ∀ y ∈ X, φ 0 ≤ φ y)
    {f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ} {η : ℝ} (hη : 0 < η)
    {h : ℕ → Fin d → ℝ} (hh : ∀ t i, 0 ≤ h t i)
    {x g : ℕ → EuclideanSpace ℝ (Fin d)} (hx1 : x 1 = 0)
    (hrun : IsCompositeMDRun η X φ f h x g) (T : ℕ)
    (hz : ∀ t ∈ Finset.Icc 1 T, ∀ i, h t i=0 → g t i=0)
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : xstar ∈ X) :
    η * regret f φ x xstar T ≤
      (∑ t ∈ Finset.Icc 1 T,
        (bregman (h t) xstar (x t)-bregman (h t) xstar (x (t+1)))) +
      (η^2/2)*(∑ t ∈ Finset.Icc 1 T, dualNormSq (h t) (g t)) := by
  by_cases hT : T=0
  · simp [hT, regret]
  · have hxend : x (T+1) ∈ X := (hrun T (by omega)).2.1
    have hl := shifted_loss_bound hη.le T hx1 hφ0 hxend
      (fun t ht => (hrun t (Finset.mem_Icc.mp ht).1).1) (xstar := xstar)
    have hs := Finset.sum_le_sum (fun t ht => mirror_step hX hφ η hη.le
      (h t) (hh t) (g t) (x t) (x (t+1)) xstar (hz t ht)
      (hrun t (Finset.mem_Icc.mp ht).1).2.1 hxstar
      (hrun t (Finset.mem_Icc.mp ht).1).2.2)
    have he := hl.trans hs
    simpa only [Finset.sum_add_distrib, Finset.mul_sum] using he

end AdaGradProof
-- END RegretBasic

-- BEGIN FTRL
open AdaGrad.Diag ShorNonsmooth.AlmostDiff
open scoped BigOperators

namespace AdaGradProof
variable {d : ℕ}

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

end AdaGradProof
-- END FTRL

-- BEGIN AdaptiveWeights
namespace AdaGradProof

open AdaGrad.Diag
open scoped BigOperators

variable {d : ℕ}

lemma abs_le_supNorm (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    |x i| ≤ supNorm x := by
  unfold supNorm
  exact le_ciSup (Finite.bddAbove_range (fun j : Fin d => |x j|)) i

lemma coord_sq_le_supNorm_sq (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    (x i) ^ 2 ≤ supNorm x ^ 2 := by
  have h := abs_le_supNorm x i
  have h0 := abs_nonneg (x i)
  nlinarith [sq_abs (x i)]

lemma s_nonneg (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) (i : Fin d) :
    0 ≤ s g t i := Real.sqrt_nonneg _

@[simp] lemma s_zero (g : ℕ → EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    s g 0 i = 0 := by simp [s]

lemma s_sq (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) (i : Fin d) :
    s g t i ^ 2 = ∑ τ ∈ Finset.Icc 1 t, (g τ i) ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma s_succ_sq (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) (i : Fin d) :
    s g (t + 1) i ^ 2 = s g t i ^ 2 + (g (t + 1) i) ^ 2 := by
  rw [s_sq, s_sq, Finset.sum_Icc_succ_top (by omega)]

lemma s_le_succ (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) (i : Fin d) :
    s g t i ≤ s g (t + 1) i := by
  have h := s_succ_sq g t i
  have h0 := s_nonneg g t i
  have h1 := s_nonneg g (t + 1) i
  nlinarith [sq_nonneg (g (t + 1) i)]

lemma s_mono (g : ℕ → EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    Monotone (fun t => s g t i) :=
  monotone_nat_of_le_succ fun t => s_le_succ g t i

lemma s_succ_le_add_abs (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) (i : Fin d) :
    s g (t + 1) i ≤ s g t i + |g (t + 1) i| := by
  have h := s_succ_sq g t i
  have h0 := s_nonneg g t i
  have h1 := s_nonneg g (t + 1) i
  have ha := abs_nonneg (g (t + 1) i)
  nlinarith [sq_abs (g (t + 1) i), mul_nonneg h0 ha]

lemma gradient_eq_zero_of_s_eq_zero (g : ℕ → EuclideanSpace ℝ (Fin d))
    (t : ℕ) (ht : 1 ≤ t) (i : Fin d) (h : s g t i = 0) : g t i = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  have hs := s_succ_sq g n i
  rw [h] at hs
  nlinarith [sq_nonneg (s g n i), sq_nonneg (g (n + 1) i)]

lemma scalar_increment_bound (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) (i : Fin d) :
    (g (t + 1) i) ^ 2 / s g (t + 1) i ≤ 2 * (s g (t + 1) i - s g t i) := by
  have h0 := s_nonneg g t i
  have h1 := s_nonneg g (t + 1) i
  have hm := s_le_succ g t i
  by_cases hz : s g (t + 1) i = 0
  · simp only [hz, div_zero]
    linarith
  · have hp : 0 < s g (t + 1) i := lt_of_le_of_ne h1 (Ne.symm hz)
    apply (div_le_iff₀ hp).2
    have hs := s_succ_sq g t i
    nlinarith [sq_nonneg (s g (t + 1) i - s g t i)]

lemma scalar_sum_bound (g : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) (i : Fin d) :
    (∑ t ∈ Finset.Icc 1 T, (g t i) ^ 2 / s g t i) ≤ 2 * s g T i := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h := scalar_increment_bound g T i
    linarith

lemma current_dual_sum_bound (g : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) :
    (∑ t ∈ Finset.Icc 1 T, dualNormSq (fun i => s g t i) (g t)) ≤
      2 * ∑ i, s g T i := by
  unfold dualNormSq
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ i, 2 * s g T i := Finset.sum_le_sum fun i _ => scalar_sum_bound g T i
    _ = _ := (Finset.mul_sum ..).symm

lemma previous_weight_ge_current (δ : ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d))
    (t : ℕ) (ht : 1 ≤ t) (hδ : supNorm (g t) ≤ δ) (i : Fin d) :
    s g t i ≤ adaWeights δ g (t - 1) i := by
  have ha := (abs_le_supNorm (g t) i).trans hδ
  have hs := s_succ_le_add_abs g (t - 1) i
  have he : t - 1 + 1 = t := by omega
  rw [he] at hs
  unfold adaWeights
  linarith

lemma previous_zero_compatibility (δ : ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d))
    (t : ℕ) (ht : 1 ≤ t) (hδ : supNorm (g t) ≤ δ) (i : Fin d)
    (hz : adaWeights δ g (t - 1) i = 0) : g t i = 0 := by
  have hs := previous_weight_ge_current δ g t ht hδ i
  have h0 := s_nonneg g t i
  apply gradient_eq_zero_of_s_eq_zero g t ht i
  linarith

lemma previous_dual_le_current (δ : ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d))
    (t : ℕ) (ht : 1 ≤ t) (hδ : supNorm (g t) ≤ δ) :
    dualNormSq (adaWeights δ g (t - 1)) (g t) ≤
      dualNormSq (fun i => s g t i) (g t) := by
  apply Finset.sum_le_sum
  intro i _
  have hw := previous_weight_ge_current δ g t ht hδ i
  by_cases hz : s g t i = 0
  · have hg := gradient_eq_zero_of_s_eq_zero g t ht i hz
    simp [hg]
  · exact div_le_div_of_nonneg_left (sq_nonneg _) (lt_of_le_of_ne (s_nonneg g t i)
      (Ne.symm hz)) hw

lemma previous_dual_sum_bound (δ : ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ)
    (hδ : ∀ t ∈ Finset.Icc 1 T, supNorm (g t) ≤ δ) :
    (∑ t ∈ Finset.Icc 1 T, dualNormSq (adaWeights δ g (t - 1)) (g t)) ≤
      2 * ∑ i, s g T i := by
  calc
    _ ≤ ∑ t ∈ Finset.Icc 1 T, dualNormSq (fun i => s g t i) (g t) := by
      apply Finset.sum_le_sum
      intro t ht
      exact previous_dual_le_current δ g t (Finset.mem_Icc.mp ht).1 (hδ t ht)
    _ ≤ _ := current_dual_sum_bound g T

end AdaGradProof
-- END AdaptiveWeights

-- BEGIN NormDrift
namespace AdaGradProof

open AdaGrad.Diag
open scoped BigOperators

variable {d : ℕ}

lemma adaptive_prox_bound (δ : ℝ) (hδ : 0 ≤ δ)
    (g : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) (u : EuclideanSpace ℝ (Fin d)) :
    prox (adaWeights δ g T) u ≤
      δ * ‖u‖ ^ 2 + supNorm u ^ 2 * ∑ i, s g T i := by
  have hs : (∑ i, s g T i * (u i) ^ 2) ≤ supNorm u ^ 2 * ∑ i, s g T i := by
    calc
      _ ≤ ∑ i, s g T i * supNorm u ^ 2 := by
        exact Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (coord_sq_le_supNorm_sq u i) (s_nonneg g T i)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hn : 0 ≤ δ * ‖u‖ ^ 2 := mul_nonneg hδ (sq_nonneg _)
  have hsn : 0 ≤ supNorm u ^ 2 * ∑ i, s g T i :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => s_nonneg g T i)
  unfold prox adaWeights
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
  linarith

lemma s_bregman_nonneg (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ)
    (u v : EuclideanSpace ℝ (Fin d)) :
    0 ≤ bregman (fun i => s g t i) u v := by
  unfold bregman
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ =>
    mul_nonneg (s_nonneg g t i) (sq_nonneg _))

lemma bregman_increment_bound (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ)
    (u v : EuclideanSpace ℝ (Fin d)) (R : ℝ)
    (hR : ∀ i, (u i - v i) ^ 2 ≤ R) :
    bregman (fun i => s g (t + 1) i) u v - bregman (fun i => s g t i) u v ≤
      R / 2 * ((∑ i, s g (t + 1) i) - ∑ i, s g t i) := by
  have hsum : (∑ i, (s g (t + 1) i - s g t i) * (u i - v i) ^ 2) ≤
      ∑ i, (s g (t + 1) i - s g t i) * R :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hR i)
      (sub_nonneg.mpr (s_le_succ g t i))
  unfold bregman
  simp_rw [sub_mul] at hsum
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul] at hsum
  linarith

lemma potential_sum_with_terminal_bound (g x : ℕ → EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d)) (R : ℝ) (T : ℕ)
    (hR : ∀ t ∈ Finset.Icc 1 T, ∀ i, (u i - x t i) ^ 2 ≤ R) :
    (∑ t ∈ Finset.Icc 1 T,
      (bregman (fun i => s g t i) u (x t) -
        bregman (fun i => s g t i) u (x (t + 1)))) +
        bregman (fun i => s g T i) u (x (T + 1)) ≤ R / 2 * ∑ i, s g T i := by
  induction T with
  | zero => simp [bregman]
  | succ T ih =>
    have hp := ih (fun t ht => hR t (Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp ht).1, (Finset.mem_Icc.mp ht).2.trans (Nat.le_succ T)⟩))
    have hi := bregman_increment_bound g T u (x (T + 1)) R
      (hR (T + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
    rw [Finset.sum_Icc_succ_top (by omega)]
    linarith

lemma potential_sum_bound (g x : ℕ → EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d)) (T : ℕ) (hT : 1 ≤ T) :
    (∑ t ∈ Finset.Icc 1 T,
      (bregman (fun i => s g t i) u (x t) -
        bregman (fun i => s g t i) u (x (t + 1)))) ≤
      (Finset.Icc 1 T).sup' (Finset.nonempty_Icc.mpr hT)
        (fun t => supNorm (u - x t) ^ 2) / 2 * ∑ i, s g T i := by
  have hcoord : ∀ t ∈ Finset.Icc 1 T, ∀ i,
      (u i - x t i) ^ 2 ≤ (Finset.Icc 1 T).sup' (Finset.nonempty_Icc.mpr hT)
        (fun t => supNorm (u - x t) ^ 2) := by
    intro t ht i
    calc
      _ ≤ supNorm (u - x t) ^ 2 := by
        simpa using coord_sq_le_supNorm_sq (u - x t) i
      _ ≤ _ := Finset.le_sup' (f := fun t => supNorm (u - x t) ^ 2) ht
  have h := potential_sum_with_terminal_bound g x u _ T hcoord
  have hn := s_bregman_nonneg g T u (x (T + 1))
  linarith

end AdaGradProof
-- END NormDrift

-- BEGIN NativeRoot
open AdaGradProof

namespace AdaGrad.Diag

/-- Duchi, Hazan, Singer, JMLR 12 (2011), Theorem 5, p. 2132: the regret of AdaGrad with diagonal
matrices (Figure 1, p. 2130). Let `X ⊆ ℝ^d` be closed and convex with `0 ∈ X`, the losses `f_t` and
the regularizer `ϕ` convex, with `ϕ` minimized over `X` at `x_1 = 0`, let `η > 0` and `T ≥ 1`.

1. For every `δ ≥ 0` and every run of Figure 1 with the primal-dual subgradient update (3) such
   that `δ ≥ max_{t≤T} ‖g_t‖∞`, and every `x* ∈ X`,
   `R_φ(T) ≤ (δ/η)‖x*‖₂² + (1/η)‖x*‖∞² ∑_i ‖g_{1:T,i}‖₂ + η ∑_i ‖g_{1:T,i}‖₂`.
2. For every run of Figure 1 with `δ = 0` and the composite mirror descent update (4), and every
   `x* ∈ X`,
   `R_φ(T) ≤ (1/(2η)) max_{t≤T} ‖x* − x_t‖∞² ∑_i ‖g_{1:T,i}‖₂ + η ∑_i ‖g_{1:T,i}‖₂`.

Here `‖g_{1:T,i}‖₂ = s g T i`, and `‖·‖` on `EuclideanSpace ℝ (Fin d)` is the Euclidean norm. -/
theorem theorem_5 {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d))) (hXc : Convex ℝ X)
    (hXcl : IsClosed X) (hX0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ X)
    (ϕ : EuclideanSpace ℝ (Fin d) → ℝ) (hϕ : ConvexOn ℝ Set.univ ϕ)
    (hϕ0 : ∀ y ∈ X, ϕ 0 ≤ ϕ y)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (hf : ∀ t, ConvexOn ℝ Set.univ (f t))
    (η : ℝ) (hη : 0 < η) (T : ℕ) (hT : 1 ≤ T) :
    (∀ (δ : ℝ) (x g : ℕ → EuclideanSpace ℝ (Fin d)), 0 ≤ δ →
        IsPrimalDualRun η δ X ϕ f x g →
        (∀ t ∈ Finset.Icc 1 T, supNorm (g t) ≤ δ) →
        ∀ xstar ∈ X,
          regret f ϕ x xstar T
            ≤ δ / η * ‖xstar‖ ^ 2 + 1 / η * supNorm xstar ^ 2 * ∑ i, s g T i
              + η * ∑ i, s g T i) ∧
    (∀ (x g : ℕ → EuclideanSpace ℝ (Fin d)),
        IsMirrorDescentRun η 0 X ϕ f x g →
        ∀ xstar ∈ X,
          regret f ϕ x xstar T
            ≤ 1 / (2 * η) * (Finset.Icc 1 T).sup' (Finset.nonempty_Icc.mpr hT)
                  (fun t => supNorm (xstar - x t) ^ 2) * ∑ i, s g T i
              + η * ∑ i, s g T i) := by
  have _ := hXcl
  have _ := hf
  constructor
  · intro δ x g hδ hrun hgrad xstar hxstar
    obtain ⟨hx1, hrun⟩ := hrun
    have hh : ∀ t i, 0 ≤ adaWeights δ g t i := by
      intro t i
      exact add_nonneg hδ (s_nonneg g t i)
    have hm : ∀ t i, adaWeights δ g t i ≤ adaWeights δ g (t + 1) i := by
      intro t i
      dsimp [adaWeights]
      linarith [s_le_succ g t i]
    have hz : ∀ t ∈ Finset.Icc 1 T, ∀ i,
        adaWeights δ g (t - 1) i = 0 → g t i = 0 := by
      intro t ht i he
      exact previous_zero_compatibility δ g t (Finset.mem_Icc.mp ht).1 (hgrad t ht) i he
    have hr := primal_dual_regret_bound hXc hX0 hϕ hϕ0 hη hh hm hx1 hrun T hz xstar hxstar
    have hp := adaptive_prox_bound δ hδ g T xstar
    have hd := previous_dual_sum_bound δ g T hgrad
    have hc := mul_le_mul_of_nonneg_left hd (show 0 ≤ η ^ 2 / 2 by positivity)
    apply (mul_le_mul_iff_right₀ hη).mp
    have he : η * (δ / η * ‖xstar‖ ^ 2 + 1 / η * supNorm xstar ^ 2 * ∑ i, s g T i
        + η * ∑ i, s g T i) = δ * ‖xstar‖ ^ 2 + supNorm xstar ^ 2 * ∑ i, s g T i
          + η ^ 2 * ∑ i, s g T i := by
      field_simp [ne_of_gt hη]
    rw [he]
    nlinarith
  · intro x g hrun xstar hxstar
    obtain ⟨hx1, hrun⟩ := hrun
    have hh : ∀ t i, 0 ≤ adaWeights 0 g t i := by
      intro t i
      simpa only [adaWeights, zero_add] using s_nonneg g t i
    have hz : ∀ t ∈ Finset.Icc 1 T, ∀ i,
        adaWeights 0 g t i = 0 → g t i = 0 := by
      intro t ht i he
      apply gradient_eq_zero_of_s_eq_zero g t (Finset.mem_Icc.mp ht).1 i
      simpa only [adaWeights, zero_add] using he
    have hr := mirror_descent_regret_bound hXc hϕ hϕ0 hη hh hx1 hrun T hz xstar hxstar
    have hw : adaWeights 0 g = fun t i => s g t i := by
      funext t i
      exact zero_add _
    rw [hw] at hr
    have hp := potential_sum_bound g x xstar T hT
    have hd := current_dual_sum_bound g T
    have hc := mul_le_mul_of_nonneg_left hd (show 0 ≤ η ^ 2 / 2 by positivity)
    apply (mul_le_mul_iff_right₀ hη).mp
    have he : η * (1 / (2 * η) * (Finset.Icc 1 T).sup' (Finset.nonempty_Icc.mpr hT)
          (fun t => supNorm (xstar - x t) ^ 2) * ∑ i, s g T i + η * ∑ i, s g T i) =
        (Finset.Icc 1 T).sup' (Finset.nonempty_Icc.mpr hT)
          (fun t => supNorm (xstar - x t) ^ 2) / 2 * ∑ i, s g T i + η ^ 2 * ∑ i, s g T i := by
      field_simp [ne_of_gt hη]
    rw [he]
    nlinarith

end AdaGrad.Diag
-- END NativeRoot

open AdaGrad.Diag

theorem solution {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d))) (hXc : Convex ℝ X)
    (hXcl : IsClosed X) (hX0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ X)
    (ϕ : EuclideanSpace ℝ (Fin d) → ℝ) (hϕ : ConvexOn ℝ Set.univ ϕ)
    (hϕ0 : ∀ y ∈ X, ϕ 0 ≤ ϕ y)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (hf : ∀ t, ConvexOn ℝ Set.univ (f t))
    (η : ℝ) (hη : 0 < η) (T : ℕ) (hT : 1 ≤ T) :
    (∀ (δ : ℝ) (x g : ℕ → EuclideanSpace ℝ (Fin d)), 0 ≤ δ →
        IsPrimalDualRun η δ X ϕ f x g →
        (∀ t ∈ Finset.Icc 1 T, supNorm (g t) ≤ δ) →
        ∀ xstar ∈ X,
          regret f ϕ x xstar T
            ≤ δ / η * ‖xstar‖ ^ 2 + 1 / η * supNorm xstar ^ 2 * ∑ i, s g T i
              + η * ∑ i, s g T i) ∧
    (∀ (x g : ℕ → EuclideanSpace ℝ (Fin d)),
        IsMirrorDescentRun η 0 X ϕ f x g →
        ∀ xstar ∈ X,
          regret f ϕ x xstar T
            ≤ 1 / (2 * η) * (Finset.Icc 1 T).sup' (Finset.nonempty_Icc.mpr hT)
                  (fun t => supNorm (xstar - x t) ^ 2) * ∑ i, s g T i
              + η * ∑ i, s g T i) :=
  AdaGrad.Diag.theorem_5 X hXc hXcl hX0 ϕ hϕ hϕ0 f hf η hη T hT
