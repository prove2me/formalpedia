-- Prove2me | solution 1 for AronszajnRK.SubspaceSum.projection_sum_series
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T11:13:39.932728+00:00
-- url     : https://prove2.me/submissions/be10f494-00ec-4a20-8bad-e7441b7e3215

import Mathlib
import Definitions.Def_AronszajnRK_SubspaceSum_sumProjection
import Definitions.Def_AronszajnRK_SubspaceSum_intersectionProjection

set_option autoImplicit false

namespace AltProj503

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma pow_inner (S : E →L[ℂ] E) (hS : ∀ u v : E, inner ℂ (S u) v = inner ℂ u (S v)) (g : E) :
    ∀ n m : ℕ, inner ℂ ((S ^ m) g) ((S ^ n) g) = inner ℂ ((S ^ (m + n)) g) g := by
  intro n
  induction n with
  | zero => intro m; simp
  | succ n ih =>
    intro m
    have e1 : (S ^ (n + 1)) g = S ((S ^ n) g) := by
      rw [pow_succ', ContinuousLinearMap.mul_apply]
    have e2 : S ((S ^ m) g) = (S ^ (m + 1)) g := by
      rw [pow_succ', ContinuousLinearMap.mul_apply]
    rw [e1, ← hS, e2, ih (m + 1), show m + 1 + n = m + (n + 1) by omega]

lemma exists_tendsto_pow [CompleteSpace E] (S : E →L[ℂ] E)
    (hS : ∀ u v : E, inner ℂ (S u) v = inner ℂ u (S v))
    (hB : ∀ h : E, ‖S h‖ ^ 2 ≤ RCLike.re (inner ℂ (S h) h)) (g : E) :
    ∃ y, Tendsto (fun m : ℕ => (S ^ m) g) atTop (𝓝 y) := by
  have hN : ∀ h : E, ‖S h‖ ≤ ‖h‖ := by
    intro h
    have h1 := hB h
    have h2 : RCLike.re (inner ℂ (S h) h) ≤ ‖S h‖ * ‖h‖ := re_inner_le_norm _ _
    by_contra hc
    push_neg at hc
    have : 0 ≤ ‖h‖ := norm_nonneg _
    nlinarith
  set a : ℕ → ℝ := fun k => RCLike.re (inner ℂ ((S ^ k) g) g) with ha
  have hev : ∀ j, a (2 * j) = ‖(S ^ j) g‖ ^ 2 := by
    intro j
    rw [ha]
    dsimp only
    rw [two_mul, ← pow_inner S hS g j j, inner_self_eq_norm_sq]
  have hodd : ∀ j, a (2 * j + 1) = RCLike.re (inner ℂ (S ((S ^ j) g)) ((S ^ j) g)) := by
    intro j
    rw [ha]
    dsimp only
    rw [show 2 * j + 1 = (j + 1) + j by ring, ← pow_inner S hS g j (j + 1), pow_succ',
      ContinuousLinearMap.mul_apply]
  have hanti : Antitone a := by
    refine antitone_nat_of_succ_le (fun k => ?_)
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
    · rw [hodd, hev]
      have h2 : RCLike.re (inner ℂ (S ((S ^ j) g)) ((S ^ j) g)) ≤
          ‖S ((S ^ j) g)‖ * ‖(S ^ j) g‖ := re_inner_le_norm _ _
      have h3 := hN ((S ^ j) g)
      have h4 : 0 ≤ ‖(S ^ j) g‖ := norm_nonneg _
      nlinarith
    · have e : (S ^ (j + 1)) g = S ((S ^ j) g) := by
        rw [pow_succ', ContinuousLinearMap.mul_apply]
      rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, hev, hodd, e]
      exact hB _
  have hnn : ∀ k, 0 ≤ a k := by
    intro k
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
    · rw [hev]; positivity
    · rw [hodd]; exact le_trans (sq_nonneg _) (hB _)
  have hL : Tendsto a atTop (𝓝 (⨅ k, a k)) :=
    tendsto_atTop_ciInf hanti ⟨0, by rintro _ ⟨k, rfl⟩; exact hnn k⟩
  set L := ⨅ k, a k
  have hd : ∀ m n : ℕ, dist ((S ^ m) g) ((S ^ n) g) =
      Real.sqrt (a (2 * m) + a (2 * n) - 2 * a (m + n)) := by
    intro m n
    rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg _), @norm_sub_sq ℂ, hev, hev]
    congr 1
    have : a (m + n) = RCLike.re (inner ℂ ((S ^ m) g) ((S ^ n) g)) := by
      rw [ha]; dsimp only; rw [pow_inner S hS g n m]
    rw [this]
    ring
  have t1 : Tendsto (fun p : ℕ × ℕ => 2 * p.1) atTop atTop :=
    tendsto_atTop_atTop.2 (fun b => ⟨(b, 0), fun p hp => by have := hp.1; simp at this ⊢; omega⟩)
  have t2 : Tendsto (fun p : ℕ × ℕ => 2 * p.2) atTop atTop :=
    tendsto_atTop_atTop.2 (fun b => ⟨(0, b), fun p hp => by have := hp.2; simp at this ⊢; omega⟩)
  have t3 : Tendsto (fun p : ℕ × ℕ => p.1 + p.2) atTop atTop :=
    tendsto_atTop_atTop.2 (fun b => ⟨(b, 0), fun p hp => by have := hp.1; simp at this ⊢; omega⟩)
  have hb : Tendsto (fun p : ℕ × ℕ => a (2 * p.1) + a (2 * p.2) - 2 * a (p.1 + p.2)) atTop
      (𝓝 (L + L - 2 * L)) :=
    ((hL.comp t1).add (hL.comp t2)).sub ((hL.comp t3).const_mul 2)
  rw [show L + L - 2 * L = 0 by ring] at hb
  have hc : CauchySeq (fun m : ℕ => (S ^ m) g) := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    have := (Real.continuous_sqrt.tendsto 0).comp hb
    rw [Real.sqrt_zero] at this
    refine this.congr (fun p => ?_)
    simp only [Function.comp_apply]
    rw [hd]
  exact cauchySeq_tendsto_of_complete hc

theorem core [CompleteSpace E] (K₁ K₂ K₀ : Submodule ℂ E) [K₁.HasOrthogonalProjection]
    [K₂.HasOrthogonalProjection] [K₀.HasOrthogonalProjection]
    (hK₀ : ∀ z, z ∈ K₀ ↔ z ∈ K₁ ∧ z ∈ K₂) (f : E) :
    Tendsto (fun m : ℕ => ((K₂.starProjection * K₁.starProjection) ^ m) f) atTop
      (𝓝 (K₀.starProjection f)) := by
  set P₁ := K₁.starProjection with hP₁
  set P₂ := K₂.starProjection with hP₂
  have sa1 : ∀ u v : E, inner ℂ (P₁ u) v = inner ℂ u (P₁ v) :=
    K₁.inner_starProjection_left_eq_right
  have sa2 : ∀ u v : E, inner ℂ (P₂ u) v = inner ℂ u (P₂ v) :=
    K₂.inner_starProjection_left_eq_right
  have id1 : ∀ x, P₁ (P₁ x) = P₁ x := fun x =>
    Submodule.starProjection_eq_self_iff.2 (K₁.starProjection_apply_mem x)
  have id2 : ∀ x, P₂ (P₂ x) = P₂ x := fun x =>
    Submodule.starProjection_eq_self_iff.2 (K₂.starProjection_apply_mem x)
  set S : E →L[ℂ] E := P₁ * P₂ * P₁ with hSdef
  have hSa : ∀ x, S x = P₁ (P₂ (P₁ x)) := fun x => rfl
  have hSsym : ∀ u v : E, inner ℂ (S u) v = inner ℂ u (S v) := by
    intro u v
    rw [hSa, hSa, sa1, sa2, sa1]
  have hre : ∀ h, RCLike.re (inner ℂ (S h) h) = ‖P₂ (P₁ h)‖ ^ 2 := by
    intro h
    have e : inner ℂ (P₂ (P₁ h)) (P₂ (P₁ h)) = inner ℂ (P₂ (P₁ h)) (P₁ h) := by
      rw [← sa2, id2]
    rw [hSa, sa1, ← e, inner_self_eq_norm_sq]
  have hB : ∀ h : E, ‖S h‖ ^ 2 ≤ RCLike.re (inner ℂ (S h) h) := by
    intro h
    rw [hre, hSa]
    have := K₁.norm_starProjection_apply_le (P₂ (P₁ h))
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  obtain ⟨y, hy⟩ := exists_tendsto_pow S hSsym hB (P₁ f)
  have hSy : S y = y := by
    have h1 : Tendsto (fun m : ℕ => (S ^ (m + 1)) (P₁ f)) atTop (𝓝 (S y)) := by
      have := (S.continuous.tendsto y).comp hy
      refine this.congr (fun m => ?_)
      simp only [Function.comp_apply]
      rw [pow_succ']
      rfl
    have h2 : Tendsto (fun m : ℕ => (S ^ (m + 1)) (P₁ f)) atTop (𝓝 y) :=
      (tendsto_add_atTop_iff_nat 1).2 hy
    exact tendsto_nhds_unique h1 h2
  have hy1 : y ∈ K₁ := by
    rw [← hSy, hSa]
    exact K₁.starProjection_apply_mem _
  have hP1y : P₁ y = y := Submodule.starProjection_eq_self_iff.2 hy1
  have hy2 : y ∈ K₂ := by
    rw [K₂.mem_iff_norm_starProjection y]
    have e : ‖y‖ ^ 2 = ‖P₂ y‖ ^ 2 := by
      have := hre y
      rw [hSy, hP1y, inner_self_eq_norm_sq] at this
      exact this
    exact ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 e).symm
  have hP2y : P₂ y = y := Submodule.starProjection_eq_self_iff.2 hy2
  have horth : ∀ z ∈ K₀, inner ℂ (f - y) z = 0 := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := (hK₀ z).1 hz
    have hP1z : P₁ z = z := Submodule.starProjection_eq_self_iff.2 hz1
    have hP2z : P₂ z = z := Submodule.starProjection_eq_self_iff.2 hz2
    have hSz : S z = z := by rw [hSa, hP1z, hP2z, hP1z]
    have hconst : ∀ m : ℕ, inner ℂ ((S ^ m) (P₁ f)) z = inner ℂ (P₁ f) z := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', ContinuousLinearMap.mul_apply, hSsym, hSz, ih]
    have hlim : Tendsto (fun m : ℕ => inner ℂ ((S ^ m) (P₁ f)) z) atTop (𝓝 (inner ℂ y z)) :=
      hy.inner tendsto_const_nhds
    have heq : inner ℂ y z = inner ℂ (P₁ f) z := by
      refine tendsto_nhds_unique hlim ?_
      simp_rw [hconst]
      exact tendsto_const_nhds
    rw [inner_sub_left, heq, sa1, hP1z, sub_self]
  have hP0 : K₀.starProjection f = y :=
    Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((hK₀ y).2 ⟨hy1, hy2⟩) horth
  have hK1m : ∀ m : ℕ, P₁ ((S ^ m) (P₁ f)) = (S ^ m) (P₁ f) := by
    intro m
    cases m with
    | zero => simp [id1]
    | succ m => rw [pow_succ', ContinuousLinearMap.mul_apply, hSa, id1]
  have hid : ∀ m : ℕ, ((P₂ * P₁) ^ (m + 1)) f = P₂ ((S ^ m) (P₁ f)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, pow_succ',
        ContinuousLinearMap.mul_apply (S) (S ^ m), hSa, hK1m]
      rfl
  rw [hP0, ← tendsto_add_atTop_iff_nat 1]
  simp_rw [hid]
  have := (P₂.continuous.tendsto y).comp hy
  rw [hP2y] at this
  exact this


lemma proj_diff [CompleteSpace E] (K U : Submodule ℂ E) [K.HasOrthogonalProjection]
    [U.HasOrthogonalProjection] (hUK : U ≤ K) [(K ⊓ Uᗮ).HasOrthogonalProjection] :
    K.starProjection - U.starProjection = (K ⊓ Uᗮ).starProjection := by
  ext x
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [ContinuousLinearMap.sub_apply]
    refine Submodule.mem_inf.2 ⟨K.sub_mem (K.starProjection_apply_mem x)
      (hUK (U.starProjection_apply_mem x)), (Submodule.mem_orthogonal _ _).2 ?_⟩
    intro u hu
    rw [inner_sub_right, ← K.inner_starProjection_left_eq_right,
      ← U.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 (hUK hu),
      Submodule.starProjection_eq_self_iff.2 hu, sub_self]
  · intro w hw
    obtain ⟨hwK, hwU⟩ := Submodule.mem_inf.1 hw
    rw [ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_left,
      K.inner_starProjection_left_eq_right, U.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 hwK,
      (Submodule.starProjection_apply_eq_zero_iff U).2 hwU, inner_zero_right]
    ring

end AltProj503

namespace ProjId43c38e6a

theorem ab_pow {R : Type*} [Ring R] (a b : R) (k : ℕ) : a * (b * a) ^ k = (a * b) ^ k * a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, ← mul_assoc, ih]
    simp only [mul_assoc]

theorem key {R : Type*} [Ring R] (P p q : R) (hp : p * p = p) (hq : q * q = q)
    (hpP : p * P = p) (hqP : q * P = q) (hPp : P * p = p) (hPq : P * q = q) (hPP : P * P = P)
    (n : ℕ) :
    ((P - p) * (P - q)) ^ (n + 1) =
      P - (∑ k ∈ Finset.range (n + 1),
        (p * (q * p) ^ k + q * (p * q) ^ k - (q * p) ^ (k + 1) - (p * q) ^ (k + 1))) -
        (q * p) ^ (n + 1) := by
  have hp' : ∀ z, p * (p * z) = p * z := fun z => by rw [← mul_assoc, hp]
  have hq' : ∀ z, q * (q * z) = q * z := fun z => by rw [← mul_assoc, hq]
  have hpP' : ∀ z, p * (P * z) = p * z := fun z => by rw [← mul_assoc, hpP]
  have hqP' : ∀ z, q * (P * z) = q * z := fun z => by rw [← mul_assoc, hqP]
  have hPp' : ∀ z, P * (p * z) = p * z := fun z => by rw [← mul_assoc, hPp]
  have hPq' : ∀ z, P * (q * z) = q * z := fun z => by rw [← mul_assoc, hPq]
  have hPP' : ∀ z, P * (P * z) = P * z := fun z => by rw [← mul_assoc, hPP]
  set f : ℕ → R := fun k =>
    p * (q * p) ^ k + q * (p * q) ^ k - (q * p) ^ (k + 1) - (p * q) ^ (k + 1) with hf
  set g : ℕ → R := fun k =>
    q * (p * q) ^ (k + 1) + p * (q * p) ^ (k + 1) - (q * p) ^ (k + 1) - (p * q) ^ (k + 1 + 1)
    with hg
  have h1 : P * ((P - p) * (P - q)) = P - p - q + p * q := by
    simp only [mul_sub, sub_mul, mul_assoc, hPP', hPp', hPq', hpP', hPP, hPp, hPq, hpP]
    abel
  have h2 : ∀ N : ℕ, (q * p) ^ (N + 1) * ((P - p) * (P - q)) = 0 := by
    intro N
    rw [pow_succ]
    simp only [mul_sub, sub_mul, mul_assoc, hp', hq', hpP', hqP', hp, hq, hpP, hqP]
    abel
  have h3 : ∀ k, f k * ((P - p) * (P - q)) = g k := by
    intro k
    simp only [hf, hg]
    rw [ab_pow p q k, ab_pow q p k, ab_pow q p (k + 1), ab_pow p q (k + 1)]
    simp only [pow_succ]
    simp only [mul_sub, sub_mul, mul_add, add_mul, mul_assoc, hp', hq', hpP', hqP', hp, hq,
      hpP, hqP]
    abel
  have h4 : ∀ N : ℕ, (∑ k ∈ Finset.range (N + 1), f k) + (q * p) ^ (N + 1) =
      p + q - p * q + ∑ k ∈ Finset.range N, g k := by
    intro N
    induction N with
    | zero =>
      simp only [hf, Finset.sum_range_one, Finset.sum_range_zero, pow_zero, mul_one, zero_add,
        pow_one, add_zero]
      abel
    | succ N ih =>
      rw [Finset.sum_range_succ f (N + 1), Finset.sum_range_succ g N,
        eq_sub_of_add_eq ih]
      simp only [hf, hg]
      abel
  induction n with
  | zero =>
    simp only [zero_add, pow_one, Finset.sum_range_one, hf, pow_zero, mul_one]
    simp only [mul_sub, sub_mul, hPP, hPq, hpP]
    abel
  | succ n ih =>
    rw [pow_succ, ih]
    change (P - ∑ k ∈ Finset.range (n + 1), f k - (q * p) ^ (n + 1)) * ((P - p) * (P - q)) =
      P - ∑ k ∈ Finset.range (n + 1 + 1), f k - (q * p) ^ (n + 1 + 1)
    rw [sub_mul, sub_mul, h1, h2, Finset.sum_mul, Finset.sum_congr rfl (fun k _ => h3 k),
      eq_sub_of_add_eq (h4 (n + 1))]
    abel

end ProjId43c38e6a

open AronszajnRK.SubspaceSum in
theorem cpv_5a66 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (F₁ F₂ : ClosedSubmodule ℂ E) (f : E) :
    let P : E →L[ℂ] E := sumProjection F₁ F₂
    let P₁ : E →L[ℂ] E := (F₁ : Submodule ℂ E).starProjection
    let P₂ : E →L[ℂ] E := (F₂ : Submodule ℂ E).starProjection
    Filter.Tendsto (fun m : ℕ => (((P - P₁) * (P - P₂)) ^ m) f)
      Filter.atTop (nhds 0) := by
  intro P P₁ P₂
  set K : Submodule ℂ E := ((F₁ ⊔ F₂ : ClosedSubmodule ℂ E) : Submodule ℂ E) with hK
  have hKc : IsClosed (K : Set E) := (F₁ ⊔ F₂).isClosed
  have h1K : (F₁ : Submodule ℂ E) ≤ K := fun x hx => (le_sup_left : F₁ ≤ F₁ ⊔ F₂) hx
  have h2K : (F₂ : Submodule ℂ E) ≤ K := fun x hx => (le_sup_right : F₂ ≤ F₁ ⊔ F₂) hx
  have hc1 : IsClosed ((K ⊓ (F₁ : Submodule ℂ E)ᗮ : Submodule ℂ E) : Set E) := by
    rw [Submodule.coe_inf]
    exact hKc.inter (Submodule.isClosed_orthogonal _)
  haveI : CompleteSpace (K ⊓ (F₁ : Submodule ℂ E)ᗮ : Submodule ℂ E) :=
    completeSpace_coe_iff_isComplete.2 hc1.isComplete
  have hc2 : IsClosed ((K ⊓ (F₂ : Submodule ℂ E)ᗮ : Submodule ℂ E) : Set E) := by
    rw [Submodule.coe_inf]
    exact hKc.inter (Submodule.isClosed_orthogonal _)
  haveI : CompleteSpace (K ⊓ (F₂ : Submodule ℂ E)ᗮ : Submodule ℂ E) :=
    completeSpace_coe_iff_isComplete.2 hc2.isComplete
  have e1 : P - P₁ = (K ⊓ (F₁ : Submodule ℂ E)ᗮ).starProjection :=
    AltProj503.proj_diff K (F₁ : Submodule ℂ E) h1K
  have e2 : P - P₂ = (K ⊓ (F₂ : Submodule ℂ E)ᗮ).starProjection :=
    AltProj503.proj_diff K (F₂ : Submodule ℂ E) h2K
  rw [e1, e2]
  have hK0 : ∀ z, z ∈ (⊥ : Submodule ℂ E) ↔
      z ∈ K ⊓ (F₂ : Submodule ℂ E)ᗮ ∧ z ∈ K ⊓ (F₁ : Submodule ℂ E)ᗮ := by
    intro z
    constructor
    · intro hz
      rw [Submodule.mem_bot] at hz
      subst hz
      exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
    · rintro ⟨hz2, hz1⟩
      obtain ⟨hzK, hzo2⟩ := Submodule.mem_inf.1 hz2
      obtain ⟨-, hzo1⟩ := Submodule.mem_inf.1 hz1
      rw [Submodule.mem_bot]
      let C : ClosedSubmodule ℂ E :=
        { toSubmodule := (ℂ ∙ z)ᗮ, isClosed' := Submodule.isClosed_orthogonal _ }
      have hC1 : F₁ ≤ C := by
        intro x hx
        show x ∈ (ℂ ∙ z)ᗮ
        rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
        exact inner_eq_zero_symm.1 ((Submodule.mem_orthogonal _ _).1 hzo1 x hx)
      have hC2 : F₂ ≤ C := by
        intro x hx
        show x ∈ (ℂ ∙ z)ᗮ
        rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
        exact inner_eq_zero_symm.1 ((Submodule.mem_orthogonal _ _).1 hzo2 x hx)
      have hzC : z ∈ C := (sup_le hC1 hC2 : F₁ ⊔ F₂ ≤ C) hzK
      have : z ∈ (ℂ ∙ z)ᗮ := hzC
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_self_eq_zero] at this
      exact this
  have := AltProj503.core (K ⊓ (F₂ : Submodule ℂ E)ᗮ) (K ⊓ (F₁ : Submodule ℂ E)ᗮ) ⊥ hK0 f
  rw [Submodule.starProjection_bot, ContinuousLinearMap.zero_apply] at this
  exact this


open AronszajnRK.SubspaceSum in
theorem altp_5a66 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (F₁ F₂ : ClosedSubmodule ℂ E) (f : E) :
    let P₁ : E →L[ℂ] E := (F₁ : Submodule ℂ E).starProjection
    let P₂ : E →L[ℂ] E := (F₂ : Submodule ℂ E).starProjection
    Filter.Tendsto (fun m : ℕ => ((P₂ * P₁) ^ m) f) Filter.atTop
      (nhds (intersectionProjection F₁ F₂ f)) := by
  intro P₁ P₂
  unfold intersectionProjection
  exact AltProj503.core (F₁ : Submodule ℂ E) (F₂ : Submodule ℂ E)
    ((F₁ ⊓ F₂ : ClosedSubmodule ℂ E) : Submodule ℂ E) (fun z => by simp) f


open AronszajnRK.SubspaceSum in
theorem pid_5a66 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (F₁ F₂ : ClosedSubmodule ℂ E) (m : ℕ) (hm : 1 ≤ m) :
    let P : E →L[ℂ] E := sumProjection F₁ F₂
    let P₁ : E →L[ℂ] E := (F₁ : Submodule ℂ E).starProjection
    let P₂ : E →L[ℂ] E := (F₂ : Submodule ℂ E).starProjection
    ((P - P₁) * (P - P₂)) ^ m =
      P - (∑ k ∈ Finset.range m,
        (P₁ * (P₂ * P₁) ^ k + P₂ * (P₁ * P₂) ^ k -
          (P₂ * P₁) ^ (k + 1) - (P₁ * P₂) ^ (k + 1))) -
        (P₂ * P₁) ^ m := by
  intro P P₁ P₂
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have le1 : (F₁ : Submodule ℂ E) ≤ ((F₁ ⊔ F₂ : ClosedSubmodule ℂ E) : Submodule ℂ E) :=
    ClosedSubmodule.toSubmodule_le_toSubmodule.mpr le_sup_left
  have le2 : (F₂ : Submodule ℂ E) ≤ ((F₁ ⊔ F₂ : ClosedSubmodule ℂ E) : Submodule ℂ E) :=
    ClosedSubmodule.toSubmodule_le_toSubmodule.mpr le_sup_right
  have idem : ∀ K : ClosedSubmodule ℂ E,
      (K : Submodule ℂ E).starProjection * (K : Submodule ℂ E).starProjection =
        (K : Submodule ℂ E).starProjection :=
    fun K => (K : Submodule ℂ E).isIdempotentElem_starProjection
  have right : ∀ U V : ClosedSubmodule ℂ E, (U : Submodule ℂ E) ≤ (V : Submodule ℂ E) →
      (U : Submodule ℂ E).starProjection * (V : Submodule ℂ E).starProjection =
        (U : Submodule ℂ E).starProjection :=
    fun U V h => Submodule.starProjection_comp_starProjection_of_le h
  have left : ∀ U V : ClosedSubmodule ℂ E, (U : Submodule ℂ E) ≤ (V : Submodule ℂ E) →
      (V : Submodule ℂ E).starProjection * (U : Submodule ℂ E).starProjection =
        (U : Submodule ℂ E).starProjection := by
    intro U V h
    ext x
    show (V : Submodule ℂ E).starProjection ((U : Submodule ℂ E).starProjection x) =
      (U : Submodule ℂ E).starProjection x
    rw [Submodule.starProjection_eq_self_iff]
    exact h (Submodule.starProjection_apply_mem _ x)
  exact ProjId43c38e6a.key P P₁ P₂ (idem F₁) (idem F₂) (right _ _ le1) (right _ _ le2)
    (left _ _ le1) (left _ _ le2) (idem _) n


open AronszajnRK.SubspaceSum in
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (F₁ F₂ : ClosedSubmodule ℂ E) (f : E) :
    let P₁ : E →L[ℂ] E := (F₁ : Submodule ℂ E).starProjection
    let P₂ : E →L[ℂ] E := (F₂ : Submodule ℂ E).starProjection
    Filter.Tendsto
      (fun m : ℕ =>
        (intersectionProjection F₁ F₂ +
          ∑ k ∈ Finset.range m,
            (P₁ * (P₂ * P₁) ^ k + P₂ * (P₁ * P₂) ^ k -
              (P₂ * P₁) ^ (k + 1) - (P₁ * P₂) ^ (k + 1))) f)
      Filter.atTop (nhds (sumProjection F₁ F₂ f)) := by
  intro P₁ P₂
  have hA := altp_5a66 F₁ F₂ f
  have hC := cpv_5a66 F₁ F₂ f
  simp only at hA hC
  have hlim : Filter.Tendsto
      (fun m : ℕ => intersectionProjection F₁ F₂ f + (sumProjection F₁ F₂ f -
        ((P₂ * P₁) ^ m) f - (((sumProjection F₁ F₂ - P₁) * (sumProjection F₁ F₂ - P₂)) ^ m) f))
      Filter.atTop (nhds (sumProjection F₁ F₂ f)) := by
    have := (tendsto_const_nhds (x := intersectionProjection F₁ F₂ f)).add
      (((tendsto_const_nhds (x := sumProjection F₁ F₂ f)).sub hA).sub hC)
    simpa using this
  rw [← Filter.tendsto_add_atTop_iff_nat 1] at hlim ⊢
  refine hlim.congr (fun n => ?_)
  have hk := pid_5a66 F₁ F₂ (n + 1) (by omega)
  simp only at hk
  rw [ContinuousLinearMap.add_apply]
  congr 1
  have e : (∑ k ∈ Finset.range (n + 1),
      (P₁ * (P₂ * P₁) ^ k + P₂ * (P₁ * P₂) ^ k - (P₂ * P₁) ^ (k + 1) - (P₁ * P₂) ^ (k + 1))) =
      sumProjection F₁ F₂ - (P₂ * P₁) ^ (n + 1) -
        ((sumProjection F₁ F₂ - P₁) * (sumProjection F₁ F₂ - P₂)) ^ (n + 1) := by
    rw [hk]; abel
  rw [e]
  simp only [ContinuousLinearMap.sub_apply]
