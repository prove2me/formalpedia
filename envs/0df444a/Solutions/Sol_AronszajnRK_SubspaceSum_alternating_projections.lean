-- Prove2me | solution 1 for AronszajnRK.SubspaceSum.alternating_projections
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T09:31:50.393164+00:00
-- url     : https://prove2.me/submissions/3db0aa83-7b4f-4c9d-8b5e-217536dbf309

import Mathlib
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

end AltProj503

open AronszajnRK.SubspaceSum in
theorem solution {E : Type*} [NormedAddCommGroup E]
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
