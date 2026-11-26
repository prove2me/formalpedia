-- Prove2me | solution 1 for Arxiv2602_11197.forward_map_operator_splitting
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:45:09.012099+00:00
-- url     : https://prove2.me/submissions/687907f5-ddc4-449d-8b6b-07cd25899d6c

import Mathlib
import Definitions.Def_Arxiv2602_11197_Basic

set_option autoImplicit false

namespace S73FM
open Arxiv2602_11197

lemma cont0 (i : Fin 2) : Continuous (fun x : Plane => x i) := (EuclideanSpace.proj i).continuous

lemma uniq (L₁ L₂ : ℝ) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) : UniqueDiffOn ℝ (closedDomain L₁ L₂) := by
  apply uniqueDiffOn_convex
  · intro x hx y hy a b ha hb hab
    simp only [closedDomain, Set.mem_setOf_eq] at hx hy ⊢
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · have ho : IsOpen (domain L₁ L₂) := by
      unfold domain
      simp only [Set.setOf_and]
      exact (isOpen_lt continuous_const (cont0 0)).inter ((isOpen_lt (cont0 0) continuous_const).inter
        ((isOpen_lt continuous_const (cont0 1)).inter (isOpen_lt (cont0 1) continuous_const)))
    have hsub : domain L₁ L₂ ⊆ interior (closedDomain L₁ L₂) :=
      interior_maximal (fun x hx => by
        simp only [domain, closedDomain, Set.mem_setOf_eq] at hx ⊢
        exact ⟨hx.1.le, hx.2.1.le, hx.2.2.1.le, hx.2.2.2.le⟩) ho
    refine ⟨!₂[L₁ / 2, L₂ / 2], hsub ?_⟩
    simp only [domain, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith

lemma nd_add (L₁ L₂ : ℝ) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (u w : Plane → ℂ) (x : Plane)
    (hx : x ∈ closedDomain L₁ L₂)
    (hu : DifferentiableWithinAt ℝ u (closedDomain L₁ L₂) x)
    (hw : DifferentiableWithinAt ℝ w (closedDomain L₁ L₂) x) :
    normalDeriv L₁ L₂ (u + w) x = normalDeriv L₁ L₂ u x + normalDeriv L₁ L₂ w x := by
  unfold normalDeriv
  rw [fderivWithin_add (uniq L₁ L₂ hL₁ hL₂ x hx) hu hw]
  rfl

lemma abc_sub (L₁ L₂ : ℝ) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (x : Plane)
    (hx : x ∈ absorbingBoundary L₁ L₂) : x ∈ closedDomain L₁ L₂ := by
  simp only [absorbingBoundary, closedDomain, Set.mem_union, Set.mem_setOf_eq] at hx ⊢
  rcases hx with (h | h) | h
  · exact ⟨h.1.ge, by linarith, h.2.1.le, h.2.2.le⟩
  · exact ⟨by linarith, h.1.le, h.2.1.le, h.2.2.le⟩
  · exact ⟨h.1.le, h.2.1.le, by linarith, h.2.2.le⟩

lemma interior_eq (ω : ℝ) (v vbg : Plane → ℝ) (s pbg dp : Plane → ℂ) (x : Plane)
    (h1 : ContDiffAt ℝ 2 dp x) (h2 : ContDiffAt ℝ 2 pbg x) :
    helmholtzOp ω v (dp + pbg) x + s x =
      helmholtzOp ω vbg dp x + ((ω ^ 2 * deltaM v vbg x : ℝ) : ℂ) * (dp x + pbg x) +
        (helmholtzOp ω vbg pbg x + s x) := by
  unfold helmholtzOp deltaM
  rw [h1.laplacian_add h2]
  simp only [Pi.add_apply]
  push_cast
  ring

lemma cd_iff (dp pbg : Plane → ℂ) (x : Plane) (h2 : ContDiffAt ℝ 2 pbg x) :
    ContDiffAt ℝ 2 dp x ↔ ContDiffAt ℝ 2 (dp + pbg) x := by
  refine ⟨fun h => h.add h2, fun h => ?_⟩
  have := h.sub h2
  have e : (fun y => (dp + pbg) y - pbg y) = dp := by funext y; simp
  rwa [e] at this

lemma dw_iff (dp pbg : Plane → ℂ) (S : Set Plane) (x : Plane)
    (h2 : DifferentiableWithinAt ℝ pbg S x) :
    DifferentiableWithinAt ℝ dp S x ↔ DifferentiableWithinAt ℝ (dp + pbg) S x := by
  refine ⟨fun h => h.add h2, fun h => ?_⟩
  have := h.sub h2
  have e : dp + pbg - pbg = dp := by funext y; simp
  rwa [e] at this

/-- core equivalence, used for both theorems -/
lemma core (L₁ L₂ ω : ℝ) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (v vbg : Plane → ℝ)
    (s pbg dp : Plane → ℂ) (hpbg : IsHelmholtzSolution L₁ L₂ ω vbg s pbg) :
    IsResidualSolutionDerived L₁ L₂ ω v vbg pbg dp ↔ IsHelmholtzSolution L₁ L₂ ω v s (dp + pbg) := by
  obtain ⟨hI, hA, hF⟩ := hpbg
  unfold IsResidualSolutionDerived IsHelmholtzSolution
  constructor
  · rintro ⟨dI, dA, dF⟩
    refine ⟨?_, ?_, ?_⟩
    · filter_upwards [hI, dI] with x hx dx
      refine ⟨dx.1.add hx.1, ?_⟩
      have E := interior_eq ω v vbg s pbg dp x dx.1 hx.1
      rw [dx.2, hx.2] at E
      linear_combination E
    · intro x hx
      obtain ⟨hd, he⟩ := hA x hx
      obtain ⟨dd, de⟩ := dA x hx
      refine ⟨dd.add hd, ?_⟩
      rw [nd_add L₁ L₂ hL₁ hL₂ dp pbg x (abc_sub L₁ L₂ hL₁ hL₂ x hx) dd hd]
      simp only [Pi.add_apply]
      push_cast at de ⊢
      linear_combination de + he
    · intro x hx
      simp [hF x hx, dF x hx]
  · rintro ⟨dI, dA, dF⟩
    refine ⟨?_, ?_, ?_⟩
    · filter_upwards [hI, dI] with x hx dx
      have c1 : ContDiffAt ℝ 2 dp x := (cd_iff dp pbg x hx.1).2 dx.1
      refine ⟨c1, ?_⟩
      have E := interior_eq ω v vbg s pbg dp x c1 hx.1
      rw [dx.2, hx.2] at E
      linear_combination -E
    · intro x hx
      obtain ⟨hd, he⟩ := hA x hx
      obtain ⟨dd, de⟩ := dA x hx
      have d1 := (dw_iff dp pbg _ x hd).2 dd
      refine ⟨d1, ?_⟩
      rw [nd_add L₁ L₂ hL₁ hL₂ dp pbg x (abc_sub L₁ L₂ hL₁ hL₂ x hx) d1 hd] at de
      simp only [Pi.add_apply] at de
      push_cast
      linear_combination de - he
    · intro x hx
      have := dF x hx
      simp only [Pi.add_apply, hF x hx, add_zero] at this
      exact this

end S73FM

open Arxiv2602_11197 S73FM in
theorem solution (L₁ L₂ ω : ℝ) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hω : 0 < ω)
    (vbg dv : Plane → ℝ) (hvbg : ∀ x ∈ closedDomain L₁ L₂, 0 < vbg x)
    (hv : ∀ x ∈ closedDomain L₁ L₂, 0 < vbg x + dv x)
    (s pbg : Plane → ℂ) (hpbg : IsHelmholtzSolution L₁ L₂ ω vbg s pbg) (dp : Plane → ℂ) :
    IsResidualSolutionDerived L₁ L₂ ω (vbg + dv) vbg pbg dp ↔
      IsHelmholtzSolution L₁ L₂ ω (vbg + dv) s (dp + pbg) :=
  core L₁ L₂ ω hL₁ hL₂ (vbg + dv) vbg s pbg dp hpbg
