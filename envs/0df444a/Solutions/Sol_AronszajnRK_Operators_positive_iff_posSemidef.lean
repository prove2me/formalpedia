-- Prove2me | solution 1 for AronszajnRK.Operators.positive_iff_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T00:53:52.052072+00:00
-- url     : https://prove2.me/submissions/d5a79c47-8c93-4391-a99a-6252a494d68d

import Mathlib
import Definitions.Def_AronszajnRK_Operators_opKernel

open scoped InnerProductSpace ComplexOrder

set_option autoImplicit false

namespace P03576c6f

variable {H : Type*} {X : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]

lemma eval_eq_inner (f : H) (x : X) : f x = ⟪RKHS.kerFun H x 1, f⟫_ℂ := by
  rw [RKHS.kerFun_inner]; simp

lemma opKernel_eq (L : H →L[ℂ] H) (x y : X) :
    AronszajnRK.Operators.opKernel L x y = ⟪L (RKHS.kerFun H x 1), RKHS.kerFun H y 1⟫_ℂ := by
  unfold AronszajnRK.Operators.opKernel
  rw [eval_eq_inner, ContinuousLinearMap.adjoint_inner_right]

lemma quad_eq (L : H →L[ℂ] H) (ξ : X →₀ ℂ) :
    (ξ.sum fun i a ↦ ξ.sum fun j b ↦
      star a * (Matrix.of (AronszajnRK.Operators.opKernel L : X → X → ℂ)) i j * b)
      = ⟪L (ξ.sum fun i c ↦ c • RKHS.kerFun H i 1), ξ.sum fun i c ↦ c • RKHS.kerFun H i 1⟫_ℂ := by
  rw [map_finsuppSum, Finsupp.sum_inner]
  refine Finsupp.sum_congr fun i _ ↦ ?_
  rw [Finsupp.inner_sum]
  refine Finsupp.sum_congr fun j _ ↦ ?_
  rw [map_smul, inner_smul_left, inner_smul_right, Matrix.of_apply, opKernel_eq]
  rw [Complex.star_def]
  ring

lemma span_le (S : Submodule ℂ H) (hS : ∀ x : X, RKHS.kerFun H x 1 ∈ S) :
    Submodule.span ℂ {RKHS.kerFun H x v | (x : X) (v : ℂ)} ≤ S := by
  rw [Submodule.span_le]
  rintro _ ⟨x, v, rfl⟩
  have : RKHS.kerFun H x v = v • RKHS.kerFun H x 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [SetLike.mem_coe, this]
  exact S.smul_mem v (hS x)

end P03576c6f

open AronszajnRK.Operators InnerProductSpace ComplexOrder in
theorem solution {H : Type*} {X : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ] (L : H →L[ℂ] H) :
    (∀ f : H, 0 ≤ ⟪f, L f⟫_ℂ) ↔ (Matrix.of (opKernel L : X → X → ℂ)).PosSemidef := by
  constructor
  · intro hpos
    have hP : L.IsPositive := by
      rw [ContinuousLinearMap.isPositive_iff_complex]
      intro x
      have h := hpos x
      rw [← inner_conj_symm] at h
      rw [Complex.nonneg_iff] at h
      simp only [Complex.conj_re, Complex.conj_im] at h
      refine ⟨Complex.ext (by simp) (by simp; linarith [h.2]), h.1⟩
    have hsym := hP.isSymmetric
    refine ⟨?_, fun ξ ↦ ?_⟩
    · ext x y
      simp only [Matrix.conjTranspose_apply, Matrix.of_apply, P03576c6f.opKernel_eq]
      rw [Complex.star_def, inner_conj_symm]
      exact (hsym _ _).symm
    · rw [P03576c6f.quad_eq]
      rw [show ∀ g : H, ⟪L g, g⟫_ℂ = ⟪g, L g⟫_ℂ from fun g ↦ hsym g g]
      exact hpos _
  · intro hM f
    set k : X → H := fun x ↦ RKHS.kerFun H x 1 with hk
    have hspan : ∀ g ∈ Submodule.span ℂ (Set.range k), 0 ≤ ⟪g, L g⟫_ℂ := by
      intro g hg
      rw [Finsupp.mem_span_range_iff_exists_finsupp] at hg
      obtain ⟨ξ, rfl⟩ := hg
      have h := hM.2 ξ
      rw [P03576c6f.quad_eq] at h
      rw [← inner_conj_symm]
      exact star_nonneg_iff.mpr h
    have hclosed : IsClosed {g : H | 0 ≤ ⟪g, L g⟫_ℂ} :=
      isClosed_le continuous_const (continuous_id.inner (L.continuous))
    have hle : Submodule.span ℂ {RKHS.kerFun H x v | (x : X) (v : ℂ)} ≤
        Submodule.span ℂ (Set.range k) :=
      P03576c6f.span_le _ fun x ↦ Submodule.subset_span ⟨x, rfl⟩
    have hdense := RKHS.kerFun_dense (𝕜 := ℂ) (H := H) (X := X) (V := ℂ)
    have hf : f ∈ (Submodule.span ℂ (Set.range k)).topologicalClosure := by
      have := Submodule.topologicalClosure_mono hle
      rw [hdense, top_le_iff] at this
      rw [this]; trivial
    have hf' : f ∈ closure (Submodule.span ℂ (Set.range k) : Set H) := by
      rw [← Submodule.topologicalClosure_coe]; exact hf
    exact closure_minimal (fun g hg ↦ hspan g hg) hclosed hf'
