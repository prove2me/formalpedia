-- Prove2me | solution 1 for AronszajnRK.Inclusion.intersection_closed_transformation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T11:09:03.029348+00:00
-- url     : https://prove2.me/submissions/cc174d35-d6ea-49ae-88d3-f7359579857a

import Mathlib
import Definitions.Def_AronszajnRK_Inclusion_IsClosedTransformation

set_option autoImplicit false

open Filter Topology in
theorem solution {X H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [RKHS ℂ H₂ X ℂ] :
    ∃ T : (LinearMap.range ((RKHS.coeCLM ℂ : H₂ →L[ℂ] X → ℂ) : H₂ →ₗ[ℂ] X → ℂ)).comap
        ((RKHS.coeCLM ℂ : H₁ →L[ℂ] X → ℂ) : H₁ →ₗ[ℂ] X → ℂ) →ₗ[ℂ] H₂,
      (∀ f, ⇑(T f) = ⇑(f : H₁)) ∧ AronszajnRK.Inclusion.IsClosedTransformation T := by
  set L₁ : H₁ →ₗ[ℂ] X → ℂ := ((RKHS.coeCLM ℂ : H₁ →L[ℂ] X → ℂ) : H₁ →ₗ[ℂ] X → ℂ) with hL₁
  set L₂ : H₂ →ₗ[ℂ] X → ℂ := ((RKHS.coeCLM ℂ : H₂ →L[ℂ] X → ℂ) : H₂ →ₗ[ℂ] X → ℂ) with hL₂
  have inj₂ : Function.Injective L₂ := RKHS.coeCLM_injective
  let E : H₂ ≃ₗ[ℂ] LinearMap.range L₂ := LinearEquiv.ofInjective L₂ inj₂
  let S : (LinearMap.range L₂).comap L₁ →ₗ[ℂ] LinearMap.range L₂ :=
    LinearMap.codRestrict (LinearMap.range L₂) (L₁ ∘ₗ ((LinearMap.range L₂).comap L₁).subtype)
      (fun f => f.2)
  let T := (E.symm : LinearMap.range L₂ →ₗ[ℂ] H₂) ∘ₗ S
  have key : ∀ f, L₂ (T f) = L₁ (f : H₁) := by
    intro f
    calc L₂ (T f) = ((E (E.symm (S f)) : LinearMap.range L₂) : X → ℂ) :=
          (LinearEquiv.ofInjective_apply L₂ (h := inj₂) (E.symm (S f))).symm
      _ = ((S f : LinearMap.range L₂) : X → ℂ) := by rw [E.apply_symm_apply]
      _ = L₁ (f : H₁) := rfl
  refine ⟨T, fun f => key f, ?_⟩
  intro u f f₁ hu hT
  have c1 : Tendsto (fun n => L₁ (u n : H₁)) atTop (𝓝 (L₁ f)) :=
    ((RKHS.coeCLM ℂ : H₁ →L[ℂ] X → ℂ).continuous.tendsto f).comp hu
  have c2 : Tendsto (fun n => L₂ (T (u n))) atTop (𝓝 (L₂ f₁)) :=
    ((RKHS.coeCLM ℂ : H₂ →L[ℂ] X → ℂ).continuous.tendsto f₁).comp hT
  have heq : L₁ f = L₂ f₁ := by
    refine tendsto_nhds_unique c1 ?_
    simpa only [key] using c2
  have hf : f ∈ (LinearMap.range L₂).comap L₁ := ⟨f₁, heq.symm⟩
  refine ⟨hf, inj₂ ?_⟩
  rw [key]
  exact heq
