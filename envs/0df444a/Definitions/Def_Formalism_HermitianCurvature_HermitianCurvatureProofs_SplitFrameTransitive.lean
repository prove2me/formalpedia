-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitFrameTransitive
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitFrameTransitive
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:20:56.516627+00:00
-- url     : https://prove2.me/theorems/8b2a1f62-e6fd-4332-98e2-38b778b5eacb
-- title:
--   Split Frame Transitive
-- statement:
--   Definitions and structural lemmas for Split Frame Transitive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitFrameTransitive.lean

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.S3x4
open Matrix Finset Module
section Lin
variable {K : Type*} [Field K]
end Lin
end Formalism.FourierDecayAlt.P.S3x4
namespace Formalism.FourierDecayAlt.P.S3x4
open Matrix Finset Module
section Lin
variable {K : Type*} [Field K]
variable {V A A' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup A] [Module K A]
  [AddCommGroup A'] [Module K A']
def kerPart (π : V →ₗ[K] A) (σ : A →ₗ[K] V) (hσ : ∀ x, π (σ x) = x) (j : A' →ₗ[K] V) :
    A' →ₗ[K] LinearMap.ker π :=
  LinearMap.codRestrict _ (j - σ ∘ₗ π ∘ₗ j) (fun x => by simp [hσ])
lemma kerPart_coe (π : V →ₗ[K] A) (σ : A →ₗ[K] V) (hσ : ∀ x, π (σ x) = x) (j : A' →ₗ[K] V)
    (x : A') : (kerPart π σ hσ j x : V) = j x - σ (π (j x)) := rfl
lemma injective_iff_kerPart (π : V →ₗ[K] A) (σ : A →ₗ[K] V) (hσ : ∀ x, π (σ x) = x)
    (j : A' →ₗ[K] V) :
    Function.Injective j ↔ LinearMap.ker (π ∘ₗ j) ⊓ LinearMap.ker (kerPart π σ hσ j) = ⊥ := by
  rw [Submodule.eq_bot_iff, ← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  constructor
  · rintro h x ⟨hx1, hx2⟩
    apply h
    have h1 : π (j x) = 0 := hx1
    have h2 : (kerPart π σ hσ j x : V) = 0 := by
      rw [LinearMap.mem_ker.mp hx2]; rfl
    rw [kerPart_coe, h1, map_zero, sub_zero] at h2
    exact h2
  · rintro h x hx
    have hx' : j x = 0 := hx
    apply h
    refine ⟨?_, ?_⟩
    · show π (j x) = 0
      rw [hx', map_zero]
    · show kerPart π σ hσ j x = 0
      apply Subtype.ext
      rw [kerPart_coe, hx']; simp
def fibEquiv (π : V →ₗ[K] A) (σ : A →ₗ[K] V) (hσ : ∀ x, π (σ x) = x) (R : A' →ₗ[K] A) :
    {j : A' →ₗ[K] V // Function.Injective j ∧ π ∘ₗ j = R} ≃
      {Y : A' →ₗ[K] LinearMap.ker π // LinearMap.ker R ⊓ LinearMap.ker Y = ⊥} where
  toFun j := ⟨kerPart π σ hσ j.1, by
    have := (injective_iff_kerPart π σ hσ j.1).mp j.2.1
    rwa [j.2.2] at this⟩
  invFun Y := ⟨(LinearMap.ker π).subtype ∘ₗ Y.1 + σ ∘ₗ R, by
    have h1 : π ∘ₗ ((LinearMap.ker π).subtype ∘ₗ Y.1 + σ ∘ₗ R) = R := by
      ext x; simp [hσ]
    have h2 : kerPart π σ hσ ((LinearMap.ker π).subtype ∘ₗ Y.1 + σ ∘ₗ R) = Y.1 := by
      ext x; rw [kerPart_coe]; simp [hσ]
    refine ⟨?_, h1⟩
    rw [injective_iff_kerPart π σ hσ, h1, h2]
    exact Y.2⟩
  left_inv j := by
    apply Subtype.ext
    ext x
    have := j.2.2
    simp [kerPart_coe, ← this]
  right_inv Y := by
    apply Subtype.ext
    ext x; rw [kerPart_coe]; simp [hσ]
end Lin
end Formalism.FourierDecayAlt.P.S3x4
namespace Formalism.FourierDecayAlt.P.S3x4
open Matrix Finset Module
section Mat
variable {K : Type} [Field K]
end Mat
end Formalism.FourierDecayAlt.P.S3x4
namespace Formalism.FourierDecayAlt.P
open Matrix Finset Module Formalism.FourierDecayAlt.P.S3x4
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.S3x4
open Matrix Finset Module Formalism.FourierDecayAlt.S3
end Formalism.FourierDecayAlt.P.S3x4
namespace Formalism.FourierDecayAlt.P
open Matrix Finset Module Formalism.FourierDecayAlt.P.S3x4 Formalism.FourierDecayAlt.S3
end Formalism.FourierDecayAlt.P


