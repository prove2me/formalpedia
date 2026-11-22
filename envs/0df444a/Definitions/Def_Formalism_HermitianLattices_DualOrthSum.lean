-- Prove2me | Definitions.Def_Formalism_HermitianLattices_DualOrthSum
-- name    : Formalism_HermitianLattices_DualOrthSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:06:24.750694+00:00
-- url     : https://prove2.me/theorems/dafe5541-1937-4c15-b275-f41ebf3cdf7f
-- title:
--   Dual Orth Sum
-- statement:
--   Definitions and structural lemmas for Dual Orth Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/DualOrthSum.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
namespace Formalism.HermitianLatticesTheory
def DualOrthSum : Prop :=
  ∀ (R K V : Type) [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (V₁ V₂ : Submodule K V), IsCompl V₁ V₂ →
    (∀ x ∈ V₁, ∀ y ∈ V₂, h x y = 0) → (∀ x ∈ V₂, ∀ y ∈ V₁, h x y = 0) →
    ∀ L₁ L₂ : Submodule R V, (L₁ : Set V) ⊆ V₁ → (L₂ : Set V) ⊆ V₂ →
      dual h (L₁ ⊔ L₂) = (dual h L₁ ⊓ V₁.restrictScalars R) ⊔ (dual h L₂ ⊓ V₂.restrictScalars R)
def DualLine : Prop :=
  ∀ (R K V : Type) [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) →
    ∀ z : V, h z z ≠ 0 →
      dual h (Submodule.span R {z}) ⊓ (Submodule.span K {z}).restrictScalars R =
        Submodule.span R {(h z z)⁻¹ • z} ∧
      ∀ (V' : Submodule K V) (L' : Submodule R V), IsCompl V' (Submodule.span K {z}) →
        (∀ x ∈ V', h x z = 0) → (L' : Set V) ⊆ V' →
        dual h L' ⊓ V'.restrictScalars R = L' →
        dual h (L' ⊔ Submodule.span R {z}) = L' ⊔ Submodule.span R {(h z z)⁻¹ • z}
end Formalism.HermitianLatticesTheory


