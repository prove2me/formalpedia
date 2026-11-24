-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:32.711696+00:00
-- url     : https://prove2.me/theorems/a48640a5-e842-475b-a8c5-00659f963a90
-- title:
--   St Irreducible Germ Primitive Form
-- statement:
--   Definitions and structural lemmas for St Irreducible Germ Primitive Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StIrreducibleGermPrimitiveForm.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleFiniteGermProjectionOpenAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology
def IrreducibleGermPrimitiveForm.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X x → GermIrreducibleAt X x →
    (∃ W ∈ 𝓝 x, ∀ x' ∈ X ∩ W, A x' = A x → x' = x) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) → (∀ᶠ z in 𝓝 x, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A x), h y = 0) →
    ∃ (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
      (q : σ → Fin N → (Fin d → ℂ) → ℂ),
      (∀ j, AnalyticAt ℂ (a j) (A x)) ∧ AnalyticAt ℂ δ (A x) ∧ (∀ i j, AnalyticAt ℂ (q i j) (A x)) ∧
      (¬ ∀ᶠ y in 𝓝 (A x), δ y = 0) ∧
      (∀ᶠ z in 𝓝 x, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) ∧
      (∀ᶠ y in 𝓝 (A x), δ y ≠ 0 →
        (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) ∧
      ∀ i, ∀ᶠ z in 𝓝 x, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


