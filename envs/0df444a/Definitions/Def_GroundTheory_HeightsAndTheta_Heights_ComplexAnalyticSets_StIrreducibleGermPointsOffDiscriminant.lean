-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPointsOffDiscriminant
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPointsOffDiscriminant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:19.708455+00:00
-- url     : https://prove2.me/theorems/907bd3b9-35da-4782-9721-45d9915781d8
-- title:
--   St Irreducible Germ Points Off Discriminant
-- statement:
--   Definitions and structural lemmas for St Irreducible Germ Points Off Discriminant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StIrreducibleGermPointsOffDiscriminant.lean

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
def IrreducibleGermPointsOffDiscriminant.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X x → GermIrreducibleAt X x →
    (∃ W ∈ 𝓝 x, ∀ x' ∈ X ∩ W, A x' = A x → x' = x) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) → (∀ᶠ z in 𝓝 x, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A x), h y = 0) →
    ∃ δ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ δ (A x) ∧ (¬ ∀ᶠ y in 𝓝 (A x), δ y = 0) ∧
      ∀ W ∈ 𝓝 x, ∀ᶠ y in 𝓝 (A x), δ y ≠ 0 → ∃ x' ∈ X ∩ W, A x' = y
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


