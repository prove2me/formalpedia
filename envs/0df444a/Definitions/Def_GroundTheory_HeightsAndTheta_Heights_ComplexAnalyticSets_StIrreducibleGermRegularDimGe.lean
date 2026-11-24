-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermRegularDimGe
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermRegularDimGe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:34.786466+00:00
-- url     : https://prove2.me/theorems/624f9d0f-bb08-4645-8f3c-e894aac0fcc9
-- title:
--   St Irreducible Germ Regular Dim Ge
-- statement:
--   Definitions and structural lemmas for St Irreducible Germ Regular Dim Ge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StIrreducibleGermRegularDimGe.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermProjectionImageNear
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
def IrreducibleGermRegularDimGe.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∃ N ∈ 𝓝 w, ∀ x ∈ X ∩ N, ∀ (e : ℕ) (A' : (σ → ℂ) →L[ℂ] (Fin e → ℂ)) (O : Set (Fin e → ℂ))
      (V : Set (σ → ℂ)) (g : (Fin e → ℂ) → σ → ℂ),
      IsOpen O → IsOpen V → x ∈ V → AnalyticOnNhd ℂ g O → (∀ y ∈ O, A' (g y) = y) → X ∩ V = g '' O →
        d ≤ e
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


