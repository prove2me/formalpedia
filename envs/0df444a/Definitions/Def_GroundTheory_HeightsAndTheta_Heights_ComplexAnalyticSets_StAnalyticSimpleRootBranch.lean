-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticSimpleRootBranch
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticSimpleRootBranch
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:36:04.787789+00:00
-- url     : https://prove2.me/theorems/79ab537e-e797-435b-8830-3c5e69ba1a8d
-- title:
--   St Analytic Simple Root Branch
-- statement:
--   Definitions and structural lemmas for St Analytic Simple Root Branch, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StAnalyticSimpleRootBranch.lean

import Mathlib
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
def AnalyticSimpleRootBranch.Statement : Prop :=
  ∀ (d N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (y : Fin d → ℂ) (τ : ℂ),
    (∀ j, AnalyticAt ℂ (a j) y) →
    τ ^ N + ∑ j, a j y * τ ^ (j : ℕ) = 0 →
    (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).derivative.eval τ ≠ 0 →
    ∃ (U : Set (Fin d → ℂ)) (B : Set ℂ) (ψ : (Fin d → ℂ) → ℂ),
      IsOpen U ∧ y ∈ U ∧ IsOpen B ∧ τ ∈ B ∧ AnalyticOnNhd ℂ ψ U ∧ ψ y = τ ∧
        ∀ y' ∈ U, ψ y' ∈ B ∧ ∀ s ∈ B, (s ^ N + ∑ j, a j y' * s ^ (j : ℕ) = 0 ↔ s = ψ y')
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


