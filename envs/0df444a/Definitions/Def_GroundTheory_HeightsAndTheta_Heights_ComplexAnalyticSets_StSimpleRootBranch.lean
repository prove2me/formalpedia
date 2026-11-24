-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSimpleRootBranch
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSimpleRootBranch
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:30.031657+00:00
-- url     : https://prove2.me/theorems/ee3d733c-c529-42cd-ad1c-f3c378bcddbd
-- title:
--   St Simple Root Branch
-- statement:
--   Definitions and structural lemmas for St Simple Root Branch, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSimpleRootBranch.lean

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
namespace GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
def SimpleRootBranch.Statement : Prop :=
  ∀ (d : ℕ) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (y : Fin d → ℂ) (τ : ℂ),
    (p.map (MvPolynomial.eval y)).IsRoot τ →
      (p.map (MvPolynomial.eval y)).derivative.eval τ ≠ 0 →
        ∃ (U : Set (Fin d → ℂ)) (B : Set ℂ) (ψ : (Fin d → ℂ) → ℂ),
          IsOpen U ∧ y ∈ U ∧ IsOpen B ∧ τ ∈ B ∧ DifferentiableOn ℂ ψ U ∧ ψ y = τ ∧
            ∀ w ∈ U, ψ w ∈ B ∧
              ∀ s ∈ B, ((p.map (MvPolynomial.eval w)).IsRoot s ↔ s = ψ w)
end
end GroundTheory.Heights₂.Heights.ComplexSets


