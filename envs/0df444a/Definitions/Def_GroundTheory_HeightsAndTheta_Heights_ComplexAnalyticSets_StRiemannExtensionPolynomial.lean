-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRiemannExtensionPolynomial
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRiemannExtensionPolynomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:51:16.113683+00:00
-- url     : https://prove2.me/theorems/c45b217d-1ea1-4029-9e1b-c8255ff0242a
-- title:
--   St Riemann Extension Polynomial
-- statement:
--   Definitions and structural lemmas for St Riemann Extension Polynomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StRiemannExtensionPolynomial.lean

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
open MvPolynomial
noncomputable section
def RiemannExtensionPolynomial.Statement : Prop :=
  ∀ (k : ℕ) (P : MvPolynomial (Fin k) ℂ) (O : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → ℂ),
    P ≠ 0 → IsOpen O → ContinuousOn f O → DifferentiableOn ℂ f (O ∩ {y | eval y P ≠ 0}) →
    DifferentiableOn ℂ f O
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


