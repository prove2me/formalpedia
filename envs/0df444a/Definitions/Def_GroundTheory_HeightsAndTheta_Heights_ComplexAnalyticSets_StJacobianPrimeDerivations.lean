-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StJacobianPrimeDerivations
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StJacobianPrimeDerivations
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:14.241277+00:00
-- url     : https://prove2.me/theorems/81c19af4-602d-48c0-8fba-376f978e6a10
-- title:
--   St Jacobian Prime Derivations
-- statement:
--   Definitions and structural lemmas for St Jacobian Prime Derivations, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StJacobianPrimeDerivations.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormalFibresRegular
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
def JacobianPrimeDerivations.Statement : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ) (p : Ideal (MvPolynomial (Fin n) k)), p.IsPrime →
    ∃ (h : ℕ) (f : Fin h → MvPolynomial (Fin n) k)
      (D : Fin h → Derivation ℤ (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k))
      (s : MvPolynomial (Fin n) k),
      (∀ i, f i ∈ p) ∧ s ∉ p ∧ (∀ x ∈ p, s * x ∈ Ideal.span (Set.range f)) ∧
        (Matrix.of fun i j => D j (f i)).det ∉ p
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


