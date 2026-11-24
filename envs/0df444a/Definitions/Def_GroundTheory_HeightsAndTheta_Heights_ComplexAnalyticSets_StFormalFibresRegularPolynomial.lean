-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormalFibresRegularPolynomial
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormalFibresRegularPolynomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:04.431667+00:00
-- url     : https://prove2.me/theorems/1209f6c6-e8c3-466d-aabb-c84811f0b70b
-- title:
--   St Formal Fibres Regular Polynomial
-- statement:
--   Definitions and structural lemmas for St Formal Fibres Regular Polynomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StFormalFibresRegularPolynomial.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatNormalFibres
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
def FormalFibresRegularPolynomial.Statement : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ) (M : Ideal (MvPolynomial (Fin n) k)), M.IsMaximal →
    ∀ (P : Ideal (AdicCompletion M (MvPolynomial (Fin n) k))) [P.IsPrime],
      IsRegularLocalRing (primeFibreLocalRing (MvPolynomial (Fin n) k) P)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


