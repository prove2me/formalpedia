-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormalFibresRegular
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormalFibresRegular
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:40.806745+00:00
-- url     : https://prove2.me/theorems/c8e8fb5f-5f1f-4872-9e1f-e130303f0521
-- title:
--   St Formal Fibres Regular
-- statement:
--   Definitions and structural lemmas for St Formal Fibres Regular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StFormalFibresRegular.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatNormalFibres
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
def FormalFibresRegular.Statement : Prop :=
  ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A], Algebra.FiniteType k A →
    ∀ (m : Ideal A), m.IsMaximal → ∀ (P : Ideal (AdicCompletion m A)) [P.IsPrime],
      IsRegularLocalRing (primeFibreLocalRing A P)
noncomputable def polyOriginIdeal : Ideal (MvPolynomial (Fin 1) ℂ) :=
  RingHom.ker (MvPolynomial.eval (0 : Fin 1 → ℂ))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


