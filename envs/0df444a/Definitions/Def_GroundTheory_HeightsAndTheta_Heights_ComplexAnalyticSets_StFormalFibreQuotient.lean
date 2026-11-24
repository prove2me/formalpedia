-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormalFibreQuotient
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormalFibreQuotient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:04.284227+00:00
-- url     : https://prove2.me/theorems/7289208e-b310-4280-b503-7a060d3900a9
-- title:
--   St Formal Fibre Quotient
-- statement:
--   Definitions and structural lemmas for St Formal Fibre Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StFormalFibreQuotient.lean

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
def FormalFibreQuotient.Statement : Prop :=
  ∀ (B A : Type) [CommRing B] [CommRing A] (f : B →+* A), Function.Surjective f → IsNoetherianRing B →
    ∀ (m : Ideal A) (P : Ideal (AdicCompletion m A)) [P.IsPrime],
      ∃ P' : PrimeSpectrum (AdicCompletion (m.comap f) B),
        P'.asIdeal.comap (algebraMap B (AdicCompletion (m.comap f) B)) =
            (P.comap (algebraMap A (AdicCompletion m A))).comap f ∧
          Nonempty (primeFibreLocalRing A P ≃+* primeFibreLocalRing B P'.asIdeal)
noncomputable def dropSecondVariable : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  MvPolynomial.aeval fun i => if i = 0 then MvPolynomial.X 0 else 0
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


