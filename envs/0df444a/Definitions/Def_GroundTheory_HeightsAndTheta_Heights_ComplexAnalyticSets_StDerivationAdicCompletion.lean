-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDerivationAdicCompletion
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDerivationAdicCompletion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:13.603909+00:00
-- url     : https://prove2.me/theorems/ca07803d-d641-4d00-860e-17cf590b689b
-- title:
--   St Derivation Adic Completion
-- statement:
--   Definitions and structural lemmas for St Derivation Adic Completion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StDerivationAdicCompletion.lean

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
def DerivationAdicCompletion.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (D : Derivation ℤ R R),
    ∃ D' : Derivation ℤ (AdicCompletion I R) (AdicCompletion I R),
      ∀ r : R, D' (algebraMap R (AdicCompletion I R) r) = algebraMap R (AdicCompletion I R) (D r)
noncomputable def polyDerivX : Derivation ℤ (MvPolynomial (Fin 1) ℂ) (MvPolynomial (Fin 1) ℂ) :=
  (MvPolynomial.pderiv (0 : Fin 1)).restrictScalars ℤ
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


