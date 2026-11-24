-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDiscrAdjoin
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDiscrAdjoin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:21.025967+00:00
-- url     : https://prove2.me/theorems/3232ae15-adf4-4b1d-9c74-b0320774f1bb
-- title:
--   St Discr Adjoin
-- statement:
--   Definitions and structural lemmas for St Discr Adjoin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StDiscrAdjoin.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
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
noncomputable section
def DiscrAdjoin.Statement : Prop :=
  ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (ℓ : L), IsIntegral R ℓ →
    IntermediateField.adjoin K {ℓ} = ⊤ →
      (minpoly R ℓ).natDegree = Module.finrank K L ∧ (minpoly R ℓ).discr ≠ 0 ∧
      ∀ z : L, IsIntegral R z → (minpoly R ℓ).discr • z ∈ Algebra.adjoin R {ℓ}
end
end GroundTheory.Heights₂.Heights.ComplexSets


