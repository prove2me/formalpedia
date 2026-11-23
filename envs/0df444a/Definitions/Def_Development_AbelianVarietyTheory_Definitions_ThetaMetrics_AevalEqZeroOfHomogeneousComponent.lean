-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
-- name    : Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:45.96278+00:00
-- url     : https://prove2.me/theorems/0eab5e4a-e041-4c83-bb78-eae2b4cfa743
-- title:
--   Aeval Eq Zero Of Homogeneous Component
-- statement:
--   Definitions and structural lemmas for Aeval Eq Zero Of Homogeneous Component, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AevalEqZeroOfHomogeneousComponent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace GlobalTheory.Chow
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [CommRing K] {σ β : Type*}
end GlobalTheory.Chow


