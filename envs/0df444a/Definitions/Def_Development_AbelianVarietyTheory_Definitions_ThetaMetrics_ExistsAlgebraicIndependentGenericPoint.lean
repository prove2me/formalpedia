-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsAlgebraicIndependentGenericPoint
-- name    : Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsAlgebraicIndependentGenericPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:56.958623+00:00
-- url     : https://prove2.me/theorems/a330faca-3338-4aff-8f57-d341059b8467
-- title:
--   Exists Algebraic Independent Generic Point
-- statement:
--   Definitions and structural lemmas for Exists Algebraic Independent Generic Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsAlgebraicIndependentGenericPoint.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
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
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
section Dimension
end Dimension
section Principal
end Principal
section Injective
end Injective
section Existence
variable {K : Type u} [Field K] {σ β : Type} [Fintype σ] [Fintype β]
end Existence
end GlobalTheory.Chow


