-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceInvariantNormBoundedStatement
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceInvariantNormBoundedStatement
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:26:40.700095+00:00
-- url     : https://prove2.me/theorems/4c41db0c-4ea7-53d6-9ee7-0242ac7b0e02
-- title:
--   Siegel Weil Difference Invariant Norm Bounded Statement
-- statement:
--   Definitions and structural lemmas for Siegel Weil Difference Invariant Norm Bounded Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelWeilDifferenceInvariantNormBoundedStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceInvariantNormBounded
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical


