-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDefiniteHermitianOfFourMulLtStatement
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDefiniteHermitianOfFourMulLtStatement
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:59:37.227486+00:00
-- url     : https://prove2.me/theorems/1c145c24-33e5-53f7-8f64-7e0e14794206
-- title:
--   Siegel Weil Definite Hermitian Of Four Mul Lt Statement
-- statement:
--   Definitions and structural lemmas for Siegel Weil Definite Hermitian Of Four Mul Lt Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelWeilDefiniteHermitianOfFourMulLtStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDefiniteHermitianOfFourMulLt
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


