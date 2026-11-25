-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilFormulaDegreeSuccStatement
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilFormulaDegreeSuccStatement
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T06:02:08.28705+00:00
-- url     : https://prove2.me/theorems/df48d3e4-29a5-4305-9170-7d79e0aec713
-- title:
--   Siegel Weil Formula Degree Succ Statement
-- statement:
--   Definitions and structural lemmas for Siegel Weil Formula Degree Succ Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelWeilFormulaDegreeSuccStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilFormulaDegreeSucc
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


