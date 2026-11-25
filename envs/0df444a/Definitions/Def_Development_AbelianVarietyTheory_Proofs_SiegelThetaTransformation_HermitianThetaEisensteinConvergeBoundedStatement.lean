-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBoundedStatement
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBoundedStatement
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:44:17.942211+00:00
-- url     : https://prove2.me/theorems/53cb5131-6aa5-49d0-a9b7-b1d092891eda
-- title:
--   Hermitian Theta Eisenstein Converge Bounded Statement
-- statement:
--   Definitions and structural lemmas for Hermitian Theta Eisenstein Converge Bounded Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianThetaEisensteinConvergeBoundedStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBounded
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
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
open scoped ComplexConjugate ComplexOrder Real


