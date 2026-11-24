-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroupStatement
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroupStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:34.801164+00:00
-- url     : https://prove2.me/theorems/6ef44104-eafe-48f1-b0b9-96f3d4e6d301
-- title:
--   Hermitian Weil Action Comm Positive Unitary Group Statement
-- statement:
--   Definitions and structural lemmas for Hermitian Weil Action Comm Positive Unitary Group Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianWeilActionCommPositiveUnitaryGroupStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroup
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


