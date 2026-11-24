-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLawsStatement
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLawsStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:58.47391+00:00
-- url     : https://prove2.me/theorems/0dbd5451-e08a-4c54-9ff0-04a0819a6834
-- title:
--   Hermitian Heisenberg Operator Laws Statement
-- statement:
--   Definitions and structural lemmas for Hermitian Heisenberg Operator Laws Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianHeisenbergOperatorLawsStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
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


