-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:58.219038+00:00
-- url     : https://prove2.me/theorems/2556d4b9-cc8e-4024-a321-c2659a78e907
-- title:
--   Weil Action Level Sup Norm Uniform In Lattice Statement
-- statement:
--   Definitions and structural lemmas for Weil Action Level Sup Norm Uniform In Lattice Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/WeilActionLevelSupNormUniformInLatticeStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
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


