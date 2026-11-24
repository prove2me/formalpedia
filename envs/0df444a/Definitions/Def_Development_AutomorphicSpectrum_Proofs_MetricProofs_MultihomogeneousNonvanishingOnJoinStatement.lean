-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MultihomogeneousNonvanishingOnJoinStatement
-- name    : Development_AutomorphicSpectrum_Proofs_MetricProofs_MultihomogeneousNonvanishingOnJoinStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:53.534222+00:00
-- url     : https://prove2.me/theorems/b2759aae-159e-4fd5-a4b7-801315811e38
-- title:
--   Multihomogeneous Nonvanishing On Join Statement
-- statement:
--   Definitions and structural lemmas for Multihomogeneous Nonvanishing On Join Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/MultihomogeneousNonvanishingOnJoinStatement.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MultihomogeneousNonvanishingOnJoin
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology


