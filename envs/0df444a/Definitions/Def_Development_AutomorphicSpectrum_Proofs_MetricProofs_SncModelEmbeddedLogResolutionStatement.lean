-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncModelEmbeddedLogResolutionStatement
-- name    : Development_AutomorphicSpectrum_Proofs_MetricProofs_SncModelEmbeddedLogResolutionStatement
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T16:02:15.783435+00:00
-- url     : https://prove2.me/theorems/78338b20-ed6a-4746-b443-95bc89d65b69
-- title:
--   Snc Model Embedded Log Resolution Statement
-- statement:
--   Definitions and structural lemmas for Snc Model Embedded Log Resolution Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncModelEmbeddedLogResolutionStatement.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncModelEmbeddedLogResolution
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)


