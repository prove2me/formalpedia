-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncModelEmbeddedLogResolution
-- name    : Development_AutomorphicSpectrum_Proofs_MetricProofs_SncModelEmbeddedLogResolution
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T15:48:55.871972+00:00
-- url     : https://prove2.me/theorems/001677c8-8635-46b7-b7e1-4126a222f6f6
-- title:
--   Snc Model Embedded Log Resolution
-- statement:
--   Definitions and structural lemmas for Snc Model Embedded Log Resolution, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncModelEmbeddedLogResolution.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterAlgRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LocTransfer
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Immersion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterMinor
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCompactEmbeddedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionTransitionPolynomialStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCoverAndConeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionLocalChartPolynomialStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionRegularLocalRingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionBoundaryNormalCrossingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
  GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes


