-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionBoundaryNormalCrossing
-- name    : Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionBoundaryNormalCrossing
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T15:25:26.978805+00:00
-- url     : https://prove2.me/theorems/7fd2cad1-95e1-4cfc-8307-653c70c94dd7
-- title:
--   Snc Resolution Boundary Normal Crossing
-- statement:
--   Definitions and structural lemmas for Snc Resolution Boundary Normal Crossing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionBoundaryNormalCrossing.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MinimalPrimesOfMultihomogSupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_RegularSystemOfParametersLocalRingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncChartRegularAtConePointStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncChartRegularWithBoundaryChoiceStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncChartMultihomogOrderAtPointStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_UnitTimesParameterMonomialStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SymbolicPowerInAffineChartStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SymbolicPowerFromAffineChartStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncChartParametersAtConePointStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par


