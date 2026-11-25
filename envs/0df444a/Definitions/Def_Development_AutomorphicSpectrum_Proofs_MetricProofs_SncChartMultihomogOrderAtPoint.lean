-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncChartMultihomogOrderAtPoint
-- name    : Development_AutomorphicSpectrum_Proofs_MetricProofs_SncChartMultihomogOrderAtPoint
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T14:12:37.538266+00:00
-- url     : https://prove2.me/theorems/8749cb55-e29d-54e4-b8a2-521f0314bcab
-- title:
--   Snc Chart Multihomog Order At Point
-- statement:
--   Definitions and structural lemmas for Snc Chart Multihomog Order At Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncChartMultihomogOrderAtPoint.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono


