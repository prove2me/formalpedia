-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionLocalChartPolynomial
-- name    : Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionLocalChartPolynomial
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T14:07:49.874657+00:00
-- url     : https://prove2.me/theorems/6f8448e3-0c19-4417-ad4c-4fde5906a33d
-- title:
--   Snc Resolution Local Chart Polynomial
-- statement:
--   Definitions and structural lemmas for Snc Resolution Local Chart Polynomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionLocalChartPolynomial.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv


