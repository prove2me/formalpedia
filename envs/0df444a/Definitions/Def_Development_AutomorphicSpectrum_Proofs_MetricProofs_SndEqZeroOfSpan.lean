-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SndEqZeroOfSpan
-- name    : Development_AutomorphicSpectrum_Proofs_MetricProofs_SndEqZeroOfSpan
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T14:19:54.015662+00:00
-- url     : https://prove2.me/theorems/b677a7a8-041c-43f1-90b3-ac150eaece09
-- title:
--   Snd Eq Zero Of Span
-- statement:
--   Definitions and structural lemmas for Snd Eq Zero Of Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SndEqZeroOfSpan.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ExistsAlgHomAdjoinInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan
open TrivSqZeroExt
def dualPt {σ : Type} (t v : σ → ℂ) : σ → TrivSqZeroExt ℂ ℂ := fun q => inl (t q) + inr (v q)
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan


