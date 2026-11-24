-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralHkDiag
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralHkDiag
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T12:55:38.961196+00:00
-- url     : https://prove2.me/theorems/d33d5b17-52c2-4688-a3b7-fc37956a1ce9
-- title:
--   Integral Hk Diag
-- statement:
--   Definitions and structural lemmas for Integral Hk Diag, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/IntegralHkDiag.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Module
open scoped ComplexConjugate
namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof
def e1 (z : ℂ) : ℂ := Complex.exp (((-(‖z‖ ^ 2)) : ℝ) : ℂ)
def hk (k l : ℕ) (z : ℂ) : ℂ := z ^ k * star z ^ l * e1 z
def jr (k : ℕ) : ℝ := ∫ z : ℂ, (‖z‖ ^ 2) ^ k * Real.exp (-(‖z‖ ^ 2))
end PositivityTheory.Rg.Sw.FFTSteps.PosProof


