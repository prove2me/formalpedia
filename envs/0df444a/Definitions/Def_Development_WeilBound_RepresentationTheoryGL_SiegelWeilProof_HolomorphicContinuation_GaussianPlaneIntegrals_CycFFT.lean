-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFT
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFT
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:42:24.215696+00:00
-- url     : https://prove2.me/theorems/e0db1550-48be-43b2-aec7-0b44c46233fa
-- title:
--   Cyc FFT
-- statement:
--   Definitions and structural lemmas for Cyc FFT, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/CycFFT.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace PositivityTheory.Rg.Sw.FFTSteps.CycF
variable {m n : ℕ} {ε : Fin m → Bool}
end PositivityTheory.Rg.Sw.FFTSteps.CycF
namespace PositivityTheory.Rg.Sw.FFTSteps
open CycF
end PositivityTheory.Rg.Sw.FFTSteps


