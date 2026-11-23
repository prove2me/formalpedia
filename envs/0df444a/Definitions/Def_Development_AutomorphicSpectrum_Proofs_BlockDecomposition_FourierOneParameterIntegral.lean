-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierOneParameterIntegral
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierOneParameterIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:30.821145+00:00
-- url     : https://prove2.me/theorems/b7c1d58c-3849-4300-af6a-858ae3ab3a3a
-- title:
--   Fourier One Parameter Integral
-- statement:
--   Definitions and structural lemmas for Fourier One Parameter Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierOneParameterIntegral.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
namespace GlobalTheory.CompanionTheory.OneParamFourier
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [MeasurableSpace A] [BorelSpace A]
end GlobalTheory.CompanionTheory.OneParamFourier


