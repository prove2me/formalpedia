-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialDecayByMidpoints
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialDecayByMidpoints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:09.84392+00:00
-- url     : https://prove2.me/theorems/127f61c3-27c8-4565-a8bf-6ac3956ebb83
-- title:
--   Exponential Decay By Midpoints
-- statement:
--   Definitions and structural lemmas for Exponential Decay By Midpoints, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExponentialDecayByMidpoints.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
namespace GlobalTheory.CompanionTheory.TubeFourier
end GlobalTheory.CompanionTheory.TubeFourier


