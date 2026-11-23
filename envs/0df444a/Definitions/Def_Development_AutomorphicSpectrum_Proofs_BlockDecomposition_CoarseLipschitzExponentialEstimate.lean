-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoarseLipschitzExponentialEstimate
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoarseLipschitzExponentialEstimate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:54.401616+00:00
-- url     : https://prove2.me/theorems/e1e02e83-66b5-495d-9847-b521d859718a
-- title:
--   Coarse Lipschitz Exponential Estimate
-- statement:
--   Definitions and structural lemmas for Coarse Lipschitz Exponential Estimate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CoarseLipschitzExponentialEstimate.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
namespace GlobalTheory.CompanionTheory.EisCross
open PositivityTheory.RgEis
end GlobalTheory.CompanionTheory.EisCross


