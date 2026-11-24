-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInversionFiniteDim
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInversionFiniteDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:45.457015+00:00
-- url     : https://prove2.me/theorems/2fbb4f77-2cc9-4797-a1e3-5c62bceb51fe
-- title:
--   Fourier Inversion Finite Dim
-- statement:
--   Definitions and structural lemmas for Fourier Inversion Finite Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInversionFiniteDim.lean

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
open scoped FourierTransform RealInnerProductSpace
noncomputable section
namespace GlobalTheory.CompanionTheory.EisTube
universe u
end GlobalTheory.CompanionTheory.EisTube


