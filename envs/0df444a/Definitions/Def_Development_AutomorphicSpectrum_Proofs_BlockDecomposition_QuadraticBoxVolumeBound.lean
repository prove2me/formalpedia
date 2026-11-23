-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuadraticBoxVolumeBound
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuadraticBoxVolumeBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:25:04.5864+00:00
-- url     : https://prove2.me/theorems/3d1adb56-ebdd-4653-a885-543afd1c27d1
-- title:
--   Quadratic Box Volume Bound
-- statement:
--   Definitions and structural lemmas for Quadratic Box Volume Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuadraticBoxVolumeBound.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoreR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology GlobalTheory.CompanionTheory.WeilSiegel.Inf0
open scoped ENNReal NNReal Matrix
noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox
variable {P ι : Type}
end GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox


