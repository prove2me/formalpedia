-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContDiffIntegralDensity
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContDiffIntegralDensity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:21.320944+00:00
-- url     : https://prove2.me/theorems/f64f1ad4-d138-433c-b368-8a25d44d15ad
-- title:
--   Cont Diff Integral Density
-- statement:
--   Definitions and structural lemmas for Cont Diff Integral Density, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContDiffIntegralDensity.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
namespace GlobalTheory.CompanionTheory.SmoothParam
variable {Ω P Y F : Type} [MeasurableSpace Ω] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
noncomputable def pderiv (H : P × Y → F) : P × Y → (P →L[ℝ] F) :=
  fun z => fderiv ℝ (fun q => H (q, z.2)) z.1
end GlobalTheory.CompanionTheory.SmoothParam


