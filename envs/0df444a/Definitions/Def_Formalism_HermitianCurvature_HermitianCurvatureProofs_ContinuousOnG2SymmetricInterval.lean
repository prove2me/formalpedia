-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousOnG2SymmetricInterval
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousOnG2SymmetricInterval
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:06:56.013329+00:00
-- url     : https://prove2.me/theorems/ae199513-9e9e-491a-a152-ea6a1e09f486
-- title:
--   Continuous On G2 Symmetric Interval
-- statement:
--   Definitions and structural lemmas for Continuous On G2 Symmetric Interval, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousOnG2SymmetricInterval.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory intervalIntegral Set
noncomputable section
namespace Formalism.FourierDecayAlt.P.DiscFubiniVolume
def ee (u t : ℝ) : ℂ := Complex.exp (Complex.I * ((u * t : ℝ) : ℂ))
def g0 (t : ℝ) : ℝ := Real.sqrt (1 - t ^ 2)
def g1 (t : ℝ) : ℝ := -t / Real.sqrt (1 - t ^ 2)
def g2 (t : ℝ) : ℝ := -1 / ((1 - t ^ 2) * Real.sqrt (1 - t ^ 2))
end Formalism.FourierDecayAlt.P.DiscFubiniVolume


