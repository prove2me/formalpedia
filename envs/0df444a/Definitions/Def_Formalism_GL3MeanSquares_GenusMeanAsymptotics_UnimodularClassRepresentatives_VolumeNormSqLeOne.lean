-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VolumeNormSqLeOne
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VolumeNormSqLeOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:25:14.919904+00:00
-- url     : https://prove2.me/theorems/893c802f-5dc7-485b-88fb-f01f2eea7a4b
-- title:
--   Volume Norm Sq Le One
-- statement:
--   Definitions and structural lemmas for Volume Norm Sq Le One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/VolumeNormSqLeOne.lean

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
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.BallC
def ell {M : ℕ} (a : Fin M → ℝ) : Set (Fin M → ℂ) := {z | ∑ i, a i * Complex.normSq (z i) ≤ 1}
variable {M : ℕ} (a : Fin M → ℝ)
variable {a}
end Formalism.HermitianLattices.Ext.L3.BallC


