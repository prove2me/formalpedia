-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BasePointMemHalfPlane
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_BasePointMemHalfPlane
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T06:13:38.152176+00:00
-- url     : https://prove2.me/theorems/b1687e35-5492-4b60-ac78-5904c5c9db33
-- title:
--   Base Point Mem Half Plane
-- statement:
--   Definitions and structural lemmas for Base Point Mem Half Plane, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BasePointMemHalfPlane.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FderivDecomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {TT : ℝ} {α : ℂ → ℂ}
def An (TT : ℝ) : Set ℂ := {ζ | TT < Complex.normSq ζ}
def x0 (TT : ℝ) : ℂ := (Real.log (TT + 1) : ℂ)
def th (TT : ℝ) (α : ℂ → ℂ) (w : ℂ) : ℝ := prim (om α) (x0 TT) w
end
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann


