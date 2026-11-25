-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NeZeroOfAn
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_NeZeroOfAn
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:39:52.10949+00:00
-- url     : https://prove2.me/theorems/b6aedf2c-d93d-4168-84f4-9e34e3e21d43
-- title:
--   Ne Zero Of An
-- statement:
--   Definitions and structural lemmas for Ne Zero Of An, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NeZeroOfAn.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThShiftInt
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
def uu (TT : ℝ) (α : ℂ → ℂ) (ζ : ℂ) : ℂ := Complex.exp (I * (th TT α (Complex.log ζ) : ℂ))
def br (s : Bool) (ζ : ℂ) : ℂ := if s then Complex.log ζ else Complex.log (-ζ) + Real.pi * I
def brD (s : Bool) : Set ℂ := if s then Complex.slitPlane else {ζ | -ζ ∈ Complex.slitPlane}
end
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann


