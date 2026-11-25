-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtBrReal
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtBrReal
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:57:38.482141+00:00
-- url     : https://prove2.me/theorems/5b766f36-eb18-5cf5-8b87-d19a5a76014b
-- title:
--   Has FDeriv At Br Real
-- statement:
--   Definitions and structural lemmas for Has FDeriv At Br Real, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtBrReal.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NeZeroOfAn
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
def ug (TT : ℝ) (α : ℂ → ℂ) (s : Bool) (z : ℂ) : ℂ := Complex.exp (I * (th TT α (br s z) : ℂ))
end
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann


