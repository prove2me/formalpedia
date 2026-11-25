-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothDecayOfWeighted
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothDecayOfWeighted
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T03:39:34.836591+00:00
-- url     : https://prove2.me/theorems/d1c17f88-50c2-57b4-8907-bfc8ce1a866f
-- title:
--   Smooth Decay Of Weighted
-- statement:
--   Definitions and structural lemmas for Smooth Decay Of Weighted, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SmoothDecayOfWeighted.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormIteratedFDerivWithinInvOneLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module
open scoped Nat
noncomputable section
namespace Formalism.FourierDecayAlt.P5.HerC.Fou
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
def au (j : ℕ) : ℝ := j ! * j ! * 4 ^ j
end Formalism.FourierDecayAlt.P5.HerC.Fou


