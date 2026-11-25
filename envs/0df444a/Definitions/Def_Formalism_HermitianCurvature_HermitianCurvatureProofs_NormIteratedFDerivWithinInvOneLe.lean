-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormIteratedFDerivWithinInvOneLe
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_NormIteratedFDerivWithinInvOneLe
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T03:30:30.81696+00:00
-- url     : https://prove2.me/theorems/d1bc2fcf-3c5e-5e23-84c6-ad93811a2bce
-- title:
--   Norm Iterated FDeriv Within Inv One Le
-- statement:
--   Definitions and structural lemmas for Norm Iterated FDeriv Within Inv One Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormIteratedFDerivWithinInvOneLe.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralIteratedFDerivEqZero
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Set
open scoped Nat
noncomputable section
namespace Formalism.FourierDecayAlt.P5.HerC.Fou
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
end Formalism.FourierDecayAlt.P5.HerC.Fou


