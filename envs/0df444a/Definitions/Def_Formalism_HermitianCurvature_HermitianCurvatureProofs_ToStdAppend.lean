-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ToStdAppend
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ToStdAppend
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T09:02:48.606663+00:00
-- url     : https://prove2.me/theorems/1ce748da-e56b-40d2-9ae8-7146a0352ba6
-- title:
--   To Std Append
-- statement:
--   Definitions and structural lemmas for To Std Append, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ToStdAppend.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsiNegBetaL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.GermFibreKernels
open Formalism.FourierDecayAlt NumberField
noncomputable section
def fs (r : ℕ) (g : ℝ) (b s : ℕ) (t : ℂ) : ℂ :=
  (((g / (2 * Real.pi)) ^ S6.nuBlock (r : ℤ) (b : ℤ) (s : ℤ) : ℝ) : ℂ) * Complex.I ^ (s - 1) * t
section loc
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]
end loc
end
end Formalism.FourierDecayAlt.P.GermFibreKernels


