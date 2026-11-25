-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsiNegBetaL
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_PsiNegBetaL
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T08:37:34.674215+00:00
-- url     : https://prove2.me/theorems/ec52b3ad-fe80-53fb-b422-25a2fd5b1651
-- title:
--   Psi Neg Beta L
-- statement:
--   Definitions and structural lemmas for Psi Neg Beta L, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsiNegBetaL.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermLocalOfFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.GermRealisation
open Formalism.FourierDecayAlt NumberField
noncomputable section
section loc
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]
def betaL (S : C.HidaSetting E Wp Wq) : ℂ := ((4 * Real.pi / (S.g : ℝ) : ℝ) : ℂ)
end loc
end
end Formalism.FourierDecayAlt.P.GermRealisation


