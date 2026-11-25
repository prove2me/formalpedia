-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSystemAdmissibleSize
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSystemAdmissibleSize
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T03:54:51.489915+00:00
-- url     : https://prove2.me/theorems/4bd64e3d-87b9-4ddf-b220-83645e533d2e
-- title:
--   Level System Admissible Size
-- statement:
--   Definitions and structural lemmas for Level System Admissible Size, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelSystemAdmissibleSize.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.CutMP
open NumberField Finset
noncomputable section
section defs
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
end defs
end
end Formalism.FourierDecayAlt.P.CutMP


