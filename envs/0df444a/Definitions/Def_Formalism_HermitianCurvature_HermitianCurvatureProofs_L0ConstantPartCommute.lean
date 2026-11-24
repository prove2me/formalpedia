-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T12:45:52.616081+00:00
-- url     : https://prove2.me/theorems/82cdac1e-8513-4349-a791-9f9a8e49ce70
-- title:
--   L0 Constant Part Commute
-- statement:
--   Definitions and structural lemmas for L0 Constant Part Commute, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/L0ConstantPartCommute.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
namespace Formalism.FourierDecayAlt.P.Fr3
section Io
variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
end Io
section Level
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)
end Level
section Frame
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ} {L : LevelData A r} {f : FrameData S A}
end Frame
end Formalism.FourierDecayAlt.P.Fr3
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.Fr3
end Formalism.FourierDecayAlt.P


