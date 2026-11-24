-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T12:47:36.804614+00:00
-- url     : https://prove2.me/theorems/9f8110b9-a714-4a22-9581-638c65f145e0
-- title:
--   Commute Level Zero Element
-- statement:
--   Definitions and structural lemmas for Commute Level Zero Element, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
namespace Formalism.FourierDecayAlt.P.Fr9
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ}
section Level
variable (L : LevelData A r)
variable {L}
end Level
section Frame
variable {L : LevelData A r} {f : FrameData S A}
end Frame
section Free
variable {b : S}
variable {L : LevelData A r} {f : FrameData S A}
end Free
section Reduce
variable {b : S}
variable {L : LevelData A r} {f : FrameData S A}
end Reduce
section LevelId
variable (L : LevelData A r)
end LevelId
section Ee
variable {L : LevelData A r} {f : FrameData S A}
end Ee
section LL
variable {L : LevelData A r} {f : FrameData S A}
end LL
end Formalism.FourierDecayAlt.P.Fr9
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


