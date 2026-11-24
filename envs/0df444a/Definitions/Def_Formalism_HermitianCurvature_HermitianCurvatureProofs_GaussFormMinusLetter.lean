-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T12:47:52.888065+00:00
-- url     : https://prove2.me/theorems/82d5cfdc-95c3-4341-ac47-36e2f91870d7
-- title:
--   Gauss Form Minus Letter
-- statement:
--   Definitions and structural lemmas for Gauss Form Minus Letter, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
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
namespace Formalism.FourierDecayAlt.P.Fr8
section Mon
variable {M : Type} [Monoid M]
end Mon
section Slots
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
end Slots
section Level
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
variable {L : LevelData A r} {f : FrameData S A}
end Level
end Formalism.FourierDecayAlt.P.Fr8
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


