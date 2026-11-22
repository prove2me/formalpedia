-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinusLetterFrameOfData
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_MinusLetterFrameOfData
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:39:59.627879+00:00
-- url     : https://prove2.me/theorems/06339acf-d54b-4507-befe-32747933e1d6
-- title:
--   Minus Letter Frame Of Data
-- statement:
--   Definitions and structural lemmas for Minus Letter Frame Of Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinusLetterFrameOfData.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommuteInvLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
namespace Formalism.FourierDecayAlt.P.Fr10
open Formalism.FourierDecayAlt.P.Wd1
section Gen
variable {B : Type} [Ring B]
end Gen
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
section Frame
variable {r : ℕ} (L : LevelData A r) (f : FrameData S A)
end Frame
end Formalism.FourierDecayAlt.P.Fr10
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


