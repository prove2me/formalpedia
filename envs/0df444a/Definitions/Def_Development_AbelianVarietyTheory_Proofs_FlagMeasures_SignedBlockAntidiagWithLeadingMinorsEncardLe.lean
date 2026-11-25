-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SignedBlockAntidiagWithLeadingMinorsEncardLe
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_SignedBlockAntidiagWithLeadingMinorsEncardLe
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T03:10:32.261202+00:00
-- url     : https://prove2.me/theorems/197d9a9d-b378-4e61-80d0-8dd73a5028dc
-- title:
--   Signed Block Antidiag With Leading Minors Encard Le
-- statement:
--   Definitions and structural lemmas for Signed Block Antidiag With Leading Minors Encard Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SignedBlockAntidiagWithLeadingMinorsEncardLe.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.SignedBlockCount
open Formalism.MainNotions.S.Loc
variable {K : Type} [Field K]
noncomputable def minor (bs : List (Kˣ × ℕ+)) (l : ℕ) : K :=
  (Matrix.of fun a b : Fin l => ptEntryL bs a b).det
end GlobalTheory.SignedBlockCount
namespace GlobalTheory
end GlobalTheory


