-- Prove2me | Definitions.Def_MIPRE_Foundations_SyncMergeByQuestion
-- name    : MIPRE_Foundations_SyncMergeByQuestion
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:46:52.708548+00:00
-- url     : https://prove2.me/theorems/6ca1943d-25ea-47d7-8396-58127b7ee9b0
-- title:
--   Definitions of SyncMergeByQuestion: Perfect PCC strategies under question-dependent answer encoding Answers can be encoded separately at each question
-- statement:
--   The definitions of the module `MIPRE.Foundations.SyncMergeByQuestion` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Perfect PCC strategies under question-dependent answer encoding. Answers can be encoded separately at each question. The encoding need only preserve acceptance for nonzero effects on question pairs of positive weight. This allows format and range facts supplied by an honest strategy's support.
--
--   **Definitions** (1): `MIPRE.SyncStrategy.mergeAnswersByQuestion` (Group outcomes using the encoder appropriate to each question.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SyncMergeByQuestion` (`MIPRE/Foundations/SyncMergeByQuestion.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 6 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SyncMergeByQuestion.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SyncMergeByQuestion.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameTransportByQuestion
import Theorems.Thm_MIPRE_tracialValue_eq_one_of_re_eq_zero

/-! # Perfect PCC strategies under question-dependent answer encoding

Answers can be encoded separately at each question. The encoding need only
preserve acceptance for nonzero effects on question pairs of positive weight.
This allows format and range facts supplied by an honest strategy's support.
-/

noncomputable section
namespace MIPRE.SyncStrategy
open Matrix Finset Classical
variable {X A B : Type*} [Fintype X] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] {G : SynchronousGame X A}

/-- Group outcomes using the encoder appropriate to each question. -/
def mergeAnswersByQuestion (S : SyncStrategy G) (H : SynchronousGame X B)
    (f : X → A → B) : SyncStrategy H :=
  ⟨S.d,S.d_pos,S.P.mergeByQuestion f⟩

end MIPRE.SyncStrategy


