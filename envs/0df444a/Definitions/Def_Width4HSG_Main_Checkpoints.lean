-- Prove2me | Definitions.Def_Width4HSG_Main_Checkpoints
-- name    : Width4HSG_Main_Checkpoints
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:18:30.729406+00:00
-- url     : https://prove2.me/theorems/84a6056a-aed2-4b1f-932e-b043762daf53
-- title:
--   The checkpoint class K₃,ℓ
-- statement:
--   A checkpoint partition begins at layer zero, ends at the final layer, and has strictly increasing cuts. Every checkpoint has at most two forward-reachable live states. Each interval has at most ℓ colliding layers, including its closing transition. Class membership is structural and contains no density assumption.
-- source:
--   Krak, Beyond Width-3: Better Hitting Set Generators for Width-4 Read-Once Branching Programs, STOC 2027 submission, p. 26, PDF SHA256 4ef018bd96382f87d7be4ed375c984df83c46ccdc42ab98e0d7d589b27b1c050

import Mathlib
import Definitions.Def_Width4HSG_Main_LiveProgram

noncomputable section
open scoped BigOperators

namespace Width4HSG.Main

structure CheckpointPartition (d : ℕ) where
  intervals : ℕ
  cut : Fin (intervals + 1) → Fin (d + 1)
  first : cut 0 = 0
  last : cut (Fin.last intervals) = Fin.last d
  increasing : StrictMono cut

def CheckpointPartition.ValidFor {n d : ℕ} (T : CheckpointPartition d)
    (P : LiveProgram n d) (ℓ : ℕ) : Prop :=
  (∀ j, (P.reachable (T.cut j).val).card ≤ 2) ∧
  ∀ j : Fin T.intervals,
    P.collisions (T.cut j.castSucc).val (T.cut j.succ).val ≤ ℓ

def InCheckpointClass {n d : ℕ} (P : LiveProgram n d) (ℓ : ℕ) : Prop :=
  ∃ T : CheckpointPartition d, T.ValidFor P ℓ

end Width4HSG.Main


