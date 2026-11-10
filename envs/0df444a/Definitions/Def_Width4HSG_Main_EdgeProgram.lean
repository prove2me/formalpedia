-- Prove2me | Definitions.Def_Width4HSG_Main_EdgeProgram
-- name    : Width4HSG_Main_EdgeProgram
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:19:32.914471+00:00
-- url     : https://prove2.me/theorems/0d1fe669-b14a-4d98-ad2a-e4efee70638a
-- title:
--   Width-w conjunction and disjunction edge programs
-- statement:
--   A Boolean designation on each edge is independent of its input label. A conjunction program accepts when every traversed designation is accepting; a disjunction program accepts when at least one is. The final-state labels of the underlying transition structure are ignored.
-- source:
--   Krak, Beyond Width-3: Better Hitting Set Generators for Width-4 Read-Once Branching Programs, STOC 2027 submission, p. 19, PDF SHA256 4ef018bd96382f87d7be4ed375c984df83c46ccdc42ab98e0d7d589b27b1c050

import Mathlib
import Definitions.Def_Width4HSG_Main_ROBP

noncomputable section
open scoped BigOperators

namespace Width4HSG.Main

structure EdgeProgram (w n : ℕ) where
  program : ROBP w n
  marked : Fin n → Fin w → Bool → Bool

def EdgeProgram.andEval {w n : ℕ} (P : EdgeProgram w n) (x : Bits n) : Bool :=
  (List.finRange n).all (fun i => P.marked i (P.program.state x i.val) (x i))

def EdgeProgram.orEval {w n : ℕ} (P : EdgeProgram w n) (x : Bits n) : Bool :=
  (List.finRange n).any (fun i => P.marked i (P.program.state x i.val) (x i))

end Width4HSG.Main


