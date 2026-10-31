-- Prove2me | Definitions.Def_StuckmanMastermind_NPC_Instance
-- name    : StuckmanMastermind_NPC_Instance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-31T00:51:56.853618+00:00
-- url     : https://prove2.me/theorems/31b16b87-99fd-43a1-8cca-ab9e6b312d0b
-- title:
--   Mastermind instances and simultaneous satisfiability
-- statement:
--   A row consists of a code and a prescribed pair of natural black/white scores. An instance records its color count, length, and finite list of rows. Canonical means that the guesses are strictly lexicographically increasing, giving one row per guess and representing precisely a finite set with one feedback pair per member. Satisfiable means that a single code has exactly the prescribed score against every row. No feasibility promise is imposed on the feedback; scores exceeding the length remain representable and unsatisfiable. There is no bound on the number of rows or length. The empty row list is allowed, including at length zero. Negative scores are outside the nonnegative feedback syntax.
-- source:
--   Stuckman and Zhang, arXiv:cs/0512049v1, §2.1 input/output specification, PDF p. 4; https://arxiv.org/abs/cs/0512049v1

import Definitions.Def_StuckmanMastermind_NPC_Score

namespace StuckmanMastermind.NPC

structure Row (κ ℓ : ℕ) where
  guess : Code κ ℓ
  feedback : ℕ × ℕ

def guessEntries {κ ℓ : ℕ} (x : Code κ ℓ) : List ℕ :=
  List.ofFn fun i => (x i).val

structure Instance where
  colors : ℕ
  length : ℕ
  rows : List (Row colors length)

def Instance.Canonical (I : Instance) : Prop :=
  I.rows.Pairwise fun r s => List.Lex (· < ·) (guessEntries r.guess) (guessEntries s.guess)

def Instance.Satisfiable (I : Instance) : Prop :=
  ∃ s : Code I.colors I.length, ∀ r ∈ I.rows, score r.guess s = r.feedback

end StuckmanMastermind.NPC


