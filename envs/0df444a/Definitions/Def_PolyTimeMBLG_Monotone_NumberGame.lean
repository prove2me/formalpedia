-- Prove2me | Definitions.Def_PolyTimeMBLG_Monotone_NumberGame
-- name    : PolyTimeMBLG_Monotone_NumberGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:38:33.417258+00:00
-- url     : https://prove2.me/theorems/4c863bc8-0d69-4070-a1ea-270c2810e525
-- title:
--   p. 8 — the game with numbers
-- statement:
--   The **game with numbers** is played on a board, a finite multiset of natural numbers (repetitions allowed).
--
--   1. Initially the board holds any number of $0$'s (possibly none).
--   2. Play proceeds in steps. In a step, the board $B$ must be nonempty; one occurrence of its minimum $m$ is replaced by $m+1$, giving the **intermediate board** $I$. Then a nonempty sub-multiset of $I$ is erased (it may contain the new $m+1$), and then any number $z\ge0$ of new $0$'s is added, giving the next board $B'$.
--
--   A **play of $T$ steps** is a sequence of boards $B_0,B_1,\dots,B_T$ with intermediate boards $I_1,\dots,I_T$ such that $B_0$ consists of zeros and step $t$ goes from $B_{t-1}$ through $I_t$ to $B_t$. Nothing bounds the initial number of zeros, the number of zeros added, the values reached or the length of the play.
--
--   In the proof of Theorem 11 the board records, at successive crucial moments, how many times each currently maximal unmarked word has been output.
--
--   **Formalization Note** Boards are `Multiset ℕ`. A play is given by two sequences `board, inter : ℕ → Multiset ℕ`; only `board 0, …, board T` and `inter 1, …, inter T` are constrained. Requiring an occurrence of the minimum makes a step from the empty board impossible, so a play reaching the empty board stops there.
-- source:
--   Héctor Jimenez, Alexander Kozachinskiy, Vicente Opazo, STOC 2027 submission #402 (October 2026), proof of Theorem 11, the game with numbers (two bullet points), p. 8. PDF SHA-256 2e6ec485290626cb762f55f7c45588eeb0047572a27748b20af18d34ebad7511

import Mathlib

namespace PolyTimeMBLG.Monotone

/-- One step of the game with numbers (p. 8) from board `B` (a finite multiset of naturals):
one occurrence of the minimum `m` of the nonempty board `B` is increased by 1, giving the
intermediate board `I`; then a nonempty sub-multiset `D` of `I` is erased; then `z ≥ 0` zeros
are added, giving the next board `B'`. -/
def GameStep (B I B' : Multiset ℕ) : Prop :=
  ∃ m ∈ B, (∀ x ∈ B, m ≤ x) ∧ I = (m + 1) ::ₘ B.erase m ∧
    ∃ D : Multiset ℕ, D ≠ 0 ∧ D ≤ I ∧ ∃ z : ℕ, B' = (I - D) + Multiset.replicate z 0

/-- A legal play of `T` steps: the initial board `board 0` consists of zeros only (any number,
possibly none), and for each `t < T` step `t + 1` goes from `board t` through the intermediate
board `inter (t + 1)` to `board (t + 1)`. Values of `board`, `inter` beyond the play are unused. -/
def IsPlay (T : ℕ) (board inter : ℕ → Multiset ℕ) : Prop :=
  (∃ z : ℕ, board 0 = Multiset.replicate z 0) ∧
    ∀ t < T, GameStep (board t) (inter (t + 1)) (board (t + 1))

end PolyTimeMBLG.Monotone


