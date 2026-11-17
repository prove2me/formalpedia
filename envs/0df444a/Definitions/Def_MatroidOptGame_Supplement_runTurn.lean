-- Prove2me | Definitions.Def_MatroidOptGame_Supplement_runTurn
-- name    : MatroidOptGame_Supplement_runTurn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:52:25.634606+00:00
-- url     : https://prove2.me/theorems/a7819a04-f9f7-4270-bc64-7dd7c0739f1d
-- title:
--   One turn of an oracle player
-- statement:
--   Given an oracle $O$, an oracle player $P$, the current history $h$ and the transcript so far, one **turn** runs $P$: each query $F$ is answered by $O(F)$ and appended to the transcript, until $P$ moves. The result is the new transcript and the move. A step limit ("fuel") makes the definition total; with budget $s$, $s+1$ steps always suffice.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2, pp.13–16

import Mathlib
import Definitions.Def_MatroidOptGame_Supplement_OraclePlayer

namespace MatroidOptGame.Supplement

/-- One turn of the oracle player `P` at history `h`, answered by the oracle `O`, starting from
transcript `tr`, with at most `fuel` steps: each query `F` is answered by `O F` and appended to the
transcript, until `P` moves. Returns the final transcript and the move (`none` if the fuel runs
out first).
Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2, pp.13–16 (queries made between moves).
**Formalization Note.** Under `Supplement.WithinBudget s P`, fuel `s + 1` is never exhausted,
since each query lengthens the transcript and `P` moves once it has `s` entries. -/
def runTurn {α : Type*} (O : Finset α → ℤ) (P : OraclePlayer α)
    (h : List α) : ℕ → List (Finset α × ℤ) → List (Finset α × ℤ) × Option α
  | 0, tr => (tr, none)
  | k + 1, tr =>
    match P h tr with
    | .query F => runTurn O P h k (tr ++ [(F, O F)])
    | .move e => (tr, some e)

end MatroidOptGame.Supplement


