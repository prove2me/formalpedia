-- Prove2me | Definitions.Def_MatroidOptGame_Supplement_transcriptBefore
-- name    : MatroidOptGame_Supplement_transcriptBefore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:53:13.400354+00:00
-- url     : https://prove2.me/theorems/adf7a7f0-e262-445c-91a3-b6ca3e7bc44c
-- title:
--   Transcript of an oracle player before its current turn
-- statement:
--   For an oracle player $P$ moving at the positions of parity $p$ ($0$ for MAX, $1$ for MIN) with budget $s$, the transcript at history $h$ is obtained by replaying its turns at the earlier positions of $h$ of parity $p$, in order, each answered by the oracle and each continuing the transcript of the previous one. Because the player is deterministic, its transcript is a function of the history and the oracle.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2, pp.13–16

import Mathlib
import Definitions.Def_MatroidOptGame_Supplement_runTurn

namespace MatroidOptGame.Supplement

/-- The transcript the oracle player `P` (moving at the positions of parity `p`: `0` for MAX,
`1` for MIN) has accumulated when it is about to play at history `h`: its turns at the earlier
prefixes `h.take k` (`k < |h|`, `k ≡ p mod 2`) are replayed in order, each with fuel `s + 1`,
carrying the transcript from turn to turn.
Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2, pp.13–16 (queries before the first move and between moves).
**Formalization Note.** The player is deterministic and the oracle fixed, so the transcript is a
function of the history; replaying it is how a deterministic oracle player becomes a strategy on
histories. -/
def transcriptBefore {α : Type*} (O : Finset α → ℤ) (P : OraclePlayer α)
    (p s : ℕ) (h : List α) : List (Finset α × ℤ) :=
  (List.range h.length).foldl
    (fun tr k => if k % 2 = p then (runTurn O P (h.take k) (s + 1) tr).1 else tr) []

end MatroidOptGame.Supplement


