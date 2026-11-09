-- Prove2me | Definitions.Def_MatroidOptGame_gameInput
-- name    : MatroidOptGame_gameInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:08.990979+00:00
-- url     : https://prove2.me/theorems/a7fb189c-bd5d-40b4-ba20-e83200013f5e
-- title:
--   Input encoding of a game position
-- statement:
--   The machine input describing a position of the game on the ground set $\{0, \dots, n-1\}$: integer memory cell $0$ holds $n$; cells $1, \dots, n$ hold the weights $w(0), \dots, w(n-1)$; cell $n+1$ holds the number of moves so far; and the following cells hold the moves of the history in order, as element indices. All other cells are $0$. The matroid is not part of the input: it is reached through its independence oracle.
--
--   The paper notes that every state of the game has a description of linear size, so the next move given the current state can be asked to be computable in polynomial time.
--
--   **Formalization Note** The encoding determines $n$, $w$ and the history uniquely.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 1, p.1; Section 2, p.4

import Mathlib
import Definitions.Def_LSWNewArcAudit_NewArc_OracleRAM

namespace MatroidOptGame

/-- The RAM input describing the ground set size `n`, the weights `w` and a history `h`:
integer cell `0` holds `n`, cells `1, …, n` hold `w(0), …, w(n − 1)`, cell `n + 1` holds the
length of `h`, and cells `n + 2, n + 3, …` hold the moves of `h` in order (as indices in
`0, …, n − 1`). All other integer cells and all real cells are `0`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 1, p.1 ("any state of the game has linear size description, so the next
move of a player, given the current state, might be poly-time computable"), and p.4 (the matroid
is given by listing `E` and an independence oracle).

**Formalization Note.** The encoding is injective in `(n, w, h)`. The matroid itself is not part
of the input; it is reached through `indepOracle`. -/
def gameInput (n : ℕ) (w : Fin n → ℕ) (h : List (Fin n)) : LSWNewArcAudit.NewArc.RAMInput where
  integers := fun a =>
    if 0 ≤ a then
      ((((n : ℤ) :: List.ofFn (fun i => (w i : ℤ))) ++ ((h.length : ℤ) :: h.map (fun e => (e.val : ℤ))))[a.toNat]?).getD 0
    else 0
  reals := fun _ => 0

end MatroidOptGame


