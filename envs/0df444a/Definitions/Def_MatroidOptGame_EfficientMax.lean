-- Prove2me | Definitions.Def_MatroidOptGame_EfficientMax
-- name    : MatroidOptGame_EfficientMax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:57:38.451305+00:00
-- url     : https://prove2.me/theorems/d0257302-f04b-49d9-bd95-0a58f7673b81
-- title:
--   Efficient MAX strategy
-- statement:
--   A MAX strategy $c$ is **efficient**, computed by the program $P$ with constant $C$, if it is legal and at every live position $h$ where MAX is to move, $c$ names an element $e$ and $P$, run on the encoding of $h$ (the ground set size, the weights and the history) with the independence oracle of $M$, computes the index of $e$ within work $C\,(n+1)^C$, where $n = |E|$.
--
--   The work bound must hold at every position of MAX's turn, not only along the play against a particular opponent.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Theorem 1, p.4; Section 1, p.1

import Mathlib
import Definitions.Def_LSWNewArcAudit_NewArc_OracleRAM
import Definitions.Def_MatroidOptGame_Live
import Definitions.Def_MatroidOptGame_Strategy
import Definitions.Def_MatroidOptGame_LegalMax
import Definitions.Def_MatroidOptGame_ComputesWithin

namespace MatroidOptGame

/-- `c` is a legal MAX strategy computed by the oracle-RAM program `P` within work `C·(n+1)^C`: at
every live position `h` where MAX moves, `c h = some e` and `P`, run on the input `enc h` with the
independence oracle of `M`, outputs the index of `e`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Theorem 1, p.4 ("there is an efficient strategy for MAX"), and Section 1, p.1.

**Formalization Note.** "Efficient" means one fixed program, polynomial work in `|E| = n` at
every position of the player's turn (not only on the path of play), with the matroid reached only
through the oracle and the weights and history read from the input `enc h` (`gameInput n w h`, or
`pairInput n w B₁ B₂ h` when the strategy is given two bases). -/
def EfficientMax (P : LSWNewArcAudit.NewArc.OracleProgram) (C : ℕ) {n : ℕ} (M : Matroid (Fin n))
    (enc : List (Fin n) → LSWNewArcAudit.NewArc.RAMInput) (c : Strategy (Fin n)) : Prop :=
  LegalMax M c ∧ ∀ h : List (Fin n), Live M h → h.length % 2 = 0 →
    ∃ e, c h = some e ∧ ComputesWithin P M (enc h) (C * (n + 1) ^ C) (e.val : ℤ)

end MatroidOptGame


