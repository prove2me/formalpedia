-- Prove2me | Definitions.Def_MatroidOptGame_EfficientMin
-- name    : MatroidOptGame_EfficientMin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:57:21.870494+00:00
-- url     : https://prove2.me/theorems/933f1455-24c1-449f-bc8d-88357c15fa96
-- title:
--   Efficient MIN strategy
-- statement:
--   A MIN strategy $s$ is **efficient**, computed by the program $P$ with constant $C$, if it is legal and at every live position $h$ where MIN is to move, $s$ names an element $e$ and $P$, run on the encoding of $h$ with the independence oracle of $M$, computes the index of $e$ within work $C\,(n+1)^C$, where $n = |E|$.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Theorem 1, p.4; Lemmas 5 and 6, p.6; Section 1, p.1

import Mathlib
import Definitions.Def_LSWNewArcAudit_NewArc_OracleRAM
import Definitions.Def_MatroidOptGame_Live
import Definitions.Def_MatroidOptGame_Strategy
import Definitions.Def_MatroidOptGame_LegalMin
import Definitions.Def_MatroidOptGame_ComputesWithin

namespace MatroidOptGame

/-- `s` is a legal MIN strategy computed by the oracle-RAM program `P` within work `C·(n+1)^C`: at
every live position `h` where MIN moves, `s h = some e` and `P`, run on the input `enc h` with the
independence oracle of `M`, outputs the index of `e`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Theorem 1, p.4 ("there is an efficient strategy for MIN"), Lemmas 5 and 6,
pp.6, and Section 1, p.1.

**Formalization Note.** As for `EfficientMax`: one program, polynomial work in `n` at every
position of MIN's turn, matroid through the oracle only. -/
def EfficientMin (P : LSWNewArcAudit.NewArc.OracleProgram) (C : ℕ) {n : ℕ} (M : Matroid (Fin n))
    (enc : List (Fin n) → LSWNewArcAudit.NewArc.RAMInput) (s : Strategy (Fin n)) : Prop :=
  LegalMin M s ∧ ∀ h : List (Fin n), Live M h → h.length % 2 = 1 →
    ∃ e, s h = some e ∧ ComputesWithin P M (enc h) (C * (n + 1) ^ C) (e.val : ℤ)

end MatroidOptGame


