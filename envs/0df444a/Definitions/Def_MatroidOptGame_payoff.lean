-- Prove2me | Definitions.Def_MatroidOptGame_payoff
-- name    : MatroidOptGame_payoff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:54:33.611049+00:00
-- url     : https://prove2.me/theorems/05d0743b-38ad-4e50-8fbb-6c90b7c85f2c
-- title:
--   MAX's payoff $p(c,s)$
-- statement:
--   MAX's **payoff** $p(c, s)$ for strategies $c$ (MAX) and $s$ (MIN) is
--   $$
--   p(c, s) = \begin{cases} \infty & \text{if, at the end of the play, MAX's deletions include a cut of } M,\\ w(S) & \text{otherwise, where } S \text{ is the base secured by MIN.} \end{cases}
--   $$
--   MAX maximizes and MIN minimizes this quantity.
--
--   **Formalization Note** Valued in $\mathbb N \cup \{\infty\}$ (`ℕ∞`).
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3

import Mathlib
import Definitions.Def_MatroidOptGame_weight
import Definitions.Def_MatroidOptGame_minSet
import Definitions.Def_MatroidOptGame_CutDeleted
import Definitions.Def_MatroidOptGame_Strategy
import Definitions.Def_MatroidOptGame_playout

namespace MatroidOptGame

open Classical in
/-- MAX's payoff `p(c, s)`: `∞` if MAX's deletions include a cut, otherwise the weight `w(S)` of
the base MIN has secured.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2, p.3 ("MAX's payoff p(c, s) is ∞ in the first case and w(S_j) in the
second case"). -/
noncomputable def payoff {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α) (w : α → ℕ)
    (c s : Strategy α) : ℕ∞ :=
  if CutDeleted M (playout M c s) then ⊤ else (weight w (minSet (playout M c s)) : ℕ∞)

end MatroidOptGame


