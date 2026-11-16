-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_WinCfg
-- name    : DoublyEffIP_Supplement_WinCfg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:38:02.293132+00:00
-- url     : https://prove2.me/theorems/e5846592-8f77-4843-8025-ef528f7af222
-- title:
--   A configuration of $M$ with space $S$
-- statement:
--   A **space-$S$ configuration** of a machine $M$ consists of its state (a control state or a halting answer) and, for each tape, the head position and the contents of the window of $2S+1$ cells around the starting cell.
--
--   A computation that visits at most $S$ cells in total stays inside these windows on every tape, so these objects carry every configuration of space $S$. They play the role of the paper's configurations $x_{\mathrm{start}},x_{\mathrm{end}}\in\{0,1\}^{S(n)}$ of "a Turing machine $M$ with time complexity $T(n)$ and space complexity $S(n)$".
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 4.1, p.14

import Mathlib
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT.Computation

namespace DoublyEffIP.Supplement

/-- **A configuration of `M` with space `S`** — the configurations `x_start, x_end ∈ {0,1}^{S(n)}`
of "a Turing machine M with time complexity T(n) and space complexity S(n)" in Section 4.1 of
Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), p.14.

The state of the machine `M` and, for each of its tapes, the head position and the contents of the
window of `2S + 1` cells around the starting cell (window index `j` is the absolute cell `j − S`).

**Formalization Note.** A run that visits at most `S` cells in total (the published
`visitedSpace`, which every tape's window contains with the starting cell) stays inside this window
on every tape, so these configurations carry every configuration of space `S`. -/
structure WinCfg (M : PrimitiveMachine) (S : ℕ) where
  /-- the state: an answer (halted) or a control state -/
  state : Bool ⊕ Fin M.stateCount
  /-- the head position of each tape, in the window -/
  head : Fin M.tapeCount → Fin (2 * S + 1)
  /-- the contents of each tape's window (`none` is blank) -/
  cells : Fin M.tapeCount → Fin (2 * S + 1) → Option Bool

end DoublyEffIP.Supplement


