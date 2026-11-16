-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_winStep
-- name    : DoublyEffIP_Supplement_winStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:38:31.352967+00:00
-- url     : https://prove2.me/theorems/6dded5e2-49cd-4b53-a0a8-32cfe422089f
-- title:
--   One step of $M$ on space-$S$ configurations
-- statement:
--   The **step** of $M$ on space-$S$ configurations: in control state $q$ the machine reads the scanned cell of tape $\mathrm{scan}(q)$ and, by its transition, either halts with an answer, or enters $q'$ and moves that head one cell or writes that cell. A halted configuration is fixed.
--
--   This is the transition of the published machine model, restricted to the windows.
--
--   **Formalization Note** A head never leaves its window: a move off the edge leaves it in place. Computations of space at most $S$ never reach the edge, so on them this is $M$'s own step; the clip only makes the step total on all space-$S$ configurations, as the language $L_t$ on $\{0,1\}^S\times\{0,1\}^S$ requires.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 4.1, p.14 (M transitions from configuration x_start to x_end)

import Mathlib
import Definitions.Def_DoublyEffIP_Supplement_WinCfg
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT.Computation

namespace DoublyEffIP.Supplement

/-- **One step of `M` on space-`S` configurations** — "M transitions from configuration x_start to
configuration x_end" (Section 4.1 of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), p.14).

The transition of the published `PrimitiveMachine.step`: in control state `q`, read the scanned
cell of tape `scan q`; halt with an answer, or enter `q'` and move that head or write that cell. A
halted configuration is fixed.

**Formalization Note.** A head never leaves the window: a move off its edge leaves the head in
place. Runs of space at most `S` never reach the edge, so on them this is `M`'s own step; the clip
only makes the step total on all `S`-bit configurations, as the source's `L_t` on
`{0,1}^S × {0,1}^S` needs. -/
def winStep (M : PrimitiveMachine) (S : ℕ) (c : WinCfg M S) : WinCfg M S :=
  match c.state with
  | .inl _ => c
  | .inr q =>
    let i := M.scan q
    match M.transition q (c.cells i (c.head i)) with
    | .inl b => { c with state := .inl b }
    | .inr (q', .move .left) =>
      { c with state := .inr q',
                head := Function.update c.head i
                  ⟨(c.head i).val - 1, lt_of_le_of_lt (Nat.sub_le _ _) (c.head i).isLt⟩ }
    | .inr (q', .move .right) =>
      { c with state := .inr q',
                head := Function.update c.head i
                  ⟨min ((c.head i).val + 1) (2 * S), by omega⟩ }
    | .inr (q', .write sym) =>
      { c with state := .inr q',
                cells := Function.update c.cells i (Function.update (c.cells i) (c.head i) sym) }

end DoublyEffIP.Supplement


