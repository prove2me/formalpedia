-- Prove2me | Definitions.Def_NetworkControl_Backpressure_StronglyStable
-- name    : NetworkControl_Backpressure_StronglyStable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:21:10.511801+00:00
-- url     : https://prove2.me/theorems/7eba3fbc-d269-4b0c-9d11-9f7936e408d0
-- title:
--   Definitions 3.1-3.2 — strong stability of a queue and of a network
-- statement:
--   Restated locally (drafts cannot import chunk `03-capacity-region`'s copy). A queue backlog
--   sequence $U$ (with $U(t)$ read as $\mathbb E\{U(t)\}$) is *strongly stable* (Def. 3.1, p. 24)
--   if $\limsup_{t\to\infty}\frac1t\sum_{\tau=0}^{t-1}\mathbb E\{U(\tau)\}<\infty$ — for a
--   real-valued sequence this is equivalent to the Cesàro average being bounded above for every
--   $t$, stated here in that quantifier-light form. A network of $L$ queues is *strongly stable*
--   (Def. 3.2, p. 24) if every individual queue is.
-- source:
--   Georgiadis, Neely & Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, FnT Networking 2006, p. 24, Definitions 3.1-3.2

import Mathlib

namespace NetworkControl.Backpressure

/-- Definition 3.1 (p. 24), restated locally in this chunk's own sub-namespace (drafts cannot
import chunk `03-capacity-region`'s copy). A queue backlog sequence `U` (with `U t` interpreted
as `E{U(t)}`) is strongly stable if it has a bounded time-average — for a real sequence this is
equivalent to the book's `limsup < ∞` (see `03-capacity-region`'s `SELF_REVIEW.md` for the
equivalence argument), stated here in the same quantifier-light form. -/
def StronglyStable (U : ℕ → ℝ) : Prop :=
  ∃ M : ℝ, ∀ t : ℕ, (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, U τ ≤ M

/-- Definition 3.2 (p. 24): a network of `L` queues is strongly stable if every individual queue
is. `U i` is the expected-backlog sequence of queue `i`. -/
def NetworkStronglyStable {L : ℕ} (U : Fin L → ℕ → ℝ) : Prop :=
  ∀ i : Fin L, StronglyStable (U i)

end NetworkControl.Backpressure


