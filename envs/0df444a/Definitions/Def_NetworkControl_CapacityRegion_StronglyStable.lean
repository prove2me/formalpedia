-- Prove2me | Definitions.Def_NetworkControl_CapacityRegion_StronglyStable
-- name    : NetworkControl_CapacityRegion_StronglyStable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:18:44.904238+00:00
-- url     : https://prove2.me/theorems/8d45b8cb-b530-43de-b7bb-d06fa14a3f58
-- title:
--   Definition 3.1 — strong stability of a queue
-- statement:
--   A queue backlog sequence $U$ (with $U(t)$ read as $\mathbb E\{U(t)\}$, the expected backlog
--   in slot $t$) is *strongly stable* if it has a bounded time average:
--   $\limsup_{t\to\infty}\frac1t\sum_{\tau=0}^{t-1}\mathbb E\{U(\tau)\}<\infty$ (Def. 3.1, p. 24).
--
--   **Formalization note.** For a real-valued sequence, "finite limsup" and "the Cesàro average
--   is bounded above for every $t$" are the same condition: any finite prefix of a real sequence
--   is automatically bounded, so an eventual bound (what limsup gives) and a global bound agree.
--   `StronglyStable` states that equivalent, quantifier-light form directly, rather than
--   unfolding Mathlib's `Filter.limsup` machinery for a conditionally-complete lattice.
-- source:
--   Georgiadis, Neely & Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, FnT Networking 2006, p. 24, Definition 3.1

import Mathlib

namespace NetworkControl.CapacityRegion

/-- Definition 3.1 (p. 24). A queue backlog sequence `U` (with `U t` interpreted as `E{U(t)}`,
the expected backlog in slot `t`) is strongly stable if it has a bounded time-average:
`limsup_{t→∞} (1/t) Σ_{τ=0}^{t-1} E{U(τ)} < ∞`. For a real-valued sequence this finite-limsup
condition is exactly equivalent to the Cesàro average being bounded above for every `t`
(any finite prefix of a real sequence is automatically bounded, so an eventual bound and a
global bound agree here); we state that equivalent, quantifier-light form directly. -/
def StronglyStable (U : ℕ → ℝ) : Prop :=
  ∃ M : ℝ, ∀ t : ℕ, (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, U τ ≤ M

end NetworkControl.CapacityRegion


