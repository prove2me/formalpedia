-- Prove2me | Definitions.Def_SimpleMenus_BreakpointAssumption
-- name    : SimpleMenus_BreakpointAssumption
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:37:00.167539+00:00
-- url     : https://prove2.me/theorems/44bcefab-9049-4a44-bd96-2f5b2ab8f451
-- title:
--   Assumption 1 with breakpoint set $\mathcal B=\{b_1<\dots<b_m\}\subset(0,\bar v)$
-- statement:
--   Let $\mathcal B$ be a finite set with $0<b_1<\dots<b_m<\bar v$. The family $\phi_1,\dots,\phi_K$ satisfies Assumption 1 with breakpoint set $\mathcal B$ if every $\phi_k$
--
--   1. is bounded on $[0,\bar v]$;
--   2. is continuous and nondecreasing on every open piece of $[0,\bar v]$ cut by $\mathcal B$;
--   3. has no breakpoint at $0$ or at $\bar v$: it is continuous at $0$ from the right and at $\bar v$ from the left.
--
--   This is the setting of Theorem 1, where $\mathcal B$ is the set of all breakpoints of the $\phi_k$; it implies Assumption 1.
--
--   **Formalization Note** Any finite $\mathcal B\subseteq(0,\bar v)$ satisfying these conditions may be used; the set of all breakpoints is one. Item 3 is the reading of the paper's "$0<b_1$" and "$b_m<\bar v$".
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, Assumption 1, p.9, and the paragraph before Theorem 1, p.11

import Mathlib
import Definitions.Def_SimpleMenus_IsPiece

open Set

namespace SimpleMenus

/-- Assumption 1 with the breakpoint set `B = {b_1, …, b_m}`, `0 < b_1 < ⋯ < b_m < v̄`
(Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, Assumption 1, p.9, and the paragraph before Theorem 1, p.11): every `ϕ_k` is bounded on
`[0, v̄]`, continuous and nondecreasing on each open piece cut by `B`, and has no breakpoint at `0`
or at `v̄` (it is continuous at `0` from the right and at `v̄` from the left).

Formalization Note: `B` is any finite subset of `(0, v̄)` for which these conditions hold; the set
of all breakpoints of the `ϕ_k` is one such set. The two endpoint conditions are the reading of
"`0 < b_1`" and "`b_m < v̄`": a jump at `0` or at `v̄` would be a breakpoint outside `(0, v̄)`.
This implies `Assumption1` (take `P = B` for every `k`). -/
def BreakpointAssumption (vbar : ℝ) {K : ℕ} (phi : Fin K → ℝ → ℝ) (B : Finset ℝ) : Prop :=
  (B : Set ℝ) ⊆ Ioo 0 vbar ∧
    ∀ k, (∃ C : ℝ, ∀ w ∈ Icc 0 vbar, |phi k w| ≤ C) ∧
      (∀ a b, IsPiece vbar B a b →
        ContinuousOn (phi k) (Ioo a b) ∧ MonotoneOn (phi k) (Ioo a b)) ∧
      ContinuousWithinAt (phi k) (Ici 0) 0 ∧ ContinuousWithinAt (phi k) (Iic vbar) vbar

end SimpleMenus


