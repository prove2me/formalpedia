-- Prove2me | Definitions.Def_SimpleMenus_IsMergedGrid
-- name    : SimpleMenus_IsMergedGrid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:35:56.370966+00:00
-- url     : https://prove2.me/theorems/776b821d-471f-42c8-a3c3-9a6765041625
-- title:
--   Merged grid $u_1\le\dots\le u_{m+n}$ of $\mathcal V$ and $\mathcal B$
-- statement:
--   For price levels $\mathcal V=\{v_1,\dots,v_n\}$ and breakpoints $\mathcal B=\{b_1,\dots,b_m\}$, the valuations of $\mathcal B$ and $\mathcal V$ are arranged in ascending order, $u_1\le u_2\le\dots\le u_{m+n}$, and $u_{n+m+1}=\bar v$ is appended.
--
--   **Formalization Note** The grid is a monotone vector whose multiset of values is that of $v$ plus $\mathcal B$; ties (a price level equal to a breakpoint, or equal price levels) are kept. Indices are 0-based: the extended grid has entries $0,\dots,n+m$, the last being $\bar v$.
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, p.11

import Mathlib

namespace SimpleMenus

/-- `u_1 ≤ ⋯ ≤ u_{m+n}` is the ascending arrangement of the valuations in `B` and
`V = {v_1, …, v_n}` (Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, p.11): `u` is monotone and its multiset of values is that of `v`
plus `B`.

Formalization Note: indices are 0-based. Ties are kept (a price level equal to a breakpoint, or
two equal price levels, appear twice), as "`u_1 ≤ u_2 ≤ ⋯`" allows. -/
def IsMergedGrid {n : ℕ} (v : Fin n → ℝ) (B : Finset ℝ) (u : Fin (n + B.card) → ℝ) : Prop :=
  Monotone u ∧ Multiset.map u Finset.univ.val = Multiset.map v Finset.univ.val + B.val

/-- The grid with `u_{n+m+1} = v̄` appended (Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, p.11, "we represent `u_{n+m+1} = v̄`").
0-based: the entries `0, …, N − 1` are `u`, the entry `N` is `v̄`. -/
def extGrid {N : ℕ} (u : Fin N → ℝ) (vbar : ℝ) (j : Fin (N + 1)) : ℝ :=
  if h : (j : ℕ) < N then u ⟨j, h⟩ else vbar

end SimpleMenus


