-- Prove2me | Definitions.Def_SimpleMenus_IsPiece
-- name    : SimpleMenus_IsPiece
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:35:58.266454+00:00
-- url     : https://prove2.me/theorems/1a778fd8-4ddf-4e16-8162-65fe32cb591a
-- title:
--   Open piece of $[0,\bar v]$ cut by a finite set of breakpoints
-- statement:
--   Let $P\subseteq[0,\bar v]$ be finite. An open piece of $[0,\bar v]$ cut by $P$ is an interval $(a,b)$ where $a<b$ are points of $P\cup\{0,\bar v\}$ with no point of $P$ strictly between them.
--
--   These are the segments on which Assumption 1 asks each $\phi_k$ to be continuous and nondecreasing.
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, Assumption 1, p.9 ("finite segments"), and the breakpoint set, p.11

import Mathlib

open Set

namespace SimpleMenus

/-- `(a, b)` is one of the open pieces into which the finite set `P ⊆ [0, v̄]` cuts `[0, v̄]`:
`a < b` are consecutive points of `P ∪ {0, v̄}` (Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, Assumption 1, p.9, "finite segments", and
the breakpoint set, p.11).

Formalization Note: consecutiveness is "no point of `P` lies strictly between `a` and `b`". -/
def IsPiece (vbar : ℝ) (P : Finset ℝ) (a b : ℝ) : Prop :=
  a ∈ insert 0 (insert vbar (P : Set ℝ)) ∧ b ∈ insert 0 (insert vbar (P : Set ℝ)) ∧ a < b ∧
    ∀ c ∈ P, c ∉ Ioo a b

end SimpleMenus


