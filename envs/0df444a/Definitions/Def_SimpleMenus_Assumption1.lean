-- Prove2me | Definitions.Def_SimpleMenus_Assumption1
-- name    : SimpleMenus_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:36:45.279447+00:00
-- url     : https://prove2.me/theorems/37f6b9b3-3d69-4f67-b281-d5eb9ac57b0a
-- title:
--   Assumption 1: bounded, piecewise continuous, piecewise nondecreasing $\phi_k$
-- statement:
--   **Assumption 1.** Each $\phi_k$ is bounded and piecewise continuous on $[0,\bar v]$, with finitely many segments, and is nondecreasing within each segment.
--
--   Precisely: for every $k$ there is a constant $C$ with $|\phi_k(w)|\le C$ on $[0,\bar v]$, and a finite set $P\subseteq[0,\bar v]$ such that $\phi_k$ is continuous and nondecreasing on every open piece cut by $P$.
--
--   This is the standing assumption of Proposition 1 and Theorem 1.
--
--   **Formalization Note** The values of $\phi_k$ at the points of $P$ are unconstrained beyond boundedness (single-point segments); this is the broadest reading of "finite segments".
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, Assumption 1, p.9

import Mathlib
import Definitions.Def_SimpleMenus_IsPiece

open Set

namespace SimpleMenus

/-- Assumption 1: each `ϕ_k` is bounded and piecewise continuous on `[0, v̄]`, with finitely many
segments, and nondecreasing within each segment (Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, Assumption 1, p.9).

Formalization Note: the segments are the open pieces cut by a finite set `P ⊆ [0, v̄]` of
breakpoints (chosen per `k`); on each piece `ϕ_k` is continuous and monotone. The values of `ϕ_k`
at the points of `P` are unrestricted beyond boundedness (single-point segments). Boundedness is
on `[0, v̄]`; values outside `[0, v̄]` play no role. -/
def Assumption1 (vbar : ℝ) {K : ℕ} (phi : Fin K → ℝ → ℝ) : Prop :=
  ∀ k, (∃ C : ℝ, ∀ w ∈ Icc 0 vbar, |phi k w| ≤ C) ∧
    ∃ P : Finset ℝ, (P : Set ℝ) ⊆ Icc 0 vbar ∧
      ∀ a b, IsPiece vbar P a b → ContinuousOn (phi k) (Ioo a b) ∧ MonotoneOn (phi k) (Ioo a b)

end SimpleMenus


