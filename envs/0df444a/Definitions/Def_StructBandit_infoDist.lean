-- Prove2me | Definitions.Def_StructBandit_infoDist
-- name    : StructBandit_infoDist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:31:57.725926+00:00
-- url     : https://prove2.me/theorems/6ee48029-37c3-430e-bbb6-a5ef2707414a
-- title:
--   Information distance $I(M',M)$
-- statement:
--   For nonnegative vectors $M',M$ indexed by the reward set, the **information distance** is
--
--   $$
--   I(M',M):=\sum_{r\in\mathfrak R}\Big[M'(r)\log\frac{M'(r)}{M(r)}-M'(r)+M(r)\Big]
--   $$
--
--   if $M'\ll M$ (that is, $M(r)=0\Rightarrow M'(r)=0$ for all $r$), and $I(M',M)=+\infty$ otherwise, with $0\log 0=0$. On probability vectors it is the Kullback–Leibler divergence.
--
--   It measures how far the observations of one arm are from a hypothesized reward distribution, and enters the distance function, the regret lower bound and the concentration bounds.
--
--   **Formalization Note** The value is an extended real; Lean's `Real.log 0 = 0` and `x / 0 = 0` coincide with the conventions above on every term, so they decide no case.
-- source:
--   Van Parys & Golrezaei, Optimal Learning for Structured Bandits, arXiv:2007.07302v3, Eq. (5), p.11

import Mathlib

open scoped BigOperators

namespace StructBandit

open Classical in
/-- **The information distance** `I(M′, M)` (arXiv:2007.07302v3, Eq. (5), p.11):
`I(M′,M) := ∑_{r∈R} [M′(r) log(M′(r)/M(r)) − M′(r) + M(r)]` if `M′ ≪ M`, and `+∞` otherwise, where
`M′ ≪ M` means `M(r) = 0 ⟹ M′(r) = 0` for all `r`. On probability vectors it is the Kullback–Leibler
divergence.

**Formalization Note.** The value is an extended real (`⊤` = `+∞`). In the finite branch every term
with `M′(r) = 0` is `0 · log(·) − 0 + M(r) = M(r)`, the usual convention `0 log 0 = 0`, and every term with
`M(r) = 0` has `M′(r) = 0` and is `0`; so Lean's `Real.log 0 = 0` and `x / 0 = 0` decide no case. The
page prints a stray bracket ("…+M(r)]"). -/
noncomputable def infoDist {α : Type*} [Fintype α] (M' M : α → ℝ) : EReal :=
  if ∀ r, M r = 0 → M' r = 0 then
    ((∑ r, (M' r * Real.log (M' r / M r) - M' r + M r) : ℝ) : EReal)
  else ⊤

end StructBandit


