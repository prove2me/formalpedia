-- Prove2me | Definitions.Def_PLCMarkets_ExactCover_X3C
-- name    : PLCMarkets_ExactCover_X3C
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T01:03:08.568526+00:00
-- url     : https://prove2.me/theorems/8732381d-1a7a-4773-9e8c-6589e71e09f9
-- title:
--   Exact Cover by 3-Sets (X3C): exact covers of a family of subsets (§8)
-- statement:
--   An instance of **Exact Cover by 3-Sets** (X3C) is a family $\mathcal C=(C_1,\dots,C_n)$ of subsets of a ground set $X=\{x_1,\dots,x_n\}$ with the same number $n$ of elements; in the problem each $C_i$ has exactly three elements. An **exact cover** is a subfamily $\mathcal C'\subseteq\mathcal C$ such that every element of $X$ belongs to exactly one set of $\mathcal C'$. Writing $\mathcal C'=\{C_i : i\in S\}$ for a set $S$ of indices, the family has an exact cover when
--
--   $$
--   \exists\,S\subseteq\{1,\dots,n\}\ \ \forall x\in X\ \ \exists!\,i:\ i\in S\ \text{and}\ x\in C_i .
--   $$
--
--   X3C is the NP-complete problem (Garey and Johnson 1979) from which Vazirani and Yannakakis reduce the existence of a market equilibrium.
--
--   **Formalization Note.** The ground set and the index set are both $\{0,\dots,n-1\}$ (0-based, where the paper writes $x_1,\dots,x_n$ and $C_1,\dots,C_n$). The family is indexed, so it may repeat a set; "exactly one set" then counts indices. The three-element condition is stated as a hypothesis of the theorems that use it.
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, p. 10:19, §8 (definition of X3C)

import Mathlib

namespace PLCMarkets.ExactCover

/-- An instance of Exact Cover by 3-Sets (X3C) (Vazirani–Yannakakis 2011, §8, p. 10:19) is a family
`C = (C_i)_{i < n}` of subsets of the ground set `X = {x_0, …, x_{n-1}}`, here `Fin n`; each `C_i`
is required to have exactly three elements (`(C i).card = 3`, stated as a hypothesis where used).

`HasExactCover C` holds when some subfamily `C'`, given by a set `S` of indices, covers `X`
exactly: every element `x` belongs to `C_i` for exactly one index `i ∈ S`. -/
def HasExactCover {n : ℕ} (C : Fin n → Finset (Fin n)) : Prop :=
  ∃ S : Finset (Fin n), ∀ x : Fin n, ∃! i, i ∈ S ∧ x ∈ C i

end PLCMarkets.ExactCover


