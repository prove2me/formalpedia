-- Prove2me | Definitions.Def_Sherbrooke_objective
-- name    : Sherbrooke_objective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:22:31.498202+00:00
-- url     : https://prove2.me/theorems/b974a1b3-b4dd-4898-8c31-0b8f9b7d4857
-- title:
--   The objective (11): $\sum_i \bigl[c_i m_i+\Xi_i(m_i)\bigr]$
-- statement:
--   Let $\iota$ be a finite set of items. Each item $i$ has a unit cost $c_i\in\mathbb R$ and a function $\Xi_i:\mathbb N\to\mathbb R$. For a vector of stock levels $m=(m_i)_{i\in\iota}$ with $m_i\in\{0,1,2,\dots\}$, the **objective (11)** is
--
--   $$
--   \sum_{i\in\iota}\bigl[c_i m_i+\Xi_i(m_i)\bigr].
--   $$
--
--   In the METRIC model, $c_i$ is the unit cost of item $i$ and $\Xi_i(m)$ is the Lagrangian-weighted expected base backorders of the best allocation of $m$ units of item $i$ among the depot and the bases; minimizing (11) trades investment against backorders. The Appendix Theorem is stated for arbitrary functions $\Xi_i$.
--
--   **Formalization Note** The item set is a `Fintype` (an empty item set gives objective $0$); stock levels are natural numbers, cast to reals in the product $c_i m_i$.
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Operations Research 16 (1968), doi:10.1287/opre.16.1.122, Appendix, Theorem, eq. (11), p. 140

import Mathlib

namespace Sherbrooke

/-- **The objective of (11).** Sherbrooke, *METRIC*, Operations Research 16 (1968), Appendix,
Theorem, eq. (11), p. 140: `Σ_i [c_i m_i + Ξ_i(m_i)]`, to be minimized over stock levels
`m_i = 0, 1, 2, …`.

For a finite set of items `ι`, unit costs `c : ι → ℝ`, item functions `Ξ : ι → ℕ → ℝ` and a
stock vector `m : ι → ℕ`, `objective c Ξ m = Σ_i (c_i m_i + Ξ_i(m_i))`.

**Formalization Note.** Items are a `Fintype` (the empty item set is allowed, with objective
`0`); stock levels are natural numbers, cast to `ℝ` in the product `c_i m_i`. In the METRIC model
`c_i` is the unit cost of item `i` and `Ξ_i(m)` the Lagrangian-weighted expected base backorders
of the best allocation of `m` units of item `i` (p. 135); the definition is stated for arbitrary
real data. -/
def objective {ι : Type*} [Fintype ι] (c : ι → ℝ) (Ξ : ι → ℕ → ℝ) (m : ι → ℕ) : ℝ :=
  ∑ i, (c i * (m i : ℝ) + Ξ i (m i))

end Sherbrooke


