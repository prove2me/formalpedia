-- Prove2me | Definitions.Def_CardinalMatching_IsFracPerfectMatching
-- name    : CardinalMatching_IsFracPerfectMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:26:31.385085+00:00
-- url     : https://prove2.me/theorems/9863926d-82d4-40a0-86c6-25178f98cc2f
-- title:
--   Fractional perfect matching (allocation), the polytope $P_{\mathrm{PM}}$
-- statement:
--   In a one-sided matching market there is a finite set $A$ of agents and a finite set $G$ of goods with $|A| = |G| = n$. A **fractional perfect matching**, or **allocation**, is a matrix $x = (x_{ij})_{i\in A, j\in G}$ in the polytope
--   $$
--   P_{\mathrm{PM}} = \Big\{ x \;:\; \sum_{j\in G} x_{ij} = 1\ \ \forall i\in A,\quad \sum_{i\in A} x_{ij} = 1\ \ \forall j\in G,\quad x_{ij}\ge 0\ \ \forall i, j \Big\}.
--   $$
--   By the Birkhoff–von Neumann theorem such an $x$ is a lottery over perfect matchings; agent $i$'s expected utility is $u_i\cdot x_i = \sum_{j} u_{ij}x_{ij}$.
--
--   All fairness and efficiency notions of the mission (envy-freeness, Pareto-optimality) are relative to this polytope.
--
--   **Formalization Note** Agents and goods are arbitrary finite types; an allocation is a real matrix `A → G → ℝ`.
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, §2, p.5 (allocations) and §2.1, p.6 (display of P_PM)

import Mathlib

namespace CardinalMatching

/-- **Fractional perfect matching** (an *allocation*): the polytope `P_PM` of Tröbst–Vazirani,
*Cardinal-Utility Matching Markets*, arXiv:2402.08851v6, §2.1, p.6 (and p.5: "fractional perfect
matchings and linear utilities (which we will also just refer to as allocations)"):
`x ∈ P_PM` iff `∑_{j∈G} x_ij = 1` for every agent `i`, `∑_{i∈A} x_ij = 1` for every good `j`, and
`x_ij ≥ 0` for all `i, j`.

**Formalization Note** Agents and goods are arbitrary finite types `A`, `G` (the paper's finite
sets; for the market of §2, `|A| = |G| = n`). An allocation is a real matrix `x : A → G → ℝ`. -/
def IsFracPerfectMatching {A G : Type} [Fintype A] [Fintype G] (x : A → G → ℝ) : Prop :=
  (∀ i, ∑ j, x i j = 1) ∧ (∀ j, ∑ i, x i j = 1) ∧ ∀ i j, 0 ≤ x i j

end CardinalMatching


