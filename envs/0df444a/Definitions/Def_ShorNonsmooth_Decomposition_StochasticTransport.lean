-- Prove2me | Definitions.Def_ShorNonsmooth_Decomposition_StochasticTransport
-- name    : ShorNonsmooth_Decomposition_StochasticTransport
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T16:21:24.153203+00:00
-- url     : https://prove2.me/theorems/c9f46186-850b-4f7b-9d38-113363750bd2
-- title:
--   The stochastic transportation problem (4.163)–(4.165)
-- statement:
--   There are $m$ plants and $n$ building sites. Plant $i$ produces $a_i$, the unit transportation cost from plant $i$ to site $j$ is $c_{ij}$, the demand of site $j$ is a random variable $\xi_j$ with probability density $p_j$, and $r_j$ is the penalty per unit of unsatisfied demand at site $j$. For $t^+ = \max\{0,t\}$:
--
--   1. $p$ is a **probability density** if $p \ge 0$, $p$ is Lebesgue integrable and $\int p(z)\,dz = 1$;
--   2. the **expected shortage** of a demand with density $p$ at supply level $t$ is $E(\xi - t)^+ = \int (z-t)^+ p(z)\,dz$;
--   3. the **objective** of the problem is
--   $$
--   \sum_{i,j=1}^{m,n} c_{ij} x_{ij} + \sum_{j=1}^n r_j\, E\Big(\xi_j - \sum_{i=1}^m x_{ij}\Big)^+ ; \qquad (4.163)
--   $$
--   4. the **feasible set** is $\sum_{j=1}^n x_{ij} \le a_i$ for $i = 1,\dots,m$ (4.164) and $x_{ij} \ge 0$ (4.165).
--
--   The problem minimizes transportation costs plus expected losses from deficits in supply; it is a two-stage stochastic program.
--
--   **Formalization Note** A shipment plan is a function `Fin m → Fin n → ℝ`. The expectation is written through the density as a Bochner integral; it equals the book's expectation when $z\,p(z)$ is integrable, which the theorem assumes.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, pp. 131–132, formulas (4.163)–(4.165)

import Mathlib

namespace ShorNonsmooth.Decomposition

open MeasureTheory

/-! Shor (1985), §4.6, subsection 4 "The Stochastic Transportation Problem", pp. 131–132:
`m` plants, `n` building sites, shipments `x i j`, costs `c i j`, capacities `a i`, penalties `r j`,
and random demands `ξ_j` with probability densities `p_j`. -/

/-- `p` is a **probability density function** on `ℝ`: nonnegative, Lebesgue integrable, total mass 1. -/
def IsDensity (p : ℝ → ℝ) : Prop :=
  (∀ z, 0 ≤ p z) ∧ Integrable p ∧ ∫ z, p z = 1

/-- p. 132: the **expected shortage** `E(ξ − t)⁺ = ∫ (z − t)⁺ p(z) dz` of a random variable `ξ` with
density `p`, where `t⁺ = max{0, t}`. -/
noncomputable def expectedShortage (p : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ z, max (z - t) 0 * p z

/-- p. 131, (4.163): the objective
`Σ_{i,j} c_ij x_ij + Σ_j r_j E(ξ_j − Σ_i x_ij)⁺` of the stochastic transportation problem. -/
noncomputable def stochTransportObjective {m n : ℕ} (c : Fin m → Fin n → ℝ) (r : Fin n → ℝ)
    (p : Fin n → ℝ → ℝ) (x : Fin m → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, c i j * x i j + ∑ j, r j * expectedShortage (p j) (∑ i, x i j)

/-- p. 132, (4.164)–(4.165): the feasible set `Σ_j x_ij ≤ a_i` for every plant `i`, `x_ij ≥ 0`. -/
def stochTransportFeasible {m n : ℕ} (a : Fin m → ℝ) : Set (Fin m → Fin n → ℝ) :=
  {x | (∀ i, ∑ j, x i j ≤ a i) ∧ ∀ i j, 0 ≤ x i j}

end ShorNonsmooth.Decomposition


