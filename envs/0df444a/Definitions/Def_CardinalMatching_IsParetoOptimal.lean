-- Prove2me | Definitions.Def_CardinalMatching_IsParetoOptimal
-- name    : CardinalMatching_IsParetoOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:27:23.663071+00:00
-- url     : https://prove2.me/theorems/1c19bc06-1e73-4710-8d66-67294861f70f
-- title:
--   Pareto-better and Pareto-optimal allocations
-- statement:
--   Given allocations $x$ and $y$, $y$ is **Pareto-better** than $x$ if
--   $$
--   u_i\cdot y_i \ge u_i\cdot x_i \ \text{ for all agents } i \quad\text{and}\quad u_i\cdot y_i > u_i\cdot x_i \ \text{ for some agent } i .
--   $$
--   The allocation $x$ is **Pareto-optimal** if no allocation $y\in P_{\mathrm{PM}}$ is Pareto-better than it.
--
--   Pareto-optimality is relative to all fractional perfect matchings: neither to integral matchings nor to sub-stochastic matrices.
--
--   **Formalization Note** The module defines both `IsParetoBetter` and `IsParetoOptimal`; membership of $x$ itself in $P_{\mathrm{PM}}$ is stated separately.
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Definition 5, p.5

import Mathlib
import Definitions.Def_CardinalMatching_IsFracPerfectMatching

namespace CardinalMatching

/-- **Pareto-better** (Tröbst–Vazirani, *Cardinal-Utility Matching Markets*, arXiv:2402.08851v6,
Definition 5, p.5): `y` is Pareto-better than `x` if `u_i · y_i ≥ u_i · x_i` for all agents `i`
and `u_i · y_i > u_i · x_i` for some agent `i`. -/
def IsParetoBetter {A G : Type} [Fintype G] (u : A → G → ℝ) (y x : A → G → ℝ) : Prop :=
  (∀ i, ∑ j, u i j * x i j ≤ ∑ j, u i j * y i j) ∧ ∃ i, ∑ j, u i j * x i j < ∑ j, u i j * y i j

/-- **Pareto-optimality** (Tröbst–Vazirani, *Cardinal-Utility Matching Markets*,
arXiv:2402.08851v6, Definition 5, p.5): `x` is Pareto-optimal if no other allocation is
Pareto-better than it.

**Formalization Note** "Allocation" is a fractional perfect matching (`IsFracPerfectMatching`,
the polytope `P_PM`, p.6), so Pareto-optimality is relative to **all** of `P_PM` — not to
integral matchings and not to sub-stochastic matrices. Membership of `x` itself in `P_PM` is
stated separately wherever the paper requires it. -/
def IsParetoOptimal {A G : Type} [Fintype A] [Fintype G] (u : A → G → ℝ) (x : A → G → ℝ) :
    Prop :=
  ¬ ∃ y : A → G → ℝ, IsFracPerfectMatching y ∧ IsParetoBetter u y x

end CardinalMatching


