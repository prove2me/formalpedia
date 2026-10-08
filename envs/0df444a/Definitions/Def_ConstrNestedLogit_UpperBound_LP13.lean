-- Prove2me | Definitions.Def_ConstrNestedLogit_UpperBound_LP13
-- name    : ConstrNestedLogit_UpperBound_LP13
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:03:39.394793+00:00
-- url     : https://prove2.me/theorems/170e4c58-de2d-4ab7-9f50-63ed6ae269fb
-- title:
--   §7.1, p. 26 — the linear program (13) over the knapsack-relaxation solutions
-- statement:
--   Let $v_0$ be the preference weight of the no-purchase option, $\gamma_i$ the dissimilarity parameter of nest $i$, and $\{X_i : i \in M\}$ finite sets of vectors in $[0,1]^n$ (in the paper, $X_i = \{x_i^g : g \in \mathcal G_i\}$, the solutions of the linear programming relaxation of the knapsack problem (10)). The linear program (13) is
--
--   $$\min\Big\{ z \;:\; v_0\, z \ge \sum_{i\in M} y_i,\quad y_i \ge \Big(\sum_{j\in N} v_{ij} x_{j}\Big)^{\gamma_i}\Big\{\frac{\sum_{j\in N} v_{ij} r_{ij} x_{j}}{\sum_{j\in N} v_{ij} x_{j}} - z\Big\}\ \ \forall x \in X_i,\ i \in M \Big\},$$
--
--   with decision variables $(z, y) = (z, y_1, \dots, y_m)$. A pair $(z, y)$ is **feasible** when it satisfies both families of constraints, and **optimal** when it is feasible and $z$ is no larger than the $z$-component of every feasible pair.
--
--   The constraint term is the nest-$i$ term $V_i(x)^{\gamma_i}(R_i(x) - z)$ of the nested logit model evaluated at a fractional vector, with $V_i(x) = \sum_j v_{ij}x_j$ and $R_i(x) = \sum_j v_{ij}r_{ij}x_j / V_i(x)$. Proposition 7 shows that the optimal value of (13) bounds the optimal expected revenue from above.
--
--   **Formalization Note** The constraint term is the published `NestedLogitVariants.General.F I i x z`, which equals the displayed term when the within-nest no-purchase weights $v_{i0}$ are zero (every statement of this mission assumes this). Powers are real powers (`Real.rpow`) and $a/0 = 0$ in Lean, so at $x = 0$ the term is $0^{\gamma_i}(0 - z) = 0$ for $\gamma_i > 0$. The first constraint is written $\sum_i y_i \le v_0 z$.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 26, §7.1, linear program (13)

import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model
import Definitions.Def_NestedLogitVariants_General_Relaxation

namespace ConstrNestedLogit.UpperBound

open NestedLogitVariants.General

variable {ι : Type*} {n : ℕ}

/-- `(z, y)` is feasible for the linear program (13) (§7.1, p. 26) built on the vectors `X i`
(the paper's `{x_i^g : g ∈ G_i}`): `v_0 z ≥ ∑_{i ∈ M} y_i`, and for every nest `i` and every
`x ∈ X i`,
`y_i ≥ (∑_j v_{ij} x_j)^{γ_i} (∑_j v_{ij} r_{ij} x_j / ∑_j v_{ij} x_j − z)`, which is `F I i x z`
when `v_{i0} = 0`. -/
def LP13Feasible [Fintype ι] (I : Instance ι n) (X : ι → Finset (Fin n → ℝ)) (z : ℝ)
    (y : ι → ℝ) : Prop :=
  (∑ i, y i) ≤ I.v0 * z ∧ ∀ i, ∀ x ∈ X i, F I i x z ≤ y i

/-- `(z, y)` is an optimal solution of the linear program (13): feasible, and `z` is no larger than
the `z`-component of any feasible solution (the program minimizes `z`). -/
def LP13Optimal [Fintype ι] (I : Instance ι n) (X : ι → Finset (Fin n → ℝ)) (z : ℝ)
    (y : ι → ℝ) : Prop :=
  LP13Feasible I X z y ∧ ∀ z' y', LP13Feasible I X z' y' → z ≤ z'

end ConstrNestedLogit.UpperBound


