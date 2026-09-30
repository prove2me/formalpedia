-- Prove2me | Definitions.Def_MarkovChainChoice_SingleResource_Assortment
-- name    : MarkovChainChoice_SingleResource_Assortment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:14:53.174111+00:00
-- url     : https://prove2.me/theorems/c9236178-1009-4f6f-9812-cf027644a20a
-- title:
--   The (Assortment) problem and its (Dual) linear program
-- statement:
--   Let each product $j\in N$ carry a revenue $r_j\in\mathbb R$. The **(Assortment)** problem asks for an offer set maximizing expected revenue,
--   $$\max_{S\subseteq N}\ \sum_{j\in N} P_{j,S}\, r_j ,$$
--   and $\hat S$ is an optimal solution when $\sum_{j} P_{j,S}r_j \le \sum_j P_{j,\hat S} r_j$ for every $S\subseteq N$.
--
--   The **(Dual)** linear program is
--   $$\min_{v\in\mathbb R^n}\Big\{\sum_{j\in N}\lambda_j v_j \;:\; v_j\ge r_j\ \ \forall j\in N,\quad v_j \ge \sum_{i\in N}\rho_{j,i}v_i\ \ \forall j\in N\Big\}.$$
--   A vector $v$ is dual feasible if it satisfies both families of constraints, and dual optimal if it is feasible and its objective $\sum_j\lambda_j v_j$ is no larger than that of any feasible vector.
--
--   These are the objects of Theorem 2 and Lemma 3, which the single-resource analysis applies with adjusted revenues.
--
--   **Formalization Note** `expRevenue M r S` $=\sum_j P_{j,S} r_j$ with `purchase` from the (Balance) definition; `IsOptimalAssortment` states optimality against every offer set (the maximum over the finite family of subsets is attained). `DualFeasible` uses $\rho_{j,i}$ (row $j$), the index order of (Dual). `IsDualOptimal` is stated as "feasible and no worse than every feasible point", not with an infimum. Revenues carry no sign assumption.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1326, Section 3, (Assortment) and (Dual)

import Mathlib
import Definitions.Def_MarkovChainChoice_Shared_Balance
open MarkovChainChoice.Shared

namespace MarkovChainChoice.SingleResource

variable {n : ℕ}

/-- The expected revenue `Σ_{j∈N} P_{j,S} r_j` of the offer set `S` with product revenues `r`,
the objective of the (Assortment) problem, Feldman–Topaloglu 2017, p. 1326. -/
noncomputable def expRevenue (M : Model n) (r : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ j, purchase M S j * r j

/-- `S` is an optimal solution of (Assortment) `max_{S ⊆ N} Σ_{j∈N} P_{j,S} r_j`. -/
def IsOptimalAssortment (M : Model n) (r : Fin n → ℝ) (S : Finset (Fin n)) : Prop :=
  ∀ S' : Finset (Fin n), expRevenue M r S' ≤ expRevenue M r S

/-- Feasibility for (Dual), p. 1326: `v_j ≥ r_j` and `v_j ≥ Σ_{i∈N} ρ_{j,i} v_i` for all `j`. -/
def DualFeasible (M : Model n) (r v : Fin n → ℝ) : Prop :=
  ∀ j, r j ≤ v j ∧ ∑ i, M.rho j i * v i ≤ v j

/-- `v` is an optimal solution of (Dual): `min_{v ∈ ℝⁿ} {Σ_j λ_j v_j : v feasible}`. -/
def IsDualOptimal (M : Model n) (r v : Fin n → ℝ) : Prop :=
  DualFeasible M r v ∧
    ∀ w, DualFeasible M r w → ∑ j, M.lam j * v j ≤ ∑ j, M.lam j * w j

end MarkovChainChoice.SingleResource


