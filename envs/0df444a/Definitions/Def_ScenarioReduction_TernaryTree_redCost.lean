-- Prove2me | Definitions.Def_ScenarioReduction_TernaryTree_redCost
-- name    : ScenarioReduction_TernaryTree_redCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:08:20.568296+00:00
-- url     : https://prove2.me/theorems/8363d8b2-ced3-476d-a507-c3029966ed8e
-- title:
--   Reduction cost $D_J = \sum_{i\in J} p_i \min_{j\notin J} c(\omega_i,\omega_j)$ of deleting the scenarios in $J$ (eq. (8))
-- statement:
--   Let a discrete probability distribution be carried by finitely many scenarios, indexed by a finite set $I$, with probabilities $p_i$, and let $c(i, j)$ be the cost ("distance") between scenarios $i$ and $j$. For an index set $J \subset I$ of scenarios to be deleted, with at least one scenario kept ($I \setminus J \neq \emptyset$), the **reduction cost** is
--
--   $$
--   D_J = \sum_{i \in J} p_i \min_{j \notin J} c(i, j).
--   $$
--
--   Each deleted scenario is charged its probability times its cost to the nearest kept scenario. By Theorem 2.1 of the paper, $D_J$ is the optimal (Kantorovich-type) distance between the original distribution and the best distribution supported on the kept scenarios, and the optimal reduction problem (8) minimizes $D_J$ over all $J$ with $\#J = N - n$.
--
--   **Formalization Note** The minimum over $j \notin J$ is a `Finset.inf'` over the complement of $J$, which requires a proof that the complement is nonempty; there is therefore no default value for $J = I$.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), p. 190, eq. (8)

import Mathlib

namespace ScenarioReduction.TernaryTree

/-- The reduction cost of eq. (8) of Heitsch–Römisch (2003): for scenarios indexed by a finite
type `ι` with probabilities `p` and cost `c`, deleting the index set `J` (whose complement is
nonempty) costs `D_J = Σ_{i ∈ J} p i · min_{j ∉ J} c i j`. -/
noncomputable def redCost {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ)
    (c : ι → ι → ℝ) (J : Finset ι) (hJ : Jᶜ.Nonempty) : ℝ :=
  ∑ i ∈ J, p i * Jᶜ.inf' hJ (fun j => c i j)

end ScenarioReduction.TernaryTree


