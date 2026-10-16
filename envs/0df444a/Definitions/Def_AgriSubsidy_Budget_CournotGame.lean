-- Prove2me | Definitions.Def_AgriSubsidy_Budget_CournotGame
-- name    : AgriSubsidy_Budget_CournotGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T08:03:58.032854+00:00
-- url     : https://prove2.me/theorems/ba4ac5cd-e03d-44b8-918b-5340503958ba
-- title:
--   Finite Cournot market with affine inverse demand
-- statement:
--   A **finite Cournot market** has $N$ producers, an inverse demand curve $p(Q)=\alpha-\beta Q$, and a unit cost $d_j$ for producer $j$. If the output profile is $q$, producer $j$ earns
--
--   $$\pi_j(q)=(\alpha-d_j-\beta\sum_i q_i)q_j.$$
--
--   An equilibrium is a nonnegative output profile at which no producer can raise its profit by changing only its own output to another nonnegative quantity. This general market is reused by the agricultural subsidy model.
--
--   **Formalization Note** Producers are indexed by `Fin N`; positivity of $\alpha$ and $\beta$ is imposed by the paper-specific standing assumptions. At $N=0$ the structure exists, but every theorem in this mission assumes $N>0$.
-- source:
--   Fan, Feng, Li, Shanthikumar, Wu, Output-Oriented Agricultural Subsidy Design, SSRN 4378693 (version of 2023-03-18), pp. 5–6, 10, demand formula and (1)

import Mathlib

namespace AgriSubsidy.Budget

/-- A finite Cournot market with affine inverse demand and individual unit costs. -/
structure CournotGame (N : ℕ) where
  alpha : ℝ
  beta : ℝ
  unitCost : Fin N → ℝ

def CournotGame.profit {N : ℕ} (G : CournotGame N)
    (q : Fin N → ℝ) (j : Fin N) : ℝ :=
  (G.alpha - G.unitCost j - G.beta * ∑ i, q i) * q j

def CournotGame.IsEquilibrium {N : ℕ} (G : CournotGame N)
    (q : Fin N → ℝ) : Prop :=
  (∀ j, 0 ≤ q j) ∧
    ∀ j, ∀ x : ℝ, 0 ≤ x →
      G.profit (Function.update q j x) j ≤ G.profit q j

end AgriSubsidy.Budget


