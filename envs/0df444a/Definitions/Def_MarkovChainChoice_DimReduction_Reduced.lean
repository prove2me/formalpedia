-- Prove2me | Definitions.Def_MarkovChainChoice_DimReduction_Reduced
-- name    : MarkovChainChoice_DimReduction_Reduced
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T09:35:21.628986+00:00
-- url     : https://prove2.me/theorems/38b7aa8b-0df0-4002-9b74-578c575d1850
-- title:
--   The (Reduced) linear program for network revenue management
-- statement:
--   Consider a network with resources $M=\{1,\dots,m\}$, a selling horizon of $T$ periods, capacities $c_q$ for $q\in M$, consumption $a_{q,j}$ of resource $q$ by one sale of product $j$, and revenues $r_j$. With a Markov chain choice model $(\lambda,\rho)$ governing customer choice, the **(Reduced) linear program** is
--   $$
--   \max_{(x,z)\in\mathbb R^{2n}_+}\Big\{\sum_{j\in N}T\,r_j\,x_j \;:\; \sum_{j\in N}T\,a_{q,j}\,x_j\le c_q\ \ \forall q\in M,\quad x_j+z_j=\lambda_j+\sum_{i\in N}\rho_{i,j}z_i\ \ \forall j\in N\Big\}.
--   $$
--   This file defines feasibility for (Reduced), its objective, and the predicate "$(x,z)$ is an optimal solution": $(x,z)$ is feasible and its objective value is at least that of every feasible solution.
--
--   **Formalization Note** $T$ is a natural number cast to $\mathbb R$; no sign conditions are imposed on $c$, $a$, $r$, as in the paper. Optimality is expressed as feasibility plus comparison with every feasible point, not through a supremum.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1331, Section 6, display (Reduced)

import Mathlib
import Definitions.Def_MarkovChainChoice_Shared_Model
open MarkovChainChoice.Shared

namespace MarkovChainChoice.DimReduction

/-- Feasibility in the (Reduced) linear program (p. 1331): `x, z ≥ 0`,
`∑_j T a_{q,j} x_j ≤ c_q` for every resource `q`, and
`x_j + z_j = λ_j + ∑_i ρ_{i,j} z_i` for every product `j`. -/
def ReducedFeasible {n m : ℕ} (M : Model n) (T : ℕ) (c : Fin m → ℝ) (a : Fin m → Fin n → ℝ)
    (x z : Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ x j) ∧ (∀ j, 0 ≤ z j) ∧ (∀ q, ∑ j, (T : ℝ) * a q j * x j ≤ c q) ∧
    ∀ j, x j + z j = M.lam j + ∑ i, M.rho i j * z i

/-- The objective `∑_j T r_j x_j` of the (Reduced) linear program. -/
def reducedObj {n : ℕ} (T : ℕ) (r : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ j, (T : ℝ) * r j * x j

/-- `(x, z)` is an optimal solution of the (Reduced) linear program: it is feasible and its
objective is at least that of every feasible solution. -/
def IsReducedOptimal {n m : ℕ} (M : Model n) (T : ℕ) (c : Fin m → ℝ) (a : Fin m → Fin n → ℝ)
    (r : Fin n → ℝ) (x z : Fin n → ℝ) : Prop :=
  ReducedFeasible M T c a x z ∧
    ∀ x' z', ReducedFeasible M T c a x' z' → reducedObj T r x' ≤ reducedObj T r x

end MarkovChainChoice.DimReduction


