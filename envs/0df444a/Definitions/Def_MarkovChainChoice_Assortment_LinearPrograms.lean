-- Prove2me | Definitions.Def_MarkovChainChoice_Assortment_LinearPrograms
-- name    : MarkovChainChoice_Assortment_LinearPrograms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:09:32.961077+00:00
-- url     : https://prove2.me/theorems/af6b3fe9-5dc8-41a8-acf8-756e1bc3e052
-- title:
--   The polyhedron $\mathcal H$, the linear program over it, and the (Dual) problem
-- statement:
--   Fix a Markov chain choice model $(\lambda,\rho)$ on $N=\{1,\dots,n\}$ and revenues $r\in\mathbb R^n$.
--
--   **The polyhedron $\mathcal H$.**
--
--   $$
--   \mathcal H=\Big\{(x,z)\in\mathbb R^{2n}_+:\ x_j+z_j=\lambda_j+\sum_{i\in N}\rho_{i,j}z_i\ \ \forall j\in N\Big\}.
--   $$
--
--   **The primal linear program.** $\max\{\sum_{j\in N}r_jx_j : (x,z)\in\mathcal H\}$; a point $(x,z)$ is an optimal solution if it lies in $\mathcal H$ and no point of $\mathcal H$ has a larger objective value.
--
--   **(Dual).**
--
--   $$
--   \min_{v\in\mathbb R^n}\Big\{\sum_{j\in N}\lambda_jv_j:\ v_j\ge r_j\ \ \forall j\in N,\ \ v_j\ge\sum_{i\in N}\rho_{j,i}v_i\ \ \forall j\in N\Big\}.
--   $$
--
--   A vector $v$ is dual feasible if it satisfies both families of constraints, and an optimal solution of (Dual) if it is dual feasible and $\sum_j\lambda_jv_j\le\sum_j\lambda_jw_j$ for every dual feasible $w$.
--
--   These are the two linear programs through which the assortment problem is solved.
--
--   **Formalization Note.** $\mathbb R^{2n}$ is `(Fin n → ℝ) × (Fin n → ℝ)` with first component $x$ and second $z$. Note the index order: $\mathcal H$ sums the inflow $\rho_{i,j}z_i$ into $j$, while (Dual) sums the row $\rho_{j,i}v_i$ of $j$. Optimality is stated as "feasible and at least as good as every feasible point", not via `sSup`/`sInf`.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1326, Section 3 (the polyhedron ℋ, the linear program following Lemma 1, and (Dual)); DOI 10.1287/opre.2017.1628

import Mathlib
import Definitions.Def_MarkovChainChoice_Assortment_Model

namespace MarkovChainChoice.Assortment

variable {n : ℕ}

/-- The polyhedron `ℋ ⊆ ℝ^{2n}_+` (p. 1326):
`ℋ = {(x, z) ∈ ℝ^{2n}_+ : x_j + z_j = λ_j + ∑_{i ∈ N} ρ_{i,j} z_i ∀ j ∈ N}`,
as a subset of `(Fin n → ℝ) × (Fin n → ℝ)` (first component `x`, second `z`). -/
def H (M : Model n) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | (∀ j, 0 ≤ p.1 j) ∧ (∀ j, 0 ≤ p.2 j) ∧
    ∀ j, p.1 j + p.2 j = M.lam j + ∑ i, M.rho i j * p.2 i}

/-- The objective `∑_{j ∈ N} r_j x_j` of the linear program over `ℋ` (p. 1326). -/
def lpObjective (r : Fin n → ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  ∑ j, r j * p.1 j

/-- `p` is an optimal solution of the linear program
`max_{(x,z) ∈ ℝ^{2n}_+} {∑_j r_j x_j : x_j + z_j = λ_j + ∑_i ρ_{i,j} z_i ∀ j}` (p. 1326):
it lies in `ℋ` and no point of `ℋ` has a larger objective. -/
def IsLPOptimal (M : Model n) (r : Fin n → ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) : Prop :=
  p ∈ H M ∧ ∀ q ∈ H M, lpObjective r q ≤ lpObjective r p

/-- Feasibility for (Dual) (p. 1326): `v_j ≥ r_j` and `v_j ≥ ∑_{i ∈ N} ρ_{j,i} v_i` for all `j`. -/
def DualFeasible (M : Model n) (r : Fin n → ℝ) (v : Fin n → ℝ) : Prop :=
  ∀ j, r j ≤ v j ∧ ∑ i, M.rho j i * v i ≤ v j

/-- `v` is an optimal solution of
(Dual) `min_{v ∈ ℝ^n} {∑_j λ_j v_j : v_j ≥ r_j ∀ j, v_j ≥ ∑_i ρ_{j,i} v_i ∀ j}` (p. 1326). -/
def IsDualOptimal (M : Model n) (r : Fin n → ℝ) (v : Fin n → ℝ) : Prop :=
  DualFeasible M r v ∧
    ∀ w, DualFeasible M r w → ∑ j, M.lam j * v j ≤ ∑ j, M.lam j * w j

end MarkovChainChoice.Assortment


