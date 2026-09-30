-- Prove2me | Definitions.Def_MarkovChainChoice_Reduced_LinearPrograms
-- name    : MarkovChainChoice_Reduced_LinearPrograms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:30:36.635969+00:00
-- url     : https://prove2.me/theorems/7c6b4906-7c53-4fc1-b79f-c9b10d187029
-- title:
--   The polyhedron ℋ and the (Choice Based) and (Reduced) linear programs of network revenue management
-- statement:
--   Fix a Markov chain choice model with data $\lambda,\rho$ on the products $N=\{1,\dots,n\}$. The polyhedron
--   $$\mathcal H = \Big\{(x,z)\in\mathbb R^{2n}_+ :\ x_j + z_j = \lambda_j + \sum_{i\in N}\rho_{i,j} z_i\ \ \forall j\in N\Big\}$$
--   collects the nonnegative solutions of the flow-balance equations with free split between available visits $x$ and unavailable visits $z$.
--
--   **Network data.** There are $m$ resources $M=\{1,\dots,m\}$ with capacities $c_q$, a selling horizon of $T$ periods, and products $j$ with revenues $r_j$ that consume $a_{q,j}$ units of resource $q$ when sold.
--
--   The **(Choice Based)** linear program has one variable $u_S$ per subset $S\subseteq N$ (the probability of offering $S$ in a period):
--   $$\max_{u\in\mathbb R^{2^n}_+}\Big\{\sum_{S\subseteq N}\sum_{j\in N} T r_j P_{j,S} u_S :\ \sum_{S\subseteq N}\sum_{j\in N} T a_{q,j} P_{j,S} u_S \le c_q\ \ \forall q\in M,\ \ \sum_{S\subseteq N} u_S = 1\Big\}.$$
--
--   The **(Reduced)** linear program has $2n$ variables:
--   $$\max_{(x,z)\in\mathbb R^{2n}_+}\Big\{\sum_{j\in N} T r_j x_j :\ \sum_{j\in N} T a_{q,j} x_j \le c_q\ \ \forall q\in M,\ \ x_j+z_j=\lambda_j+\sum_{i\in N}\rho_{i,j} z_i\ \ \forall j\in N\Big\}.$$
--   An **optimal solution** of either program is a feasible point whose objective value is at least that of every feasible point.
--
--   Finally, given offer sets $S^1,\dots,S^K$ and weights $\gamma^1,\dots,\gamma^K$, the vector $\hat u$ puts weight $\hat u_S = \sum_{k:\,S^k=S}\gamma^k$ on each subset $S$; when the $S^k$ are distinct this is $\hat u_{S^k}=\gamma^k$ and $\hat u_S = 0$ for $S\notin\{S^1,\dots,S^K\}$.
--
--   **Formalization Note** `H M` is a set of pairs `(x, z)` in `(Fin n → ℝ) × (Fin n → ℝ)`. Resources are `Fin m`, `T : ℕ` enters as the real number `(T : ℝ)` exactly where the paper writes it (objective and capacity rows), `a q j` $=a_{q,j}$, and no sign conditions are imposed on $c$, $a$, $r$ (the paper has none). `ReducedFeasible` is membership in `H M` plus the capacity rows. Optimality is stated as "feasible and at least as good as every feasible point" rather than through a supremum. `uHat S γ` is $\hat u$; summing over the indices with $S^k=S$ is the only consistent reading of the paper's $\hat u_{S^k}=\gamma^k$ when some $S^k$ coincide.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1326 (definition of ℋ), pp. 1330–1331, Section 6 (network data, (Choice Based), (Reduced)), p. 1331, Theorem 7 (definition of û)

import Mathlib
import Definitions.Def_MarkovChainChoice_Reduced_Model

namespace MarkovChainChoice.Reduced

variable {m n : ℕ}

/-- The polyhedron `ℋ ⊆ ℝ^{2n}_+` (p. 1326):
`ℋ = {(x, z) ∈ ℝ^{2n}_+ : x_j + z_j = λ_j + ∑_{i ∈ N} ρ_{i,j} z_i ∀ j ∈ N}`,
as a subset of `(Fin n → ℝ) × (Fin n → ℝ)` (first component `x`, second `z`). -/
def H (M : Model n) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | (∀ j, 0 ≤ p.1 j) ∧ (∀ j, 0 ≤ p.2 j) ∧
    ∀ j, p.1 j + p.2 j = M.lam j + ∑ i, M.rho i j * p.2 i}

/-! Network data (§6, pp. 1330–1331): resources `M = {1, …, m}` encoded as `Fin m`,
`T` time periods, capacities `c q`, consumption `a q j = a_{q,j}` (units of resource `q`
used by product `j`), revenues `r j`. No sign conditions are imposed, as in the paper. -/

/-- Feasibility for (Choice Based) (p. 1331): `u ∈ ℝ^{2^n}_+` (one variable `u_S` per offer
set `S ⊆ N`), `∑_{S ⊆ N} ∑_{j ∈ N} T a_{q,j} P_{j,S} u_S ≤ c_q` for all `q`, and
`∑_{S ⊆ N} u_S = 1`. -/
def ChoiceBasedFeasible (M : Model n) (T : ℕ) (a : Fin m → Fin n → ℝ) (c : Fin m → ℝ)
    (u : Finset (Fin n) → ℝ) : Prop :=
  (∀ S, 0 ≤ u S) ∧
  (∀ q, ∑ S, ∑ j, (T : ℝ) * a q j * purchase M S j * u S ≤ c q) ∧
  ∑ S, u S = 1

/-- The objective `∑_{S ⊆ N} ∑_{j ∈ N} T r_j P_{j,S} u_S` of (Choice Based) (p. 1331). -/
noncomputable def choiceBasedObjective (M : Model n) (T : ℕ) (r : Fin n → ℝ)
    (u : Finset (Fin n) → ℝ) : ℝ :=
  ∑ S, ∑ j, (T : ℝ) * r j * purchase M S j * u S

/-- `u` is an optimal solution of (Choice Based) (p. 1331): it is feasible and no feasible
point has a larger objective value. -/
def IsChoiceBasedOptimal (M : Model n) (T : ℕ) (a : Fin m → Fin n → ℝ) (c : Fin m → ℝ)
    (r : Fin n → ℝ) (u : Finset (Fin n) → ℝ) : Prop :=
  ChoiceBasedFeasible M T a c u ∧
    ∀ v, ChoiceBasedFeasible M T a c v →
      choiceBasedObjective M T r v ≤ choiceBasedObjective M T r u

/-- Feasibility for (Reduced) (p. 1331): `(x, z) ∈ ℝ^{2n}_+`,
`∑_{j ∈ N} T a_{q,j} x_j ≤ c_q` for all `q`, and
`x_j + z_j = λ_j + ∑_{i ∈ N} ρ_{i,j} z_i` for all `j`; i.e. `(x, z) ∈ ℋ` plus the capacity rows. -/
def ReducedFeasible (M : Model n) (T : ℕ) (a : Fin m → Fin n → ℝ) (c : Fin m → ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) : Prop :=
  p ∈ H M ∧ ∀ q, ∑ j, (T : ℝ) * a q j * p.1 j ≤ c q

/-- The objective `∑_{j ∈ N} T r_j x_j` of (Reduced) (p. 1331). -/
def reducedObjective (T : ℕ) (r : Fin n → ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  ∑ j, (T : ℝ) * r j * p.1 j

/-- `p = (x, z)` is an optimal solution of (Reduced) (p. 1331): it is feasible and no feasible
point has a larger objective value. -/
def IsReducedOptimal (M : Model n) (T : ℕ) (a : Fin m → Fin n → ℝ) (c : Fin m → ℝ)
    (r : Fin n → ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) : Prop :=
  ReducedFeasible M T a c p ∧
    ∀ p', ReducedFeasible M T a c p' → reducedObjective T r p' ≤ reducedObjective T r p

/-- The (Choice Based) solution `û` built in Theorem 7 (p. 1331) from offer sets
`S^1, …, S^K` and weights `γ^1, …, γ^K`: `û_S = ∑_{k : S^k = S} γ^k`. When the `S^k` are
distinct this is the paper's `û_{S^k} = γ^k` and `û_S = 0` for `S ∉ {S^1, …, S^K}`. -/
def uHat {K : ℕ} (S : Fin K → Finset (Fin n)) (γ : Fin K → ℝ) : Finset (Fin n) → ℝ :=
  fun S' => ∑ k ∈ Finset.univ.filter (fun k => S k = S'), γ k

end MarkovChainChoice.Reduced


