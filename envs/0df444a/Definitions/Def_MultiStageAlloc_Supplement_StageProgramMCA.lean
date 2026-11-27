-- Prove2me | Definitions.Def_MultiStageAlloc_Supplement_StageProgramMCA
-- name    : MultiStageAlloc_Supplement_StageProgramMCA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:17:33.428799+00:00
-- url     : https://prove2.me/theorems/3238af18-74ec-54b1-9068-5d816df53de9
-- title:
--   The stage program $\mathcal P^{\mathrm{MCA}}_k$ and the price-level masses $H_{j,\tau}$ (§4.1–4.2)
-- statement:
--   Fix a stage $k$ and a state $\eta=(\eta_{j,\tau})_{j\in V,\tau\in[T]}$, the price distribution left by the earlier stages. For variables $x_{i,c,j},y_{j,\tau},z_{i,c}\ge0$, with $x$ and $z$ indexed by the users $i\in U_k$, let
--   $$
--   H_{j,\tau}(x,y)=\sum_{\substack{i\in U_k,\ c\in C:\\ w_{i,c,j}\ge \hat w_\tau}}x_{i,c,j}+\sum_{\tau'=\tau}^{T}y_{j,\tau'} .
--   $$
--   The program $\mathcal P^{\mathrm{MCA}}_k$ maximizes
--   $$
--   \sum_{i\in U_k}\sum_{c\in C}\sum_{j\in V}w_{i,c,j}x_{i,c,j}-\sum_{j\in V}\sum_{\tau\in[T]}\hat w_\tau\bigl(\eta_{j,\tau}-y_{j,\tau}\bigr)-\sum_{j\in V}\sum_{\tau\in[T]}(\hat w_\tau-\hat w_{\tau-1})\,F_k\bigl(H_{j,\tau}(x,y)\bigr)
--   $$
--   subject to
--
--   1. $\sum_{i\in U_k}\sum_{c\in C}x_{i,c,j}+\sum_{\tau\in[T]}y_{j,\tau}\le1$ for every $j\in V$;
--   2. $\sum_{c\in C}z_{i,c}\le1$ for every $i\in U_k$;
--   3. $x_{i,c,j}\le\xi_{i,c,j}z_{i,c}$ for $i\in U_k$, $c\in C$, $j\in V$;
--   4. $y_{j,\tau}\le\eta_{j,\tau}$ for $j\in V$, $\tau\in[T]$.
--
--   The regularizer $F_k(a)=\int_0^a f_k$ is that of Proposition 1, with $F_K\equiv0$, so the last stage is a linear program. A triple $(x,y,z)$ is an optimal solution if it is feasible and no feasible triple has a larger objective.
--
--   **Formalization Note** Optimality is a predicate, because the optimum need not be unique. $y$ is indexed by all $\tau\in\mathbb N$, but only $\tau\in[T]$ enters the program.
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, §4.1, p.25 (P^MCA_k) and §4.2, p.27 (H_{j,τ})

import Mathlib
import Definitions.Def_MultiStageAlloc_Regularizers
import Definitions.Def_MultiStageAlloc_Supplement_MCAInstance

namespace MultiStageAlloc.Supplement

variable {U C V : Type*} [Fintype U] [Fintype C] [Fintype V] {K : ℕ}

/-- **The batch `U_k`** of users arriving at stage `k`. -/
noncomputable def batchSet (I : MCAInstance U C V K) (k : ℕ) : Finset U :=
  Finset.univ.filter (fun i => I.batch i = k)

/-- **`H_{j,τ}(x, y)`**, Feng & Niazadeh, arXiv:2211.16581v1, §4.2, p.27: for stage `k`,
`H_{j,τ}(x, y) = ∑_{i ∈ U_k, c ∈ C : w_{i,c,j} ≥ ŵ_τ} x_{i,c,j} + ∑_{τ' ≥ τ} y_{j,τ'}`, the amount
advertiser `j` holds at prices at least `ŵ_τ`. The sum over `τ'` runs over `τ ≤ τ' ≤ T`. -/
noncomputable def levelH (I : MCAInstance U C V K) (k : ℕ) (x : U → C → V → ℝ)
    (y : V → ℕ → ℝ) (j : V) (τ : ℕ) : ℝ :=
  (∑ i ∈ batchSet I k, ∑ c, if I.wgrid τ ≤ I.price i c j then x i c j else 0) +
    ∑ τ' ∈ Finset.Icc τ I.T, y j τ'

/-- **The feasible set of program (P^MCA_k)**, arXiv:2211.16581v1, §4.1, p.25, given the state
`η = η^(k-1)`: `x, y, z ≥ 0`; `x` and `z` are indexed by the users of `U_k` (they vanish elsewhere);
`∑_{i ∈ U_k, c} x_{i,c,j} + ∑_{τ ∈ [T]} y_{j,τ} ≤ 1` for every `j`; `∑_c z_{i,c} ≤ 1` for `i ∈ U_k`;
`x_{i,c,j} ≤ ξ_{i,c,j} z_{i,c}` for `i ∈ U_k`; and `y_{j,τ} ≤ η_{j,τ}` for `τ ∈ [T]`.

**Formalization Note.** `y` is a function on `V × ℕ`; only `τ ∈ [T] = {1, …, T}` enters the
objective, the constraints and the state update, and values at other `τ` are unconstrained apart from
`y ≥ 0`. -/
def MCAStageFeasible (I : MCAInstance U C V K) (k : ℕ) (η : V → ℕ → ℝ) (x : U → C → V → ℝ)
    (y : V → ℕ → ℝ) (z : U → C → ℝ) : Prop :=
  (∀ i c j, 0 ≤ x i c j) ∧ (∀ j τ, 0 ≤ y j τ) ∧ (∀ i c, 0 ≤ z i c) ∧
    (∀ i c j, I.batch i ≠ k → x i c j = 0) ∧ (∀ i c, I.batch i ≠ k → z i c = 0) ∧
    (∀ j, (∑ i ∈ batchSet I k, ∑ c, x i c j) + ∑ τ ∈ Finset.Icc 1 I.T, y j τ ≤ 1) ∧
    (∀ i, I.batch i = k → ∑ c, z i c ≤ 1) ∧
    (∀ i c j, I.batch i = k → x i c j ≤ I.ξ i c j * z i c) ∧
    ∀ j τ, τ ∈ Finset.Icc 1 I.T → y j τ ≤ η j τ

/-- **The objective of program (P^MCA_k)**, arXiv:2211.16581v1, §4.1, p.25:
`∑_{i ∈ U_k, c, j} w_{i,c,j} x_{i,c,j} - ∑_{j, τ ∈ [T]} ŵ_τ (η_{j,τ} - y_{j,τ})
 - ∑_{j, τ ∈ [T]} (ŵ_τ - ŵ_{τ-1}) F_k(H_{j,τ}(x, y))`, with `F_k = regF K k` the regularizer of
Proposition 1 (`F_K ≡ 0`, so stage `K` is a linear program). -/
noncomputable def mcaStageObj (I : MCAInstance U C V K) (k : ℕ) (η : V → ℕ → ℝ)
    (x : U → C → V → ℝ) (y : V → ℕ → ℝ) : ℝ :=
  (∑ i ∈ batchSet I k, ∑ c, ∑ j, I.price i c j * x i c j) -
    (∑ j, ∑ τ ∈ Finset.Icc 1 I.T, I.wgrid τ * (η j τ - y j τ)) -
    ∑ j, ∑ τ ∈ Finset.Icc 1 I.T, (I.wgrid τ - I.wgrid (τ - 1)) * regF K k (levelH I k x y j τ)

/-- **`(x, y, z)` is an optimal solution of (P^MCA_k)** given the state `η`.

**Formalization Note.** A predicate, since the optimum need not be unique; every statement about
"the optimal solution" holds for every optimal solution. -/
def IsMCAStageOptimal (I : MCAInstance U C V K) (k : ℕ) (η : V → ℕ → ℝ) (x : U → C → V → ℝ)
    (y : V → ℕ → ℝ) (z : U → C → ℝ) : Prop :=
  MCAStageFeasible I k η x y z ∧
    ∀ x' y' z', MCAStageFeasible I k η x' y' z' → mcaStageObj I k η x' y' ≤ mcaStageObj I k η x y

end MultiStageAlloc.Supplement


