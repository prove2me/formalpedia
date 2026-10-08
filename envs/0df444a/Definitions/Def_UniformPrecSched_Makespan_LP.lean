-- Prove2me | Definitions.Def_UniformPrecSched_Makespan_LP
-- name    : UniformPrecSched_Makespan_LP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T20:12:11.238519+00:00
-- url     : https://prove2.me/theorems/05f2e217-407a-4a98-91cf-9407854b23a9
-- title:
--   The linear program LP (1)–(5), (8), the bad speeds B_j, the assignment algorithm, and x̂
-- statement:
--   Fix an instance of $Q|prec|C_{\max}$ with speed classes $\bar s_1 > \cdots > \bar s_K$ of sizes $m_1, \dots, m_K$.
--
--   1. **The linear program LP.** Its variables are $x_{kj}$ ($k = 1,\dots,K$, $j = 1,\dots,n$), $C_j$ and $D$. A triple $(x, C, D)$ is feasible when
--   $$\sum_{k=1}^K x_{kj} = 1 \quad (1), \qquad \frac{1}{m_k \bar s_k}\sum_{j=1}^n p_j x_{kj} \le D \quad (2), \qquad \sum_{k=1}^K \frac{p_j}{\bar s_k} x_{kj} \le C_j \quad (3),$$
--   $$\sum_{k=1}^K \frac{p_j}{\bar s_k} x_{kj} \le C_j - C_{j'} \ \text{ if } j' \prec j \quad (4), \qquad C_j \le D \quad (5), \qquad x_{kj} \ge 0 \quad (8),$$
--   for all $j$ and $k$. LP is: minimize $D$ subject to (1)–(5) and (8). An optimal solution is a feasible one whose $D$ is at most that of every feasible solution.
--   2. **Averaged processing time.** $\bar p_j = \sum_{k=1}^K (p_j/\bar s_k)\, x_{kj}$.
--   3. **Bad speeds.** For a threshold $\gamma$, $B_j = \{k : p_j/\bar s_k > \gamma\, \bar p_j\}$; the paper uses $\gamma = 2$ (p. 7) and $\gamma = \sqrt K + 1$ (p. 8).
--   4. **The assignment algorithm.** An assignment $k(j)$ is computed by the assignment algorithm from $x$ with threshold $\gamma$ when, for every job $j$, $k(j) \notin B_j$ and $\bar s_{k(j)} m_{k(j)}$ is largest among the indices $k \notin B_j$.
--   5. **Indicator.** $\hat x_{kj} = 1$ if $k = k(j)$ and $\hat x_{kj} = 0$ otherwise.
--
--   The LP is the relaxation whose solution guides the assignment of jobs to speeds; Lemmas 3.1–3.4 bound the chain length and the load of the resulting assignment in terms of $D$.
--
--   **Formalization Note** The speed-class index is zero-based (Lean `0` is $\bar s_1$). The assignment algorithm is a predicate: when several indices maximize $\bar s_k m_k$ the paper does not say which is "the index", and every maximizer is allowed. "Optimal" is stated as minimality of $D$ among feasible solutions; existence of an optimum is a separate milestone.
-- source:
--   Chudak & Shmoys, Approximation algorithms for precedence-constrained scheduling problems on parallel machines that run at different speeds, authors' manuscript (preprint of J. Algorithms, 1999, DOI 10.1006/jagm.1998.0987), pp. 5–6, constraints (1)–(5), (8) and LP; p. 7, p̄_j, B_j, k(j); p. 8, modified B_j; p. 7 and p. 9, x̂ (Lemmas 3.2, 3.4)

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Model

namespace UniformPrecSched.Makespan

variable {n m : ℕ}

/-- `(x, C, D)` is a feasible solution of the linear program `LP` (pp. 5–6), i.e. it satisfies
constraints (1)–(5) and (8); the speed-class index `κ` is the paper's `k`:
* (1) `Σ_k x_kj = 1` for every job `j`;
* (2) `(1/(m_k s̄_k)) Σ_j p_j x_kj ≤ D` for every speed class `k`;
* (3) `Σ_k (p_j/s̄_k) x_kj ≤ C_j` for every job `j`;
* (4) `Σ_k (p_j/s̄_k) x_kj ≤ C_j − C_{j'}` whenever `j' ≺ j`;
* (5) `C_j ≤ D` for every job `j`;
* (8) `x_kj ≥ 0`. -/
def LPFeasible (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ) (C : Fin n → ℝ)
    (D : ℝ) : Prop :=
  (∀ j, ∑ κ, x κ j = 1) ∧
  (∀ κ, (1 / ((classCount I κ : ℝ) * classSpeed I κ)) * ∑ j, I.p j * x κ j ≤ D) ∧
  (∀ j, ∑ κ, I.p j / classSpeed I κ * x κ j ≤ C j) ∧
  (∀ j' j, I.prec j' j → ∑ κ, I.p j / classSpeed I κ * x κ j ≤ C j - C j') ∧
  (∀ j, C j ≤ D) ∧
  (∀ κ j, 0 ≤ x κ j)

/-- `(x, C, D)` is an optimal solution of `LP` (p. 6): it is feasible and its objective value
`D` is at most that of every feasible solution. -/
def LPOptimal (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ) (C : Fin n → ℝ)
    (D : ℝ) : Prop :=
  LPFeasible I x C D ∧ ∀ x' C' D', LPFeasible I x' C' D' → D ≤ D'

/-- The (averaged) processing time `p̄_j = Σ_k (p_j/s̄_k) x_kj` of job `j` under `x` (p. 7). -/
noncomputable def pbar (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ κ, I.p j / classSpeed I κ * x κ j

/-- The set of bad speeds `B_j = {k : p_j/s̄_k > γ p̄_j}` for job `j` (p. 7 with `γ = 2`,
p. 8 with `γ = √K + 1`). -/
noncomputable def badSet (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ) (γ : ℝ)
    (j : Fin n) : Finset (Fin (numSpeeds I)) :=
  Finset.univ.filter fun κ => γ * pbar I x j < I.p j / classSpeed I κ

/-- `k` is an assignment the assignment algorithm of pp. 7–8 can compute from `x` with
threshold `γ`: for every job `j`, `k(j) ∉ B_j` and `s̄_{k(j)} m_{k(j)}` is largest among the
indices not in `B_j` (any maximizer is allowed; the paper does not specify ties). -/
def IsLPAssignment (I : Instance n m) (x : Fin (numSpeeds I) → Fin n → ℝ) (γ : ℝ)
    (k : Assignment I) : Prop :=
  ∀ j, k j ∉ badSet I x γ j ∧
    ∀ κ ∉ badSet I x γ j,
      classSpeed I κ * (classCount I κ : ℝ) ≤ classSpeed I (k j) * (classCount I (k j) : ℝ)

/-- The 0-1 indicator `x̂_kj` of an assignment (Lemmas 3.2 and 3.4): `x̂_kj = 1` if `k = k(j)`
and `x̂_kj = 0` otherwise. -/
noncomputable def xhat (I : Instance n m) (k : Assignment I) :
    Fin (numSpeeds I) → Fin n → ℝ :=
  fun κ j => if κ = k j then 1 else 0

end UniformPrecSched.Makespan


