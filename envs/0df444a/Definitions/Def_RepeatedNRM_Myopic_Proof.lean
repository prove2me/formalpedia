-- Prove2me | Definitions.Def_RepeatedNRM_Myopic_Proof
-- name    : RepeatedNRM_Myopic_Proof
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:59.856976+00:00
-- url     : https://prove2.me/theorems/bcc1e7f7-1307-4156-9ee1-78efb5106b81
-- title:
--   p. ec2 and p. ec3 — the dual of the myopic LP (7) and the customer class C_j of Definition 2
-- statement:
--   Two objects used in the proof of Theorem 2.
--
--   1. **The dual of (7)** (p. ec2) at budgets $\mathbf b$: minimize $\sum_i s_i\lambda_i+\sum_j b_j\mu_j$ subject to $\lambda_i+p_{ij}\mu_j\ge p_{ij}$ for all $i,j$, $\lambda\ge 0$, $\mu\ge 0$. Here $\mu_j$ is the multiplier of customer $j$'s budget constraint (1) and $\lambda_i$ that of the supply constraint (2) of product $i$. A pair $(\mu,\lambda)$ is **dual optimal** if it is feasible and its objective is at most that of every feasible pair.
--   2. **The class $C_j$** (Definition 2, p. ec3) of an allocation $x$ and a customer $j$: the smallest set of customers that contains $j$ and contains every customer $k$ with $x_{ik}>0$ for some product $i\in A_l$ of a member $l$. By construction, every product desired by a member of $C_j$ is allocated, if at all, only to members of $C_j$.
--
--   **Formalization Note.** Definition 2 prints an iteration "$C_j\leftarrow D_j(C_j)$" starting from $\{j\}$, with $D_j(C)=\{k : x_{ik}>0$ for some $i\in\bigcup_{l\in C}A_l\}$. Read as a replacement, the iteration can drop $j$ itself (when $j$ receives none of its desired products) and need not be monotone. The definition here is its cumulative reading, the least closed set containing $j$, which has the property the paper states after the definition. The printed range "$k\in\{1,\dots,n\}$" is read as the customers $\{1,\dots,m\}$.
-- source:
--   Calmon, Ciocan & Romero, accepted manuscript (TSpace), p. ec2 (dual of (7)) and p. ec3 (Definition 2)

import Mathlib
import Definitions.Def_RepeatedNRM_Myopic_Model

namespace RepeatedNRM.Myopic

variable (I : Instance)

/-- Feasibility for the dual of the linear program (7) (p. ec2): `λ_i ≥ 0`, `μ_j ≥ 0` and
`λ_i + p_ij μ_j ≥ p_ij` for all `i, j`. -/
def DualFeasible (μ : Fin I.m → ℝ) (lam : Fin I.n → ℝ) : Prop :=
  (∀ i, 0 ≤ lam i) ∧ (∀ j, 0 ≤ μ j) ∧ ∀ i j, I.p i j ≤ lam i + I.p i j * μ j

/-- The dual objective `∑_i s_i λ_i + ∑_j b_j μ_j` (p. ec2). -/
def dualObj (b : Fin I.m → ℝ) (μ : Fin I.m → ℝ) (lam : Fin I.n → ℝ) : ℝ :=
  ∑ i, I.s i * lam i + ∑ j, b j * μ j

/-- `(μ, λ)` is an optimal solution of the dual of (7) at budgets `b`. -/
def DualOptimal (b : Fin I.m → ℝ) (μ : Fin I.m → ℝ) (lam : Fin I.n → ℝ) : Prop :=
  DualFeasible I μ lam ∧
    ∀ μ' lam', DualFeasible I μ' lam' → dualObj I b μ lam ≤ dualObj I b μ' lam'

/-- Membership in the class `C_j` of Definition 2 (p. ec3), in closure form: `j` is in it, and
whenever `l` is in it and customer `k` receives a positive amount of a product `i ∈ A_l`, `k` is
in it. -/
inductive InClass (A : Fin I.m → Finset (Fin I.n)) (x : Fin I.n → Fin I.m → ℝ) (j : Fin I.m) :
    Fin I.m → Prop
  | self : InClass A x j j
  | step {l k : Fin I.m} {i : Fin I.n} : InClass A x j l → i ∈ A l → 0 < x i k → InClass A x j k

/-- The class of customers `C_j` of Definition 2 (p. ec3): the least set of customers containing
`j` and closed under "receives a positive amount of a product desired by a member". -/
noncomputable def customerClass (A : Fin I.m → Finset (Fin I.n)) (x : Fin I.n → Fin I.m → ℝ)
    (j : Fin I.m) : Finset (Fin I.m) := by
  classical
  exact Finset.univ.filter (InClass I A x j)

end RepeatedNRM.Myopic


