-- Prove2me | Definitions.Def_DynamicOnlineLP_DLA_Instance
-- name    : DynamicOnlineLP_DLA_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T19:20:22.222424+00:00
-- url     : https://prove2.me/theorems/574aa9ba-aa14-4ab1-9757-9061dea7f7d0
-- title:
--   Online LP instance (π_t ≥ 0, a_t ∈ [0,1]^m, b), OPT, general position, arrival order σ, LP_s(d), uniform average over permutations
-- statement:
--   An **instance** of the online linear program consists of $n$ columns, column $j$ carrying an objective coefficient $\pi_j\ge 0$ and a constraint column $a_j=(a_{1j},\dots,a_{mj})\in[0,1]^m$, and a right-hand side $b\in\mathbb R^m$. Its offline problem is (1):
--
--   $$\mathrm{OPT}=\max\Big\{\sum_{j=1}^n\pi_jx_j \;:\; \sum_{j=1}^n a_{ij}x_j\le b_i\ (i=1,\dots,m),\ 0\le x_j\le 1\Big\}.$$
--
--   In the **random permutation model** the columns arrive in the order given by a uniformly random permutation $\sigma$ of $\{1,\dots,n\}$: the column arriving at time $t$ is column $\sigma(t)$. For an arrival order $\sigma$, $\mathrm{OPT}_s(d)$ denotes the optimal value of the partial program $\mathrm{LP}_s(d)$ on the columns arriving at times $1,\dots,s$ with right-hand side $d$. Expectations and probabilities over the arrival order are averages over all $n!$ permutations:
--
--   $$\mathbb E_\sigma[f(\sigma)]=\frac1{n!}\sum_{\sigma}f(\sigma),\qquad \mathbb P_\sigma[A]=\frac{\#\{\sigma: \sigma\in A\}}{n!}.$$
--
--   The instance is in **general position** (Assumption 3) if for any price vector $p\in\mathbb R^m$ at most $m$ columns satisfy $p^{\top}a_j=\pi_j$.
--
--   These are the data of Assumptions 1–3 and Definition 1 (competitive ratio) of Agrawal, Wang and Ye.
--
--   **Formalization Note** Columns are `Fin n`, constraints `Fin m`, times are 0-based: Lean time $t$ is the paper's time $t+1$, and `firstTimes n s` is the paper's $\{1,\dots,s\}$. The nonnegativity of $\pi$ and the bounds $0\le a_{ij}\le 1$ are fields of the structure; $b$ is an arbitrary real vector, and theorems add $b\ge 0$ (or a lower bound on $b$) where needed, so that $\mathrm{OPT}$ is a true optimum.
-- source:
--   Agrawal, Wang, Ye, A Dynamic Near-Optimal Algorithm for Online Linear Programming, Oper. Res. 62(4), 2014, p. 876, Eqs. (1)–(2); p. 877, Assumptions 1–2 and Definition 1; p. 881, Assumption 3; p. 884, LP_s(d) and OPT_s(d)

import Mathlib
import Definitions.Def_DynamicOnlineLP_DLA_PackingLP

namespace DynamicOnlineLP.DLA

/-- An instance of the (offline) linear program (1) of Agrawal–Wang–Ye 2014: `n` columns, column
`j` carrying an objective coefficient `π_j ≥ 0` and a constraint column `a_j ∈ [0,1]^m`, and a
right-hand side `b ∈ ℝ^m`. -/
structure Instance (m n : ℕ) where
  π : Fin n → ℝ
  a : Fin n → Fin m → ℝ
  b : Fin m → ℝ
  π_nonneg : ∀ j : Fin n, 0 ≤ π j
  a_nonneg : ∀ j : Fin n, ∀ i : Fin m, 0 ≤ a j i
  a_le_one : ∀ j : Fin n, ∀ i : Fin m, a j i ≤ 1

/-- `OPT`: the optimal value of the offline linear program (1) over all `n` columns. -/
noncomputable def Instance.OPT {m n : ℕ} (I : Instance m n) : ℝ :=
  optValue (Finset.univ : Finset (Fin n)) I.π I.a I.b

/-- Assumption 3 (general position) for the whole input: for any price vector `p ∈ ℝ^m`, at most
`m` columns satisfy `pᵀ a_t = π_t`. -/
def Instance.GeneralPosition {m n : ℕ} (I : Instance m n) : Prop :=
  GeneralPositionOn (Finset.univ : Finset (Fin n)) I.π I.a

/-- Objective coefficients in arrival order `σ`: the column arriving at (0-based) time `t` is
column `σ t`. -/
def Instance.arrPi {m n : ℕ} (I : Instance m n) (σ : Equiv.Perm (Fin n)) : Fin n → ℝ :=
  fun t => I.π (σ t)

/-- Constraint columns in arrival order `σ`. -/
def Instance.arrA {m n : ℕ} (I : Instance m n) (σ : Equiv.Perm (Fin n)) : Fin n → Fin m → ℝ :=
  fun t => I.a (σ t)

/-- The first `s` arrival times `{0, …, s−1}` (the paper's times `1, …, s`). -/
def firstTimes (n s : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun t : Fin n => t.val < s)

/-- `OPT_s(d)` in arrival order `σ`: optimal value of the partial LP `LP_s(d)` on the columns
arriving at times `1, …, s`, with right-hand side `d`. -/
noncomputable def Instance.partialOPT {m n : ℕ} (I : Instance m n) (σ : Equiv.Perm (Fin n))
    (s : ℕ) (d : Fin m → ℝ) : ℝ :=
  optValue (firstTimes n s) (I.arrPi σ) (I.arrA σ) d

/-- Expectation over a uniformly random arrival order: the average of `f` over all `n!`
permutations of `Fin n`. -/
noncomputable def avgPerm {n : ℕ} (f : Equiv.Perm (Fin n) → ℝ) : ℝ :=
  (∑ σ : Equiv.Perm (Fin n), f σ) / (Fintype.card (Equiv.Perm (Fin n)) : ℝ)

/-- Probability of an event over a uniformly random arrival order: the fraction of the `n!`
permutations of `Fin n` at which it holds. -/
noncomputable def probPerm {n : ℕ} (P : Equiv.Perm (Fin n) → Prop) : ℝ :=
  by classical exact
    ((Finset.univ.filter P).card : ℝ) / (Fintype.card (Equiv.Perm (Fin n)) : ℝ)

end DynamicOnlineLP.DLA


