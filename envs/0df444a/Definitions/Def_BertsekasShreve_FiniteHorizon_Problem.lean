-- Prove2me | Definitions.Def_BertsekasShreve_FiniteHorizon_Problem
-- name    : BertsekasShreve_FiniteHorizon_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T01:14:58.438918+00:00
-- url     : https://prove2.me/theorems/423004ef-5bd2-44f2-affa-d39e89e81353
-- title:
--   The N-stage problem of Section 2.2: J_{N,π}, J*_N, uniform N-stage optimality, ε-optimality, dominated convergence
-- statement:
--   Fix a model $(S,C,U,H)$ of Section 2.1 and a terminal function $J_0\in F$ (the book requires $J_0(x)>-\infty$ for all $x$, eq. (4) of Chapter 2; the theorems of the mission carry this as a hypothesis).
--
--   1. The **$N$-stage cost** of a policy $\pi=(\mu_0,\mu_1,\dots)$ is
--   $$J_{N,\pi}=(T_{\mu_0}T_{\mu_1}\cdots T_{\mu_{N-1}})(J_0),$$
--   and the **$N$-stage optimal cost** is $J^*_N(x)=\inf_{\pi\in\Pi}J_{N,\pi}(x)$ for $x\in S$.
--   2. $\pi$ is **$N$-stage optimal** if $J_{N,\pi}=J^*_N$. A policy $\pi^*=(\mu^*_0,\mu^*_1,\dots)$ is **uniformly $N$-stage optimal** if the policy $(\mu^*_i,\mu^*_{i+1},\dots)$ is $(N-i)$-stage optimal for every $i=0,1,\dots,N-1$.
--   3. Given $\varepsilon>0$, $\pi_\varepsilon$ is **$N$-stage $\varepsilon$-optimal** if for every $x\in S$
--   $$J_{N,\pi_\varepsilon}(x)\le\begin{cases}J^*_N(x)+\varepsilon&\text{if }J^*_N(x)>-\infty,\\ -1/\varepsilon&\text{if }J^*_N(x)=-\infty.\end{cases}$$
--   4. If $\{\varepsilon_n\}$ is a sequence of positive numbers with $\varepsilon_n\downarrow0$, a sequence of policies $\{\pi_n\}$ exhibits **$\{\varepsilon_n\}$-dominated convergence to optimality** if $\lim_{n\to\infty}J_{N,\pi_n}=J^*_N$ pointwise and, for $n=2,3,\dots$,
--   $$J_{N,\pi_n}(x)\le\begin{cases}J^*_N(x)+\varepsilon_n&\text{if }J^*_N(x)>-\infty,\\ J_{N,\pi_{n-1}}(x)+\varepsilon_n&\text{if }J^*_N(x)=-\infty.\end{cases}$$
--
--   These are the objects in which the questions of Chapter 3 are asked: whether $J^*_N=T^N(J_0)$ (the dynamic programming algorithm computes the optimal cost) and whether optimal or nearly optimal policies exist.
--
--   **Formalization Note** $J^*_N$ is an infimum over policies, not over controls, so the identity $J^*_N=T^N(J_0)$ is not true by definition. Sequences in item 4 are indexed by `ℕ`; only the entries with index $n\ge1$ are meaningful and the dominance clauses are required for $n\ge2$, as printed.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, pp. 28–29, Section 2.2, eqs. (4), (5), (7) of Chapter 2 and the definitions of N-stage optimal, uniformly N-stage optimal, N-stage ε-optimal and {ε_n}-dominated convergence to optimality

import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model

namespace BertsekasShreve.FiniteHorizon

open Filter Topology

namespace Model

variable {S C : Type*} (m : Model S C)

/-- The `N`-stage cost function of the policy `π` with terminal function `J₀`,
`J_{N,π} = (T_{μ₀} T_{μ₁} ⋯ T_{μ_{N−1}})(J₀)`, eq. (5) of Chapter 2. -/
def costN (J₀ : S → EReal) (N : ℕ) (π : m.Policy) : S → EReal := m.comp π N J₀

/-- The `N`-stage optimal cost function `J*_N(x) = inf_{π ∈ Π} J_{N,π}(x)`, eq. (7) of
Chapter 2. The infimum is over policies, not over controls. -/
noncomputable def optCostN (J₀ : S → EReal) (N : ℕ) : S → EReal :=
  fun x => ⨅ π : m.Policy, m.costN J₀ N π x

/-- `π` is `N`-stage optimal: `J_{N,π} = J*_N` (p. 29). -/
def IsNStageOptimal (J₀ : S → EReal) (N : ℕ) (π : m.Policy) : Prop :=
  m.costN J₀ N π = m.optCostN J₀ N

/-- `π* = (μ₀*, μ₁*, …)` is uniformly `N`-stage optimal: the policy `(μ_i*, μ_{i+1}*, …)` is
`(N − i)`-stage optimal for every `i = 0, 1, …, N − 1` (p. 29). -/
def IsUniformlyNStageOptimal (J₀ : S → EReal) (N : ℕ) (π : m.Policy) : Prop :=
  ∀ i, i < N → m.IsNStageOptimal J₀ (N - i) (π.shift i)

/-- `π_ε` is `N`-stage `ε`-optimal (p. 29):
`J_{N,π_ε}(x) ≤ J*_N(x) + ε` if `J*_N(x) > −∞`, and `J_{N,π_ε}(x) ≤ −1/ε` if `J*_N(x) = −∞`. -/
def IsNStageEpsOptimal (J₀ : S → EReal) (N : ℕ) (ε : ℝ) (π : m.Policy) : Prop :=
  ∀ x, (m.optCostN J₀ N x ≠ ⊥ → m.costN J₀ N π x ≤ m.optCostN J₀ N x + (ε : EReal)) ∧
    (m.optCostN J₀ N x = ⊥ → m.costN J₀ N π x ≤ ((-(1 / ε) : ℝ) : EReal))

/-- The sequence of policies `{π_n}` exhibits `{ε_n}`-dominated convergence to optimality
(p. 29): `lim_{n→∞} J_{N,π_n} = J*_N` pointwise, and for `n = 2, 3, …`,
`J_{N,π_n}(x) ≤ J*_N(x) + ε_n` if `J*_N(x) > −∞`,
`J_{N,π_n}(x) ≤ J_{N,π_{n−1}}(x) + ε_n` if `J*_N(x) = −∞`.
Sequences are indexed by `n = 1, 2, …`; the entries at index `0` play no role. -/
def IsDominatedConvergence (J₀ : S → EReal) (N : ℕ) (ε : ℕ → ℝ) (πs : ℕ → m.Policy) : Prop :=
  (∀ x, Tendsto (fun n => m.costN J₀ N (πs n) x) atTop (𝓝 (m.optCostN J₀ N x))) ∧
    ∀ n, 2 ≤ n → ∀ x,
      (m.optCostN J₀ N x ≠ ⊥ → m.costN J₀ N (πs n) x ≤ m.optCostN J₀ N x + (ε n : EReal)) ∧
      (m.optCostN J₀ N x = ⊥ →
        m.costN J₀ N (πs n) x ≤ m.costN J₀ N (πs (n - 1)) x + (ε n : EReal))

end Model

end BertsekasShreve.FiniteHorizon


