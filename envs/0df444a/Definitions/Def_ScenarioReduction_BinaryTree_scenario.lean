-- Prove2me | Definitions.Def_ScenarioReduction_BinaryTree_scenario
-- name    : ScenarioReduction_BinaryTree_scenario
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:02:09.218693+00:00
-- url     : https://prove2.me/theorems/e6a6a9a0-0df8-48a0-8dee-491aa08c1cb1
-- title:
--   Regular binary scenario tree, eq. (19): $\omega_i^k=\sum_{j=0}^k\delta^j_{i_j}$ with $\delta^j_{i_j}=(2i_j-3)\delta^j$
-- statement:
--   Fix a horizon $K\in\mathbb N$ and nonnegative level parameters $\delta^1,\dots,\delta^K$, with $\delta^0=0$ at the root. A **regular binary scenario tree** has $N=2^K$ scenarios. Each scenario is determined by a choice of branch $i_k\in\{1,2\}$ at every level $k=1,\dots,K$ (level $0$ is the common root and carries no choice), and the scenario is the vector $\omega_i=(\omega_i^0,\dots,\omega_i^K)\in\mathbb R^{K+1}$ with
--
--   $$\omega_i^k=\sum_{j=0}^{k}\delta^j_{i_j},\qquad \delta^j_{i_j}=(2i_j-3)\,\delta^j\in\{-\delta^j,\delta^j\},\qquad k=0,\dots,K.$$
--
--   So at level $j$ the path moves down by $\delta^j$ (branch $i_j=1$) or up by $\delta^j$ (branch $i_j=2$), and every scenario starts at $\omega_i^0=0$.
--
--   This is the scenario model of Section 3 of Heitsch and Römisch, on which the minimal reduction distance of Proposition 3.1 is computed.
--
--   **Formalization Note** Scenarios are indexed by $\sigma:\{0,\dots,K-1\}\to\{0,1\}$ (`Fin K → Fin 2`), so there are exactly $2^K$ of them; the Fin-index $r$ stores the branch at tree level $r+1$, and `lev σ k` returns it for $k\in\{1,\dots,K\}$ as $i_k-1$ (value $0$ is the paper's $i_k=1$, i.e. $-\delta^k$; value $1$ is $i_k=2$, i.e. $+\delta^k$). `lev` returns a default $0$ outside $1\le k\le K$, which is never used. The parameters are a function $\delta:\mathbb N\to\mathbb R$ of which only $\delta(1),\dots,\delta(K)$ enter; the level-$0$ term $\delta^0_{i_0}=0$ is omitted from the sum, which runs over $j=1,\dots,k$. The scenario is a vector of type `Fin (K+1) → ℝ`, whose Mathlib norm is the maximum norm $\max_k|\omega^k|$.
-- source:
--   Heitsch, Römisch, Scenario Reduction Algorithms in Stochastic Programming, Comput. Optim. Appl. 24 (2003), pp. 195–196, eq. (19) and the case d = 2

import Mathlib

namespace ScenarioReduction.BinaryTree

/-- Branch index at tree level `k` (paper's `i_k - 1 ∈ {0, 1}`) of the scenario indexed by
`σ : Fin K → Fin 2`: Fin-index `r` stores level `r + 1`, so level `k ∈ {1, …, K}` is `σ ⟨k - 1, _⟩`.
Level `0` (the root, which carries no choice) and levels above `K` return the default `0`;
they are never used with a nonzero weight. -/
def lev {K : ℕ} (σ : Fin K → Fin 2) (k : ℕ) : Fin 2 :=
  if h : 1 ≤ k ∧ k ≤ K then σ ⟨k - 1, by omega⟩ else 0

/-- Scenario `ω_σ = (ω^0, …, ω^K) ∈ ℝ^{K+1}` of the regular binary tree, eq. (19):
`ω^k = ∑_{j=1}^{k} δ^j_{i_j}` with `δ^j_{i_j} = (2 i_j - 3) δ^j` and `i_j = lev σ j + 1 ∈ {1, 2}`.
The level-0 term `δ^0_{i_0} = 0` is omitted, so `ω^0 = 0` (the common root). -/
noncomputable def scenario {K : ℕ} (δ : ℕ → ℝ) (σ : Fin K → Fin 2) : Fin (K + 1) → ℝ :=
  fun k => ∑ r ∈ Finset.Icc 1 k.val, (2 * (((lev σ r).val : ℝ) + 1) - 3) * δ r

end ScenarioReduction.BinaryTree


