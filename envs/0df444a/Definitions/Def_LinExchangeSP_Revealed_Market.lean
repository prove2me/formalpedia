-- Prove2me | Definitions.Def_LinExchangeSP_Revealed_Market
-- name    : LinExchangeSP_Revealed_Market
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:56.50764+00:00
-- url     : https://prove2.me/theorems/9bbb3f40-059c-4be8-8fcc-0ac1532abc43
-- title:
--   §2, Definitions 2.1–2.2, pp. 4–5 — the linear exchange market, MBB edges, money allocations, surpluses, market equilibria
-- statement:
--   This file fixes the linear exchange market of Garg and Végh and its equilibrium notion.
--
--   1. **Market** (p. 4). There are $n$ agents $A=[n]$ and $n$ divisible goods $G=\{g_1,\dots,g_n\}$, one unit of each. Agent $i$ arrives with the unit of good $g_i$. Agent $i$ has utility $u_{ij}\ge 0$ for a unit of good $g_j$. The **edge set** is $E=\{(i,g_j): u_{ij}>0\}$ and $m=|E|$. Every agent has at least one edge and every good has at least one edge.
--   2. **Maximum bang-per-buck** (p. 4). At prices $p=(p_j)_{g_j\in G}$, agent $i$'s bang-per-buck is
--   $$\alpha_i=\max_{g_k\in G}\frac{u_{ik}}{p_k},$$
--   and $(i,g_j)\in E$ is an **MBB edge** if $u_{ij}/p_j=\alpha_i$. The set of MBB edges is $\mathrm{MBB}(p)\subseteq E$.
--   3. **Money allocation** (Definition 2.1). A money flow $f=(f_{ij})$ records the money agent $i$ spends on good $g_j$. The pair $(p,f)$ is a money allocation if (i) $p>0$ and $f\ge 0$; (ii) $\operatorname{supp}(f)\subseteq\mathrm{MBB}(p)$; (iii) $\sum_{g_j\in G}f_{ij}\le p_i$ for every agent $i$; (iv) $\sum_{i\in A}f_{ij}\le p_j$ for every good $g_j$.
--   4. **Surpluses** (Definition 2.1). The surplus of agent $i$ is $c_i(p,f)=p_i-\sum_{g_j}f_{ij}$ and the surplus of good $g_j$ is $s_j(p,f)=p_j-\sum_{i}f_{ij}$. We write $\lVert s(p,f)\rVert_1=\sum_j|s_j(p,f)|$ and $\lVert s(p,f)\rVert_\infty=\max_j|s_j(p,f)|$.
--   5. **Market equilibrium** (Definition 2.2). A money allocation $(p,f)$ is a market equilibrium if
--   $$\lVert s(p,f)\rVert_1=0.$$
--
--   Agent $i$'s budget is $p_i$, the price of the good it owns; an equilibrium is a price vector together with a spending pattern on MBB goods that exhausts every budget and clears every good. These objects are shared by every statement of the mission.
--
--   **Formalization Note** Agents and goods are both indexed by `Fin n` (0-based), so the good owned by agent `i` has index `i`. The market structure carries the paper's assumption that every agent and every good has an edge. An MBB edge is required to lie in $E$ ($u_{ij}>0$), as $\mathrm{MBB}(p)\subseteq E$ on p. 4. Prices and money are real numbers. $\lVert s\rVert_\infty$ is a supremum over `Fin n`, equal to $0$ when $n=0$.
-- source:
--   Garg & Végh, A strongly polynomial algorithm for linear exchange markets, arXiv:1809.06266v3, pp. 4–5, §2 (The linear exchange market), Definition 2.1, Definition 2.2

import Mathlib

namespace LinExchangeSP.Revealed

/-- A linear exchange market (§2, p. 4). Agents and goods are both indexed by `Fin n`
(0-based; the paper's `A = [n]` and `G = {g_1, …, g_n}`); agent `i` arrives with the unit of good
`i`. `u i j ≥ 0` is agent `i`'s utility for a unit of good `j`. Every agent has a good with positive
utility and every good has an agent with positive utility for it. -/
structure Market (n : ℕ) where
  u : Fin n → Fin n → ℝ
  u_nonneg : ∀ i j, 0 ≤ u i j
  agent_edge : ∀ i, ∃ j, 0 < u i j
  good_edge : ∀ j, ∃ i, 0 < u i j

variable {n : ℕ}

/-- `E ⊆ A × G`: the pairs `(i, j)` with `u i j > 0` (p. 4). -/
def Market.E (M : Market n) : Set (Fin n × Fin n) := {e | 0 < M.u e.1 e.2}

/-- `m := |E|` (p. 4). -/
noncomputable def Market.m (M : Market n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e : Fin n × Fin n => 0 < M.u e.1 e.2)).card

/-- `MBB(p) ⊆ E` (p. 4): the edges `(i, j) ∈ E` such that good `j` attains the maximum bang-per-buck
`α_i = max_k u i k / p k` of agent `i`. -/
def Market.MBB (M : Market n) (p : Fin n → ℝ) : Set (Fin n × Fin n) :=
  {e | 0 < M.u e.1 e.2 ∧ ∀ k, M.u e.1 k / p k ≤ M.u e.1 e.2 / p e.2}

/-- `supp(f)`: the pairs carrying nonzero money (p. 4). -/
def supp (f : Fin n → Fin n → ℝ) : Set (Fin n × Fin n) := {e | f e.1 e.2 ≠ 0}

/-- The surplus of agent `i`: `c_i(p, f) = p_i − Σ_j f_ij` (Definition 2.1, p. 4). -/
def agentSurplus (p : Fin n → ℝ) (f : Fin n → Fin n → ℝ) (i : Fin n) : ℝ := p i - ∑ j, f i j

/-- The surplus of good `j`: `s_j(p, f) = p_j − Σ_i f_ij` (Definition 2.1, p. 4). -/
def goodSurplus (p : Fin n → ℝ) (f : Fin n → Fin n → ℝ) (j : Fin n) : ℝ := p j - ∑ i, f i j

/-- `‖s(p, f)‖₁ = Σ_j |s_j(p, f)|` (p. 4). -/
def surplusL1 (p : Fin n → ℝ) (f : Fin n → Fin n → ℝ) : ℝ := ∑ j, |goodSurplus p f j|

/-- `‖s(p, f)‖∞ = max_j |s_j(p, f)|` (p. 4); for `n = 0` the supremum over the empty index is `0`. -/
noncomputable def surplusLinf (p : Fin n → ℝ) (f : Fin n → Fin n → ℝ) : ℝ :=
  ⨆ j, |goodSurplus p f j|

/-- Definition 2.1 (p. 4): `(p, f)` is a money allocation if (i) `p > 0` and `f ≥ 0`;
(ii) `supp(f) ⊆ MBB(p)`; (iii) every agent spends at most `p_i`; (iv) every good is sold for at most
`p_j`. -/
def Market.IsMoneyAllocation (M : Market n) (p : Fin n → ℝ) (f : Fin n → Fin n → ℝ) : Prop :=
  (∀ j, 0 < p j) ∧ (∀ i j, 0 ≤ f i j) ∧ supp f ⊆ M.MBB p ∧
    (∀ i, ∑ j, f i j ≤ p i) ∧ (∀ j, ∑ i, f i j ≤ p j)

/-- Definition 2.2 (p. 5): a money allocation with `‖s(p, f)‖₁ = 0` is a market equilibrium. -/
def Market.IsMarketEquilibrium (M : Market n) (p : Fin n → ℝ) (f : Fin n → Fin n → ℝ) : Prop :=
  M.IsMoneyAllocation p f ∧ surplusL1 p f = 0

end LinExchangeSP.Revealed


