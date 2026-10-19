-- Prove2me | Definitions.Def_TradingPostNSW_Leontief_Setting
-- name    : TradingPostNSW_Leontief_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:34.365054+00:00
-- url     : https://prove2.me/theorems/d1609e60-65cb-4b15-a12e-289d744210f5
-- title:
--   §2, §4, Def. 4.6, pp. 6, 12, 14–15, 22 — Leontief Fisher instance, NSW, Trading Post with entrance fee, pure Nash equilibrium, ε-market equilibrium
-- statement:
--   This file fixes the model of §2 and §4 of Brânzei, Gkatzelis and Mehta.
--
--   There are $n$ agents $i \in N = \{1,\dots,n\}$ and $m$ divisible goods $j \in M = \{1,\dots,m\}$, one unit of each. Agent $i$ has a Leontief valuation vector $v_i = (v_{i,1},\dots,v_{i,m}) \in \mathbb{R}^m_+$ and a budget $B_i$. Its **demand set** is $D_i = \{ j \mid v_{i,j} > 0\}$, and its **Leontief utility** for a bundle $y \in \mathbb{R}^m$ is
--   $$u_i(y) = \min_{j \in D_i} \frac{y_j}{v_{i,j}}.$$
--   The standing assumptions are: $m \ge 1$, every $v_{i,j} \ge 0$, every $B_i \ge 1$ (p. 6), and every $D_i$ is nonempty. **Perfect competition** (p. 12) says that every good $j$ has two distinct agents $i \ne k$ with $v_{i,j} > 0$ and $v_{k,j} > 0$.
--
--   An allocation $x$ is **feasible** if $x_{i,j} \ge 0$ and $\sum_i x_{i,j} = 1$ for every good $j$. With total budget $B = \sum_i B_i$, the **Nash social welfare** is
--   $$\mathrm{NSW}(x) = \Big( \prod_{i=1}^n u_i(x_i)^{B_i} \Big)^{1/B}.$$
--
--   In the **Trading Post game with entrance fee** $\Delta$, written $\mathcal{TP}(\Delta)$, agent $i$ chooses bids $b_i \in [0,B_i]^m$ with $\sum_j b_{i,j} = B_i$. The **effective bid** is $\bar b_{i,j} = b_{i,j}$ if $b_{i,j} \ge \Delta$ and $\bar b_{i,j} = 0$ otherwise, and the induced allocation is
--   $$x_{i,j} = \frac{\bar b_{i,j}}{\sum_{k=1}^n \bar b_{k,j}} \ \text{ if } \bar b_{i,j} > 0, \qquad x_{i,j} = 0 \ \text{ otherwise}.$$
--   A bid profile $b$ is a **pure Nash equilibrium** if every $b_i$ is a strategy and no agent can raise its utility by switching unilaterally to another strategy.
--
--   For a bid profile $b$, the prices $p_j = \sum_i b_{i,j}$ are read off the bids. For prices $p$, $\phi_i(p) = \sum_j v_{i,j} p_j$ is the money agent $i$ needs for unit utility. A pair $(p, x)$ with $p \ge 0$, $x \ge 0$ and $\sum_i x_{i,j} \le 1$ is an **$\epsilon$-market equilibrium** (Definition 4.6) if
--
--   1. every good with $p_j > 0$ is completely sold, $\sum_i x_{i,j} = 1$;
--   2. every agent exhausts its budget, $\sum_j x_{i,j} p_j = B_i$;
--   3. for every bundle $y \ge 0$ with $p \cdot y \le B_i$, $u_i(y) \le u_i(x_i)(1+\epsilon)$.
--
--   Finally, at a profile $b$ with induced allocation $x$, the fraction $\phi_{i,j} = x_{i,j}/v_{i,j}$ measures how much of its need for good $j$ agent $i$ receives, and the **tight set** $S_i = \{ j \in D_i \mid \phi_{i,j} = u_i(x_i)\}$ collects the goods received in the smallest fraction.
--
--   These objects are shared by every statement of the mission: the price-of-anarchy goal, the equilibrium structure lemmas of the proof of Theorem 4.7, and the Fisher-market statements of the proof of Theorem 4.8.
--
--   **Formalization Note** Agents and goods are `Fin n` and `Fin m`; all quantities are real. The utility is a `Finset.inf'` over $D_i$, with value $0$ if $D_i$ is empty, a branch never reached under the standing assumptions. Definition 4.6 (iii) prints bundles $y \in [0,1]^m$; it is encoded over all $y \ge 0$, as the proof of Theorem 4.8 uses it (p. 22: $u_i(p') = \max\{u_i(y) \mid y \ge 0;\ p'\cdot y \le B_i\}$); under the printed reading Theorem 4.8 is false. The fraction $\phi_{i,j}$ is computed from the induced allocation; the page writes it with the nominal bids $\tilde b$, which coincide with the effective ones at an equilibrium. The p. 6 normalization "w.l.o.g. $v_{i,j} \ge 1$" is not imposed.
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, pp. 6, 12, 14–15, 22, §2, §4, §4.2, Definition 4.6, proof of Theorem 4.7, proof of Theorem 4.8

import Mathlib

namespace TradingPostNSW.Leontief

/-- A Fisher-market instance with `n` agents and `m` divisible goods (one unit of each):
Leontief coefficients `v i j` and budgets `B i` (Brânzei–Gkatzelis–Mehta, §2, p. 6). -/
structure Instance (n m : ℕ) where
  v : Fin n → Fin m → ℝ
  B : Fin n → ℝ

variable {n m : ℕ}

/-- The demand set `D_i = {j | v_{i,j} > 0}` of agent `i` (proof of Theorem 4.7, p. 15). -/
noncomputable def D (I : Instance n m) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun j => 0 < I.v i j)

/-- Standing assumptions of §2, p. 6: at least one good, `v_i ∈ ℝ^m_+`, budgets `B_i ≥ 1`,
and every agent demands at least one good (needed for the Leontief minimum). -/
structure Standing (I : Instance n m) : Prop where
  pos_m : 0 < m
  v_nonneg : ∀ i j, 0 ≤ I.v i j
  one_le_B : ∀ i, 1 ≤ I.B i
  D_nonempty : ∀ i, (D I i).Nonempty

/-- Perfect competition (§4, p. 12): every good is demanded by two distinct agents. -/
def PerfectCompetition (I : Instance n m) : Prop :=
  ∀ j, ∃ i k, i ≠ k ∧ 0 < I.v i j ∧ 0 < I.v k j

/-- Leontief utility `u_i(y) = min_{j ∈ D_i} y_j / v_{i,j}` (p. 6). The `else` branch is
never reached under `Standing`. -/
noncomputable def u (I : Instance n m) (i : Fin n) (y : Fin m → ℝ) : ℝ :=
  if hD : (D I i).Nonempty then (D I i).inf' hD (fun j => y j / I.v i j) else 0

/-- Feasible allocations `F = {x | x_{i,j} ≥ 0, Σ_i x_{i,j} = 1}` (p. 6). -/
def Feasible (I : Instance n m) (x : Fin n → Fin m → ℝ) : Prop :=
  (∀ i j, 0 ≤ x i j) ∧ ∀ j, ∑ i, x i j = 1

/-- Total budget `B = Σ_i B_i` (p. 6). -/
def totalBudget (I : Instance n m) : ℝ := ∑ i, I.B i

/-- Nash social welfare `NSW(x) = (Π_i u_i(x_i)^{B_i})^{1/B}` (p. 6). -/
noncomputable def NSW (I : Instance n m) (x : Fin n → Fin m → ℝ) : ℝ :=
  (∏ i, (u I i (x i)) ^ (I.B i)) ^ (1 / totalBudget I)

/-- Trading Post strategy set `S_i = {b_i ∈ [0, B_i]^m | Σ_j b_{i,j} = B_i}` (p. 12). -/
def Strategy (I : Instance n m) (i : Fin n) (bi : Fin m → ℝ) : Prop :=
  (∀ j, 0 ≤ bi j ∧ bi j ≤ I.B i) ∧ ∑ j, bi j = I.B i

/-- Effective bid with entrance fee `Δ`: `b̄_{i,j} = b_{i,j}` if `b_{i,j} ≥ Δ`, else `0` (p. 14). -/
noncomputable def effBid (Δ : ℝ) (b : Fin n → Fin m → ℝ) (i : Fin n) (j : Fin m) : ℝ :=
  if Δ ≤ b i j then b i j else 0

/-- Allocation of `TP(Δ)`: `x_{i,j} = b̄_{i,j} / Σ_k b̄_{k,j}` if `b̄_{i,j} > 0`, else `0` (p. 14). -/
noncomputable def tpAlloc (Δ : ℝ) (b : Fin n → Fin m → ℝ) (i : Fin n) (j : Fin m) : ℝ :=
  if 0 < effBid Δ b i j then effBid Δ b i j / ∑ k, effBid Δ b k j else 0

/-- Pure Nash equilibrium of `TP(Δ)`: every agent plays a strategy in `S_i`, and no unilateral
deviation to another strategy in `S_i` raises its Leontief utility. -/
def IsPNE (I : Instance n m) (Δ : ℝ) (b : Fin n → Fin m → ℝ) : Prop :=
  (∀ i, Strategy I i (b i)) ∧
    ∀ i (b' : Fin m → ℝ), Strategy I i b' →
      u I i (tpAlloc Δ (Function.update b i b') i) ≤ u I i (tpAlloc Δ b i)

/-- Prices read off the bids, `p_j = Σ_i b_{i,j}` (proof of Theorem 4.7, p. 15). -/
def bidPrice (b : Fin n → Fin m → ℝ) (j : Fin m) : ℝ := ∑ i, b i j

/-- `φ_i(p) = Σ_j v_{i,j} p_j`, the money agent `i` needs for unit utility at prices `p` (p. 22). -/
def phi (I : Instance n m) (i : Fin n) (p : Fin m → ℝ) : ℝ := ∑ j, I.v i j * p j

/-- `ε`-market equilibrium (Definition 4.6, p. 15), with bundles `y ≥ 0` in clause (iii). -/
structure IsEpsME (I : Instance n m) (ε : ℝ) (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ) : Prop where
  p_nonneg : ∀ j, 0 ≤ p j
  x_nonneg : ∀ i j, 0 ≤ x i j
  supply : ∀ j, ∑ i, x i j ≤ 1
  sold : ∀ j, 0 < p j → ∑ i, x i j = 1
  budget : ∀ i, ∑ j, x i j * p j = I.B i
  eps_opt : ∀ i (y : Fin m → ℝ), (∀ j, 0 ≤ y j) → ∑ j, p j * y j ≤ I.B i →
    u I i y ≤ u I i (x i) * (1 + ε)

/-- The fraction `φ_{i,j} = x_{i,j} / v_{i,j}` of good `j` that agent `i` receives, relative to
its need (proof of Theorem 4.7, p. 15). -/
noncomputable def frac (I : Instance n m) (Δ : ℝ) (b : Fin n → Fin m → ℝ) (i : Fin n)
    (j : Fin m) : ℝ :=
  tpAlloc Δ b i j / I.v i j

/-- The tight set `S_i = {j ∈ D_i | φ_{i,j} = u_i}` (proof of Theorem 4.7, p. 15). -/
noncomputable def tight (I : Instance n m) (Δ : ℝ) (b : Fin n → Fin m → ℝ) (i : Fin n) :
    Finset (Fin m) :=
  (D I i).filter (fun j => frac I Δ b i j = u I i (tpAlloc Δ b i))

end TradingPostNSW.Leontief


