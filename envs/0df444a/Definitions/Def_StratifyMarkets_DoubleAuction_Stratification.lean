-- Prove2me | Definitions.Def_StratifyMarkets_DoubleAuction_Stratification
-- name    : StratifyMarkets_DoubleAuction_Stratification
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:53:30.296858+00:00
-- url     : https://prove2.me/theorems/6e91a03d-2be8-4cd4-b73c-65383adff00e
-- title:
--   Market stratifications and their bilateral gains Strat (Definition 2.3); ordered fully tradable matchings and OrderedMatching (Definition 2.6)
-- statement:
--   A **(market) stratification** (Definition 2.3) consists of $N\ge1$ submarket boundaries and prices
--   $$0\le m_0<m_1<\dots<m_N\le1,\qquad m_{k-1}\le p_k\le m_k\quad(k=1,\dots,N).$$
--   Submarket $k$ is the closed interval $[m_{k-1},m_k]$ with fixed price $p_k$. In bilateral trade, a buyer with value $v$ and a seller with cost $c$ trade iff some $k$ has $m_{k-1}\le c\le p_k$ and $p_k\le v\le m_k$, and the gains from trade of the stratification are
--   $$\mathrm{Strat}=\sum_{k=1}^N\mathbb E_{v,c}\Big[(v-c)\cdot\mathbb 1\{m_{k-1}\le c\le p_k\text{ and }p_k\le v\le m_k\}\Big].$$
--
--   An **ordered fully tradable matching** (Definition 2.6) consists of buyer boundaries $0\le m^B_0\le\dots\le m^B_N\le1$ and seller boundaries $0\le m^S_0\le\dots\le m^S_N\le1$ ($N\ge0$); the $k$-th seller interval $[m^S_{k-1},m^S_k]$ is matched with the $k$-th buyer interval $[m^B_{k-1},m^B_k]$, and full tradability requires $m^S_k\le m^B_{k-1}$ for $k=1,\dots,N$. Its gains from trade are
--   $$\mathrm{OrderedMatching}=\sum_{k=1}^N\mathbb E_{v,c}\Big[(v-c)\cdot\mathbb 1\{m^S_{k-1}\le c\le m^S_k\text{ and }m^B_{k-1}\le v\le m^B_k\}\Big].$$
--
--   The stratification structure is shared with the double auction (`DAInstance.strat`), where the worst-rationed rule runs in each submarket.
--
--   **Formalization Note.** Indices are 0-based: `Stratification` has `m : Fin (N+1) → ℝ` strictly monotone with `0 ≤ m 0`, `m (Fin.last N) ≤ 1`, and `p : Fin N → ℝ` with `m k.castSucc ≤ p k ≤ m k.succ`; submarket `k : Fin N` is the paper's submarket $k+1$. `OrderedMatching` has monotone `mB mS : Fin (N+1) → ℝ` in $[0,1]$ and `tradable : mS k.succ ≤ mB k.castSucc`. Expectations are integrals over `I.law = μS.prod μB` of `if … then x.2 − x.1 else 0`, with `x = (c, v)`; the integrands are bounded and measurable, so integrable. Submarkets are closed (weak inequalities, Remark 2.4).
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), pp. 9–11, Definition 2.3, Remark 2.4, Definition 2.6

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Bilateral

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- A (market) stratification (Definition 2.3, p. 9): `N ≥ 1` submarkets with boundaries
`0 ≤ m₀ < m₁ < ⋯ < m_N ≤ 1` and fixed prices `p₁, …, p_N` with `m_{k−1} ≤ p_k ≤ m_k`.
Indices are 0-based: submarket `k : Fin N` is `[m k.castSucc, m k.succ]` with price `p k`
(the paper's submarket `k + 1`). -/
structure Stratification where
  /-- the number of submarkets -/
  N : ℕ
  one_le_N : 1 ≤ N
  /-- the boundaries `m₀, …, m_N` -/
  m : Fin (N + 1) → ℝ
  /-- the prices `p₁, …, p_N` (0-based) -/
  p : Fin N → ℝ
  zero_le_m : 0 ≤ m 0
  m_le_one : m (Fin.last N) ≤ 1
  m_strictMono : StrictMono m
  p_mem : ∀ k : Fin N, m k.castSucc ≤ p k ∧ p k ≤ m k.succ

/-- Bilateral gains from trade of a stratification (Definition 2.3 and the display below Remark 2.4,
p. 9): `Strat = Σ_k E_{v,c}[(v − c) · 1{m_{k−1} ≤ c ≤ p_k and p_k ≤ v ≤ m_k}]`, with closed
submarkets (weak inequalities, Remark 2.4). A point `x` of `BTInstance.law` is `x = (c, v)`. -/
noncomputable def BTInstance.strat (I : BTInstance) (σ : Stratification) : ℝ :=
  ∑ k : Fin σ.N, ∫ x : ℝ × ℝ,
    (if σ.m k.castSucc ≤ x.1 ∧ x.1 ≤ σ.p k ∧ σ.p k ≤ x.2 ∧ x.2 ≤ σ.m k.succ then x.2 - x.1 else 0)
      ∂I.law

/-- An ordered fully tradable matching (Definition 2.6, p. 11): buyer boundaries
`0 ≤ m^B_0 ≤ ⋯ ≤ m^B_N ≤ 1`, seller boundaries `0 ≤ m^S_0 ≤ ⋯ ≤ m^S_N ≤ 1`, the `k`-th seller
interval `[m^S_{k−1}, m^S_k]` matched with the `k`-th buyer interval `[m^B_{k−1}, m^B_k]`, and full
tradability `m^S_k ≤ m^B_{k−1}` for `k = 1, …, N`. Indices are 0-based: pair `k : Fin N` is
seller interval `[mS k.castSucc, mS k.succ]` with buyer interval `[mB k.castSucc, mB k.succ]`. -/
structure OrderedMatching where
  /-- the number of matched pairs -/
  N : ℕ
  /-- buyer boundaries `m^B_0, …, m^B_N` -/
  mB : Fin (N + 1) → ℝ
  /-- seller boundaries `m^S_0, …, m^S_N` -/
  mS : Fin (N + 1) → ℝ
  zero_le_mB : 0 ≤ mB 0
  mB_le_one : mB (Fin.last N) ≤ 1
  mB_mono : Monotone mB
  zero_le_mS : 0 ≤ mS 0
  mS_le_one : mS (Fin.last N) ≤ 1
  mS_mono : Monotone mS
  tradable : ∀ k : Fin N, mS k.succ ≤ mB k.castSucc

/-- `OrderedMatching = Σ_k E_{v,c}[(v − c) · 1{m^S_{k−1} ≤ c ≤ m^S_k and m^B_{k−1} ≤ v ≤ m^B_k}]`
(p. 11), the gains from trade of an ordered fully tradable matching. -/
noncomputable def BTInstance.orderedMatching (I : BTInstance) (M : OrderedMatching) : ℝ :=
  ∑ k : Fin M.N, ∫ x : ℝ × ℝ,
    (if M.mS k.castSucc ≤ x.1 ∧ x.1 ≤ M.mS k.succ ∧ M.mB k.castSucc ≤ x.2 ∧ x.2 ≤ M.mB k.succ
      then x.2 - x.1 else 0) ∂I.law

end StratifyMarkets.DoubleAuction


