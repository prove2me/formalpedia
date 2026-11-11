-- Prove2me | Definitions.Def_BetterKMedian_LMPGreedy_FRPrimalDual
-- name    : BetterKMedian_LMPGreedy_FRPrimalDual
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:19:13.224042+00:00
-- url     : https://prove2.me/theorems/d3e6bbd5-f166-4ee5-81dd-b5abdae1ccd0
-- title:
--   Definition B.2 and Definition 3.7 — the inner primal LPs and the factor-revealing dual
-- statement:
--   First bidding times: `ValidTau n τ` iff $j\le\tau_j\le n$ for $1\le j\le n$.
--
--   **Definition B.2** (inner primal LP for $\tau$, `PrimalFeasible n γ r d m βᵃ βᵇ f`): $\sum_{i=1}^nd_i\le1$; $m_i\le r_{j,i}+d_j$ ($1\le j<i\le n$); $r_{j,i}\le m_i+d_j$ ($1\le j\le i\le n$); $r_{j,i}\ge r_{j,i+1}$ ($1\le j\le i\le n$); $m_i\ge m_{i+1}$ ($1\le i<n$); $r_{j,i}-\gamma d_j\le\beta^a_{i,j}$ ($1\le j<i\le n$); $r_{i,i}-\gamma d_j\le\beta^b_{i,j}$ ($1\le i\le j\le n$); $\sum_{j<i}\beta^a_{i,j}+\sum_{j\ge i}\beta^b_{i,j}\le f$ ($1\le i\le n$); all variables $\ge0$ for $1\le i,j\le n+1$. Objective (`primalObjective`): $\sum_{j=1}^n(r_{j,\tau_j}-(\gamma-1)r_{j,\tau_j+1})-f$.
--
--   **Definition 3.7** (inner dual for $\tau$, `DualFeasible n γ τ ĝ g s t ρ`): (f) $\sum_i\hat g_i\le1$; ($\beta_{i,j}$) $\hat g_i\ge g_{i,j}$; ($\Delta r_{j,i}$) $\sum_{q=j+1}^ng_{j,q}+\sum_{p=j}^i(g_{p,j}+t_{p,j}-s_{p,j})\ge0,1,2-\gamma$ for $i<,=,>\tau_j$ ($1\le j\le i\le n$); ($\Delta m_i$) $\sum_{p\le i}\sum_{j\le p}s_{p,j}-\sum_{p\le i}\sum_{j\le p}t_{p,j}\ge0$; ($d_j$) $\rho\ge\gamma\sum_ig_{i,j}+\sum_{i\ge j}s_{i,j}+\sum_{i\ge j}t_{i,j}$; $\hat g,g,t,s\ge0$, $s_{i,i}=0$. The inner program minimizes $\rho$; Definition 3.7 is the maximum over $\tau$. Neither optimum is formed as a supremum or infimum: statements quantify over feasible points.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (2026), STOC 2027 submission, SHA-256 5c2605b2…f461, Definition B.2, printed p. 35 (PDF 37); Definition 3.7, printed p. 16 (PDF 18), restated p. 36 (PDF 38)

import Mathlib

set_option autoImplicit false

/-!
# The factor-revealing primal family (Definition B.2) and dual family (Definition 3.7)

Buhai et al., *A Better-than-2 Approximation for k-Median* (2026), STOC 2027 submission,
SHA-256 5c2605b2…f461, Definition B.2, printed p. 35 (PDF 37); Definition 3.7, printed p. 16
(PDF 18), restated printed p. 36 (PDF 38).

Both are a maximum, over all choices of first bidding times `τ_j ∈ {j, …, n}` (`1 ≤ j ≤ n`),
of an inner linear program. Here the inner programs are given by their feasibility predicates
and objectives; the outer maximum and the inner optimum are never formed as a supremum or
infimum (statements quantify over feasible points instead).

Conventions: the paper's 1-based indices; variables are functions on `ℕ` (or `ℕ × ℕ`), and
their values outside the index ranges occur in no constraint. `τ : ℕ → ℕ`, used for
`1 ≤ j ≤ n`.
-/

namespace BetterKMedian.LMPGreedy

open Finset

/-- First bidding times: `τ_j ∈ {j, …, n}` for every client `1 ≤ j ≤ n`. -/
def ValidTau (n : ℕ) (τ : ℕ → ℕ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ n → j ≤ τ j ∧ τ j ≤ n

/-- The inner primal LP of **Definition B.2** (p. 35) for first bidding times `τ`: constraints
on `r_{j,i}`, `d_j`, `m_i`, `β^a_{i,j}`, `β^b_{i,j}`, `f`:
* (ρ) `Σ_{i=1}^n d_i ≤ 1`;
* (s_{i,j}) `m_i ≤ r_{j,i} + d_j` for `1 ≤ j < i ≤ n`;
* (t_{i,j}) `r_{j,i} ≤ m_i + d_j` for `1 ≤ j ≤ i ≤ n`;
* (y_{i,j}) `r_{j,i} ≥ r_{j,i+1}` for `1 ≤ j ≤ i ≤ n`;
* (y'_i) `m_i ≥ m_{i+1}` for `1 ≤ i < n`;
* (g^a_{i,j}) `r_{j,i} − γ · d_j ≤ β^a_{i,j}` for `1 ≤ j < i ≤ n`;
* (g^b_{i,j}) `r_{i,i} − γ · d_j ≤ β^b_{i,j}` for `1 ≤ i ≤ j ≤ n`;
* (ĝ_i) `Σ_{j=1}^{i−1} β^a_{i,j} + Σ_{j=i}^n β^b_{i,j} ≤ f` for `1 ≤ i ≤ n`;
* `r_{j,i}, d_j, m_i, β^a_{i,j}, β^b_{i,j}, f ≥ 0` for `1 ≤ i, j ≤ n + 1`.
(`τ` enters only the objective.) -/
def PrimalFeasible (n : ℕ) (γ : ℝ) (r : ℕ → ℕ → ℝ) (d m : ℕ → ℝ) (ba bb : ℕ → ℕ → ℝ)
    (f : ℝ) : Prop :=
  (∑ i ∈ Icc 1 n, d i) ≤ 1 ∧
  (∀ j i : ℕ, 1 ≤ j → j < i → i ≤ n → m i ≤ r j i + d j) ∧
  (∀ j i : ℕ, 1 ≤ j → j ≤ i → i ≤ n → r j i ≤ m i + d j) ∧
  (∀ j i : ℕ, 1 ≤ j → j ≤ i → i ≤ n → r j (i + 1) ≤ r j i) ∧
  (∀ i : ℕ, 1 ≤ i → i < n → m (i + 1) ≤ m i) ∧
  (∀ j i : ℕ, 1 ≤ j → j < i → i ≤ n → r j i - γ * d j ≤ ba i j) ∧
  (∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ n → r i i - γ * d j ≤ bb i j) ∧
  (∀ i : ℕ, 1 ≤ i → i ≤ n →
      (∑ j ∈ Ico 1 i, ba i j) + (∑ j ∈ Icc i n, bb i j) ≤ f) ∧
  (∀ i j : ℕ, 1 ≤ i → i ≤ n + 1 → 1 ≤ j → j ≤ n + 1 →
      0 ≤ r j i ∧ 0 ≤ d j ∧ 0 ≤ m i ∧ 0 ≤ ba i j ∧ 0 ≤ bb i j) ∧
  0 ≤ f

/-- The objective of the inner primal LP of Definition B.2 for first bidding times `τ`:
`Σ_{j=1}^n (r_{j,τ_j} − (γ − 1) · r_{j,τ_j+1}) − f`. -/
noncomputable def primalObjective (n : ℕ) (γ : ℝ) (τ : ℕ → ℕ) (r : ℕ → ℕ → ℝ) (f : ℝ) : ℝ :=
  (∑ j ∈ Icc 1 n, (r j (τ j) - (γ - 1) * r j (τ j + 1))) - f

/-- The right-hand side of the constraint (Δr_{j,i}) of Definition 3.7:
`0` if `i < τ_j`, `1` if `i = τ_j`, `2 − γ` if `i > τ_j`. -/
noncomputable def dualRhs (γ : ℝ) (τ : ℕ → ℕ) (j i : ℕ) : ℝ :=
  if i < τ j then 0 else if i = τ j then 1 else 2 - γ

/-- The inner program of **Definition 3.7** (p. 16) for first bidding times `τ`: the point
`(ĝ, g, s, t)` with value `ρ` is feasible when
* (f) `Σ_{i=1}^n ĝ_i ≤ 1`;
* (β_{i,j}) `ĝ_i ≥ g_{i,j}` for `1 ≤ j, i ≤ n`;
* (Δr_{j,i}) `Σ_{q=j+1}^n g_{j,q} + Σ_{p=j}^i (g_{p,j} + t_{p,j} − s_{p,j}) ≥ dualRhs` for
  `1 ≤ j ≤ i ≤ n`;
* (Δm_i) `Σ_{p=1}^i Σ_{j=1}^p s_{p,j} − Σ_{p=1}^i Σ_{j=1}^p t_{p,j} ≥ 0` for `1 ≤ i ≤ n`;
* (d_j) `ρ ≥ γ · Σ_{i=1}^n g_{i,j} + Σ_{i=j}^n s_{i,j} + Σ_{i=j}^n t_{i,j}` for `1 ≤ j ≤ n`;
* `ĝ_i, g_{i,j}, t_{i,j}, s_{i,j} ≥ 0` and `s_{i,i} = 0` for `1 ≤ i, j ≤ n`.
The inner program minimizes `ρ`. -/
def DualFeasible (n : ℕ) (γ : ℝ) (τ : ℕ → ℕ) (ghat : ℕ → ℝ) (g s t : ℕ → ℕ → ℝ) (ρ : ℝ) :
    Prop :=
  (∑ i ∈ Icc 1 n, ghat i) ≤ 1 ∧
  (∀ j i : ℕ, 1 ≤ j → j ≤ n → 1 ≤ i → i ≤ n → g i j ≤ ghat i) ∧
  (∀ j i : ℕ, 1 ≤ j → j ≤ i → i ≤ n →
      dualRhs γ τ j i ≤
        (∑ q ∈ Icc (j + 1) n, g j q) + ∑ p ∈ Icc j i, (g p j + t p j - s p j)) ∧
  (∀ i : ℕ, 1 ≤ i → i ≤ n →
      0 ≤ (∑ p ∈ Icc 1 i, ∑ j ∈ Icc 1 p, s p j) - ∑ p ∈ Icc 1 i, ∑ j ∈ Icc 1 p, t p j) ∧
  (∀ j : ℕ, 1 ≤ j → j ≤ n →
      γ * (∑ i ∈ Icc 1 n, g i j) + (∑ i ∈ Icc j n, s i j) + (∑ i ∈ Icc j n, t i j) ≤ ρ) ∧
  (∀ i j : ℕ, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n →
      0 ≤ ghat i ∧ 0 ≤ g i j ∧ 0 ≤ t i j ∧ 0 ≤ s i j) ∧
  (∀ i : ℕ, 1 ≤ i → i ≤ n → s i i = 0)

end BetterKMedian.LMPGreedy


