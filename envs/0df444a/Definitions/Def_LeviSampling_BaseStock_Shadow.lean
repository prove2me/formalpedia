-- Prove2me | Definitions.Def_LeviSampling_BaseStock_Shadow
-- name    : LeviSampling_BaseStock_Shadow
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:14.202982+00:00
-- url     : https://prove2.me/theorems/3eac6a3c-4458-4af7-9e1c-d9a07089079e
-- title:
--   Shadow dynamic program of a base-stock policy and upper base-stock policies (Definition 3.2, pp. 830–831)
-- statement:
--   The **shadow dynamic program** of §3.2. Periods are $0$-based as in the model file. A **base-stock policy** is a vector of levels $L = (L_k)$; in period $k$ it raises the inventory $x$ to $\max(x, L_k)$.
--
--   1. $\tilde G_k(x)$ is the expected cost over periods $k, \dots, T-1$ of the base-stock policy $L_k, \dots, L_{T-1}$ started with inventory $x$:
--   $$\tilde G_k(x) = C_k(\max(x, L_k)) + \mathbb E\big[\tilde G_{k+1}(\max(x, L_k) - D_k)\big], \qquad \tilde G_k \equiv 0 \text{ for } k \ge T.$$
--   2. $\tilde U_t(y) = C_t(y) + \mathbb E[\tilde G_{t+1}(y - D_t)]$ is the expected cost over periods $t, \dots, T-1$ of ordering up to $y$ in period $t$ and following $L_{t+1}, \dots, L_{T-1}$ afterwards (pp. 830–831).
--   3. $\tilde V_t(x) = \min_{y \ge x} \tilde U_t(y)$.
--   4. **$\bar R_j$ exists and equals $r$**: $\tilde U_j$ is convex and $r$ is its smallest minimizer (p. 831: an optimal ordering policy in period $j$ is a base-stock policy).
--   5. **Definition 3.2** (p. 831): $L_s, \dots, L_{T-1}$ is an **upper base-stock policy** if for every period $j$ with $s \le j < T$, $\bar R_j$ exists and $L_j \ge \bar R_j$.
--
--   **Formalization Note** The paper's interval $[s+1, T]$ is the $0$-based range $s, \dots, T-1$. "$\bar R_j$ exists" is rendered as "$\tilde U_j$ is convex and has a smallest minimizer"; the paper equates the existence of an optimal base-stock decision in period $j$ with the convexity of $\tilde U_j$, and defines $\bar R_j$ as its smallest minimizer. $\tilde U_t$ does not depend on the levels $L_k$ with $k \le t$.
-- source:
--   Levi, Roundy & Shmoys, Provably Near-Optimal Sampling-Based Policies for Stochastic Inventory Control Models, Math. Oper. Res. 32(4) 2007, pp. 830–831, §3.2, Definition 3.2 and the proof of Lemma 3.1

import Mathlib
import Definitions.Def_LeviSampling_BaseStock_Model

open MeasureTheory

namespace LeviSampling.BaseStock

/-! The shadow dynamic program of a base-stock policy, Levi, Roundy & Shmoys (2007), §3.2,
pp. 830–831. Periods are 0-based (period `i` is the paper's period `i + 1`). A base-stock policy
is a vector of levels `L : ℕ → ℝ`; in period `k` it raises the inventory `x` to `max x (L k)`. -/

/-- `G̃_k(x)` (proof of Lemma 3.1, p. 831): the expected cost over periods `k, …, T-1` of the
base-stock policy `L_k, …, L_{T-1}` when period `k` starts with inventory `x`:
`G̃_k(x) = C_k(max(x, L_k)) + E[G̃_{k+1}(max(x, L_k) - D_k)]`, and `G̃_k ≡ 0` for `k ≥ T`. -/
noncomputable def bsCost (T : ℕ) (μ : ℕ → Measure ℝ) (h b : ℕ → ℝ) (L : ℕ → ℝ) (k : ℕ)
    (x : ℝ) : ℝ :=
  if _hk : k < T then
    nvCost (μ k) (h k) (b k) (max x (L k)) +
      ∫ d, bsCost T μ h b L (k + 1) (max x (L k) - d) ∂(μ k)
  else 0
termination_by T - k

/-- `Ũ_t(y) = C_t(y) + E[G̃_{t+1}(y - D_t)]` (p. 831): the expected cost over periods
`t, …, T-1` of the policy that orders up to `y` in period `t` and then follows the base-stock
policy `L_{t+1}, …, L_{T-1}` (p. 830). It does not depend on `L_k` for `k ≤ t`. -/
noncomputable def shadowU (T : ℕ) (μ : ℕ → Measure ℝ) (h b : ℕ → ℝ) (L : ℕ → ℝ) (t : ℕ)
    (y : ℝ) : ℝ :=
  nvCost (μ t) (h t) (b t) y + ∫ d, bsCost T μ h b L (t + 1) (y - d) ∂(μ t)

/-- `Ṽ_t(x) = min_{y ≥ x} Ũ_t(y)` (p. 830): the minimum expected cost over periods `t, …, T-1`
starting period `t` with inventory `x`, given that `L_{t+1}, …, L_{T-1}` is followed afterwards. -/
noncomputable def shadowV (T : ℕ) (μ : ℕ → Measure ℝ) (h b : ℕ → ℝ) (L : ℕ → ℝ) (t : ℕ)
    (x : ℝ) : ℝ :=
  minAbove (shadowU T μ h b L t) x

/-- "`R̄_j` exists and equals `r`" (p. 831): given that `L_{j+1}, …, L_{T-1}` is followed, there
is an optimal ordering policy in period `j` that is a base-stock policy, i.e. `Ũ_j` is convex,
and `r = R̄_j` is the smallest minimizer of `Ũ_j`. -/
def IsShadowLevel (T : ℕ) (μ : ℕ → Measure ℝ) (h b : ℕ → ℝ) (L : ℕ → ℝ) (j : ℕ) (r : ℝ) :
    Prop :=
  ConvexOn ℝ Set.univ (shadowU T μ h b L j) ∧ IsSmallestMinimizer (shadowU T μ h b L j) r

/-- **Definition 3.2** (p. 831). The base-stock policy `L_s, …, L_{T-1}` (0-based periods
`s, …, T-1`, the paper's interval `[s + 1, T]`) is an **upper base-stock policy** if for every
period `j` with `s ≤ j < T`, `R̄_j` exists and `L_j ≥ R̄_j`. -/
def IsUpperBaseStock (T : ℕ) (μ : ℕ → Measure ℝ) (h b : ℕ → ℝ) (L : ℕ → ℝ) (s : ℕ) : Prop :=
  ∀ j, s ≤ j → j < T → ∃ r, IsShadowLevel T μ h b L j r ∧ r ≤ L j

end LeviSampling.BaseStock


