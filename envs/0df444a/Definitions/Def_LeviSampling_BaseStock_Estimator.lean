-- Prove2me | Definitions.Def_LeviSampling_BaseStock_Estimator
-- name    : LeviSampling_BaseStock_Estimator
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:48:24.712167+00:00
-- url     : https://prove2.me/theorems/e573804f-2d21-4243-bc16-314247ab506c
-- title:
--   Right-derivative path variables and the sample estimator of the shadow cost (pp. 829, 833–834)
-- statement:
--   The objects of Lemma 3.4, Corollary 3.1 and the estimator of p. 834. Periods are $0$-based. A sample path is $d = (d_k)_{k}$, a base-stock policy is a vector of levels $L$.
--
--   1. $D_{[t,j)} = \sum_{k=t}^{j-1} d_k$, the cumulative demand of periods $t, \dots, j-1$.
--   2. The event $\tilde A_{jt}(y)$: for every $k$ with $t < k \le j$, $y - D_{[t,k)} \ge L_k$ (weak inequality: the right-derivative version).
--   3. $C^r(y) = -b + (b + h)\Pr(D \le y)$, the right derivative of the newsvendor cost (p. 824).
--   4. $\tilde M^r_{tj}(y) = \mathbb 1(\tilde A_{jt}(y))\big(-b_j + (h_j + b_j)\mathbb 1(d_j \le y - D_{[t,j)})\big)$.
--   5. The path value
--   $$\varphi_t(d, y) = -b_t + (h_t + b_t)\mathbb 1(d_t \le y) + \sum_{j=t+1}^{T-1} \tilde M^r_{tj}(y).$$
--   6. The law of one sample path $(D_0, \dots, D_{T-1})$: the product of $\mu_0, \dots, \mu_{T-1}$ (independent coordinates).
--   7. The **sample right-derivative estimator** from $N$ sample paths $d^1, \dots, d^N$:
--   $$\hat U^r_t(y) = \frac1N \sum_{i=1}^N \varphi_t(d^i, y).$$
--
--   **Formalization Note** Sample paths are vectors indexed by $\mathrm{Fin}\,T$ and are read as sequences on $\mathbb N$ with value $0$ beyond the horizon; those coordinates are never used. The estimator is defined with per-period costs; the algorithm uses constant ones.
-- source:
--   Levi, Roundy & Shmoys, Provably Near-Optimal Sampling-Based Policies for Stochastic Inventory Control Models, Math. Oper. Res. 32(4) 2007, p. 824 (C^r), p. 829 (D_[t,j), A_jt), p. 834 (Lemma 3.4, Corollary 3.1, the estimator)

import Mathlib

open MeasureTheory

namespace LeviSampling.BaseStock

/-! The right-derivative variables of the shadow cost and their sample estimator,
Levi, Roundy & Shmoys (2007), §3.2, pp. 829 and 833–834. Periods are 0-based (period `i` is the
paper's period `i + 1`). A demand sample path is `d : ℕ → ℝ` (`d k` is the realized demand of
period `k`); a base-stock policy is a vector of levels `L : ℕ → ℝ`. -/

/-- The cumulative demand `D_{[t,j)} = Σ_{k=t}^{j-1} D_k` of periods `t, …, j-1` (p. 829). -/
def cumDemand (d : ℕ → ℝ) (t j : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico t j, d k

/-- The event `Ã_{jt}(y)` of the right-hand derivative (pp. 829, 834), for levels `L`: for every
`k` with `t < k ≤ j`, `y - D_{[t,k)} ≥ L_k` (weak inequality), i.e. after ordering up to `y` in
period `t`, the policy `L` places no order in periods `t+1, …, j`. -/
def reachEvent (L : ℕ → ℝ) (d : ℕ → ℝ) (t j : ℕ) (y : ℝ) : Prop :=
  ∀ k ∈ Finset.Ioc t j, L k ≤ y - cumDemand d t k

/-- The right-hand derivative of the newsvendor cost of a period with demand law `μ`, holding cost
`h` and backlogging cost `b` (p. 824): `C^r(y) = -b + (b + h) Pr(D ≤ y)`. -/
noncomputable def nvRightDeriv (μ : Measure ℝ) (h b y : ℝ) : ℝ :=
  -b + (b + h) * ProbabilityTheory.cdf μ y

open Classical in
/-- The variable `M̃^r_{tj}(y) = 𝟙(Ã_{jt}(y)) · (-b_j + (h_j + b_j) 𝟙(D_j ≤ y - D_{[t,j)}))` of
Lemma 3.4 (p. 834), evaluated on the sample path `d`. -/
noncomputable def pathTerm (h b : ℕ → ℝ) (L : ℕ → ℝ) (d : ℕ → ℝ) (t j : ℕ) (y : ℝ) : ℝ :=
  if reachEvent L d t j y then
    -b j + (h j + b j) * (if d j ≤ y - cumDemand d t j then 1 else 0)
  else 0

/-- The path value whose expectation is the right-hand derivative of `Ũ_t` (Corollary 3.1,
p. 834), on the sample path `d`:
`-b_t + (h_t + b_t) 𝟙(d_t ≤ y) + Σ_{j=t+1}^{T-1} M̃^r_{tj}(y)` (0-based periods). -/
noncomputable def pathRightDeriv (T : ℕ) (h b : ℕ → ℝ) (L : ℕ → ℝ) (d : ℕ → ℝ) (t : ℕ)
    (y : ℝ) : ℝ :=
  -b t + (h t + b t) * (if d t ≤ y then 1 else 0) +
    ∑ j ∈ Finset.Ioo t T, pathTerm h b L d t j y

/-- A sample path over the horizon, `p : Fin T → ℝ`, read as a path `ℕ → ℝ`
(periods `≥ T` are never read by the objects above when `t, j < T`; they are set to `0`). -/
def extendPath {T : ℕ} (p : Fin T → ℝ) (k : ℕ) : ℝ :=
  if hk : k < T then p ⟨k, hk⟩ else 0

/-- The law of one demand sample path `(D_0, …, D_{T-1})`: independent coordinates with laws
`μ 0, …, μ (T-1)`. -/
noncomputable def pathLaw (T : ℕ) (μ : ℕ → Measure ℝ) : Measure (Fin T → ℝ) :=
  Measure.pi fun k : Fin T => μ k

/-- The sampling-based estimator `Û^r_t(y) = (1/N) Σ_{i=1}^{N} φ_t(d^i, y)` of the right-hand
derivative of `Ũ_t` (p. 834), from `N` sample paths `paths i : Fin T → ℝ`, where `φ_t` is
`pathRightDeriv`. -/
noncomputable def sampleRightDeriv (T : ℕ) (h b : ℕ → ℝ) (L : ℕ → ℝ) (t : ℕ) {N : ℕ}
    (paths : Fin N → Fin T → ℝ) (y : ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, pathRightDeriv T h b L (extendPath (paths i)) t y

end LeviSampling.BaseStock


