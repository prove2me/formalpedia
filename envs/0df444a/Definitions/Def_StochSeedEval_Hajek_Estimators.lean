-- Prove2me | Definitions.Def_StochSeedEval_Hajek_Estimators
-- name    : StochSeedEval_Hajek_Estimators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:34.449366+00:00
-- url     : https://prove2.me/theorems/c09c00c3-8edc-4638-ab2a-2da817db1744
-- title:
--   Equations (2), (5), (7), (15) — weights, Hájek estimator, superpopulation contrast, and variance
-- statement:
--   Let $\Omega$ be a countable space of seed sets. Strategies $A$ and $B$ and the experimental design have probability mass functions $p_A$, $p_B$, and $p_\Delta$. The potential outcome is $y:\Omega\to\mathbb R$. For each seed set $s$, define the importance weights
--
--   $$w_A(s)=\frac{p_A(s)}{p_\Delta(s)},\qquad w_B(s)=\frac{p_B(s)}{p_\Delta(s)}.$$
--
--   The strategy means and their contrast are $\mu_A=\mathbb E_A[y(S)]$, $\mu_B=\mathbb E_B[y(S)]$, and $\tau_{\mathrm{sp}}=\mu_A-\mu_B$. For the first $N$ observed seed sets $S_0,\ldots,S_{N-1}$, let $\bar w_{A,N}$ and $\bar w_{B,N}$ be their sample average weights. Equation (7) defines
--
--   $$\widetilde\tau_N=\frac1N\sum_{i<N}\left(\frac{w_A(S_i)}{\bar w_{A,N}}-\frac{w_B(S_i)}{\bar w_{B,N}}\right)y(S_i).$$
--
--   Equation (15) defines the asymptotic variance
--
--   $$V_{\widetilde\tau}=\mathbb E_\Delta\left[\left(\frac{\mu_Ap_A(S)-\mu_Bp_B(S)-y(S)(p_A(S)-p_B(S))}{p_\Delta(S)}\right)^2\right].$$
--
--   The module also defines the four coordinate linear statistic and its centered influence function for the central limit theorem and variance milestone. These definitions keep the estimator and variance fixed across the mission.
--
--   **Formalization Note.** PMF values are converted from extended nonnegative reals to reals. Division by zero is Lean's total division: a missing design point has weight zero; at $N=0$ the estimator is zero; a zero finite sample weight sum produces a zero ratio term. The limiting theorem is stated under support and moment conditions that make these conventions harmless asymptotically.
-- source:
--   Chin, Eckles & Ugander, Evaluating Stochastic Seeding Strategies in Networks, arXiv:1809.09561v3, pp. 9–10, 14, equations (2), (5), (7), (15); p. 40, proof of Proposition 2

import Mathlib

open MeasureTheory
noncomputable section

namespace StochSeedEval.Hajek

/-- The importance weight for strategy A, equation (5). -/
def weightA {Ω : Type*} (pA pD : PMF Ω) (s : Ω) : ℝ :=
  (pA s).toReal / (pD s).toReal

/-- The importance weight for strategy B, equation (5). -/
def weightB {Ω : Type*} (pB pD : PMF Ω) (s : Ω) : ℝ :=
  (pB s).toReal / (pD s).toReal

/-- The mean outcome under strategy A. -/
def meanA {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (pA : PMF Ω) (y : Ω → ℝ) : ℝ := ∫ s, y s ∂pA.toMeasure

/-- The mean outcome under strategy B. -/
def meanB {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (pB : PMF Ω) (y : Ω → ℝ) : ℝ := ∫ s, y s ∂pB.toMeasure

/-- The superpopulation contrast, equation (2). -/
def contrast {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (pA pB : PMF Ω) (y : Ω → ℝ) : ℝ := meanA pA y - meanB pB y

/-- The average of a statistic over the first `N` sampled seed sets. -/
def sampleAverage {Ω Ω' : Type*} (S : ℕ → Ω' → Ω) (g : Ω → ℝ)
    (N : ℕ) (ω : Ω') : ℝ :=
  (1 / (N : ℝ)) * ∑ i ∈ Finset.range N, g (S i ω)

/-- Equation (7): the difference of two averages with normalized importance weights. -/
def hajek {Ω Ω' : Type*} (pA pB pD : PMF Ω) (y : Ω → ℝ)
    (S : ℕ → Ω' → Ω) (N : ℕ) (ω : Ω') : ℝ :=
  (1 / (N : ℝ)) *
    ∑ i ∈ Finset.range N,
      ((weightA pA pD (S i ω) / sampleAverage S (weightA pA pD) N ω) -
        (weightB pB pD (S i ω) / sampleAverage S (weightB pB pD) N ω)) * y (S i ω)

/-- The variance in equation (15). -/
def asymptoticVariance {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (pA pB pD : PMF Ω) (y : Ω → ℝ) : ℝ :=
  ∫ s, ((meanA pA y * (pA s).toReal - meanB pB y * (pB s).toReal -
    y s * ((pA s).toReal - (pB s).toReal)) / (pD s).toReal) ^ 2 ∂pD.toMeasure

/-- A linear combination of the four coordinates used in the joint central limit theorem. -/
def linearStatistic {Ω : Type*} (pA pB pD : PMF Ω) (y : Ω → ℝ)
    (c : Fin 4 → ℝ) (s : Ω) : ℝ :=
  c 0 * weightA pA pD s + c 1 * weightB pB pD s +
    c 2 * weightA pA pD s * y s + c 3 * weightB pB pD s * y s

/-- The centered influence function whose variance is equation (15). -/
def influence {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (pA pB pD : PMF Ω) (y : Ω → ℝ) (s : Ω) : ℝ :=
  weightA pA pD s * (y s - meanA pA y) -
    weightB pB pD s * (y s - meanB pB y)

end StochSeedEval.Hajek


