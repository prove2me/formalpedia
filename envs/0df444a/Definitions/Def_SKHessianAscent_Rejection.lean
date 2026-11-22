-- Prove2me | Definitions.Def_SKHessianAscent_Rejection
-- name    : SKHessianAscent_Rejection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-22T20:00:16.477167+00:00
-- url     : https://prove2.me/theorems/127fcdf2-39b0-4902-9a3d-89fe467d61d2
-- title:
--   Algorithm 4 — approximate rejection sampler with unknown normalization: output law, acceptance probability, and the cutoff $C(\varepsilon)$
-- statement:
--   Algorithm 4 has input an oracle for sampling from $\widetilde Q\approx Q$, a (possibly randomized) function $\widetilde R\approx R$ where $\frac{dP}{dQ}\propto R$, cutoff parameters $C_1,C_2$ and a failure probability $\delta'$. It draws $N$ samples from $\widetilde Q$, lets $R_0$ be the $p$-th quantile of the samples with $p=1-\frac1{6C_1}$, and then repeats: draw $X\sim\widetilde Q$ and $U\sim\mathrm{Uniform}([0,1])$, until $U\le\frac{\widetilde R(X)}{C_3R_0}$, where $C_3=8C_2$; it outputs $X$.
--
--   - `tvMeas μ ν` is $\mathrm{TV}(\mu,\nu)=\sup_B|\mu(B)-\nu(B)|$.
--   - `ratioCutoff P Q ε` is $C(\varepsilon)=\inf\{C:\mathbf E_Q(\frac{dP}{dQ}\wedge C)\ge1-\varepsilon\}$.
--   - `empQuantile p v` is the empirical $p$-quantile of $v_1,\dots,v_N$: the least $a$ such that at least $pN$ of the values are $\le a$.
--   - `acceptProb Qt ν Rt s` is the probability $\mathbf P[U\le\widetilde R(X,\theta)/s]=\mathbf E\min(1,\widetilde R(X,\theta)/s)$ that one round accepts, for threshold scale $s=C_3R_0$.
--   - `rejOut Qt ν Rt s` is the output law of the loop: the law of $X$ conditioned on acceptance.
--
--   **Formalization Note** A randomized $\widetilde R$ is a function $\widetilde R(x,\theta)$ of the point and of independent randomness $\theta\sim\nu$. The paper does not say which quantile of which values; it is the empirical quantile of the values $\widetilde R(X_i,\theta_i)$ on the $N$ samples.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, Appendix C, Algorithm 4 and Lemma C.1 (2), pp. 49–50 (identical to [DLSS26a, Algorithm 4], https://arxiv.org/abs/2605.03718, p. 26)

import Mathlib

open MeasureTheory
open scoped ENNReal BigOperators

namespace SKHessianAscent

/-!
# Algorithm 4: approximate rejection sampling with unknown normalization

H. Lee, J. S. Sandhu, J. Shi, *Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick
model at β < 1*, Appendix C, Algorithm 4 (p. 49), identical to [DLSS26a, Algorithm 4]
(arXiv:2605.03718, p. 26):

1. Input: oracle for sampling from `Q̃ ≈ Q`, (possibly randomized) function `R̃ ≈ R` where
   `dP/dQ ∝ R`, cutoff parameters `C₁`, `C₂`, failure probability `δ'`.
2. Draw `N` samples from `Q̃`, where `N = Ω(C₁² log(1/δ'))`.
3. Let `R₀` be the `p`-th quantile of the samples, where `p = 1 − 1/(6C₁)`.
4. Repeat: draw `X ∼ Q̃`, draw `U ∼ Uniform([0,1])`, until `U ≤ R̃(X)/(C₃R₀)`, where `C₃ = 8C₂`.
5. Output `X`.

**Formalization Note.** A randomized `R̃` is a function `R̃(x, θ)` of the point and of independent
randomness `θ ∼ ν`. "The `p`-th quantile of the samples" is the empirical `p`-quantile of the values
`R̃(X_i, θ_i)` (the smallest `a` with at least `pN` values `≤ a`). One round accepts with
conditional probability `min(1, R̃(X, θ)/s)`, `s = C₃R₀`; the output law of the loop is the law of
`X` conditioned on acceptance, and the acceptance probability is that of one round.
-/

noncomputable section

/-- Total variation `sup_B |μ(B) − ν(B)|` between finite measures. -/
def tvMeas {X : Type*} [MeasurableSpace X] (μ ν : Measure X) : ℝ :=
  ⨆ B : {B : Set X // MeasurableSet B}, |(μ B.1).toReal - (ν B.1).toReal|

/-- `C(ε) = inf{C : E_Q(dP/dQ ∧ C) ≥ 1 − ε}` (Lemma C.1 (2)). -/
def ratioCutoff {X : Type*} [MeasurableSpace X] (P Q : Measure X) (ε : ℝ) : ℝ :=
  sInf {C : ℝ | 1 - ε ≤ ∫ x, min (P.rnDeriv Q x).toReal C ∂Q}

/-- The empirical `p`-quantile of `v_1, …, v_N`: the least `a` with at least `pN` values `≤ a`. -/
def empQuantile {N : ℕ} (p : ℝ) (v : Fin N → ℝ) : ℝ :=
  sInf {a : ℝ | p * N ≤ ((Finset.univ.filter fun i => v i ≤ a).card : ℝ)}

/-- The acceptance probability of one round of the loop of Algorithm 4 with threshold scale
`s = C₃R₀`: `P[U ≤ R̃(X, θ)/s]` for `X ∼ Q̃`, `θ ∼ ν`, `U` uniform. -/
def acceptProb {X Θ : Type*} [MeasurableSpace X] [MeasurableSpace Θ] (Qt : Measure X)
    (ν : Measure Θ) (Rt : X → Θ → ℝ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (min 1 (Rt z.1 z.2 / s)) ∂(Qt.prod ν)

/-- The output law of Algorithm 4 for threshold scale `s`: the law of `X` given acceptance. -/
def rejOut {X Θ : Type*} [MeasurableSpace X] [MeasurableSpace Θ] (Qt : Measure X)
    (ν : Measure Θ) (Rt : X → Θ → ℝ) (s : ℝ) : Measure X :=
  (acceptProb Qt ν Rt s)⁻¹ •
    ((Qt.prod ν).withDensity fun z => ENNReal.ofReal (min 1 (Rt z.1 z.2 / s))).map Prod.fst

end

end SKHessianAscent


