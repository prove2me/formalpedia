-- Prove2me | Definitions.Def_OpenCategoryPAC_Basic
-- name    : OpenCategoryPAC_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T04:19:32.364316+00:00
-- url     : https://prove2.me/theorems/ec62d07b-fa73-487e-8563-6f78a99e5ba5
-- title:
--   Open category detection: score mixtures, the alien-CDF estimate and Algorithm 1
-- statement:
--   Objects of Sections 3–5 and Algorithm 1 of Liu, Garrepalli, Dietterich, Fern and Hendrycks (2018).
--
--   1. **Score laws.** A fixed anomaly detector assigns real scores. $\mu_0$ is the law of the score of a nominal point ($D_0$) and $\mu_a$ that of an alien point ($D_a$). For $\alpha\in(0,1]$, the mixture law is $\mu_m=(1-\alpha)\mu_0+\alpha\mu_a$ ($D_m$). The CDFs are $F_0,F_a,F_m$, with $F(t)=\mu((-\infty,t])$.
--   2. **Recovered alien CDF.** For functions $F_m,F_0$ and a weight $\alpha$, $\dfrac{F_m(t)-(1-\alpha)F_0(t)}{\alpha}$. With the true weight it equals $F_a$; with a weight $\alpha'$ it is the function $F'_a$ of Appendix B.
--   3. **Empirical CDFs and eq. (1).** For scores $x_1,\dots,x_n$, $\hat F(t)=\frac1n\#\{i:x_i\le t\}$. From the nominal scores $x$ (sample $S_0$) and the mixture scores $y$ (sample $S_m$), $\hat F_a(t)=\dfrac{\hat F_m(t)-(1-\alpha)\hat F_0(t)}{\alpha}$.
--   4. **Uniform distance.** $\sup_{t\in\mathbb R}|F(t)-G(t)|$.
--   5. **Algorithm 1.** With $S=\{x_1,\dots,x_n,y_1,\dots,y_n\}$, the returned threshold is $\hat\tau_q=\max\{u\in S:\hat F_a(u)\le q\}$.
--   6. **Alien detection rate** of a threshold $\tau$: the fraction $\mu_a((\tau,\infty))$ of aliens whose score exceeds $\tau$, i.e. that raise an alarm.
--   7. **Sample-size bound** of Theorem 1: $\frac12\ln\frac{2}{1-\sqrt{1-\delta}}\left(\frac1\epsilon\right)^2\left(\frac{2-\alpha}{\alpha}\right)^2$.
--   8. **Sampling law.** $S_0$ consists of $n$ i.i.d. draws from $\mu_0$ and, independently, $S_m$ of $n$ i.i.d. draws from $\mu_m$: the law $\mu_0^{\otimes n}\otimes\mu_m^{\otimes n}$ on $\mathbb R^n\times\mathbb R^n$.
--   9. **Admissibility** (Section 5): $F_0(t)\ge F_m(t)$ for all $t\in\mathbb R$.
--
--   **Formalization Note** The CDF is Mathlib's `cdf`. The supremum is a real supremum and is only applied to bounded functions (CDFs and their estimates). The independence of $S_0$ and $S_m$, used in Appendix A but not written in the paper, is built into the product sampling law.
-- source:
--   Liu, Garrepalli, Dietterich, Fern and Hendrycks, Open Category Detection with PAC Guarantees, arXiv:1808.00529v1 (ICML 2018), Sections 3-5 (pp. 3-4), eq. (1), Algorithm 1, Theorem 1, Appendices A-B (p. 8)

import Mathlib

/-!
Liu, Garrepalli, Dietterich, Fern and Hendrycks, *Open Category Detection with PAC Guarantees*,
arXiv:1808.00529v1 (ICML 2018): the nominal/alien mixture of anomaly-score distributions
(Sections 3–4), the empirical CDFs and the alien-CDF estimate of eq. (1), the threshold returned
by Algorithm 1, the alien detection rate, the sample-size bound and the sampling law of
Theorem 1, and admissibility (Section 5).
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace OpenCategoryPAC

/-- Section 4, p. 3: the empirical CDF `F̂(t) = (1/n) #{i : x_i ≤ t}` of the anomaly scores
`x_1, …, x_n` of a sample. -/
def empCDF {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  ((Finset.univ.filter fun i => x i ≤ t).card : ℝ) / n

/-- Section 4, p. 3: the mixture `D_m` of the nominal score law `μ0` (weight `1 - α`) and the
alien score law `μa` (weight `α`). -/
def mixture (α : ℝ) (μ0 μa : Measure ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - α) • μ0 + ENNReal.ofReal α • μa

/-- Section 4, p. 3 (display after `F_m = (1-α)F_0 + αF_a`) and Appendix B, p. 8: the alien CDF
recovered from a mixture CDF `Fm` and a nominal CDF `F0` with mixture weight `α`,
`(Fm(t) - (1 - α) F0(t)) / α`. -/
def alienCDF (α : ℝ) (Fm F0 : ℝ → ℝ) (t : ℝ) : ℝ :=
  (Fm t - (1 - α) * F0 t) / α

/-- Eq. (1), p. 3: the estimate `F̂a = (F̂m - (1 - α) F̂0) / α` computed from the nominal scores `x`
(the sample `S_0`) and the mixture scores `y` (the sample `S_m`). -/
def alienCDFEst (α : ℝ) {n : ℕ} (x y : Fin n → ℝ) (t : ℝ) : ℝ :=
  alienCDF α (empCDF y) (empCDF x) t

/-- Appendix A, p. 8: the uniform distance `sup_t |F(t) - G(t)|` between two functions
(used only for bounded functions such as CDFs and their estimates). -/
def supDev (F G : ℝ → ℝ) : ℝ :=
  ⨆ t : ℝ, |F t - G t|

/-- Algorithm 1, step 4, p. 3: the pooled score set `S = {x_1, …, x_k, y_1, …, y_n}`. -/
def pooledScores {n : ℕ} (x y : Fin n → ℝ) : Set ℝ :=
  Set.range x ∪ Set.range y

/-- Algorithm 1, step 4, p. 3: `τ` is the threshold returned by Algorithm 1 run with mixture
weight `α` and input `q`, i.e. `τ = max {u ∈ S : F̂a(u) ≤ q}`. -/
def IsAlgThreshold (α q : ℝ) {n : ℕ} (x y : Fin n → ℝ) (τ : ℝ) : Prop :=
  τ ∈ pooledScores x y ∧ alienCDFEst α x y τ ≤ q ∧
    ∀ u ∈ pooledScores x y, alienCDFEst α x y u ≤ q → u ≤ τ

/-- Section 3, p. 3: the alien detection rate of a threshold `τ`, the fraction of aliens (score law
`μa`) whose anomaly score exceeds `τ`, so that they raise an alarm. -/
def detectionRate (μa : Measure ℝ) (τ : ℝ) : ℝ :=
  (μa (Set.Ioi τ)).toReal

/-- Theorem 1, p. 4: the sample-size bound
`(1/2) ln (2 / (1 - √(1 - δ))) (1/ε)² ((2 - α)/α)²`. -/
def sampleSizeBound (α ε δ : ℝ) : ℝ :=
  1 / 2 * Real.log (2 / (1 - Real.sqrt (1 - δ))) * (1 / ε) ^ 2 * ((2 - α) / α) ^ 2

/-- Theorem 1, p. 4: the law of the two training samples, `S_0` of `n` i.i.d. nominal scores
(law `μ0`) and, independently, `S_m` of `n` i.i.d. mixture scores (law `μm`). -/
def sampleLaw (μ0 μm : Measure ℝ) [SigmaFinite μm] (n : ℕ) :
    Measure ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (Measure.pi fun _ : Fin n => μ0).prod (Measure.pi fun _ : Fin n => μm)

/-- Section 5, p. 4: the anomaly detector is admissible if the score CDFs satisfy
`F_0(x) ≥ F_m(x)` for all `x ∈ ℝ`. -/
def IsAdmissible (μ0 μm : Measure ℝ) : Prop :=
  ∀ t : ℝ, cdf μm t ≤ cdf μ0 t

end OpenCategoryPAC


