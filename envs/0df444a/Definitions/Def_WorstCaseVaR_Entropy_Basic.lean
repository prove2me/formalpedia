-- Prove2me | Definitions.Def_WorstCaseVaR_Entropy_Basic
-- name    : WorstCaseVaR_Entropy_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:16:47.534397+00:00
-- url     : https://prove2.me/theorems/44c6c58a-e47a-4f0c-b9f7-d71589cb0a06
-- title:
--   Worst-case VaR under a relative-entropy constraint: loss set, KL ball around a Gaussian, risk factor κ(ε, d)
-- statement:
--   This file fixes the objects of §1.3 and §4.2 of El Ghaoui, Oks and Oustry (2003).
--
--   Returns are vectors $x \in \mathbb{R}^n$ and a portfolio is a vector $w \in \mathbb{R}^n$; the portfolio return is $r(w,x) = w^\top x$.
--
--   1. **Loss set** (Eq. 13). For a level $\gamma \in \mathbb{R}$, $\mathcal S_\gamma = \{x : \gamma \le -x^\top w\}$.
--   2. **Quadratic form.** $w^\top \Gamma w = \sum_{i,j} w_i \Gamma_{ij} w_j$ for an $n\times n$ real matrix $\Gamma$.
--   3. **Reference Gaussian.** $P_0 = \mathcal N(\hat x, \Gamma)$, the multivariate normal distribution with mean $\hat x$ and covariance $\Gamma$.
--   4. **Relative-entropy class** (Eq. 43). For $d \in \mathbb{R}$,
--   $$\mathcal P_d = \{P \text{ probability measure on } \mathbb R^n : \mathrm{KL}(P, P_0) \le d\},\qquad \mathrm{KL}(P,P_0) = \int \log\frac{dP}{dP_0}\,dP,$$
--   with $\mathrm{KL}(P,P_0) = +\infty$ unless $P \ll P_0$ and $\log\frac{dP}{dP_0}$ is $P$-integrable.
--   5. **Feasible set of the worst-case VaR** (Eq. 4). For a class $\mathcal P$ of distributions, a portfolio $w$ and a level $\varepsilon$,
--   $$F_{\mathcal P}(w,\varepsilon) = \{\gamma \in \mathbb R : P(\mathcal S_\gamma) \le \varepsilon \text{ for every } P \in \mathcal P\}.$$
--   The worst-case Value-at-Risk $V_{\mathcal P}(w)$ is the least element of this set.
--   6. **Standard normal CDF and quantile.** $\Phi$ is the CDF of $\mathcal N(0,1)$, and $\Phi^{-1}(p) = \inf\{t : p \le \Phi(t)\}$, which inverts $\Phi$ for $p \in (0,1)$.
--   7. **Risk factor** (Eq. 45). For $\lambda > 0$ let $\rho_{\varepsilon,d}(\lambda) = \dfrac{e^{\varepsilon/\lambda - d} - 1}{e^{1/\lambda} - 1}$; then
--   $$f(\varepsilon,d) = \sup_{\lambda > 0} \rho_{\varepsilon,d}(\lambda), \qquad \kappa(\varepsilon,d) = -\Phi^{-1}(f(\varepsilon,d)).$$
--   8. **Gaussian tail.** $\phi(\gamma) = 1 - \Phi\big((\gamma + w^\top \hat x)/\sqrt{w^\top\Gamma w}\big)$.
--   9. **Partially minimised dual function** (Eq. 48). $\lambda d + \lambda \log\big((e^{1/\lambda} - 1)\phi + 1\big)$ for $\lambda > 0$ and a number $\phi$.
--
--   These are the objects in which Theorem 9 (the closed form of the entropy-constrained worst-case VaR) and the steps of its proof are stated.
--
--   **Formalization Note** Returns live in `EuclideanSpace ℝ (Fin n)`, and $P_0$ is Mathlib's `multivariateGaussian`. The paper's $\mathcal P$ is written `Pclass` in Lean. The feasible set compares $P(\mathcal S_\gamma)$, a value in $[0,\infty]$, with $\varepsilon$ through `ENNReal.ofReal`. $f$ is a Lean `sSup`: for $\varepsilon \le 1$ and $d \ge 0$ its set of values is nonempty and bounded above by $1$, so it is the true supremum there. For $d < 0$, `ENNReal.ofReal d = 0` and the class reduces to $\{P_0\}$; every statement of the mission assumes $d \ge 0$.
-- source:
--   El Ghaoui, Oks and Oustry, Worst-Case Value-at-Risk and Robust Portfolio Optimization: A Conic Programming Approach, Oper. Res. 51 (2003), p. 544, Eq. (4); p. 546, Eq. (13); p. 553, Eqs. (43), (45); p. 554, display defining φ(γ) and Eq. (48)

import Mathlib

namespace WorstCaseVaR.Entropy

open MeasureTheory ProbabilityTheory

/-- The return space `ℝⁿ`, as the Euclidean space carrying `multivariateGaussian`. -/
abbrev Returns (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- The loss set `𝒮 = {x | γ ≤ -xᵀw}` of Eq. (13): the returns `x` for which the portfolio
`w` loses at least `γ`. -/
def lossSet {n : ℕ} (w : Returns n) (γ : ℝ) : Set (Returns n) :=
  {x | γ ≤ -inner ℝ x w}

/-- The quadratic form `wᵀΓw`. -/
def quadForm {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (w : Returns n) : ℝ :=
  ∑ i, ∑ j, w i * Γ i j * w j

/-- The reference Gaussian distribution `P₀ = 𝒩(x̂, Γ)` on `ℝⁿ`. -/
noncomputable def refGaussian {n : ℕ} (xhat : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ) :
    Measure (Returns n) :=
  multivariateGaussian xhat Γ

/-- The relative-entropy class of Eq. (43): probability distributions `P` of returns with
`KL(P, P₀) ≤ d`, where `P₀ = 𝒩(x̂, Γ)`. Mathlib's `klDiv P P₀` is `∞` unless `P ≪ P₀` and the
log-likelihood ratio is `P`-integrable, and equals `∫ log (dP/dP₀) dP` otherwise (for
probability measures). -/
def klBall {n : ℕ} (xhat : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ) (d : ℝ) :
    Set (Measure (Returns n)) :=
  {P | IsProbabilityMeasure P ∧ InformationTheory.klDiv P (refGaussian xhat Γ) ≤ ENNReal.ofReal d}

/-- The feasible set of the worst-case Value-at-Risk problem (4): the levels `γ` such that
`Prob{γ ≤ -r(w, x)} ≤ ε` for every distribution `P` in the class `Pclass` (the paper's `𝒫`), with `r(w, x) = wᵀx`.
The worst-case VaR `V_𝒫(w)` is the least element of this set, when it exists. -/
def varFeasible {n : ℕ} (Pclass : Set (Measure (Returns n))) (w : Returns n) (ε : ℝ) : Set ℝ :=
  {γ | ∀ P ∈ Pclass, P (lossSet w γ) ≤ ENNReal.ofReal ε}

/-- The cumulative distribution function `Φ` of the standard normal distribution. -/
noncomputable def stdNormalCDF (t : ℝ) : ℝ :=
  cdf (gaussianReal 0 1) t

/-- The standard normal quantile: `Φ⁻¹(p) = inf {t | p ≤ Φ(t)}`. For `p ∈ (0, 1)` the set is
nonempty and bounded below, and this is the inverse of `Φ`; outside `(0, 1)` the value is not
meaningful (Lean's `sInf` returns `0` on an empty or unbounded-below set). -/
noncomputable def normalQuantile (p : ℝ) : ℝ :=
  sInf {t : ℝ | p ≤ stdNormalCDF t}

/-- The ratio `(e^{ε/λ - d} - 1) / (e^{1/λ} - 1)` whose supremum over `λ > 0` defines `f(ε, d)`
in Eq. (45). -/
noncomputable def entropyRatio (ε d lam : ℝ) : ℝ :=
  (Real.exp (ε / lam - d) - 1) / (Real.exp (1 / lam) - 1)

/-- `f(ε, d) := sup_{λ > 0} (e^{ε/λ - d} - 1) / (e^{1/λ} - 1)` of Eq. (45). For `ε ≤ 1` and
`d ≥ 0` the set of values is nonempty and bounded above by `1` (the numerator is smaller than
the positive denominator), so `sSup` is the true supremum there and not Lean's junk value. -/
noncomputable def fEntropy (ε d : ℝ) : ℝ :=
  sSup (entropyRatio ε d '' Set.Ioi 0)

/-- The entropy-constrained risk factor `κ(ε, d) := -Φ⁻¹(f(ε, d))` of Eq. (45). -/
noncomputable def kappaEntropy (ε d : ℝ) : ℝ :=
  -normalQuantile (fEntropy ε d)

/-- The Gaussian tail `φ(γ) := 1 - Φ((γ + wᵀx̂) / √(wᵀΓw))` (p. 554). -/
noncomputable def gaussianTail {n : ℕ} (xhat : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (w : Returns n) (γ : ℝ) : ℝ :=
  1 - stdNormalCDF ((γ + inner ℝ w xhat) / Real.sqrt (quadForm Γ w))

/-- The partially minimised dual function of Eq. (48):
`λ d + λ log((e^{1/λ} - 1) φ + 1)`. -/
noncomputable def dualValue (d φ lam : ℝ) : ℝ :=
  lam * d + lam * Real.log ((Real.exp (1 / lam) - 1) * φ + 1)

end WorstCaseVaR.Entropy


