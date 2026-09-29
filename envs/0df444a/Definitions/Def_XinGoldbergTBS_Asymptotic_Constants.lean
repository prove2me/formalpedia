-- Prove2me | Definitions.Def_XinGoldbergTBS_Asymptotic_Constants
-- name    : XinGoldbergTBS_Asymptotic_Constants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T01:19:31.470312+00:00
-- url     : https://prove2.me/theorems/1e279d64-5216-4d80-b8e6-325ecb8e7537
-- title:
--   Constants $g, U, p_0, \hat p_0, Q_0, \eta_0, c_0, U_0, \epsilon_0, \gamma_\epsilon, \vartheta_\epsilon, Y_0$ of Theorem 1 and $\underline\xi_0, \bar\xi_0, m_\alpha$
-- statement:
--   The explicit constants of Section 2.2.1 (p. 441) and Appendix A.3 (p. 450). Let $D'_1, \dots, D'_{L_0+1}$ be i.i.d. copies of $D$.
--
--   For $\theta \ge 0$ and $\epsilon \in (0, \mathbb E[D]]$,
--   $$\phi_\epsilon(\theta) = e^{\theta(\mathbb E[D]-\epsilon)}\,\mathbb E[e^{-\theta D}], \qquad \gamma_\epsilon = \inf_{\theta \ge 0}\phi_\epsilon(\theta),$$
--   and $\vartheta_\epsilon$ is the supremum of the set of minimizers of $\phi_\epsilon$ over $\theta \ge 0$, with $\vartheta_\epsilon = \infty$ if the infimum is not attained.
--
--   Further,
--   1. $g = \inf_{x\in\mathbb R}\mathbb E\big[G(x - \sum_{i=1}^{L_0+1} D'_i)\big]$ and $U = c\,\mathbb E[D] + \mathbb E\big[G(-\sum_{i=1}^{L_0+1} D'_i)\big]$;
--   2. $p_0 = \mathbb P(D < \mathbb E[D])$, $\hat p_0 = \big(\tfrac12 p_0(1-p_0)\big)^{1/2}$, $Q_0 = \inf\{x \ge 0 : \mathbb P(D \le x) \ge \tfrac12 p_0\}$, $\eta_0 = \inf_{z\in\mathbb R}\mathbb E|z - D|$;
--   3. $c_0 = \tfrac{1}{240}\min(b,h)\,\hat p_0\eta_0$ and $U_0 = 64(L_0+1)\dfrac{\max^2(b,h)}{\min(b,h)}\mathbb E[D]$;
--   4. $$\epsilon_0 = \min\Big(\mathbb E[D] - Q_0,\ \tfrac14(\eta_0\hat p_0)^2,\ 1 - 2^{-\hat p_0^2/400},\ \tfrac{1}{625}c_0^2\,(U_0 2^{L_0} + \eta_0 + U + 1)^{-2}\Big);$$
--   5. $$Y_0 = 25\,g^{-2}\big(U_0 2^{L_0} + \max(b,h)\,\gamma_{\epsilon_0}\vartheta_{\epsilon_0}^{-1}(1-\gamma_{\epsilon_0})^{-2}\big)^2 + L_0 + 1,$$ with $1/\infty = 0$;
--   6. $\underline\xi_0 = 2^{-\hat p_0^2/400}$, $\bar\xi_0 = 2^{-(4/(\hat p_0^2\eta_0^2))\epsilon_0^2}$, and $m_\alpha = \lceil -1/\log_2\alpha \rceil$ for $\alpha \in (0,1)$.
--
--   These constants appear in the threshold of Theorem 1 and in the auxiliary bounds of its proof.
--
--   **Formalization Note** $\vartheta_\epsilon$ takes values in $[0,\infty]$: it is $\infty$ when the minimizer set is empty (and also when it is unbounded), and $\vartheta_\epsilon^{-1}$ is computed in $[0,\infty]$ and then converted to a real number, so $1/\infty = 0$. The paper proves $\vartheta_\epsilon > 0$, so the case $\vartheta_\epsilon = 0$ does not arise. Expectations of $\sum_{i=1}^{L_0+1}D'_i$ are integrals against the $(L_0+1)$-fold product of the law of $D$. Every real infimum here is over a nonempty family bounded below by $0$, and every integrand is integrable because $D$ has finite mean and $D \ge 0$.
-- source:
--   Xin and Goldberg, Asymptotic Optimality of Tailored Base-Surge Policies in Dual-Sourcing Inventory Systems, Management Science 64(1), 2018, p. 441, Section 2.2.1; p. 450, Appendix A.3

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model

/-!
# The explicit constants of Section 2.2.1 (p. 441) and of Appendix A.3 (p. 450)

Each constant is defined exactly as on the page. `∑_{i=1}^{L₀+1} D'_i` is integrated against
the product law `μ^{⊗(L₀+1)}` of `L₀ + 1` independent copies of `D`. Every real infimum below is
over a nonempty family bounded below by `0`. The argmin supremum `ϑ_ϵ` takes values in `ℝ≥0∞`:
it is `∞` when the infimum `γ_ϵ` is not attained, and also when the minimizer set is unbounded;
`ϑ_ϵ⁻¹` uses `1/∞ = 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XinGoldbergTBS.Asymptotic

/-- Law of `(D'_1, …, D'_{L₀+1})`, i.i.d. copies of `D`. -/
def sumLaw (μ : DemandLaw) (L₀ : ℕ) : Measure (Fin (L₀ + 1) → ℝ) :=
  Measure.pi fun _ : Fin (L₀ + 1) => μ.law

/-- `g = inf_{x ∈ ℝ} 𝔼[G(x - ∑_{i=1}^{L₀+1} D'_i)]`. -/
def gConst (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) : ℝ :=
  ⨅ x : ℝ, ∫ y, G κ (x - ∑ i, y i) ∂sumLaw μ L₀

/-- `U = c 𝔼[D] + 𝔼[G(-∑_{i=1}^{L₀+1} D'_i)]`. -/
def UConst (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) : ℝ :=
  κ.c * μ.mean + ∫ y, G κ (-∑ i, y i) ∂sumLaw μ L₀

/-- `p₀ = ℙ(D < 𝔼[D])`. -/
def p0 (μ : DemandLaw) : ℝ := (μ.law (Set.Iio μ.mean)).toReal

/-- `p̂₀ = ((1/2) p₀ (1 - p₀))^{1/2}`. -/
def p0hat (μ : DemandLaw) : ℝ := Real.sqrt ((1 / 2) * p0 μ * (1 - p0 μ))

/-- `Q₀ = inf {x ∈ ℝ⁺ : ℙ(D ≤ x) ≥ (1/2) p₀}`. -/
def Q0 (μ : DemandLaw) : ℝ :=
  sInf {x : ℝ | 0 ≤ x ∧ (1 / 2) * p0 μ ≤ (μ.law (Set.Iic x)).toReal}

/-- `η₀ = inf_{z ∈ ℝ} 𝔼[|z - D|]`. -/
def eta0 (μ : DemandLaw) : ℝ := ⨅ z : ℝ, ∫ d, |z - d| ∂μ.law

/-- `c₀ = (1/240) min(b, h) p̂₀ η₀`. -/
def c0 (μ : DemandLaw) (κ : Costs) : ℝ := (1 / 240) * min κ.b κ.h * p0hat μ * eta0 μ

/-- `U₀ = 64 (L₀ + 1) (max²(b, h) / min(b, h)) 𝔼[D]`. -/
def U0 (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) : ℝ :=
  64 * ((L₀ : ℝ) + 1) * (max κ.b κ.h ^ 2 / min κ.b κ.h) * μ.mean

/-- `ϵ₀ = min(𝔼[D] - Q₀, (1/4)(η₀ p̂₀)², 1 - 2^{-p̂₀²/400},
(1/625) c₀² (U₀ 2^{L₀} + η₀ + U + 1)^{-2})`. -/
def eps0 (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) : ℝ :=
  min (μ.mean - Q0 μ)
    (min ((1 / 4) * (eta0 μ * p0hat μ) ^ 2)
      (min (1 - (2 : ℝ) ^ (-(p0hat μ ^ 2) / 400))
        ((1 / 625) * c0 μ κ ^ 2 *
          ((U0 μ κ L₀ * 2 ^ L₀ + eta0 μ + UConst μ κ L₀ + 1) ^ 2)⁻¹)))

/-- `φ_ϵ(θ) = exp(θ(𝔼[D] - ϵ)) 𝔼[exp(-θ D)]` (used for `θ ≥ 0`). -/
def phi (μ : DemandLaw) (ϵ θ : ℝ) : ℝ :=
  Real.exp (θ * (μ.mean - ϵ)) * ∫ d, Real.exp (-(θ * d)) ∂μ.law

/-- `γ_ϵ = inf_{θ ≥ 0} φ_ϵ(θ)`. -/
def gamma (μ : DemandLaw) (ϵ : ℝ) : ℝ := ⨅ θ : Set.Ici (0 : ℝ), phi μ ϵ θ

/-- The set of minimizers of `φ_ϵ` over `θ ≥ 0`. -/
def phiMinimizers (μ : DemandLaw) (ϵ : ℝ) : Set ℝ :=
  {θ : ℝ | 0 ≤ θ ∧ phi μ ϵ θ = gamma μ ϵ}

open Classical in
/-- `ϑ_ϵ`: the supremum of the set of minimizers of `φ_ϵ` over `θ ≥ 0`, and `∞` if the
infimum is not attained. -/
def vartheta (μ : DemandLaw) (ϵ : ℝ) : ℝ≥0∞ :=
  if (phiMinimizers μ ϵ).Nonempty then ⨆ θ ∈ phiMinimizers μ ϵ, ENNReal.ofReal θ else ⊤

/-- `ϑ_ϵ⁻¹` as a real number, with `1/∞ = 0`. -/
def varthetaInv (μ : DemandLaw) (ϵ : ℝ) : ℝ := (vartheta μ ϵ)⁻¹.toReal

/-- `Y₀ = 25 g^{-2} (U₀ 2^{L₀} + max(b, h) γ_{ϵ₀} ϑ_{ϵ₀}^{-1} (1 - γ_{ϵ₀})^{-2})² + L₀ + 1`. -/
def Y0 (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) : ℝ :=
  25 * (gConst μ κ L₀ ^ 2)⁻¹ *
    (U0 μ κ L₀ * 2 ^ L₀ +
      max κ.b κ.h * gamma μ (eps0 μ κ L₀) * varthetaInv μ (eps0 μ κ L₀) *
        ((1 - gamma μ (eps0 μ κ L₀)) ^ 2)⁻¹) ^ 2 + L₀ + 1

/-- `ξ̲₀ = 2^{-p̂₀²/400}` (p. 450). -/
def xiLow (μ : DemandLaw) : ℝ := (2 : ℝ) ^ (-(p0hat μ ^ 2) / 400)

/-- `ξ̄₀ = 2^{-(4/(p̂₀² η₀²)) ϵ₀²}` (p. 450). -/
def xiHigh (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(4 / (p0hat μ ^ 2 * eta0 μ ^ 2)) * eps0 μ κ L₀ ^ 2)

/-- `m_α = ⌈-1/log₂(α)⌉` (p. 450). -/
def mAlpha (α : ℝ) : ℤ := ⌈-1 / Real.logb 2 α⌉

end XinGoldbergTBS.Asymptotic


