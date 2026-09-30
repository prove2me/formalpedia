-- Prove2me | Definitions.Def_UnderstandingML_Generative
-- name    : UnderstandingML_Generative
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T05:30:06.654986+00:00
-- url     : https://prove2.me/theorems/8b63f7f8-6e4f-4383-a171-89925726e40a
-- title:
--   Chapter 24: Bernoulli and Gaussian log-likelihoods and MLEs, the log-loss (24.4), relative entropy and entropy, the latent-variable log-likelihood, F and G, the posterior E-step and EM iterations
-- statement:
--   Chapter 24 of Shalev-Shwartz and Ben-David. **Maximum likelihood (§24.1):** `bernoulliLogLik x θ` $= \log(\theta)\sum_i x_i + \log(1-\theta)\sum_i(1-x_i)$ and `bernoulliMLE x` $= \hat\theta = \frac1m\sum_i x_i$ (24.1); `gaussianLogLik x μ σ` $= -\frac1{2\sigma^2}\sum_i(x_i-\mu)^2 - m\log(\sigma\sqrt{2\pi})$, `sampleMean x` $= \hat\mu$ and `sampleStd x` $= \hat\sigma = \sqrt{\frac1m\sum_i(x_i - \hat\mu)^2}$. **Log-loss (§24.1.2):** `logLoss P θ x` $= -\log P_\theta[x]$ (24.4); on a finite domain `relEntropy P Q` $= D_{RE}[P\|Q] = \sum_x P[x]\log\frac{P[x]}{Q[x]}$, `entropy P` $= H(P) = \sum_x P[x]\log\frac1{P[x]}$, and `IsPMF P` says $P$ is a probability mass function. **EM (§24.4):** for a parametric joint $p_\theta(x, y) = P_\theta[X = x, Y = y]$, $y \in [k]$, and a sample $x_1, \dots, x_m$: `latentLogLik p x θ` $= L(\theta) = \sum_i\log\sum_y P_\theta[X = x_i, Y = y]$; `emF p x Q θ` $= F(Q,\theta) = \sum_i\sum_y Q_{i,y}\log P_\theta[X = x_i, Y = y]$; `emG p x Q θ` $= G(Q,\theta) = F(Q,\theta) - \sum_i\sum_y Q_{i,y}\log Q_{i,y}$; `IsRowStochastic Q` is $Q \in \mathcal{Q}$; `posterior p θ x y` $= P_\theta[Y = y \mid X = x]$ (the E-step (24.10)); `IsEMStep p x θ θ'` says $\theta'$ maximizes $F(Q^{(t+1)}, \cdot)$ for the posterior $Q^{(t+1)}$ of $\theta$ (the M-step (24.11)); `IsEMSequence p x θ` is a run of EM.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §24.1 pp. 343-345 (Equations (24.1)-(24.5), Gaussian likelihood), §24.4 pp. 349-351 (L(θ), F(Q, θ), Assumption 24.1, Equations (24.10)-(24.11), G(Q, θ), the set 𝒬)

import Definitions.Def_UnderstandingML_NearestNeighbor
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Chapter 24: generative models

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*,
Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §24.1–§24.5.

**Maximum likelihood (§24.1, pp. 343–345).** For a Bernoulli sample `S = (x₁, …, x_m)`,
`L(S; θ) = log(θ) ∑ᵢ xᵢ + log(1 − θ) ∑ᵢ (1 − xᵢ)` and the maximum likelihood estimator is
`θ̂ = (1/m) ∑ᵢ xᵢ` (24.1), (24.3). For a Gaussian sample, `θ = (μ, σ)` and
`L(S; θ) = −(1/(2σ²)) ∑ᵢ (xᵢ − μ)² − m log(σ√(2π))`, maximized by the sample mean `μ̂` and
`σ̂ = √((1/m) ∑ᵢ (xᵢ − μ̂)²)`. The **log-loss** is `ℓ(θ, x) = −log(P_θ[x])` (24.4), and for a
discrete distribution `P` the true risk is `D_RE[P‖P_θ] + H(P)` (24.5), with the relative
entropy `D_RE[P‖Q] = ∑ₓ P[x] log(P[x]/Q[x])` and the entropy `H(P) = ∑ₓ P[x] log(1/P[x])`.

**Latent variables and EM (§24.4, pp. 349–352).** A parametric joint `P_θ[X = x, Y = y]`,
`y ∈ [k]`, with `P_θ[X = x] = ∑_y P_θ[X = x, Y = y]`; the log-likelihood of `S` is
`L(θ) = ∑ᵢ log P_θ[X = xᵢ]`. `F(Q, θ) = ∑ᵢ ∑_y Q_{i,y} log P_θ[X = xᵢ, Y = y]` and
`G(Q, θ) = F(Q, θ) − ∑ᵢ ∑_y Q_{i,y} log Q_{i,y}` over the set `𝒬` of matrices whose rows are
probability vectors. **EM**: `Q⁽ᵗ⁺¹⁾_{i,y} = P_{θ⁽ᵗ⁾}[Y = y | X = xᵢ]` (24.10) and
`θ⁽ᵗ⁺¹⁾ = argmax_θ F(Q⁽ᵗ⁺¹⁾, θ)` (24.11).

**Conventions.** Parametric families are functions `Θ → X → ℝ` (probabilities or densities,
the book's `P[X = x]` shorthand of p. 344); the EM theorems assume the joint is positive, so
that every logarithm is genuine. `0 · log 0 = 0` in the entropy terms, as Lean's `log 0 = 0`
gives. Bernoulli samples are `Bool`-valued (`true ↦ 1`), and the Bernoulli and i.i.d. laws are
those of Chapters 2 and 19. An EM step is a predicate: the M-step returns *some* maximizer.
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-! ### Maximum likelihood for Bernoulli and Gaussian samples -/

section MLE

variable {m : ℕ}

/-- The log-likelihood `L(S; θ) = log(θ) ∑ᵢ xᵢ + log(1 − θ) ∑ᵢ (1 − xᵢ)` of a Bernoulli sample
(p. 343). -/
noncomputable def bernoulliLogLik (x : Fin m → Bool) (θ : ℝ) : ℝ :=
  Real.log θ * ∑ i, (if x i then (1 : ℝ) else 0) + Real.log (1 - θ) * ∑ i, (if x i then (0 : ℝ) else 1)

/-- The estimator `θ̂ = (1/m) ∑ᵢ xᵢ` (24.1). -/
noncomputable def bernoulliMLE (x : Fin m → Bool) : ℝ := (∑ i, if x i then (1 : ℝ) else 0) / m

/-- The Gaussian log-likelihood `L(S; (μ, σ)) = −(1/(2σ²)) ∑ᵢ (xᵢ − μ)² − m log(σ√(2π))` (p. 344). -/
noncomputable def gaussianLogLik (x : Fin m → ℝ) (μ σ : ℝ) : ℝ :=
  -(1 / (2 * σ ^ 2)) * ∑ i, (x i - μ) ^ 2 - m * Real.log (σ * Real.sqrt (2 * Real.pi))

/-- The sample mean `μ̂ = (1/m) ∑ᵢ xᵢ` (p. 344). -/
noncomputable def sampleMean (x : Fin m → ℝ) : ℝ := (∑ i, x i) / m

/-- The maximum likelihood standard deviation `σ̂ = √((1/m) ∑ᵢ (xᵢ − μ̂)²)` (p. 344). -/
noncomputable def sampleStd (x : Fin m → ℝ) : ℝ :=
  Real.sqrt ((∑ i, (x i - sampleMean x) ^ 2) / m)

end MLE

/-! ### Log-loss, relative entropy and entropy -/

section LogLoss

variable {Θ X : Type*}

/-- The **log-loss** `ℓ(θ, x) = −log(P_θ[x])` (24.4). -/
noncomputable def logLoss (P : Θ → X → ℝ) (θ : Θ) (x : X) : ℝ := -Real.log (P θ x)

/-- The **relative entropy** `D_RE[P‖Q] = ∑ₓ P[x] log(P[x]/Q[x])` on a finite domain (24.5). -/
noncomputable def relEntropy [Fintype X] (P Q : X → ℝ) : ℝ := ∑ x, P x * Real.log (P x / Q x)

/-- The **entropy** `H(P) = ∑ₓ P[x] log(1/P[x])` on a finite domain (24.5). -/
noncomputable def entropy [Fintype X] (P : X → ℝ) : ℝ := ∑ x, P x * Real.log (1 / P x)

/-- `P` is a probability mass function on the finite domain `X`. -/
def IsPMF [Fintype X] (P : X → ℝ) : Prop := (∀ x, 0 ≤ P x) ∧ ∑ x, P x = 1

end LogLoss

/-! ### Latent variables and the EM algorithm -/

section EM

variable {Θ X : Type*} {k m : ℕ}

/-- The log-likelihood `L(θ) = ∑ᵢ log(∑_y P_θ[X = xᵢ, Y = y])` of the sample under the latent
variable model `p θ x y = P_θ[X = x, Y = y]` (p. 349). -/
noncomputable def latentLogLik (p : Θ → X → Fin k → ℝ) (x : Fin m → X) (θ : Θ) : ℝ :=
  ∑ i, Real.log (∑ y, p θ (x i) y)

/-- `F(Q, θ) = ∑ᵢ ∑_y Q_{i,y} log(P_θ[X = xᵢ, Y = y])` (p. 349). -/
noncomputable def emF (p : Θ → X → Fin k → ℝ) (x : Fin m → X) (Q : Fin m → Fin k → ℝ) (θ : Θ) :
    ℝ :=
  ∑ i, ∑ y, Q i y * Real.log (p θ (x i) y)

/-- `G(Q, θ) = F(Q, θ) − ∑ᵢ ∑_y Q_{i,y} log(Q_{i,y})` (p. 350). -/
noncomputable def emG (p : Θ → X → Fin k → ℝ) (x : Fin m → X) (Q : Fin m → Fin k → ℝ) (θ : Θ) :
    ℝ :=
  emF p x Q θ - ∑ i, ∑ y, Q i y * Real.log (Q i y)

/-- `Q ∈ 𝒬`: every row of `Q` is a probability vector over `[k]` (p. 351). -/
def IsRowStochastic (Q : Fin m → Fin k → ℝ) : Prop :=
  (∀ i y, 0 ≤ Q i y) ∧ ∀ i, ∑ y, Q i y = 1

/-- The posterior `P_θ[Y = y | X = x] = P_θ[X = x, Y = y] / ∑_{y'} P_θ[X = x, Y = y']`, the
E-step (24.10). -/
noncomputable def posterior (p : Θ → X → Fin k → ℝ) (θ : Θ) (x : X) (y : Fin k) : ℝ :=
  p θ x y / ∑ y', p θ x y'

/-- One **EM iteration** from `θ` to `θ'`: the E-step sets `Q_{i,y} = P_θ[Y = y | X = xᵢ]`
(24.10) and the M-step returns a maximizer `θ'` of `F(Q, ·)` (24.11). -/
def IsEMStep (p : Θ → X → Fin k → ℝ) (x : Fin m → X) (θ θ' : Θ) : Prop :=
  ∀ θ'' : Θ, emF p x (fun i y ↦ posterior p θ (x i) y) θ'' ≤ emF p x (fun i y ↦ posterior p θ (x i) y) θ'

/-- `θ⁽⁰⁾, θ⁽¹⁾, …` is a run of the EM procedure. -/
def IsEMSequence (p : Θ → X → Fin k → ℝ) (x : Fin m → X) (θ : ℕ → Θ) : Prop :=
  ∀ t, IsEMStep p x (θ t) (θ (t + 1))

end EM

end UnderstandingML


