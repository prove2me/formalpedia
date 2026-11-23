-- Prove2me | Definitions.Def_MultiViewRedundancy_Basic
-- name    : MultiViewRedundancy_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T19:17:29.058796+00:00
-- url     : https://prove2.me/theorems/e926262c-4cce-45bf-886a-4ba1bb434a47
-- title:
--   Multi-view data, density ratio, contrastive losses, landmark and direct embeddings
-- statement:
--   Objects of Sections 2–5 of Tosh, Krishnamurthy and Hsu (2021).
--
--   1. **Multi-view distribution.** The views take values in measurable spaces $\mathcal X$ and $\mathcal Z$ (with $\mathcal Z$ standard Borel where conditional laws are needed), and the label in $\mathbb R$. A law $\rho$ of $(X,Z,Y)$ is a probability measure on $\mathcal X\times\mathcal Z\times\mathbb R$. Its view marginal $p_{X,Z}$ has marginals $p_X$ and $p_Z$.
--   2. **Regression functions (Section 2.4).** $\mathbb E[Y\mid X=x]$, $\mathbb E[Y\mid Z=z]$ and $\mathbb E[Y\mid X=x,Z=z]$ are the means of the conditional laws of $Y$ (disintegrations of $\rho$). The predictor through the other view is $\mu(x)=\mathbb E[\mathbb E[Y\mid Z]\mid X=x]$, the mean of $z\mapsto\mathbb E[Y\mid Z=z]$ under the conditional law of $Z$ given $X=x$. The redundancy quantities are $\varepsilon_X=\mathbb E[(\mathbb E[Y\mid X]-\mathbb E[Y\mid X,Z])^2]$ and $\varepsilon_Z=\mathbb E[(\mathbb E[Y\mid Z]-\mathbb E[Y\mid X,Z])^2]$, and $\varepsilon_\mu=\varepsilon_X+2\sqrt{\varepsilon_X\varepsilon_Z}+\varepsilon_Z$.
--   3. **Density ratio (Section 2.3).** $g^\star(x,z)=\dfrac{p_{X,Z}(x,z)}{p_X(x)p_Z(z)}$, the Radon–Nikodym derivative of $p_{X,Z}$ with respect to $p_X\otimes p_Z$.
--   4. **Contrastive distribution and losses (Sections 2.2, 2.3, 4).** $(X_c,Z_c,Y_c)\sim D_{\mathrm{contrast}}$ is $(X,Z,1)$ with $(X,Z)\sim p_{X,Z}$ with probability $1/2$, and $(X,\tilde Z,-1)$ with $(X,\tilde Z)\sim p_X\otimes p_Z$ otherwise. The losses are $L_{\mathrm{lm}}(f)=\mathbb E[\log(1+e^{-Y_cf(X_c,Z_c)})]$ (eq. 1) and $L_{\mathrm{direct}}(f)=\mathbb E[\log(1+f(X_c,Z_c)^{-Y_c})]$ for $f>0$ (eq. 2). The excess losses are $\varepsilon_{\mathrm{opt,lm}}=L_{\mathrm{lm}}(f)-L_{\mathrm{lm}}(\log\circ g^\star)$ and $\varepsilon_{\mathrm{opt,direct}}=L_{\mathrm{direct}}(\eta^\top\psi)-L_{\mathrm{direct}}(g^\star)$.
--   5. **Landmark embedding (Section 3).** For landmarks $z_1,\dots,z_m\in\mathcal Z$ and a bivariate $g$, $\varphi(x)=(g(x,z_1),\dots,g(x,z_m))$; $\varphi^\star$ uses $g=g^\star$. The landmark variance is $\operatorname{var}(\mathbb E[Y_1\mid Z_1]\,g^\star(X,Z_1))$ with $(X,Z_1)\sim p_X\otimes p_Z$, valued in $[0,\infty]$, and $\varepsilon_{\mathrm{lm}}=2\operatorname{var}(\cdots)/n$ for a block size $n$.
--   6. **Direct embeddings (Section 4).** For $\eta:\mathcal X\to\mathbb R^m$, $\psi:\mathcal Z\to\mathbb R^m$: $\varepsilon_{\mathrm{direct}}(\eta,\psi)=\mathbb E[(\eta(X)^\top\psi(\tilde Z)-g^\star(X,\tilde Z))^2]$ with $(X,\tilde Z)\sim p_X\otimes p_Z$, valued in $[0,\infty]$.
--   7. **Risk (eq. 3).** $R(\varphi)=\inf_{w\in\mathbb R^m}\mathbb E[(w^\top\varphi(X)-\mu(X))^2]$, valued in $[0,\infty]$.
--   8. **Hidden variables (Section 4.2).** $H\sim p_H$ renders $X$ and $Z$ conditionally independent with conditional laws $p_{X\mid H}(\cdot\mid h)$, $p_{Z\mid H}(\cdot\mid h)$ if $p_{X,Z}=\int p_{X\mid H}(\cdot\mid h)\otimes p_{Z\mid H}(\cdot\mid h)\,dp_H(h)$. The hidden-variable variance is $\operatorname{var}\Big(\frac{p_{X\mid H}(X\mid\bar H)\,p_{Z\mid H}(\tilde Z\mid\bar H)}{p_X(X)\,p_Z(\tilde Z)}\Big)$ with $(X,\tilde Z,\bar H)\sim p_X\otimes p_Z\otimes p_H$, valued in $[0,\infty]$.
--   9. **Gaussian model (Section 3.3).** $H\sim N(0,\sigma^2)$, $X\mid H\sim N(H,1)$, $Z\mid H\sim N(H,1)$, $X\perp Z\mid H$; the law of $(X,Z)$ is that of $(H+E_1,H+E_2)$ with $H,E_1,E_2$ independent and $E_i\sim N(0,1)$.
--
--   **Formalization Note** The paper assumes that all variables have probability mass functions or densities. The formalization works with general laws: densities and density ratios become Radon–Nikodym derivatives, and conditional means become means of disintegration kernels, which agree with the paper's formulas in both cases. Quantities that may be infinite in the paper (variances, $\varepsilon_{\mathrm{direct}}$, risks) take values in $[0,\infty]$. $L_{\mathrm{lm}}(\log\circ g^\star)$ is written in its equal odds form $L_{\mathrm{direct}}(g^\star)$, which stays correct where $g^\star=0$. The block size $n$ of $\varepsilon_{\mathrm{lm}}$ is a parameter; each statement says which $n$ it uses.
-- source:
--   Tosh, Krishnamurthy and Hsu, Contrastive learning, multi-view redundancy, and linear models, arXiv:2008.10150v2 (2021), Sections 2.1-2.4 (pp. 6-7), 3 and 3.3 (pp. 7-9), 4 (pp. 10-11), 5 and eq. (3) (p. 12)

import Mathlib

/-!
Tosh, Krishnamurthy and Hsu, *Contrastive learning, multi-view redundancy, and linear models*,
arXiv:2008.10150v2 (2021): the multi-view distribution and its regression functions (Section 2.1,
2.4), the density ratio and the contrastive losses (Sections 2.2, 2.3, 4, eq. (1), eq. (2)), the
landmark embedding (Section 3), direct embeddings and hidden variables (Section 4), the risk
(eq. (3)) and the Gaussian model (Section 3.3).

A law `ρ` of the triple `(X, Z, Y)` is a measure on `X × Z × ℝ`; a law `ν` of the pair of views
`(X, Z)` is a measure on `X × Z`. Conditional means are means of the disintegration kernels
(`Measure.condKernel`); density ratios are Radon–Nikodym derivatives, which covers both the
probability-mass-function and the density case of Section 2.1.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace MultiViewRedundancy

variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]

/-- Section 2.1: the joint law `p_{X,Z}` of the two views, for a law `ρ` of `(X, Z, Y)`.
Its marginals `(lawXZ ρ).fst` and `(lawXZ ρ).snd` are `p_X` and `p_Z`. -/
abbrev lawXZ (ρ : Measure (X × Z × ℝ)) : Measure (X × Z) :=
  ρ.map (fun t => (t.1, t.2.1))

/-- Section 2.3: the density ratio `g⋆(x, z) = p_{X,Z}(x, z) / (p_X(x) p_Z(z))`, the
Radon–Nikodym derivative of `p_{X,Z}` with respect to `p_X ⊗ p_Z`. -/
def densityRatio (ν : Measure (X × Z)) (x : X) (z : Z) : ℝ :=
  (ν.rnDeriv (ν.fst.prod ν.snd) (x, z)).toReal

/-- Section 2.4: the regression function `E[Y | X = x]`, the mean of the conditional law of `Y`
given `X = x`. -/
def regX (ρ : Measure (X × Z × ℝ)) [IsFiniteMeasure ρ] (x : X) : ℝ :=
  ∫ y, y ∂((ρ.map (fun t => (t.1, t.2.2))).condKernel x)

/-- Section 2.4: the regression function `E[Y | Z = z]`. -/
def regZ (ρ : Measure (X × Z × ℝ)) [IsFiniteMeasure ρ] (z : Z) : ℝ :=
  ∫ y, y ∂((ρ.map (fun t => (t.2.1, t.2.2))).condKernel z)

/-- Section 2.4: the regression function `E[Y | (X, Z) = (x, z)]`. -/
def regXZ (ρ : Measure (X × Z × ℝ)) [IsFiniteMeasure ρ] (x : X) (z : Z) : ℝ :=
  ∫ y, y ∂((ρ.map (fun t => ((t.1, t.2.1), t.2.2))).condKernel (x, z))

/-- Section 2.4: `μ(x) = E[E[Y | Z] | X = x]`, the mean of `z ↦ E[Y | Z = z]` under the
conditional law of `Z` given `X = x`. -/
def muFn [StandardBorelSpace Z] [Nonempty Z] (ρ : Measure (X × Z × ℝ)) [IsFiniteMeasure ρ]
    (x : X) : ℝ :=
  ∫ z, regZ ρ z ∂((lawXZ ρ).condKernel x)

/-- Section 2.4: `ε_X = E[(E[Y | X] - E[Y | X, Z])²]`. -/
def epsX (ρ : Measure (X × Z × ℝ)) [IsFiniteMeasure ρ] : ℝ :=
  ∫ t, (regX ρ t.1 - regXZ ρ t.1 t.2.1) ^ 2 ∂ρ

/-- Section 2.4: `ε_Z = E[(E[Y | Z] - E[Y | X, Z])²]`. -/
def epsZ (ρ : Measure (X × Z × ℝ)) [IsFiniteMeasure ρ] : ℝ :=
  ∫ t, (regZ ρ t.2.1 - regXZ ρ t.1 t.2.1) ^ 2 ∂ρ

/-- Lemma 1: `ε_μ := ε_X + 2 √(ε_X ε_Z) + ε_Z`. -/
def epsMu (ρ : Measure (X × Z × ℝ)) [IsFiniteMeasure ρ] : ℝ :=
  epsX ρ + 2 * Real.sqrt (epsX ρ * epsZ ρ) + epsZ ρ

/-- Section 3: the landmark embedding `x ↦ (g(x, Z₁), …, g(x, Z_m))` of a bivariate function `g`
with landmarks `zs = (Z₁, …, Z_m)`; `φ⋆` is the case `g = g⋆`. -/
def landmarkEmbedding {m : ℕ} (g : X → Z → ℝ) (zs : Fin m → Z) (x : X) : Fin m → ℝ :=
  fun i => g x (zs i)

/-- Lemma 2: `var(E[Y₁ | Z₁] g⋆(X, Z₁))` with `(X, Z₁) ∼ p_X ⊗ p_Z`, as an element of `[0, ∞]`. -/
def landmarkVar (ρ : Measure (X × Z × ℝ)) [IsFiniteMeasure ρ] : ℝ≥0∞ :=
  evariance (fun p : X × Z => regZ ρ p.2 * densityRatio (lawXZ ρ) p.1 p.2)
    ((lawXZ ρ).fst.prod (lawXZ ρ).snd)

/-- Lemma 2: `ε_lm := 2 var(E[Y₁ | Z₁] g⋆(X, Z₁)) / n` for the block size `n`; the paper takes
`n = ⌊m / log₂(1/δ)⌋`. -/
def epsLm (ρ : Measure (X × Z × ℝ)) [IsFiniteMeasure ρ] (n : ℕ) : ℝ :=
  2 * (landmarkVar ρ).toReal / n

/-- Eq. (3): the risk `R(φ) = inf_{w ∈ ℝ^m} E[(wᵀφ(X) - μ(X))²]` of an embedding `φ : X → ℝ^m`,
as an element of `[0, ∞]`. -/
def risk [StandardBorelSpace Z] [Nonempty Z] (ρ : Measure (X × Z × ℝ)) [IsFiniteMeasure ρ]
    {m : ℕ} (φ : X → Fin m → ℝ) : ℝ≥0∞ :=
  ⨅ w : Fin m → ℝ, ∫⁻ x, ENNReal.ofReal ((∑ i, w i * φ x i - muFn ρ x) ^ 2) ∂(lawXZ ρ).fst

/-- Section 2.2: the contrastive distribution `D_contrast` of `(X_c, Z_c, Y_c)`: with probability
`1/2` a pair `(X, Z) ∼ p_{X,Z}` with `Y_c = 1`, otherwise `(X, Z̃) ∼ p_X ⊗ p_Z` with `Y_c = -1`. -/
def contrastDist (ν : Measure (X × Z)) : Measure (X × Z × ℝ) :=
  (2⁻¹ : ℝ≥0∞) • ν.map (fun p => (p.1, p.2, (1 : ℝ))) +
    (2⁻¹ : ℝ≥0∞) • (ν.fst.prod ν.snd).map (fun p => (p.1, p.2, (-1 : ℝ)))

/-- Eq. (1): the logistic contrastive loss `L_lm(f) = E[log(1 + exp(-Y_c f(X_c, Z_c)))]`. -/
def lossLm (ν : Measure (X × Z)) (f : X → Z → ℝ) : ℝ :=
  ∫ t, Real.log (1 + Real.exp (-(t.2.2 * f t.1 t.2.1))) ∂(contrastDist ν)

/-- Eq. (2): the direct contrastive loss `L_direct(f) = E[log(1 + 1 / f(X_c, Z_c)^{Y_c})]`, for
`f > 0`. -/
def lossDirect (ν : Measure (X × Z)) (f : X → Z → ℝ) : ℝ :=
  ∫ t, Real.log (1 + 1 / f t.1 t.2.1 ^ t.2.2) ∂(contrastDist ν)

/-- Section 4: the bivariate function `(x, z) ↦ η(x)ᵀψ(z)` of a pair of embeddings. -/
def innerEmb {m : ℕ} (η : X → Fin m → ℝ) (ψ : Z → Fin m → ℝ) (x : X) (z : Z) : ℝ :=
  ∑ i, η x i * ψ z i

/-- Lemma 6: `ε_direct(η, ψ) = E[(η(X)ᵀψ(Z̃) - g⋆(X, Z̃))²]` with `(X, Z̃) ∼ p_X ⊗ p_Z`, as an
element of `[0, ∞]`. -/
def epsDirect (ν : Measure (X × Z)) {m : ℕ} (η : X → Fin m → ℝ) (ψ : Z → Fin m → ℝ) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal ((innerEmb η ψ p.1 p.2 - densityRatio ν p.1 p.2) ^ 2) ∂(ν.fst.prod ν.snd)

/-- Theorem 10: the excess landmark loss `ε_opt,lm = L_lm(f) - L_lm(log ∘ g⋆)`. The term
`L_lm(log ∘ g⋆)` is written in odds form as `L_direct(g⋆)`, which equals it and keeps the
correct value `0` of the loss at points where `g⋆ = 0`. -/
def epsOptLm (ν : Measure (X × Z)) (f : X → Z → ℝ) : ℝ :=
  lossLm ν f - lossDirect ν (densityRatio ν)

/-- Theorem 11: the excess direct loss `ε_opt,direct = L_direct((x, z) ↦ η(x)ᵀψ(z)) - L_direct(g⋆)`. -/
def epsOptDirect (ν : Measure (X × Z)) {m : ℕ} (η : X → Fin m → ℝ) (ψ : Z → Fin m → ℝ) : ℝ :=
  lossDirect ν (innerEmb η ψ) - lossDirect ν (densityRatio ν)

section Hidden

variable {H : Type*} [MeasurableSpace H]

/-- Section 4: `H ∼ ρH` renders `X` and `Z` conditionally independent, with conditional laws
`κX h` of `X` and `κZ h` of `Z` given `H = h`: `p_{X,Z} = ∫ p_{X|H}(· | h) ⊗ p_{Z|H}(· | h) dp_H(h)`. -/
def IsHiddenVariable (ν : Measure (X × Z)) (ρH : Measure H) (κX : Kernel H X) (κZ : Kernel H Z)
    [IsSFiniteKernel κX] [IsSFiniteKernel κZ] : Prop :=
  ν = ρH.bind (κX ×ₖ κZ)

/-- Lemma 7: the variance of `p_{X|H}(X | H̄) p_{Z|H}(Z̃ | H̄) / (p_X(X) p_Z(Z̃))` with
`(X, Z̃, H̄) ∼ p_X ⊗ p_Z ⊗ p_H`, as an element of `[0, ∞]`; each ratio `p_{X|H}(x | h) / p_X(x)` is
the Radon–Nikodym derivative of `κX h` with respect to `p_X`. -/
def hiddenVar [MeasurableSpace.CountableOrCountablyGenerated H X]
    [MeasurableSpace.CountableOrCountablyGenerated H Z] (ν : Measure (X × Z)) (ρH : Measure H)
    (κX : Kernel H X) (κZ : Kernel H Z) : ℝ≥0∞ :=
  evariance
    (fun t : X × Z × H =>
      (Kernel.rnDeriv κX (Kernel.const H ν.fst) t.2.2 t.1).toReal *
        (Kernel.rnDeriv κZ (Kernel.const H ν.snd) t.2.2 t.2.1).toReal)
    (ν.fst.prod (ν.snd.prod ρH))

end Hidden

/-- Section 3.3: the Gaussian model `H ∼ N(0, σ²)`, `X | H ∼ N(H, 1)`, `Z | H ∼ N(H, 1)`,
`X ⊥ Z | H`, with `v = σ²`: the law of `(H + E₁, H + E₂)` for independent `H ∼ N(0, σ²)`,
`E₁, E₂ ∼ N(0, 1)`. -/
def gaussianModel (v : ℝ≥0) : Measure (ℝ × ℝ) :=
  ((gaussianReal 0 v).prod ((gaussianReal 0 1).prod (gaussianReal 0 1))).map
    (fun t => (t.1 + t.2.1, t.1 + t.2.2))

end MultiViewRedundancy


