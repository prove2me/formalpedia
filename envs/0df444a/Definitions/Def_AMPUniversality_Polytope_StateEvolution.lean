-- Prove2me | Definitions.Def_AMPUniversality_Polytope_StateEvolution
-- name    : AMPUniversality_Polytope_StateEvolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:36:45.358277+00:00
-- url     : https://prove2.me/theorems/b8b5c1c9-d5a5-4304-8885-bd5e03fd331f
-- title:
--   Equations (C.1) and (C.11), pp. 60–62 — the state-evolution map F(σ², θ) and the correlation map 𝓕_(α,ε)(Q)
-- statement:
--   Let $\eta(u;\theta)=\operatorname{sign}(u)\,(|u|-\theta)_+$ be soft thresholding, let $p_X$ be a probability measure on $\mathbb R$, let $\delta>0$, and let $X\sim p_X$ and $Z\sim\mathsf N(0,1)$ be independent.
--
--   1. **The state-evolution map (C.1).** For $\sigma^2\ge0$ and $\theta\ge 0$,
--   $$\mathsf F(\sigma^2,\theta)=\frac1\delta\,\mathbb E\big\{[\eta(X+\sigma Z;\theta)-X]^2\big\}.$$
--   The scalar state evolution of the AMP algorithm reads $\sigma_{t+1}^2=\mathsf F(\sigma_t^2,\alpha\sigma_t)$.
--
--   2. **The correlation map (C.11).** Fix $\varepsilon\in(0,1)$, $\alpha>0$ and $p\in[0,\varepsilon]$. Let $X_\infty$ take the value $0$ with probability $1-\varepsilon$, $+\infty$ with probability $p$ and $-\infty$ with probability $\varepsilon-p$, and let $(Z_1,Z_2)$ be an independent centred Gaussian pair with $\mathbb E Z_1^2=\mathbb E Z_2^2=1$ and $\mathbb E Z_1Z_2=Q\in[0,1]$. Then
--   $$\mathcal F_{\alpha,\varepsilon}(Q)=\frac{1}{G_\varepsilon(\alpha)}\,\mathbb E\big\{[\eta(X_\infty+Z_1;\alpha)-X_\infty][\eta(X_\infty+Z_2;\alpha)-X_\infty]\big\},$$
--   where $x\mapsto\eta(x+a;b)-x$ is extended to $x=\pm\infty$ by continuity: its value is $a-b$ at $+\infty$ and $a+b$ at $-\infty$.
--
--   These maps govern the one-dimensional and two-time state-evolution recursions whose fixed-point analysis locates the phase transition.
--
--   **Formalization Note** $\mathsf F$ is written as a function of $s=\sigma^2$, with $\sigma=\sqrt s$; the page defines it for $\theta,\sigma^2>0$, and the same formula at $\sigma^2=\theta=0$ is the value $\mathsf F(0,0)$ that Lemma 7 uses. The expectation over $X_\infty$ is written as the three-atom mixture, with the continuity extension evaluated; the page does not say how the mass $\varepsilon$ splits between $+\infty$ and $-\infty$, so the split $p$ is a parameter. The Gaussian pair is realised as $Z_1=W_1$, $Z_2=QW_1+\sqrt{1-Q^2}\,W_2$ with $W_1,W_2$ independent standard normals. $G_\varepsilon$ is the function of (C.3).
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 60, equation (C.1); p. 62, equation (C.11); p. 41, soft thresholding after (6.7)

import Mathlib
import Definitions.Def_AMPUniversality_Polytope_Recovery
import Definitions.Def_AMPUniversality_Polytope_GEps

set_option autoImplicit false
open MeasureTheory

namespace AMPUniversality.Polytope

/-- (C.1), p. 60: `F(σ², θ) = (1/δ) E{[η(X + σZ; θ) − X]²}` with `X ∼ p_X` and
`Z ∼ N(0,1)` independent, written as a function of `s = σ²` (so `σ = √s`) and of `θ`.
The page defines it for `θ, σ² > 0`; the same formula at `σ² = θ = 0` gives the value
`F(0,0)` used in Lemma 7. -/
noncomputable def seMap (pX : Measure ℝ) (δ s θ : ℝ) : ℝ :=
  (1 / δ) * ∫ p : ℝ × ℝ,
    (softThreshold (p.1 + Real.sqrt s * p.2) θ - p.1) ^ 2
      ∂(pX.prod (ProbabilityTheory.gaussianReal 0 1))

/-- (C.11), p. 62: `𝓕_{α,ε}(Q) = (1/G_ε(α)) E{[η(X_∞ + Z₁; α) − X_∞][η(X_∞ + Z₂; α) − X_∞]}`.
`X_∞` takes the value `0` with probability `1 − ε`, `+∞` with probability `p` and `−∞` with
probability `ε − p`. The map `x ↦ η(x + a; b) − x` extended by continuity equals `a − b` at
`+∞` and `a + b` at `−∞`. The Gaussian pair `(Z₁, Z₂)` with unit variances and correlation `Q`
is realised as `Z₁ = W₁`, `Z₂ = Q W₁ + √(1 − Q²) W₂` with `W₁, W₂` independent standard
normals (for `Q ∈ [0,1]`). -/
noncomputable def lemma10Map (ε p α Q : ℝ) : ℝ :=
  (1 / GEps ε α) * ∫ w : ℝ × ℝ,
    ((1 - ε) * (softThreshold w.1 α *
        softThreshold (Q * w.1 + Real.sqrt (1 - Q ^ 2) * w.2) α) +
      p * ((w.1 - α) * (Q * w.1 + Real.sqrt (1 - Q ^ 2) * w.2 - α)) +
      (ε - p) * ((w.1 + α) * (Q * w.1 + Real.sqrt (1 - Q ^ 2) * w.2 + α)))
      ∂((ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1))

end AMPUniversality.Polytope


