-- Prove2me | Definitions.Def_STOC2027BoolCSP_Approximation_Supplement_Fock
-- name    : STOC2027BoolCSP_Approximation_Supplement_Fock
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:31:09.238194+00:00
-- url     : https://prove2.me/theorems/93cf271e-f030-4bd2-aac2-7d403a39a41d
-- title:
--   Multivariate Hermite polynomials, the generating function $F$, Fock norms $\|\cdot\|_u$, $W_j(f)$ and $S_u(f)$
-- statement:
--   Fix a dimension $N$. For a multi-index $\alpha\in\mathbb N^N$ write $|\alpha|=\sum_i\alpha_i$ and $\alpha!=\prod_i\alpha_i!$. The probabilists' multivariate Hermite polynomial is $H_\alpha(x)=\prod_i \mathrm{He}_{\alpha_i}(x_i)$, where $\mathrm{He}_0=1$ and $\mathrm{He}_{n+1}(x)=x\,\mathrm{He}_n(x)-\mathrm{He}_n'(x)$. Let $G\sim N(0,I_N)$.
--
--   For a bounded measurable $f:\mathbb R^N\to\mathbb R$, the **generating function** of (50) is the power series
--   $$F(z)=\sum_\alpha \frac{\mathbb E[f(G)H_\alpha(G)]}{\alpha!}\,z^\alpha .$$
--   For a power series $U$ with real or complex coefficients and a scale $u\ge 0$, the **Fock norm** is
--   $$\|U\|_u^2=\sum_\alpha \alpha!\,u^{|\alpha|}\,\big|[z^\alpha]U\big|^2\in[0,\infty].$$
--   Finally, as in (51),
--   $$W_j(f)=\sum_{|\alpha|=j}\frac{\mathbb E[f(G)H_\alpha(G)]^2}{\alpha!},\qquad S_u(f)=\sum_{j\ge1}u^jW_j(f).$$
--   Products of power series, such as $F^2$, are Cauchy products.
--
--   These are the objects of the Fock product estimate (Lemma 12.1) and of the two-hub negative stability (Theorem 12.2).
--
--   **Formalization Note** Power series are Mathlib's `MvPowerSeries (Fin N) 𝕜` over any `RCLike` field $\mathbb K$ ($\mathbb R$ or $\mathbb C$). The Fock norm, $W_j$ and $S_u$ take values in $[0,\infty]$ (`ℝ≥0∞`), so a divergent series is $\infty$, never a junk value; $\|U\|_u$ is the square root of $\|U\|_u^2$ in $[0,\infty]$. Mathlib's `Polynomial.hermite` is the probabilists' $\mathrm{He}_n$.
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 24–25 (PDF 27–28), §12.1, equations (50)–(52)

import Mathlib

namespace STOC2027BoolCSP.Approximation.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The total degree `|α| = Σ_i α_i` of a multi-index `α ∈ ℕ^N`. -/
def mdeg {N : ℕ} (α : Fin N →₀ ℕ) : ℕ := ∑ i, α i

/-- The multi-index factorial `α! = Π_i α_i!`. -/
def mfact {N : ℕ} (α : Fin N →₀ ℕ) : ℕ := ∏ i, (α i).factorial

/-- The probabilists' multivariate Hermite polynomial `H_α(x) = Π_i He_{α_i}(x_i)` (Mathlib's
`Polynomial.hermite` is the probabilists' `He_n`). -/
noncomputable def hermiteMulti {N : ℕ} (α : Fin N →₀ ℕ) (x : Fin N → ℝ) : ℝ :=
  ∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i))

/-- The standard Gaussian law `N(0, I_N)` on `ℝ^N`. -/
noncomputable def stdGaussN (N : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi fun _ : Fin N => gaussianReal 0 1

/-- The Hermite moment `E[f(G) H_α(G)]`, `G ∼ N(0, I_N)`. -/
noncomputable def hermiteMoment {N : ℕ} (f : (Fin N → ℝ) → ℝ) (α : Fin N →₀ ℕ) : ℝ :=
  ∫ z, f z * hermiteMulti α z ∂stdGaussN N

/-- The generating function `F` of equation (50), as the formal power series with coefficients
`[z^α]F = E[f(G) H_α(G)]/α!`. -/
noncomputable def genSeries {N : ℕ} (f : (Fin N → ℝ) → ℝ) : MvPowerSeries (Fin N) ℝ :=
  fun α => hermiteMoment f α / (mfact α : ℝ)

/-- The squared Fock norm `‖U‖_u² = Σ_α α! u^{|α|} |[z^α]U|²` of a power series, as an extended
nonnegative real (it is `∞` when the series diverges). -/
noncomputable def fockNormSq {N : ℕ} {𝕜 : Type*} [RCLike 𝕜] (U : MvPowerSeries (Fin N) 𝕜)
    (u : ℝ) : ℝ≥0∞ :=
  ∑' α : Fin N →₀ ℕ,
    ENNReal.ofReal ((mfact α : ℝ) * u ^ mdeg α) * (‖MvPowerSeries.coeff α U‖₊ : ℝ≥0∞) ^ 2

/-- The Fock norm `‖U‖_u = (‖U‖_u²)^{1/2}`, valued in `[0, ∞]`. -/
noncomputable def fockNorm {N : ℕ} {𝕜 : Type*} [RCLike 𝕜] (U : MvPowerSeries (Fin N) 𝕜)
    (u : ℝ) : ℝ≥0∞ :=
  fockNormSq U u ^ ((1 : ℝ) / 2)

/-- The level weight `W_j(f) = Σ_{|α| = j} E[f H_α]²/α!` of (51). -/
noncomputable def levelWeight {N : ℕ} (f : (Fin N → ℝ) → ℝ) (j : ℕ) : ℝ≥0∞ :=
  ∑' α : {α : Fin N →₀ ℕ // mdeg α = j},
    ENNReal.ofReal (hermiteMoment f α.1 ^ 2 / (mfact α.1 : ℝ))

/-- The noise stability `S_u(f) = Σ_{j ≥ 1} u^j W_j(f)` of (51), valued in `[0, ∞]`. -/
noncomputable def stab {N : ℕ} (f : (Fin N → ℝ) → ℝ) (u : ℝ) : ℝ≥0∞ :=
  ∑' j : ℕ, if 1 ≤ j then ENNReal.ofReal (u ^ j) * levelWeight f j else 0

end STOC2027BoolCSP.Approximation.Supplement


