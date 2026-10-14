-- Prove2me | Definitions.Def_MLLangevin_ConvexA2_DriftNorms
-- name    : MLLangevin_ConvexA2_DriftNorms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:30:34.776664+00:00
-- url     : https://prove2.me/theorems/cb395bd1-9db6-4ed4-a27a-eb44a574c407
-- title:
--   (18)–(19), Lemma 5.1–5.2, Proposition 5.1, pp. 11, 29–33 — ‖∇b‖_{2,∞}, ‖∆b‖²_{2,∞}, Υ₂², c₁, β₂, 𝔞₀, 𝔞₁, 𝔞₂ and S(x, γ)
-- statement:
--   This module defines the derivative norms of the drift and the constants of §2.4.2 and §5.1 of Egéa and Panloup.
--
--   Let $b:\mathbb R^d\to\mathbb R^d$, $\sigma,\alpha,L$ real numbers and $x_0,x^\star\in\mathbb R^d$.
--
--   1. **Regularity** (§2.4.2, p. 11): $b$ is $\mathcal C^2$ with bounded partial derivatives up to order 2.
--   2. **Jacobian norm** (p. 32): $\|\nabla b(x)\|_F=\big(\sum_{i,j}|\partial_jb_i(x)|^2\big)^{1/2}$ and $\|\nabla b\|_{2,\infty}=\sup_{x}\|\nabla b(x)\|_F$.
--   3. **Laplacian norm** (p. 31): $\Delta b=(\Delta b_1,\dots,\Delta b_d)$ with $\Delta\phi=\sum_j\partial^2_{x_j^2}\phi$, and $\|\Delta b\|_{2,\infty}^2=\sup_x\sum_i|\Delta b_i(x)|^2$.
--   4. **$\Upsilon_2^2$** (19):
--   $$\Upsilon_2^2=\max\Big(1,\ \frac{1}{\alpha^2}|b(x_0)|^2+\frac{\sigma\sqrt\alpha}{L^3}\|\nabla b\|_{2,\infty}|b(x_0)|+\frac{\sigma^4}{L^4}\|\Delta b\|^2_{2,\infty}+\frac{\sigma^2\alpha d^{1/2}}{L^3}\|\nabla b\|_{2,\infty}+\frac{\sigma^2d}{\alpha}\Big).$$
--   5. **$c_1$** (Lemma 5.1(ii)): $c_1(x)=|x-x^\star|+\sqrt{|b(x^\star)|^2\big(\frac1{L^2}+\frac2{\alpha^2}\big)+\frac{2\sigma^2d}{\alpha}}$.
--   6. **$\beta_2$** (Proposition 5.1(ii)): $\frac32\beta_2(x)=\frac{2L^4}{\alpha^2}|x-x^\star|^2+\mathfrak a_0|b(x^\star)|^2+\sigma\frac{L}{\sqrt\alpha}\|\nabla b\|_{2,\infty}|x-x^\star|+\mathfrak a_1|b(x^\star)|+\mathfrak a_2d$, with $\mathfrak a_0=4\big(\frac{L^2}{\alpha^2}+\frac{L^4}{\alpha^4}\big)$, $\mathfrak a_1=\sigma(\alpha^{-1/2}+\alpha^{-3/2}L)\|\nabla b\|_{2,\infty}$ and $\mathfrak a_2=\frac{\sigma^4}{\alpha^2}\|\Delta b\|^2_{2,\infty}d^{-1}+L\|\nabla b\|_{2,\infty}\sigma^2d^{-1/2}(\alpha^{-1/2}+\alpha^{-1})+\frac{2L^4\sigma^2}{\alpha^3}$.
--   7. **$S(x,\gamma)$** (Lemma 5.2(ii)): for a process $X^x$, $S(x,\gamma)=\sup_{u\in[0,\gamma]}\mathbb E[|b(X^x_u)|^2]^{1/2}\in[0,\infty]$.
--
--   These quantities measure how far the drift is from linear and set the size of every constant in the second-order ($\mathfrak a=2$) analysis.
--
--   **Formalization Note** The paper's display (18) prints $\|\nabla b\|^2_{2,\infty}=\sup_x\|\nabla b(x)\|_F$ and $\|\Delta b\|_{2,\infty}=\sup_x|\Delta b(x)|^2$; the definitions used here are those of pp. 31–32, which the proofs use and which make every formula homogeneous. Regularity is `ContDiff ℝ 2 b` together with a uniform bound on the operator norms of the first and second Fréchet derivatives, equivalent in finite dimension to bounded partial derivatives. The suprema $\|\nabla b\|_{2,\infty}$ and $\|\Delta b\|^2_{2,\infty}$ are real suprema, meaningful only under that bound, which every statement using them assumes. The fraktur constants $\mathfrak a_0,\mathfrak a_1,\mathfrak a_2$ are named `A0`, `A1`, `A2` to avoid a clash with the confluence exponent $\mathfrak a$. At $d=0$, $d^{-1}$ and $d^{-1/2}$ are read as $0$, which is harmless because $\mathfrak a_2$ only enters through $\mathfrak a_2d$. $S$ takes values in $[0,\infty]$ because it may be infinite a priori.
-- source:
--   Egéa–Panloup, arXiv:2109.07753v2, §2.4.2 and (18)–(19), p. 11; ‖∆b‖²_{2,∞} and ‖∇b‖_{2,∞}, pp. 31–32; c₁, Lemma 5.1 (ii), p. 29; S(x, γ), Lemma 5.2 (ii), p. 30; β₂, 𝔞₀, 𝔞₁, 𝔞₂, Proposition 5.1 (ii), p. 33

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_MLLangevin_ConvexA1_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MLLangevin.ConvexA2

open EthierKurtz

/-- `b` is `𝒞²` with bounded partial derivatives up to order 2 (§2.4.2, p. 11), stated with the
operator norms of the first and second Fréchet derivatives (equivalent in finite dimension). -/
def C2Bounded {d : ℕ} (b : SDEState d → SDEState d) : Prop :=
  ContDiff ℝ 2 b ∧ ∃ M : ℝ, ∀ x, ‖fderiv ℝ b x‖ ≤ M ∧ ‖iteratedFDeriv ℝ 2 b x‖ ≤ M

/-- The Frobenius norm `‖∇b(x)‖_F = (Σ_{i,j} |∂_j b_i(x)|²)^{1/2}` of the Jacobian of `b` at `x`
(p. 32), computed column by column: column `j` is `Db(x) e_j`. -/
noncomputable def jacFrob {d : ℕ} (b : SDEState d → SDEState d) (x : SDEState d) : ℝ :=
  Real.sqrt (∑ j : Fin d, ‖fderiv ℝ b x (EuclideanSpace.single j 1)‖ ^ 2)

/-- `‖∇b‖_{2,∞} = sup_x ‖∇b(x)‖_F` (pp. 31–32; pin of (18)). Meaningful when the Jacobian is
bounded (`C2Bounded b`). -/
noncomputable def gradNorm {d : ℕ} (b : SDEState d → SDEState d) : ℝ :=
  ⨆ x, jacFrob b x

/-- The vector of Laplacians `∆b(x) = (∆b_1(x), …, ∆b_d(x))`, `∆φ = Σ_j ∂²_{x_j} φ` (p. 11),
written as `Σ_j D²b(x)(e_j, e_j)`. -/
noncomputable def lapVec {d : ℕ} (b : SDEState d → SDEState d) (x : SDEState d) :
    SDEState d :=
  ∑ j : Fin d,
    iteratedFDeriv ℝ 2 b x ![EuclideanSpace.single j 1, EuclideanSpace.single j 1]

/-- `‖∆b‖²_{2,∞} = sup_x Σ_i |∆b_i(x)|² = sup_x |∆b(x)|²` (p. 31; pin of (18)). Meaningful when the
second derivative is bounded (`C2Bounded b`). -/
noncomputable def lapNormSq {d : ℕ} (b : SDEState d → SDEState d) : ℝ :=
  ⨆ x, ‖lapVec b x‖ ^ 2

/-- `Υ₂²` of (19), p. 11:
`max(1, α⁻²|b(x₀)|² + (σ√α/L³)‖∇b‖_{2,∞}|b(x₀)| + (σ⁴/L⁴)‖∆b‖²_{2,∞}
+ (σ²α d^{1/2}/L³)‖∇b‖_{2,∞} + σ²d/α)`. -/
noncomputable def Upsilon2Sq {d : ℕ} (b : SDEState d → SDEState d) (σ α L : ℝ)
    (x₀ : SDEState d) : ℝ :=
  max 1 ((α ^ 2)⁻¹ * ‖b x₀‖ ^ 2 + σ * Real.sqrt α / L ^ 3 * gradNorm b * ‖b x₀‖
    + σ ^ 4 / L ^ 4 * lapNormSq b + σ ^ 2 * α * Real.sqrt d / L ^ 3 * gradNorm b
    + σ ^ 2 * d / α)

/-- `𝔞₀ = 4(L²/α² + L⁴/α⁴)` (Proposition 5.1 (ii), p. 33). -/
noncomputable def A0 (α L : ℝ) : ℝ :=
  4 * (L ^ 2 / α ^ 2 + L ^ 4 / α ^ 4)

/-- `𝔞₁ = σ(α^{−1/2} + α^{−3/2} L)‖∇b‖_{2,∞}` (Proposition 5.1 (ii), p. 33). -/
noncomputable def A1 {d : ℕ} (b : SDEState d → SDEState d) (σ α L : ℝ) : ℝ :=
  σ * (α ^ (-(1 / 2 : ℝ)) + α ^ (-(3 / 2 : ℝ)) * L) * gradNorm b

/-- `𝔞₂ = (σ⁴/α²)‖∆b‖²_{2,∞} d⁻¹ + L‖∇b‖_{2,∞} σ² d^{−1/2}(α^{−1/2} + α⁻¹) + 2L⁴σ²/α³`
(Proposition 5.1 (ii), p. 33). -/
noncomputable def A2 {d : ℕ} (b : SDEState d → SDEState d) (σ α L : ℝ) : ℝ :=
  σ ^ 4 / α ^ 2 * lapNormSq b * (d : ℝ)⁻¹
    + L * gradNorm b * σ ^ 2 * (Real.sqrt d)⁻¹ * (α ^ (-(1 / 2 : ℝ)) + α⁻¹)
    + 2 * L ^ 4 * σ ^ 2 / α ^ 3

/-- `β₂(x)` of Proposition 5.1 (ii), p. 33, defined by
`(3/2)β₂(x) = (2L⁴/α²)|x − x⋆|² + 𝔞₀|b(x⋆)|² + σ(L/√α)‖∇b‖_{2,∞}|x − x⋆| + 𝔞₁|b(x⋆)| + 𝔞₂ d`. -/
noncomputable def beta2 {d : ℕ} (b : SDEState d → SDEState d) (σ α L : ℝ)
    (xs x : SDEState d) : ℝ :=
  2 / 3 * (2 * L ^ 4 / α ^ 2 * ‖x - xs‖ ^ 2 + A0 α L * ‖b xs‖ ^ 2
    + σ * (L / Real.sqrt α) * gradNorm b * ‖x - xs‖ + A1 b σ α L * ‖b xs‖
    + A2 b σ α L * d)

/-- `S(x, γ) = sup_{u ∈ [0, γ]} 𝔼[|b(X^x_u)|²]^{1/2}` of Lemma 5.2 (ii), p. 30, in `[0, ∞]`. -/
noncomputable def Sfun {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (b : SDEState d → SDEState d) (X : ℝ≥0 → Ω → SDEState d) (γ : ℝ) : ℝ≥0∞ :=
  ⨆ (u : ℝ≥0) (_ : (u : ℝ) ≤ γ), eLpNorm (fun ω => b (X u ω)) 2 P

end MLLangevin.ConvexA2


