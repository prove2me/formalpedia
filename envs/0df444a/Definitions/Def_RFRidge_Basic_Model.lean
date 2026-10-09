-- Prove2me | Definitions.Def_RFRidge_Basic_Model
-- name    : RFRidge_Basic_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T00:47:39.144801+00:00
-- url     : https://prove2.me/theorems/7c335cf4-f2c1-4b59-b4b1-e9f9d5d40801
-- title:
--   §2–§3.1, pp. 4–6, Asm. 3 p. 16, Def. 2 p. 18 — the kernel (6) of random features ψ, the feature map φ_M, the random-features ridge estimator (7), the expected risk, and the assumptions of Theorem 1
-- statement:
--   This file sets up the random-features ridge regression model of Rudi and Rosasco.
--
--   **Kernel (6).** Let $X$ be an input space, $(\Omega,\pi)$ a probability space of features and $\psi:X\times\Omega\to\mathbb R$. The kernel is
--   $$K(x,x')=\int_\Omega \psi(x,\omega)\,\psi(x',\omega)\,d\pi(\omega),\qquad x,x'\in X.$$
--
--   **Feature map.** Given features $\omega_1,\dots,\omega_M\in\Omega$, the random-features map is
--   $$\phi_M(x)=M^{-1/2}\big(\psi(x,\omega_1),\dots,\psi(x,\omega_M)\big)\in\mathbb R^M .$$
--
--   **Estimator (7).** Given data $(x_1,y_1),\dots,(x_n,y_n)\in X\times\mathbb R$, write
--   $$\widehat C_M=\widehat S_M^\top\widehat S_M=\frac1n\sum_{i=1}^n\phi_M(x_i)\phi_M(x_i)^\top,\qquad \widehat S_M^\top\widehat y=\frac1n\sum_{i=1}^n y_i\,\phi_M(x_i).$$
--   For $\lambda>0$ the ridge weights and the estimator are
--   $$\widehat w_{\lambda,M}=(\widehat C_M+\lambda I)^{-1}\widehat S_M^\top\widehat y,\qquad \widehat f_{\lambda,M}(x)=\phi_M(x)^\top\widehat w_{\lambda,M}.$$
--
--   **The adjoint $S_M^*$ (Definition 2).** For a function $g$ on $X$ and a probability measure $\rho_X$ on $X$, $(S_M^*g)_j=M^{-1/2}\int_X\psi(x,\omega_j)\,g(x)\,d\rho_X(x)$.
--
--   **Risk.** For a probability measure $\rho$ on $X\times\mathbb R$, the expected risk of $f:X\to\mathbb R$ is
--   $$\mathcal E(f)=\int (f(x)-y)^2\,d\rho(x,y).$$
--
--   **Assumptions.** *Assumption 3* (random features bounded and continuous): $\kappa\ge1$, $\psi$ is continuous in both variables, and $|\psi(x,\omega)|\le\kappa$ for all $x,\omega$. The *assumptions of Theorem 1* add a bound $b>0$ with $|y|\le b$ for $\rho$-almost every $(x,y)$.
--
--   These objects are the language of Theorem 1 and of Lemmas 1–2.
--
--   **Formalization Note** The feature space $\Omega$ is the type `W`. Features and samples are indexed from $0$ (`Fin M`, `Fin n`). $M^{-1/2}$ is written $(\sqrt M)^{-1}$. For $\lambda>0$ the matrix $\widehat C_M+\lambda I$ is positive definite, so the matrix inverse used is the true inverse. The risk is a Bochner integral. Assumption 3 is stated with an added field: $\psi$ is jointly measurable for the product σ-algebra of $X\times\Omega$, which does not follow from continuity without second countability. The bound $|\psi|\le\kappa$ is stated for every $(x,\omega)$, as in Assumption 3 (Theorem 1 says "almost surely"). Assumption 3's "the associated RKHS is separable" is not a field: the page notes it follows from continuity of $\psi$ and separability of $X$, and $X$ is separable in Theorem 1.
-- source:
--   Rudi & Rosasco, arXiv:1602.04474v5, Eq. (6) p. 4, Eq. (7) p. 5, §3.1 p. 5 (expected risk), Theorem 1 p. 6 (hypotheses), Assumption 3 p. 16, Definition 2 p. 18

import Mathlib

namespace RFRidge.Basic

open MeasureTheory Matrix

/-- The kernel of Eq. (6), p. 4: `K(x, x') = ∫_Ω ψ(x, ω) ψ(x', ω) dπ(ω)`. The feature space `Ω` of the
paper is the type `W`. -/
noncomputable def kernelOf {X W : Type*} [MeasurableSpace W] (π : Measure W) (ψ : X → W → ℝ)
    (x x' : X) : ℝ :=
  ∫ ω, ψ x ω * ψ x' ω ∂π

/-- The random-features map `φ_M(x) = M^{-1/2} (ψ(x, ω₁), …, ψ(x, ω_M))` (§2, p. 4), with the
features indexed `0, …, M − 1`. `M^{-1/2}` is written `(√M)⁻¹`; at `M = 0` there is no feature. -/
noncomputable def featureMap {X W : Type*} (ψ : X → W → ℝ) {M : ℕ} (ω : Fin M → W) (x : X) :
    Fin M → ℝ :=
  fun j => (Real.sqrt M)⁻¹ * ψ x (ω j)

/-- `Ŝ_M^⊤ Ŝ_M = Ĉ_M = (1/n) Σᵢ φ_M(xᵢ) φ_M(xᵢ)^⊤` (§2, p. 5; Definition 2, p. 18), an `M × M` matrix,
for data `z = ((x₀, y₀), …, (x_{n−1}, y_{n−1}))`. -/
noncomputable def empCov {X W : Type*} (ψ : X → W → ℝ) {M : ℕ} (ω : Fin M → W) {n : ℕ}
    (z : Fin n → X × ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  (n : ℝ)⁻¹ • ∑ i, Matrix.vecMulVec (featureMap ψ ω (z i).1) (featureMap ψ ω (z i).1)

/-- `Ŝ_M^⊤ ŷ = (1/n) Σᵢ yᵢ φ_M(xᵢ)` (§2, p. 5). -/
noncomputable def empCross {X W : Type*} (ψ : X → W → ℝ) {M : ℕ} (ω : Fin M → W) {n : ℕ}
    (z : Fin n → X × ℝ) : Fin M → ℝ :=
  (n : ℝ)⁻¹ • ∑ i, (z i).2 • featureMap ψ ω (z i).1

/-- The ridge weights `ŵ_{λ,M} = (Ŝ_M^⊤ Ŝ_M + λI)^{-1} Ŝ_M^⊤ ŷ` of Eq. (7), p. 5. For `λ > 0` the matrix
`Ĉ_M + λI` is positive definite, so `Matrix.inv` is its true inverse (not a junk value). -/
noncomputable def rfWeights {X W : Type*} (ψ : X → W → ℝ) (lam : ℝ) {n : ℕ} (z : Fin n → X × ℝ)
    {M : ℕ} (ω : Fin M → W) : Fin M → ℝ :=
  (empCov ψ ω z + lam • (1 : Matrix (Fin M) (Fin M) ℝ))⁻¹ *ᵥ empCross ψ ω z

/-- The random-features ridge estimator `f̂_{λ,M}(x) = φ_M(x)^⊤ ŵ_{λ,M}` of Eq. (7), p. 5, computed
from the data `z` and the features `ω`. -/
noncomputable def rfEstimator {X W : Type*} (ψ : X → W → ℝ) (lam : ℝ) {n : ℕ} (z : Fin n → X × ℝ)
    {M : ℕ} (ω : Fin M → W) : X → ℝ :=
  fun x => featureMap ψ ω x ⬝ᵥ rfWeights ψ lam z ω

/-- The operator `S_M^*` of Definition 2, p. 18, applied to a function `g` on `X`:
`(S_M^* g)_j = M^{-1/2} ∫_X ψ(x, ω_j) g(x) dρ_X(x)`. -/
noncomputable def featureAdjoint {X W : Type*} [MeasurableSpace X] (ψ : X → W → ℝ)
    (ρX : Measure X) {M : ℕ} (ω : Fin M → W) (g : X → ℝ) : Fin M → ℝ :=
  fun j => (Real.sqrt M)⁻¹ * ∫ x, ψ x (ω j) * g x ∂ρX

/-- The expected risk `E(f) = ∫ (f(x) − y)² dρ(x, y)` (§3.1, p. 5), a Bochner integral. -/
noncomputable def risk {X : Type*} [MeasurableSpace X] (ρ : Measure (X × ℝ)) (f : X → ℝ) : ℝ :=
  ∫ p, (f p.1 - p.2) ^ 2 ∂ρ

/-- Assumption 3, p. 16 (random features bounded and continuous): `κ ≥ 1`, `ψ` jointly continuous,
and `|ψ(x, ω)| ≤ κ` for all `x, ω`. Joint measurability of `ψ` for the product σ-algebra on `X × W` is
an added field: without second countability the Borel σ-algebra of `X × W` can be larger than the
product one, so it does not follow from continuity. -/
structure RFAssumptions {X W : Type*} [TopologicalSpace X] [MeasurableSpace X] [TopologicalSpace W]
    [MeasurableSpace W] (ψ : X → W → ℝ) (κ : ℝ) : Prop where
  one_le_kappa : 1 ≤ κ
  continuous : Continuous (Function.uncurry ψ)
  measurable : Measurable (Function.uncurry ψ)
  bound : ∀ x ω, |ψ x ω| ≤ κ

/-- The hypotheses of Theorem 1, p. 6: Assumption 3 on the features, and `|y| ≤ b` `ρ`-almost surely
with `b > 0`. -/
structure Thm1Assumptions {X W : Type*} [TopologicalSpace X] [MeasurableSpace X] [TopologicalSpace W]
    [MeasurableSpace W] (ψ : X → W → ℝ) (κ : ℝ) (ρ : Measure (X × ℝ)) (b : ℝ) : Prop
    extends RFAssumptions ψ κ where
  b_pos : 0 < b
  y_bound : ∀ᵐ p ∂ρ, |p.2| ≤ b

end RFRidge.Basic


