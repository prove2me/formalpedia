-- Prove2me | Definitions.Def_ProperHalfspace_Gaussian
-- name    : ProperHalfspace_Gaussian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:02:47.86999+00:00
-- url     : https://prove2.me/theorems/4002dfe4-07a2-45cf-930e-120ea84d4ccf
-- title:
--   Gaussian space: multilinear and geometric extensions, $U_\rho$, $A_E$ and $\Gamma_\rho$
-- statement:
--   On $\mathbb R^n$ with the standard Gaussian measure $N(0,I_n)$:
--
--   1. the multilinear extension $\tilde f(z)=\sum_S\hat f(S)\prod_{i\in S}z_i$ of $f:\{\pm1\}^n\to\mathbb R$;
--   2. the geometric extension $h_G(z)=\operatorname{sign}(w\cdot z-\theta)$ of a halfspace;
--   3. the Ornstein–Uhlenbeck operator $U_\rho F(x)=\mathbf E_z[F(\rho x+\sqrt{1-\rho^2}\,z)]$;
--   4. the averaging operator $A_EF(x)=\mathbf E_{z\sim N(0,\Pi_{E^\perp})}[F(\Pi_Ex+z)]$ for a subspace $E$;
--   5. the Gaussian influence PCA matrix $\Gamma_\rho(F)_{ij}=\mathbf E_x[\partial_iU_{\sqrt\rho}F(x)\,\partial_jU_{\sqrt\rho}F(x)]$.
--
--   These carry the comparison between Boolean and Gaussian correlations.
--
--   **Formalization Note** $N(0,I_n)$ is the pushforward to `EuclideanSpace ℝ (Fin n)` of the product of $n$ copies of $N(0,1)$. $A_E$ is written with $\Pi_{E^\perp}g$, $g\sim N(0,I_n)$, which has law $N(0,\Pi_{E^\perp})$. Partial derivatives are `fderiv` in the direction $e_i$.
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), §2.2, pp.12–13; §2.3, p.13; (4), p.19

import Mathlib
import Definitions.Def_ProperHalfspace_Fourier

open MeasureTheory ProbabilityTheory

namespace ProperHalfspace

/-!
# Gaussian space: multilinear and geometric extensions, the Ornstein–Uhlenbeck and averaging operators, `Γ_ρ`

De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026), §2.2, pp.12–13; §2.3, p.13; (4), p.19.

**Formalization Note.** Gaussian space is `EuclideanSpace ℝ (Fin n)` with `N(0, I_n)`, the pushforward of the product of
`n` copies of `N(0,1)`. `A_E f(x)` is written `∫ f(Π_E x + Π_{E⊥} g) dN(0, I_n)(g)`, since `Π_{E⊥} g ∼ N(0, Π_{E⊥})`.
`∂ᵢ` is `fderiv` in the direction `eᵢ`; the operators are applied in the paper only to functions for which the derivative
exists, namely multilinear polynomials.
-/

/-- The standard Gaussian measure `N(0, I_n)` on `ℝⁿ`. -/
noncomputable def stdGauss (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (Measure.pi fun _ : Fin n => gaussianReal 0 1).map (WithLp.toLp 2)

/-- The multilinear extension `f̃(z) = Σ_S f̂(S) Π_{i ∈ S} zᵢ` (p.12). -/
noncomputable def mlExt {n : ℕ} (f : Cube n → ℝ) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ S : Finset (Fin n), fourier f S * ∏ i ∈ S, z i

/-- The geometric extension `h_G(z) = sign(w · z − θ)` (p.13). -/
noncomputable def ltfG {n : ℕ} (w : Fin n → ℝ) (θ : ℝ) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if 0 ≤ ∑ i, w i * z i - θ then 1 else -1

/-- The Ornstein–Uhlenbeck operator `U_ρ F(x) = E_z[F(ρ x + √(1 − ρ²) z)]` (p.13). -/
noncomputable def ouOp {n : ℕ} (ρ : ℝ) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ z, F (ρ • x + Real.sqrt (1 - ρ ^ 2) • z) ∂stdGauss n

/-- The Gaussian averaging operator `A_E F(x) = E_{z ∼ N(0, Π_{E⊥})}[F(Π_E x + z)]` (p.13). -/
noncomputable def avgOp {n : ℕ} (E : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ g, F (E.starProjection x + Eᗮ.starProjection g) ∂stdGauss n

/-- The partial derivative `∂ᵢ G(x)`. -/
noncomputable def partialDeriv {n : ℕ} (i : Fin n) (G : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  fderiv ℝ G x (EuclideanSpace.single i 1)

/-- The Gaussian influence PCA matrix, (4), p.19:
`Γ_ρ(F)_{ij} = E_x[∂ᵢ U_{√ρ}F(x) ∂ⱼ U_{√ρ}F(x)]`. -/
noncomputable def gammaMatrix {n : ℕ} (ρ : ℝ) (F : EuclideanSpace ℝ (Fin n) → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    ∫ x, partialDeriv i (ouOp (Real.sqrt ρ) F) x * partialDeriv j (ouOp (Real.sqrt ρ) F) x ∂stdGauss n

end ProperHalfspace


