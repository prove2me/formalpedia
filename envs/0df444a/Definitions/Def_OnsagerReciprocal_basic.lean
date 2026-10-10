-- Prove2me | Definitions.Def_OnsagerReciprocal_basic
-- name    : OnsagerReciprocal_basic
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:25:20.496775+00:00
-- url     : https://prove2.me/theorems/bb2c3754-d3c9-448c-a1ff-4651ea36bba4
-- title:
--   Onsager reciprocal relations: Gaussian fluctuations, relaxation and kinetic coefficients
-- statement:
--   Basic objects of the abstract (Landau–Lifshitz) formulation of the Onsager reciprocal relations, all living in the namespace `OnsagerReciprocal`.
--
--   Let $x=(x_1,\dots,x_n)\in\mathbb R^n$ be fluctuations of $n$ thermodynamic quantities from their equilibrium values, and let $\beta$ be a real $n\times n$ matrix (in the source, $\beta_{ik}=-\frac1k\,\partial^2 S/\partial x_i\partial x_k$, a positive definite symmetric matrix) and $\lambda$ a real $n\times n$ matrix (the relaxation matrix in $\dot x_i=-\lambda_{ik}x_k$).
--
--   1. **Fluctuation weight.** $w_\beta(x)=\exp\!\big(-\tfrac12\,\beta_{ik}x_ix_k\big)$ (Einstein summation), the unnormalized Gaussian probability density of the fluctuations.
--   2. **Equilibrium average.** For $f:\mathbb R^n\to\mathbb R$,
--   $$\langle f\rangle_\beta=\frac{\int_{\mathbb R^n} f(x)\,w_\beta(x)\,dx}{\int_{\mathbb R^n} w_\beta(x)\,dx}.$$
--   3. **Conjugate quantities.** $X_i=\beta_{ik}x_k$.
--   4. **Mean relaxation.** $\xi(t;x_0)=e^{-t\lambda}x_0$, the mean value at time $t$ of the fluctuation that takes the value $x_0$ at $t=0$ (the solution of $\dot\xi=-\lambda\xi$, $\xi(0)=x_0$); and $\Xi(t;x_0)=\beta\,\xi(t;x_0)$.
--   5. **Kinetic coefficients.** $\gamma=\lambda\beta^{-1}$, i.e. $\gamma_{ik}=\lambda_{il}(\beta^{-1})_{lk}$.
--   6. **Time correlation.** $C_{ik}(t)=\langle x_i(t)\,x_k(0)\rangle=\langle \xi_i(t;x)\,x_k\rangle_\beta$.
--
--   These are the objects in which Onsager's principle $\gamma_{ik}=\gamma_{ki}$ and the intermediate steps of its proof are stated.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ` with the product Lebesgue measure. The average is a ratio of Bochner integrals, so it returns junk values ($0$) if an integrand is not integrable; all theorems using it assume $\beta$ positive definite, which makes every integrand used integrable. The matrix inverse `β⁻¹` is Mathlib's `Matrix.inv` (zero for singular matrices). The entropy $S$ and Boltzmann's constant are not modelled: $\beta$ is taken as the primitive datum, exactly as in the source's statement of the principle.
-- source:
--   Wikipedia, "Onsager reciprocal relations", https://en.wikipedia.org/w/index.php?title=Onsager_reciprocal_relations&oldid=1355014688, section "Abstract formulation" and its "Proof" subsection (pp. 5-6 of the PDF export), following L. D. Landau, E. M. Lifshitz, Statistical Physics, Part 1 (1975). Definitions: w = Ã exp(-½ β_ik x_i x_k); X_i = β_ik x_k; ẋ_i = -λ_ik x_k; γ_ik = λ_il β⁻¹_lk; mean values ξ_i(t), Ξ_i(t) (Proof).

import Mathlib

/-!
# Onsager reciprocal relations — basic objects (abstract formulation)

Source: Wikipedia, "Onsager reciprocal relations", section "Abstract formulation" and its
"Proof" subsection (oldid=1355014688), following Landau–Lifshitz, *Statistical Physics, Part 1*.

* `x = (x₁, …, xₙ)` are fluctuations from equilibrium, distributed with the (unnormalized)
  Gaussian weight `w(x) = exp(-½ βᵢₖ xᵢ xₖ)`.
* `Xᵢ = βᵢₖ xₖ` are the thermodynamic conjugate quantities.
* In the quasi-stationary regime `ẋ = -λ x`; the mean value of the fluctuation at time `t`,
  starting from the value `x₀` at `t = 0`, is `ξ(t) = exp(-t λ) x₀`, and `Ξ(t) = β ξ(t)`.
* `γ = λ β⁻¹` are the kinetic coefficients.
-/

namespace OnsagerReciprocal

open Matrix MeasureTheory

variable {n : ℕ}

/-- The unnormalized Gaussian fluctuation weight `w(x) = exp(-½ ∑ᵢₖ βᵢₖ xᵢ xₖ)`. -/
noncomputable def fluctuationWeight (β : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  Real.exp (-(1 / 2) * (x ⬝ᵥ (β *ᵥ x)))

/-- The equilibrium average `⟨f⟩ = (∫ f(x) w(x) dx) / (∫ w(x) dx)` with respect to the
Gaussian fluctuation distribution (Lebesgue measure on `ℝⁿ`). -/
noncomputable def fluctuationAverage (β : Matrix (Fin n) (Fin n) ℝ)
    (f : (Fin n → ℝ) → ℝ) : ℝ :=
  (∫ x, f x * fluctuationWeight β x) / ∫ x, fluctuationWeight β x

/-- The thermodynamic conjugate quantities `Xᵢ = βᵢₖ xₖ`. -/
def conjugate (β : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  β *ᵥ x

/-- The mean value `ξ(t) = exp(-t λ) x₀` of the fluctuation at time `t`, given that it takes
the value `x₀` at `t = 0`; it is the solution of `ξ̇ = -λ ξ`, `ξ(0) = x₀`. -/
noncomputable def meanFluctuation (lam : Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (x₀ : Fin n → ℝ) : Fin n → ℝ :=
  NormedSpace.exp ((-t) • lam) *ᵥ x₀

/-- The mean value `Ξ(t) = β ξ(t)` of the conjugate quantities at time `t`. -/
noncomputable def meanConjugate (β lam : Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (x₀ : Fin n → ℝ) : Fin n → ℝ :=
  β *ᵥ meanFluctuation lam t x₀

/-- The kinetic coefficients `γ = λ β⁻¹`, i.e. `γᵢₖ = λᵢₗ (β⁻¹)ₗₖ`. -/
noncomputable def kineticCoeff (β lam : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  lam * β⁻¹

/-- The time correlation `⟨xᵢ(t) xₖ(0)⟩ = ⟨ξᵢ(t) xₖ⟩` in the equilibrium ensemble. -/
noncomputable def timeCorrelation (β lam : Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (i k : Fin n) : ℝ :=
  fluctuationAverage β (fun x => meanFluctuation lam t x i * x k)

end OnsagerReciprocal


