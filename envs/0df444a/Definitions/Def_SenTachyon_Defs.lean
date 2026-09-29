-- Prove2me | Definitions.Def_SenTachyon_Defs
-- name    : SenTachyon_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T18:23:48.083362+00:00
-- url     : https://prove2.me/theorems/65a1c27f-74ec-4cb8-9eb2-e4bbb4ec3225
-- title:
--   Definitions for Sen (1998): brane–antibrane on T², T-duality, U(2) gauge fields
-- statement:
--   Shared definitions for the formalization of A. Sen, *Tachyon condensation on the brane antibrane system* (JHEP 08 (1998) 012). Units: $\alpha'=1$, all lengths and masses in string units.
--
--   1. **Pauli matrix** $\sigma_3=\begin{pmatrix}1&0\\0&-1\end{pmatrix}$.
--   2. **Torus area** $V(R_1,R_2)=4\pi^2R_1R_2$ of $T^2=S^1\times S^1$ with radii $R_1,R_2$.
--   3. **Unit-flux magnetic field** (eq. (1)): $F_{12}=2\pi/V$.
--   4. **T-duality** (eqs. (2), (3)): $\tilde R_i=1/R_i$ and $\tilde g=g/(R_1R_2)$.
--   5. **D-brane tension** $1/(4\pi^2 g)$ and the **mass of two D2-branes** with zero field strength on a torus of radii $R_1,R_2$ and coupling $g$: $2\cdot\frac{1}{4\pi^2 g}\cdot 4\pi^2R_1R_2$.
--   6. **Minimum mass** $M(R_1,R_2,g)$: the two-brane mass evaluated on the dual torus, i.e. with radii $1/R_1,1/R_2$ and coupling $g/(R_1R_2)$ (eq. (9) re-expressed through eqs. (2), (3)); and the **energy per unit area** $M/(4\pi^2R_1R_2)$ (eq. (11)).
--   7. **Gauge fields.** A $U(2)$ gauge field on the plane $\mathbb R^2\ni x=(x^1,x^2)$ is a pair $(A_1,A_2)$ of $2\times2$ complex-matrix-valued functions; $\partial_\mu$ is the entrywise partial derivative. The **gauge transform** is
--   $$(\Omega\circ A)_\mu=\Omega A_\mu\Omega^{-1}-i\,(\partial_\mu\Omega)\,\Omega^{-1},$$
--   and the **field strength** is $F_{12}=\partial_1A_2-\partial_2A_1-i[A_1,A_2]$.
--   8. **Background field** (eq. (4)) on the dual torus with radii $\tilde R_1,\tilde R_2$: $A_1=0$, $A_2=2\pi x^1\sigma_3/\tilde V$ with $\tilde V=4\pi^2\tilde R_1\tilde R_2$.
--   9. **Transition functions** (eq. (6)): $\Omega_1=\exp(i x^2\sigma_3/\tilde R_2)$ (matrix exponential) and $\Omega_2=1$.
--
--   These definitions fix the objects and conventions that all theorems of the mission refer to.
--
--   **Formalization Note** The gauge-field index $\mu\in\{1,2\}$ of the paper is `Fin 2` with $1\mapsto 0$, $2\mapsto 1$. Matrix inverse is Mathlib's `Matrix.inv` (which returns $0$ for singular matrices). Real divisions follow Lean's convention $a/0=0$; all theorems assume positive radii and coupling where relevant. The sign convention of the gauge transform was chosen so that the background (4) satisfies the boundary conditions (5) with the transition functions (6), as the paper asserts.
-- source:
--   A. Sen, Tachyon condensation on the brane antibrane system, JHEP 08 (1998) 012, arXiv:hep-th/9805170, https://doi.org/10.1088/1126-6708/1998/08/012, pp. 1–3, eqs. (1)–(11)

import Mathlib

/-!
# Definitions for Sen, "Tachyon condensation on the brane antibrane system" (JHEP 08 (1998) 012)

Units: `α' = 1`, all lengths and masses in string units.
Coordinates on the (dual) torus are `x = (x¹, x²) : ℝ × ℝ`; the gauge-field index `μ : Fin 2`
uses `0` for the paper's direction `1` and `1` for the paper's direction `2`.
Matrix-valued fields are functions `ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℂ`.
-/

namespace SenTachyon

/-- The Pauli matrix `σ₃ = diag(1, -1)`. -/
def pauli3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Area `V = 4π² R₁ R₂` of the torus `S¹ × S¹` with radii `R₁, R₂`. -/
noncomputable def torusArea (R₁ R₂ : ℝ) : ℝ := 4 * Real.pi ^ 2 * R₁ * R₂

/-- Eq. (1): the magnetic field `F₁₂ = 2π / V` of one unit of flux on the torus. -/
noncomputable def unitFluxField (R₁ R₂ : ℝ) : ℝ := 2 * Real.pi / torusArea R₁ R₂

/-- Eq. (2): the T-dual radius `R̃ = 1 / R`. -/
noncomputable def dualRadius (R : ℝ) : ℝ := 1 / R

/-- Eq. (3): the T-dual coupling `g̃ = g / (R₁ R₂)`. -/
noncomputable def dualCoupling (g R₁ R₂ : ℝ) : ℝ := g / (R₁ * R₂)

/-- Tension `1 / (4π² g)` of a D-brane with string coupling `g`. -/
noncomputable def dbraneTension (g : ℝ) : ℝ := 1 / (4 * Real.pi ^ 2 * g)

/-- Total mass `2 · tension(g) · area(R₁, R₂)` of two D2-branes with zero field strength
wrapped on a torus of radii `R₁, R₂` with coupling `g`. -/
noncomputable def twoBraneMass (R₁ R₂ g : ℝ) : ℝ := 2 * dbraneTension g * torusArea R₁ R₂

/-- The mass at the classical minimum, computed on the T-dual torus (radii `1/R₁, 1/R₂`,
coupling `g/(R₁R₂)`), as a function of the original parameters `R₁, R₂, g`. -/
noncomputable def minimumMass (R₁ R₂ g : ℝ) : ℝ :=
  twoBraneMass (dualRadius R₁) (dualRadius R₂) (dualCoupling g R₁ R₂)

/-- Energy per unit area `M / (4π² R₁ R₂)` on the original torus at the minimum. -/
noncomputable def minimumEnergyDensity (R₁ R₂ g : ℝ) : ℝ :=
  minimumMass R₁ R₂ g / torusArea R₁ R₂

/-- Standard basis vector of `ℝ × ℝ` in direction `μ` (`0 ↦ (1,0)`, `1 ↦ (0,1)`). -/
def coordVec (μ : Fin 2) : ℝ × ℝ := if μ = 0 then (1, 0) else (0, 1)

/-- Entrywise partial derivative `∂_μ f` of a matrix-valued function on `ℝ × ℝ`. -/
noncomputable def partialDeriv (μ : Fin 2) (f : ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (x : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => fderiv ℝ (fun y => f y i j) x (coordVec μ)

/-- A `U(2)` gauge field on `ℝ × ℝ`: its components `A_μ`, `μ ∈ {0, 1}`. -/
abbrev GaugeField := Fin 2 → ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℂ

/-- Gauge transform `(Ω ∘ A)_μ = Ω A_μ Ω⁻¹ - i (∂_μ Ω) Ω⁻¹`. -/
noncomputable def gaugeTransform (Ω : ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℂ) (A : GaugeField) :
    GaugeField :=
  fun μ x => Ω x * A μ x * (Ω x)⁻¹ - Complex.I • (partialDeriv μ Ω x * (Ω x)⁻¹)

/-- Field strength `F₁₂ = ∂₁ A₂ - ∂₂ A₁ - i [A₁, A₂]` (paper's indices 1, 2 = `0`, `1`). -/
noncomputable def fieldStrength (A : GaugeField) (x : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  partialDeriv 0 (A 1) x - partialDeriv 1 (A 0) x
    - Complex.I • (A 0 x * A 1 x - A 1 x * A 0 x)

/-- Eq. (4): background field on the dual torus of radii `R̃₁, R̃₂`:
`A₁ = 0`, `A₂ = 2π x¹ σ₃ / Ṽ`, `Ṽ = 4π² R̃₁ R̃₂`. -/
noncomputable def backgroundField (R₁t R₂t : ℝ) : GaugeField :=
  fun μ x => if μ = 0 then 0 else ((2 * Real.pi * x.1 / torusArea R₁t R₂t : ℝ) : ℂ) • pauli3

/-- Eq. (6): transition function `Ω₁ = exp(i x² σ₃ / R̃₂)` (matrix exponential). -/
noncomputable def omega1 (R₂t : ℝ) (x : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  NormedSpace.exp ((Complex.I * ((x.2 / R₂t : ℝ) : ℂ)) • pauli3)

/-- Eq. (6): transition function `Ω₂ = 1`. -/
def omega2 (_x : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℂ := 1

end SenTachyon


