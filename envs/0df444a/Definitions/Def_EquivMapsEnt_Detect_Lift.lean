-- Prove2me | Definitions.Def_EquivMapsEnt_Detect_Lift
-- name    : EquivMapsEnt_Detect_Lift
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:43.722088+00:00
-- url     : https://prove2.me/theorems/b7f7e6fd-bb80-46b5-b2be-dd4f8b430eae
-- title:
--   Equations (20)–(23): the regular action and the fibrewise lift
-- statement:
--   Let $U_n$ be the unitary group of $M_n(\mathbb C)$, let $\mu$ be a finite Borel measure on it, and set $H=L^2(U_n,\mathbb C^N;\mu)$. For $W\in U_n$, the **regular action** is $V(W)\psi(U)=\psi(W^{-1}U)$. For a linear map $\phi:M_n(\mathbb C)\to M_N(\mathbb C)$, the **lift** acts fibrewise by $\Phi(X)\psi(U)=\phi(U^*XU)\psi(U)$ and is represented by its form
--
--   $$F_X(\psi,\chi)=\int_{U_n}\langle\psi(U),\phi(U^*XU)\chi(U)\rangle\,d\mu(U).$$
--
--   The definitions also give the block quadratic form that expresses $t$-positivity of $\Phi$ and the corresponding detection set $S_m(\Phi)$. They let the infinite dimensional intermediate result be compared with finite matrix detectors.
--
--   **Formalization Note** The unitary group has its Borel measurable space. The regular action is an $L^2$ linear isometry when $\mu$ is left invariant. Forms use representatives of almost everywhere classes; their integrals are well defined because the matrix kernel is bounded and the two vectors are in $L^2$ under a finite measure. Indices are ancillary first and start at zero.
-- source:
--   Bardet, Collins & Sapra, Characterization of equivariant maps and application to entanglement detection, arXiv:1811.08193v3, p. 13, equations (20)–(23)

import Mathlib
import Definitions.Def_EquivMapsEnt_Detect_Basic

noncomputable section

namespace EquivMapsEnt.Detect

open MeasureTheory
open scoped Matrix ComplexOrder

instance unitaryMeasurableSpace (n : ℕ) :
    MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ) :=
  borel _

instance unitaryBorelSpace (n : ℕ) :
    BorelSpace (Matrix.unitaryGroup (Fin n) ℂ) := ⟨rfl⟩

/-- The Hilbert space of equation (21). -/
abbrev LiftSpace (n N : ℕ) (μ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) :=
  Lp (EuclideanSpace ℂ (Fin N)) 2 μ

/-- Equation (22): the left regular action on vector-valued square-integrable functions. -/
def regRep {n N : ℕ} (μ : Measure (Matrix.unitaryGroup (Fin n) ℂ))
    [μ.IsMulLeftInvariant]
    (W : Matrix.unitaryGroup (Fin n) ℂ) :
    LiftSpace n N μ →ₗᵢ[ℂ] LiftSpace n N μ :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun U => W⁻¹ * U)
    ⟨(continuous_const_mul (W⁻¹)).measurable, map_mul_left_eq_self μ W⁻¹⟩

/-- The matrix block with fixed ancillary indices. -/
def block {m n : ℕ} (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (i j : Fin m) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun k l => X (i, k) (j, l)

/-- The sesquilinear form of the fibrewise operator in equation (23). -/
def liftForm {n N : ℕ} (φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ]
    Matrix (Fin N) (Fin N) ℂ)
    (μ : Measure (Matrix.unitaryGroup (Fin n) ℂ))
    (X : Matrix (Fin n) (Fin n) ℂ)
    (ψ χ : LiftSpace n N μ) : ℂ :=
  ∫ U, inner ℂ (ψ.1 U)
    ((φ (star (U : Matrix (Fin n) (Fin n) ℂ) * X * (U : Matrix (Fin n) (Fin n) ℂ))).toEuclideanLin
      (χ.1 U)) ∂μ

/-- Positivity of the lift after tensoring by the `t`-dimensional identity. -/
def IsTPositiveLift {n N : ℕ} (t : ℕ)
    (φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ)
    (μ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) : Prop :=
  ∀ X : Matrix (Fin t × Fin n) (Fin t × Fin n) ℂ, X.PosSemidef →
    ∀ ξ : Fin t → LiftSpace n N μ,
      0 ≤ ∑ i : Fin t, ∑ j : Fin t, liftForm φ μ (block X i j) (ξ i) (ξ j)

/-- Equation (17) for the lift of equation (23). -/
def detectionSetLift (m : ℕ) {n N : ℕ}
    (φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ)
    (μ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) :
    Set (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :=
  {ρ | ρ ∈ densityMatrices m n ∧
    ∀ ξ : Fin m → LiftSpace n N μ,
      0 ≤ ∑ i : Fin m, ∑ j : Fin m, liftForm φ μ (block ρ i j) (ξ i) (ξ j)}

end EquivMapsEnt.Detect


