-- Prove2me | Definitions.Def_EquivMapsEnt_Detect_Basic
-- name    : EquivMapsEnt_Detect_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:23:28.497996+00:00
-- url     : https://prove2.me/theorems/8006bfc5-66ae-4cfa-aba4-098edc584aa6
-- title:
--   Definitions 2.1(ii) and (17): equivariance, positivity, and detection sets
-- statement:
--   A complex linear map $\phi:M_n(\mathbb C)\to M_N(\mathbb C)$ is **$t$-positive** when $\mathrm{id}_t\otimes\phi$ sends every positive semidefinite matrix on $\mathbb C^t\otimes\mathbb C^n$ to a positive semidefinite matrix. It is **unitarily equivariant** when each unitary $U\in U_n$ has a unitary $V\in U_N$ for which
--
--   $$\phi(UXU^*)=V\phi(X)V^*\quad\text{for every }X\in M_n(\mathbb C).$$
--
--   A **density matrix** on $\mathbb C^m\otimes\mathbb C^n$ is positive semidefinite and has trace one. Its **detection set** for $\phi$ is
--
--   $$S_m(\phi)=\{\rho\ge 0:\operatorname{Tr}\rho=1,\ (\mathrm{id}_m\otimes\phi)(\rho)\ge 0\}.$$
--
--   These definitions supply the finite matrix interface for Theorem 5.1. The ancillary factor comes first, so $\phi$ acts on the second factor.
-- source:
--   Bardet, Collins & Sapra, Characterization of equivariant maps and application to entanglement detection, arXiv:1811.08193v3, pp. 2–3 and 12, Definition 2.1(ii) and equation (17)

import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity

namespace EquivMapsEnt.Detect

open scoped Matrix ComplexOrder

/-- Positivity after adjoining a `t`-dimensional identity factor. -/
def IsTPositive {n : ℕ} {ι : Type*} [Fintype ι] (t : ℕ)
    (φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ) : Prop :=
  ∀ X : Matrix (Fin t × Fin n) (Fin t × Fin n) ℂ, X.PosSemidef →
    (QAlgorithms.idTensorSuperop (R := Fin t) (⇑φ) X).PosSemidef

/-- Definition 2.1(ii): one output unitary for each input unitary, valid for all matrices. -/
def IsUnitarilyEquivariant {n N : ℕ}
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin N) ℂ,
    ∀ X, Φ (U * X * star U) = V * Φ X * star V

/-- Density operators on `ℂ^m ⊗ ℂ^n`, with the ancillary factor first. -/
def densityMatrices (m n : ℕ) : Set (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :=
  {ρ | ρ.PosSemidef ∧ ρ.trace = 1}

/-- Equation (17), with the map acting on the second tensor factor. -/
def detectionSet (m : ℕ) {n : ℕ} {ι : Type*} [Fintype ι]
    (φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ) :
    Set (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :=
  {ρ | ρ ∈ densityMatrices m n ∧
    (QAlgorithms.idTensorSuperop (R := Fin m) (⇑φ) ρ).PosSemidef}

end EquivMapsEnt.Detect


