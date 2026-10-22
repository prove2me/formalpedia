-- Prove2me | Definitions.Def_FermiCap_Gaussian_States
-- name    : FermiCap_Gaussian_States
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:24.591817+00:00
-- url     : https://prove2.me/theorems/ca1159e9-652f-4fa7-8c70-b580fa1ff430
-- title:
--   Density, entropy, Gaussian states and covariance
-- statement:
--   A state is a positive semidefinite matrix of trace one. Its von Neumann entropy $S(\rho)=-\operatorname{Tr}(\rho\log_2\rho)$ is measured in bits, with $0\log_2 0=0$. Binary entropy is $H(t)=-t\log_2t-(1-t)\log_2(1-t)$.
--
--   Definition 1 calls $\rho$ Gaussian when, for $\lambda_j\in[-1,1]$, it has the form
--   $$\rho=U\rho_\lambda U^\dagger,\qquad \rho_\lambda=2^{-n}\prod_j(I+\lambda_j Z_j),\qquad U=\exp(iH_2+iH_1),$$
--   where $H_2$ and $H_1$ are Hermitian complex linear combinations of quadratic and linear Majorana monomials. An even Gaussian state has $H_1=0$ (Definition 2). The covariance is $M_{pq}=-(i/2)\operatorname{Tr}(\rho[c_p,c_q])$. Purity and even parity are represented by density-matrix idempotence and $P\rho=\rho$, respectively.
--
--   These predicates keep general and even Gaussian states distinct and provide the state class used by the capacity formula.
-- source:
--   Bravyi, Classical capacity of fermionic product channels, arXiv:quant-ph/0507282v1, p. 2, binary entropy after Theorem 1; p. 4, eq. (13), Definitions 1–2 and covariance definition; p. 5, eq. (18)

import Mathlib
import Definitions.Def_FermiCap_Gaussian_Majorana
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix

namespace FermiCap.Gaussian

/-- Positive semidefinite, unit-trace density matrices. -/
def IsDensity {n : ℕ} (ρ : Op n) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

/-- Binary entropy in bits. -/
def binEnt (t : ℝ) : ℝ :=
  -(t * Real.logb 2 t) - (1 - t) * Real.logb 2 (1 - t)

/-- The diagonal state ρ_λ of Eq. (13). -/
def rhoLambda (n : ℕ) (lam : Fin n → ℝ) : Op n :=
  (((2 : ℂ) ^ n)⁻¹) •
    ((List.finRange n).map (fun j =>
      (1 : Op n) + (lam j : ℂ) • pauliString (fun k => if k = j then pauliZ else 1))).prod

/-- A Gaussian state in the exact sense of Definition 1: the H₂ and H₁ terms are
Hermitian elements of the complex spans of quadratic and linear Majorana monomials. -/
def IsGaussian {n : ℕ} (ρ : Op n) : Prop :=
  IsDensity ρ ∧ ∃ (lam : Fin n → ℝ) (H₂ H₁ : Op n),
    (∀ j, -1 ≤ lam j ∧ lam j ≤ 1) ∧
    H₂ ∈ Submodule.span ℂ (Set.range
      (fun pq : Fin (2 * n) × Fin (2 * n) => majorana n pq.1 * majorana n pq.2)) ∧
    H₁ ∈ Submodule.span ℂ (Set.range (majorana n)) ∧
    H₂ᴴ = H₂ ∧ H₁ᴴ = H₁ ∧
    let U : Op n := NormedSpace.exp ((Complex.I : ℂ) • (H₂ + H₁))
    ρ = U * rhoLambda n lam * Uᴴ

/-- Even Gaussian states, Definition 2: the linear H₁ term is absent. -/
def IsEvenGaussian {n : ℕ} (ρ : Op n) : Prop :=
  IsDensity ρ ∧ ∃ (lam : Fin n → ℝ) (H₂ : Op n),
    (∀ j, -1 ≤ lam j ∧ lam j ≤ 1) ∧
    H₂ ∈ Submodule.span ℂ (Set.range
      (fun pq : Fin (2 * n) × Fin (2 * n) => majorana n pq.1 * majorana n pq.2)) ∧
    H₂ᴴ = H₂ ∧
    let U : Op n := NormedSpace.exp ((Complex.I : ℂ) • H₂)
    ρ = U * rhoLambda n lam * Uᴴ

/-- Pure states are rank-one density matrices, expressed by idempotence. -/
def IsPure {n : ℕ} (ρ : Op n) : Prop := IsDensity ρ ∧ ρ * ρ = ρ

/-- Pρ=ρ is the projector form of P|ψ⟩=|ψ⟩ for a pure state. -/
def IsEven {n : ℕ} (ρ : Op n) : Prop := parity n * ρ = ρ

/-- Covariance matrix M_pq = -(i/2) Tr(ρ[c_p,c_q]), p. 4. -/
def covariance {n : ℕ} (ρ : Op n) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  fun p q => ((-Complex.I / 2) *
    (ρ * (majorana n p * majorana n q - majorana n q * majorana n p)).trace).re

end FermiCap.Gaussian


