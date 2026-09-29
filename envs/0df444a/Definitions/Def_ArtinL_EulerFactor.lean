-- Prove2me | Definitions.Def_ArtinL_EulerFactor
-- name    : ArtinL_EulerFactor
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/0498d10c-2585-5f7a-8f5d-b310c33d8e6b
-- title:
--   Reverse characteristic polynomials and Artin L-series of a Galois representation
-- statement:
--   For an endomorphism $T$ of a finite-dimensional $K$-vector space $W$, [`ArtinL.charpolyRev T`](../def/ArtinL_EulerFactor.html#L14) is the reverse characteristic polynomial $\det(1 - X\,T)$, defined as `Matrix.charpolyRev` of the matrix of $T$ in the basis `Module.finBasis K W`. It is identified with the reverse of `LinearMap.charpoly T`, hence computed by the matrix of $T$ in any finite basis; its coefficient at $0$ is $1$, its coefficient at $1$ is $-\operatorname{tr}_K T$, its degree is at most $\dim_K W$, it is nonzero, it is unchanged under transport along a linear equivalence $e$ (via `e.conj`), and for $A \in M_m(K)$ acting by `Matrix.mulVecLin` it agrees with `A.charpolyRev`. A companion lemma in the `Matrix` namespace evaluates the $2\times 2$ case as $1 - \operatorname{tr}(A)X + \det(A)X^2$.
--
--   The remaining definitions concern a homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, realised as $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`, to $\mathrm{GL}_n(\mathbb C)$, acting on $\mathbb C^n$ through $\sigma \mapsto$ multiplication by the matrix $\rho(\sigma)$. For a subgroup $H$, `invariantsUnder ρ H` is the subspace of vectors fixed by $\rho(H)$, and `inertiaInvariants ρ A` is this subspace for $H =$ `A.inertiaSubgroupIn ℚ`, the image in the full Galois group of the inertia subgroup of a valuation subring $A \subset \overline{\mathbb Q}$. Given $A$ and $\sigma$, `eulerFactorAt ρ A σ` is $\det(1 - X\,\rho(\sigma))$ computed on the restriction of $\rho(\sigma)$ to the inertia invariants when that subspace is preserved, and $1$ otherwise. Then `eulerFactor ρ p` is `eulerFactorAt` evaluated at a choice of valuation subring $A$ with $p$ a nonunit of $A$ together with a choice of $\sigma$ acting as $x \mapsto x^p$ on the residue field of $A$, and $1$ when no such pair exists. Inverting this polynomial as a power series gives `coeffPrimePow ρ p k`; `coeff ρ m` is the product of these over the prime factorisation of $m$, with value $0$ at $m=0$ and $1$ at $m=1$, and `LSeries ρ s` is Mathlib's $L$-series $\sum_{m\ge 1} a(m)m^{-s}$ of this arithmetic function. Both `eulerFactorAt` and `eulerFactor` have constant coefficient $1$.
--
--   **Relation to Mathlib.** [`ArtinL.charpolyRev`](../def/ArtinL_EulerFactor.html#L14) packages Mathlib's `Matrix.charpolyRev` for endomorphisms, in parallel with Mathlib's `LinearMap.charpoly`; [`ArtinL.LSeries`](../def/ArtinL_EulerFactor.html#L98) is Mathlib's `LSeries` applied to the coefficient function defined here. Mathlib has no notion of Artin local factor or Artin $L$-function, and the inertia and Frobenius vocabulary used (`inertiaSubgroupIn`, `LiesOverPrime`, `IsFrobeniusAt`) is the project's own layer on Mathlib's valuation-theoretic decomposition and inertia subgroups.
--
--   **Where it is used.** This vocabulary supplies the local Euler factors, Dirichlet coefficients and $L$-series attached to a complex two-dimensional Galois representation, as needed to state the comparison between such $L$-functions and those of weight-one modular forms that enters the modularity side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ArtinL_EulerFactor.lean

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_Deformations_MatrixRepresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open Polynomial
open scoped MatrixGroups

namespace ArtinL

def charpolyRev {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (T : W →ₗ[K] W) : K[X] :=
  (LinearMap.toMatrix (Module.finBasis K W) (Module.finBasis K W) T).charpolyRev

section charpolyRev

variable {K W W' : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup W'] [Module K W'] [FiniteDimensional K W']

theorem charpolyRev_eq_reverse_charpoly (T : W →ₗ[K] W) :
    charpolyRev T = (LinearMap.charpoly T).reverse := by
  rw [charpolyRev, ← Matrix.reverse_charpoly, LinearMap.charpoly_toMatrix]

theorem charpolyRev_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K W)
    (T : W →ₗ[K] W) : (LinearMap.toMatrix b b T).charpolyRev = charpolyRev T := by
  rw [charpolyRev_eq_reverse_charpoly, ← Matrix.reverse_charpoly, LinearMap.charpoly_toMatrix]

@[simp] theorem coeff_charpolyRev_zero (T : W →ₗ[K] W) : (charpolyRev T).coeff 0 = 1 := by
  rw [charpolyRev, coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]

@[simp] theorem coeff_charpolyRev_one (T : W →ₗ[K] W) :
    (charpolyRev T).coeff 1 = -LinearMap.trace K W T := by
  rw [charpolyRev, Matrix.coeff_charpolyRev_eq_neg_trace,
    LinearMap.trace_eq_matrix_trace K (Module.finBasis K W)]

theorem natDegree_charpolyRev_le (T : W →ₗ[K] W) :
    (charpolyRev T).natDegree ≤ Module.finrank K W := by
  rw [charpolyRev_eq_reverse_charpoly]
  exact (reverse_natDegree_le _).trans (LinearMap.charpoly_natDegree T).le

theorem charpolyRev_conj (e : W ≃ₗ[K] W') (T : W →ₗ[K] W) :
    charpolyRev (e.conj T) = charpolyRev T := by
  rw [charpolyRev_eq_reverse_charpoly, charpolyRev_eq_reverse_charpoly, LinearEquiv.charpoly_conj]

theorem charpolyRev_ne_zero (T : W →ₗ[K] W) : charpolyRev T ≠ 0 := fun h => by
  simpa [h] using coeff_charpolyRev_zero T

theorem charpolyRev_mulVecLin {m : ℕ} (A : Matrix (Fin m) (Fin m) K) :
    charpolyRev (Matrix.mulVecLin A) = A.charpolyRev := by
  rw [← charpolyRev_toMatrix (Pi.basisFun K (Fin m)), ← Matrix.toLin'_apply',
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

theorem _root_.Matrix.charpolyRev_fin_two (A : Matrix (Fin 2) (Fin 2) K) :
    A.charpolyRev = 1 - C A.trace * X + C A.det * X ^ 2 := by
  rw [Matrix.charpolyRev, Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp [Matrix.smul_apply]
  ring

end charpolyRev

variable {n : ℕ}

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

def invariantsUnder (ρ : Γℚ →* GL (Fin n) ℂ) (H : Subgroup Γℚ) : Submodule ℂ (Fin n → ℂ) :=
  Representation.invariants ((Deformation.matrixRepresentation ρ).comp H.subtype)

abbrev inertiaInvariants (ρ : Γℚ →* GL (Fin n) ℂ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) : Submodule ℂ (Fin n → ℂ) :=
  invariantsUnder ρ (A.inertiaSubgroupIn ℚ)

open scoped Classical in

def eulerFactorAt (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (σ : Γℚ) : ℂ[X] :=
  if h : ∀ v ∈ inertiaInvariants ρ A,
      Deformation.matrixRepresentation ρ σ v ∈ inertiaInvariants ρ A then
    charpolyRev ((Deformation.matrixRepresentation ρ σ).restrict h)
  else 1

open scoped Classical in

def eulerFactor (ρ : Γℚ →* GL (Fin n) ℂ) (p : ℕ) : ℂ[X] :=
  if h : ∃ A : ValuationSubring (AlgebraicClosure ℚ), ∃ σ : Γℚ,
      A.LiesOverPrime p ∧ A.IsFrobeniusAt σ p then
    eulerFactorAt ρ h.choose h.choose_spec.choose
  else 1

def coeffPrimePow (ρ : Γℚ →* GL (Fin n) ℂ) (p k : ℕ) : ℂ :=
  PowerSeries.coeff k ((eulerFactor ρ p : PowerSeries ℂ)⁻¹)

def coeff (ρ : Γℚ →* GL (Fin n) ℂ) (m : ℕ) : ℂ :=
  if m = 0 then 0 else m.factorization.prod fun p k => coeffPrimePow ρ p k

def LSeries (ρ : Γℚ →* GL (Fin n) ℂ) (s : ℂ) : ℂ :=
  _root_.LSeries (coeff ρ) s

@[simp] theorem coeff_zero (ρ : Γℚ →* GL (Fin n) ℂ) : coeff ρ 0 = 0 := by
  simp [coeff]

@[simp] theorem coeff_one (ρ : Γℚ →* GL (Fin n) ℂ) : coeff ρ 1 = 1 := by
  simp [coeff]

@[simp] theorem coeff_eulerFactorAt_zero (ρ : Γℚ →* GL (Fin n) ℂ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : Γℚ) : (eulerFactorAt ρ A σ).coeff 0 = 1 := by
  unfold eulerFactorAt
  split_ifs <;> simp

@[simp] theorem coeff_eulerFactor_zero (ρ : Γℚ →* GL (Fin n) ℂ) (p : ℕ) :
    (eulerFactor ρ p).coeff 0 = 1 := by
  unfold eulerFactor
  split_ifs <;> simp

end ArtinL

end


