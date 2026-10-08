-- Prove2me | Definitions.Def_LiebThirring
-- name    : LiebThirring
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:17.280614+00:00
-- url     : https://prove2.me/theorems/5dd61638-5b12-475a-827d-746c7811843f
-- statement:
--   The file develops a sharp Lieb–Thirring inequality for one-dimensional Schrödinger operators −d²/dx² − W. H1 is the form domain H¹(ℝ;ℂ): an L² function val together with an L² function grad that is its weak derivative, meaning ∫ val·φ′ = −∫ grad·φ for every compactly supported smooth test function φ. l2Pairing(u,v) is ∫ conj(u)v, and schrodingerForm(W,u,v) is ∫ conj(u′)v′ − ∫ W conj(u)v. A function u in H1 is a negative eigenfunction at energy −k² if k>0 and schrodingerForm(W,v,u) = −k² l2Pairing(v,u) for every v in H1 (a weak eigenvalue equation). negativeMoment(γ,W) is the supremum, in [0,∞], over all finite orthonormal families of such eigenfunctions with parameters k_i, of ∑ k_i^{2γ}; this equals the sum over negative eigenvalues with multiplicity and does not presuppose finiteness. oneStateMoment(γ,W) is the analogous supremum over a single normalized eigenfunction. A potential W is Admissible for γ if it is almost everywhere nonnegative and lies in L^{γ+1/2}. potentialMass(γ,W) is ∫ W^{γ+1/2}. The semiclassical constant is Γ(γ+1)/(2√π Γ(γ+3/2)), and sharpConstant(γ) = 2((γ−1/2)/(γ+1/2))^{γ−1/2} times it. optimalConstant and oneStateConstant are the suprema of negativeMoment/potentialMass and oneStateMoment/potentialMass over admissible W of positive mass. equalityPotential(γ)(x) = (r+1)/cosh²(r x) with r = 1/(γ−1/2). MainClaim is a defined proposition, not an established theorem. It says that for every γ with 1/2<γ<3/2: negativeMoment(γ,W) ≤ sharpConstant(γ)·potentialMass(γ,W) for all admissible W; both optimalConstant and oneStateConstant equal sharpConstant(γ); the equality potential is admissible with positive mass; and it attains equality in the bound.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/LiebThirring.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/LiebThirring.lean; bytes 16..3754
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI


/-!
The form domain is H¹(R;C), represented by an L² function together with its L²
weak derivative. Null-set changes do not affect any definition below.
`negativeMoment` is the extended nonnegative sum over negative eigenvalues,
counting multiplicities: equivalently the supremum over all finite orthonormal
families of weak eigenfunctions of the form. This does not assume in advance
finiteness of the moment or a finite number of eigenvalues.
-/


noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix

namespace SharpLiebThirring

structure H1 where
  val : ℝ → ℂ
  grad : ℝ → ℂ
  val_memLp : MemLp val 2 volume
  grad_memLp : MemLp grad 2 volume
  weak_derivative : ∀ φ : ℝ → ℂ, ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
    (∫ x : ℝ, val x * deriv φ x) = -(∫ x : ℝ, grad x * φ x)

def l2Pairing (u v : H1) : ℂ := ∫ x : ℝ, star (u.val x) * v.val x

/-- The polarized form of -d²/dx² - W, on exactly H¹. -/
def schrodingerForm (W : ℝ → ℝ) (u v : H1) : ℂ :=
  (∫ x : ℝ, star (u.grad x) * v.grad x) -
    ∫ x : ℝ, (W x : ℂ) * star (u.val x) * v.val x

/-- Weak eigenfunction at the negative energy -k². -/
def IsNegativeEigenfunction (W : ℝ → ℝ) (k : ℝ) (u : H1) : Prop :=
  0 < k ∧ ∀ v : H1, schrodingerForm W v u = -(k ^ 2 : ℝ) * l2Pairing v u

def IsOrthonormalFamily {N : ℕ} (u : Fin N → H1) : Prop :=
  ∀ i j, l2Pairing (u i) (u j) = if i = j then 1 else 0

/-- An unlimited finite-family-size supremum, in ℝ≥0∞, includes the entire sum. -/
def negativeMoment (γ : ℝ) (W : ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ (N : ℕ) (u : Fin N → H1) (k : Fin N → ℝ)
    (_ : IsOrthonormalFamily u) (_ : ∀ i, IsNegativeEigenfunction W (k i) (u i)),
      ∑ i, (ENNReal.ofReal (k i)) ^ (2 * γ)

/-- The moment retaining at most one negative eigenvalue. -/
def oneStateMoment (γ : ℝ) (W : ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ (u : H1) (k : ℝ) (_ : l2Pairing u u = 1)
    (_ : IsNegativeEigenfunction W k u), (ENNReal.ofReal k) ^ (2 * γ)

def Admissible (γ : ℝ) (W : ℝ → ℝ) : Prop :=
  (∀ᵐ x : ℝ, 0 ≤ W x) ∧ MemLp W (ENNReal.ofReal (γ + 1 / 2)) volume

def potentialMass (γ : ℝ) (W : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ, (ENNReal.ofReal (W x)) ^ (γ + 1 / 2)

def semiclassicalConstant (γ : ℝ) : ℝ :=
  Real.Gamma (γ + 1) / (2 * Real.sqrt Real.pi * Real.Gamma (γ + 3 / 2))

def sharpConstant (γ : ℝ) : ℝ :=
  2 * ((γ - 1 / 2) / (γ + 1 / 2)) ^ (γ - 1 / 2) * semiclassicalConstant γ

def optimalConstant (γ : ℝ) : ℝ≥0∞ :=
  ⨆ (W : ℝ → ℝ) (_ : Admissible γ W) (_ : 0 < potentialMass γ W),
    negativeMoment γ W / potentialMass γ W

def oneStateConstant (γ : ℝ) : ℝ≥0∞ :=
  ⨆ (W : ℝ → ℝ) (_ : Admissible γ W) (_ : 0 < potentialMass γ W),
    oneStateMoment γ W / potentialMass γ W

def equalityPotential (γ : ℝ) (x : ℝ) : ℝ :=
  let r := (γ - 1 / 2)⁻¹
  (r + 1) * (Real.cosh (r * x))⁻¹ ^ 2

/-- The full spectral bound, optimal constants, and attainment at the explicit potential. -/
def MainClaim : Prop :=
  ∀ γ : ℝ, 1 / 2 < γ → γ < 3 / 2 →
    (∀ W : ℝ → ℝ, Admissible γ W →
      negativeMoment γ W ≤ ENNReal.ofReal (sharpConstant γ) * potentialMass γ W) ∧
    optimalConstant γ = ENNReal.ofReal (sharpConstant γ) ∧
    oneStateConstant γ = ENNReal.ofReal (sharpConstant γ) ∧
    Admissible γ (equalityPotential γ) ∧
    0 < potentialMass γ (equalityPotential γ) ∧
    negativeMoment γ (equalityPotential γ) =
      ENNReal.ofReal (sharpConstant γ) * potentialMass γ (equalityPotential γ)



end SharpLiebThirring
end
end OAI


