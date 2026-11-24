-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:18.812796+00:00
-- url     : https://prove2.me/theorems/1ceb6193-4aaf-44ab-a1e3-d7b462c5d548
-- title:
--   Gen Space
-- statement:
--   Definitions and structural lemmas for Gen Space, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_genMat_det_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace GS
section Slices
variable {k : Type*} [Field k] {σ : Type*}
variable {A B D : Type*} [CommRing A] [CommRing B] [CommRing D] [Algebra k A] [Algebra k B] [Algebra k D]
def slcFun (θ : A →ₗ[k] B) (P : MvPolynomial σ A) : MvPolynomial σ B :=
  ∑ e ∈ P.support, monomial e (θ (coeff e P))
theorem coeff_slcFun (θ : A →ₗ[k] B) (P : MvPolynomial σ A) (e : σ →₀ ℕ) :
    coeff e (slcFun θ P) = θ (coeff e P) := by
  classical
  simp only [slcFun, coeff_sum, coeff_monomial, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · push Not at h
    simp [h]
def slc (θ : A →ₗ[k] B) : MvPolynomial σ A →ₗ[k] MvPolynomial σ B where
  toFun := slcFun θ
  map_add' P Q := by
    ext e
    simp [coeff_slcFun]
  map_smul' c P := by
    ext e
    simp [coeff_slcFun]
@[simp] theorem coeff_slc (θ : A →ₗ[k] B) (P : MvPolynomial σ A) (e : σ →₀ ℕ) :
    coeff e (slc θ P) = θ (coeff e P) := coeff_slcFun θ P e
def slMap (P : MvPolynomial σ A) : (A →ₗ[k] k) →ₗ[k] MvPolynomial σ k where
  toFun ℓ := slc ℓ P
  map_add' ℓ ℓ' := by
    ext e
    simp
  map_smul' c ℓ := by
    ext e
    simp
def slSpace (P : MvPolynomial σ A) : Submodule k (MvPolynomial σ k) := LinearMap.range (slMap (k := k) P)
end Slices
section Sharp
variable {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
variable {A B : Type*} [CommRing A] [CommRing B]
variable {isVec S}
variable (isVec S)
end Sharp
section Universal
variable (k : Type*) [Field k] (n : ℕ)
def uDet : MvPolynomial (Fin n × Fin n) k := (Matrix.mvPolynomialX (Fin n) (Fin n) k).det
abbrev UR := Localization.Away (uDet k n)
def uMat : Matrix (Fin n) (Fin n) (UR k n) :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) k).map (algebraMap (MvPolynomial (Fin n × Fin n) k) (UR k n))
theorem uMat_det : IsUnit (uMat k n).det := by
  have : (uMat k n).det = algebraMap (MvPolynomial (Fin n × Fin n) k) (UR k n) (uDet k n) := by
    exact (RingHom.map_det (algebraMap (MvPolynomial (Fin n × Fin n) k) (UR k n))
      (Matrix.mvPolynomialX (Fin n) (Fin n) k)).symm
  rw [this]
  exact IsLocalization.Away.algebraMap_isUnit _
variable {k n}
variable {B : Type*} [CommRing B] [Algebra k B]
theorem eval_uDet (g₀ : Matrix (Fin n) (Fin n) B) :
    aeval (fun p : Fin n × Fin n => g₀ p.1 p.2) (uDet k n) = g₀.det := by
  unfold uDet
  rw [AlgHom.map_det]
  congr 1
  exact Matrix.mvPolynomialX_mapMatrix_aeval k g₀
def uAlg (k : Type*) [Field k] {n : ℕ} {B : Type*} [CommRing B] [Algebra k B]
    (g₀ : Matrix (Fin n) (Fin n) B) (h : IsUnit g₀.det) : UR k n →ₐ[k] B :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (uDet k n))
    (f := aeval (fun p : Fin n × Fin n => g₀ p.1 p.2))
    (by
      rintro ⟨_, m, rfl⟩
      rw [map_pow, eval_uDet]
      exact h.pow m)
theorem genMat_isUnit : IsUnit (genMat k n).det := isUnit_iff_ne_zero.mpr (genMat_det_ne k n)
end Universal
section Act
variable {k : Type*} [Field k] {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
def rho (G : MvPolynomial (LVar ι ζ n) k) : MvPolynomial (LVar ι ζ n) (UR k n) :=
  sharpHom isVec S (uMat k n) (uMat k n)⁻¹ (map (algebraMap k (UR k n)) G)
def ev1 (k : Type*) [Field k] (n : ℕ) : UR k n →ₐ[k] k :=
  uAlg k (1 : Matrix (Fin n) (Fin n) k) (by simp)
end Act
section Torus
variable {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
def wV : LVar ι ζ n → (Fin n → ℤ)
  | Sum.inl (i, a) => if i ∈ S then (if isVec i then Pi.single a 1 else Pi.single a (-1)) else 0
  | Sum.inr _ => 0
abbrev wt (e : LVar ι ζ n →₀ ℕ) : Fin n → ℤ := Finsupp.weight (wV isVec S) e
variable (A : Type*) [CommRing A]
abbrev TR (n : ℕ) := AddMonoidAlgebra A (Fin n → ℤ)
def dt (n : ℕ) : Matrix (Fin n) (Fin n) (TR A n) :=
  Matrix.diagonal fun a => AddMonoidAlgebra.single (Pi.single a 1) 1
def dti (n : ℕ) : Matrix (Fin n) (Fin n) (TR A n) :=
  Matrix.diagonal fun a => AddMonoidAlgebra.single (Pi.single a (-1)) 1
theorem dt_mul_dti : dt A n * dti A n = 1 := by
  rw [dt, dti, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  rw [AddMonoidAlgebra.single_mul_single, ← Pi.single_add, mul_one, AddMonoidAlgebra.one_def]
  simp
theorem dt_det : IsUnit (dt A n).det := Matrix.isUnit_det_of_right_inverse (dt_mul_dti A)
variable {A}
variable {k : Type*} [Field k] [Algebra k A]
def cf (ν : Fin n → ℤ) : TR A n →ₗ[k] A where
  toFun y := y.coeff ν
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end Torus
section Weights
variable {k : Type*} [Field k] {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
def cT (k : Type*) [Field k] (n : ℕ) : UR k n →ₐ[k] TR (UR k n) n :=
  IsScalarTower.toAlgHom k (UR k n) (TR (UR k n) n)
theorem cT_det : IsUnit (dt (UR k n) n * (uMat k n).map (cT k n : UR k n →+* TR (UR k n) n)).det := by
  rw [Matrix.det_mul]
  refine (dt_det _).mul ?_
  have : ((uMat k n).map (cT k n : UR k n →+* TR (UR k n) n)).det =
      (cT k n : UR k n →+* TR (UR k n) n) (uMat k n).det := (RingHom.map_det _ _).symm
  rw [this]
  exact (uMat_det k n).map _
def prF (k : Type*) [Field k] (n : ℕ) (ν : Fin n → ℤ) : UR k n →ₗ[k] UR k n :=
  cf ν ∘ₗ (uAlg k _ (cT_det (k := k) (n := n))).toLinearMap
def pm (k : Type*) [Field k] {n : ℕ} (π : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) k :=
  Matrix.of fun b a => if π b = a then 1 else 0
def pv (π : Equiv.Perm (Fin n)) : LVar ι ζ n → LVar ι ζ n
  | Sum.inl (i, a) => if i ∈ S then Sum.inl (i, π⁻¹ a) else Sum.inl (i, a)
  | Sum.inr z => Sum.inr z
end Weights
section Exponents
variable {k : Type*} [Field k] {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
def ant (k : Type*) [Field k] (n : ℕ) : UR k n →ₐ[k] UR k n :=
  uAlg k (uMat k n)⁻¹ (Matrix.isUnit_nonsing_inv_det _ (uMat_det k n))
variable (φ : MvPolynomial (LVar ι ζ n) k →ₗ[k] MvPolynomial (LVar ι ζ n) k)
  (φL : MvPolynomial (LVar ι ζ n) (GenField k n) →ₗ[GenField k n] MvPolynomial (LVar ι ζ n) (GenField k n))
  (h1 : ∀ f, φL (map (genφ k n) f) = map (genφ k n) (φ f))
  (h2 : ∀ f, genPoint isVec S (φ f) = φL (genPoint isVec S f))
include h1 h2
end Exponents
end GS
open GS
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


