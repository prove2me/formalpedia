-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:42.707195+00:00
-- url     : https://prove2.me/theorems/ad2b757d-4693-4b0a-870d-471685da4a80
-- title:
--   Lemma A2indep Of
-- statement:
--   Definitions and structural lemmas for Lemma A2indep Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LemmaA2indepOf.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
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
namespace A3ev
def Cols {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (N : ℕ) (F : Finset ℤ) : Prop :=
  ∀ c ∉ F,
    (∀ (R : Type) [CommRing R] (Xr : ℕ → Fin n → R), pathWord isVec μ c Xr N = oneF) ∧
    ∀ I : ℤ → Finset (Fin n), IsIndex (μ N) I → I c = ∅
def invT {A : Type*} [CommRing A] {n : ℕ} (G : (Matrix (Fin n) (Fin n) A)ˣ) :
    (Matrix (Fin n) (Fin n) A)ˣ where
  val := (↑G⁻¹ : Matrix (Fin n) (Fin n) A).transpose
  inv := (↑G : Matrix (Fin n) (Fin n) A).transpose
  val_inv := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
def extF {n : ℕ} (F : Finset ℤ) (p : ∀ c ∈ F, Finset (Fin n)) : ℤ → Finset (Fin n) :=
  fun c => if h : c ∈ F then p c h else ∅
def term {L : Type} [CommRing L] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (N : ℕ)
    (F : Finset ℤ) (g gi : Matrix (Fin n) (Fin n) L) (I I' : ℤ → Finset (Fin n)) :
    MvPolynomial (ℕ × Fin n) L :=
  (∏ c ∈ F, pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) L)) N (I' c)) *
    C (∏ c ∈ F, minorF (if 1 ≤ c then g else gi.transpose) (I' c) (I c))
end A3ev
namespace A3ev
def psum {n : ℕ} (ν : Fin n → ℤ) (j : ℕ) : ℤ := ∑ m ∈ univ.filter (fun m : Fin n => m.val < j), ν m
def height {n : ℕ} (ν : Fin n → ℤ) : ℤ := ∑ j ∈ range (n + 1), psum ν j
theorem genMat_det_ne (k : Type*) [Field k] (n : ℕ) : (genMat k n).det ≠ 0 := by
  have : genMat k n = (algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)).mapMatrix
      (Matrix.mvPolynomialX (Fin n) (Fin n) k) := by
    ext a b
    simp [genMat, Matrix.mvPolynomialX]
  rw [this, ← RingHom.map_det]
  exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
    (Matrix.det_mvPolynomialX_ne_zero (Fin n) k)
def genU (k : Type*) [Field k] (n : ℕ) : (Matrix (Fin n) (Fin n) (GenField k n))ˣ where
  val := genMat k n
  inv := (genMat k n)⁻¹
  val_inv := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (genMat_det_ne k n))
  inv_val := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (genMat_det_ne k n))
def evC (k : Type) [Field k] (n : ℕ) (isVec : ℕ → Bool) (ν : Fin n → ℤ) :
    MvPolynomial (ℕ × Fin n) k →ₗ[k] MvPolynomial (ℕ × Fin n) (GenField k n) :=
  ((weightedHomogeneousComponent (R := GenField k n) (torusW isVec) ν).restrictScalars k) ∘ₗ
    ((actAll isVec (genMat k n) (genMat k n)⁻¹).toLinearMap.restrictScalars k) ∘ₗ
      (mapAlgHom (σ := ℕ × Fin n) (Algebra.ofId k (GenField k n))).toLinearMap
def fam (k : Type) [Field k] {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} (x : PathIdx n N isVec B) :
    MvPolynomial (ℕ × Fin n) (GenField k n) :=
  brk (genMat k n) (genMat k n)⁻¹ (x.1.1 N) x.1.2 •
    psiPath (GenField k n) isVec x.1.1 N (canIdx (x.1.1 N))
end A3ev
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


