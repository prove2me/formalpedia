-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:43:50.5568+00:00
-- url     : https://prove2.me/theorems/1e13699b-06e3-4237-8692-c81dd230005e
-- title:
--   Statements Grass
-- statement:
--   Definitions and structural lemmas for Statements Grass, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsGrass.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open Matrix Finset
open scoped ComplexOrder
noncomputable section
def onePipe {R : Type*} [CommRing R] {j m : ℕ} (Z : Matrix (Fin j) (Fin m) R) :
    Matrix (Fin j) (Fin (j + m)) R :=
  Matrix.of fun a => Fin.append ((1 : Matrix (Fin j) (Fin j) R) a) (Z a)
def colsOf {R : Type*} {j N : ℕ} (A : Matrix (Fin j) (Fin N) R)
    (I : {I : Finset (Fin N) // I.card = j}) : Matrix (Fin j) (Fin j) R :=
  A.submatrix id (I.1.orderEmbOfFin I.2)
def rowsOf {R : Type*} {j N : ℕ} (B : Matrix (Fin N) (Fin j) R)
    (I : {I : Finset (Fin N) // I.card = j}) : Matrix (Fin j) (Fin j) R :=
  B.submatrix (I.1.orderEmbOfFin I.2) id
def CauchyBinet.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (j N : ℕ) (A : Matrix (Fin j) (Fin N) R) (B : Matrix (Fin N) (Fin j) R),
    (A * B).det = ∑ I : {I : Finset (Fin N) // I.card = j}, (colsOf A I).det * (rowsOf B I).det
def PlueckerNormSq.Statement : Prop :=
  ∀ (j m : ℕ) (Z : Matrix (Fin j) (Fin m) ℂ),
    ((∑ I : {I : Finset (Fin (j + m)) // I.card = j}, ‖(colsOf (onePipe Z) I).det‖ ^ 2 : ℝ) : ℂ) =
      (1 + Z * Zᴴ).det
def HadamardPSD.Statement : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.PosSemidef → ‖A.det‖ ≤ ∏ i, ‖A i i‖
def PlueckerUnitBound.Statement : Prop :=
  ∀ (j m : ℕ) (Z : Matrix (Fin j) (Fin m) ℂ), (∀ a b, ‖Z a b‖ = 1) →
    ‖(1 + Z * Zᴴ).det‖ ≤ (1 + m : ℝ) ^ j
def PlueckerKernel.Statement : Prop :=
  ∀ (j m : ℕ) (Z : Matrix (Fin j) (Fin m) ℂ), (∀ a b, ‖Z a b‖ = 1) →
    ∑ I : {I : Finset (Fin (j + m)) // I.card = j}, ‖(colsOf (onePipe Z) I).det‖ ^ 2 ≤
      (1 + m : ℝ) ^ j
def RootsOfUnityDense.Statement : Prop :=
  ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℂ),
    (∀ z : Fin n → ℂ, (∀ i, ∃ k : ℕ, 0 < k ∧ z i ^ k = 1) → MvPolynomial.eval z P = 0) → P = 0
example : ∀ a b, ‖(!![1, Complex.I] : Matrix (Fin 1) (Fin 2) ℂ) a b‖ = 1 := by
  intro a b
  fin_cases a; fin_cases b <;> simp
example : (1 : Matrix (Fin 2) (Fin 2) ℂ).PosSemidef := PosSemidef.one
example (Z : Matrix (Fin 1) (Fin 2) ℂ) : (1 + Z * Zᴴ).PosSemidef :=
  PosSemidef.one.add (posSemidef_self_mul_conjTranspose Z)
example : ∀ i, ∃ k : ℕ, 0 < k ∧ (![1, -1] : Fin 2 → ℂ) i ^ k = 1 := by
  intro i
  refine ⟨2, by norm_num, ?_⟩
  fin_cases i <;> simp
end
end GroundTheory.Heights₂.Heights


