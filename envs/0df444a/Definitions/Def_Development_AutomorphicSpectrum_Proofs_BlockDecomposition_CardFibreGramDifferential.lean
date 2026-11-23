-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFibreGramDifferential
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFibreGramDifferential
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:27:23.906261+00:00
-- url     : https://prove2.me/theorems/c0ef9bfc-ef14-4782-bfe8-f62507490942
-- title:
--   Card Fibre Gram Differential
-- statement:
--   Definitions and structural lemmas for Card Fibre Gram Differential, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardFibreGramDifferential.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatricesCardStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
namespace GlobalTheory.CompanionTheory.UnrDens.GramDiff
variable {E : Type} [CommRing E] (τ : E →+* E)
theorem cT_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E) :
    cT τ (A * B) = cT τ B * cT τ A := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]
theorem cT_add {a b : ℕ} (A B : Matrix (Fin a) (Fin b) E) :
    cT τ (A + B) = cT τ A + cT τ B := by
  ext i j
  simp [cT]
theorem cT_zero {a b : ℕ} : cT τ (0 : Matrix (Fin a) (Fin b) E) = 0 := by
  ext i j
  simp [cT]
theorem cT_neg {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) : cT τ (-A) = -cT τ A := by
  ext i j
  simp [cT]
theorem cT_cT (hτ : ∀ a, τ (τ a) = a) {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) :
    cT τ (cT τ A) = A := by
  ext i j
  simp [cT, hτ]
theorem cT_cross (hτ : ∀ a, τ (τ a) = a) {m n : ℕ} {S : Matrix (Fin m) (Fin m) E} (hS : cT τ S = S)
    (x y : Matrix (Fin m) (Fin n) E) : cT τ (cT τ x * S * y) = cT τ y * S * x := by
  rw [cT_mul, cT_mul, cT_cT τ hτ, hS, Matrix.mul_assoc]
def hermSub (n : ℕ) : AddSubgroup (Matrix (Fin n) (Fin n) E) where
  carrier := {H | cT τ H = H}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [cT_add, ha, hb]
  zero_mem' := cT_zero τ
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [cT_neg, ha]
def diffMap (hτ : ∀ a, τ (τ a) = a) {m n : ℕ} (S : Matrix (Fin m) (Fin m) E) (hS : cT τ S = S)
    (x : Matrix (Fin m) (Fin n) E) : Matrix (Fin m) (Fin n) E →+ hermSub τ n :=
  AddMonoidHom.mk'
    (fun y => ⟨cT τ y * S * x + cT τ x * S * y, by
      change cT τ (cT τ y * S * x + cT τ x * S * y) = cT τ y * S * x + cT τ x * S * y
      rw [cT_add, cT_cross τ hτ hS, cT_cross τ hτ hS, add_comm]⟩)
    (by
      intro a b
      apply Subtype.ext
      change cT τ (a + b) * S * x + cT τ x * S * (a + b) =
        (cT τ a * S * x + cT τ x * S * a) + (cT τ b * S * x + cT τ x * S * b)
      rw [cT_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add]
      abel)
end GlobalTheory.CompanionTheory.UnrDens.GramDiff


