-- Prove2me | Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_CardStabilizerVector
-- name    : Formalism_LogVandermondeBounds_LogVandermondeProofs_CardStabilizerVector
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:55:47.582081+00:00
-- url     : https://prove2.me/theorems/ffd5f9e7-4fd2-41a8-bf9e-06d8721780aa
-- title:
--   Card Stabilizer Vector
-- statement:
--   Definitions and structural lemmas for Card Stabilizer Vector, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/CardStabilizerVector.lean

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.LogVandermondeBounds.StandardLattice
open Finset
def upperEquiv (F : Type) [Field F] (n : ℕ) :
    {A : Matrix (Fin n) (Fin n) F // (∀ i j, j < i → A i j = 0) ∧ ∀ i, A i i = 1} ≃
      ({p : Fin n × Fin n // p.1 < p.2} → F) where
  toFun A p := A.1 p.1.1 p.1.2
  invFun f := ⟨fun i j => if h : i < j then f ⟨(i, j), h⟩ else if i = j then 1 else 0, by
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · simp [not_lt.mpr hji.le, hji.ne']
    · simp⟩
  left_inv A := by
    apply Subtype.ext
    funext i j
    simp only
    split_ifs with h1 h2
    · rfl
    · subst h2; exact (A.2.2 i).symm
    · exact (A.2.1 i j (lt_of_le_of_ne (not_lt.mp h1) (fun h => h2 h.symm))).symm
  right_inv f := by
    funext p
    simp [p.2]
def RowVec (F : Type) (n : ℕ) : Type := Fin n → F
instance rowVecFinite (F : Type) [Finite F] (n : ℕ) : Finite (RowVec F n) :=
  inferInstanceAs (Finite (Fin n → F))
instance rowAction (F : Type) [Field F] (n : ℕ) : MulAction (GL (Fin n) F) (RowVec F n) where
  smul g v := Matrix.vecMul (v : Fin n → F) ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  one_smul v := by
    show Matrix.vecMul (v : Fin n → F)
      (((1 : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = v
    rw [inv_one, Units.val_one]
    exact Matrix.vecMul_one _
  mul_smul g h v := by
    show Matrix.vecMul (v : Fin n → F) (((g * h)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.vecMul (Matrix.vecMul (v : Fin n → F) ((h⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    rw [mul_inv_rev, Units.val_mul]
    exact (Matrix.vecMul_vecMul (v : Fin n → F) _ _).symm
end Formalism.LogVandermondeBounds.StandardLattice


