-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeneralLinearGroupCharEqOneOfDetEqOne
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeneralLinearGroupCharEqOneOfDetEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:12.857342+00:00
-- url     : https://prove2.me/theorems/781d92ec-901a-4cd4-bfd1-7533902eedb3
-- title:
--   General Linear Group Char Eq One Of Det Eq One
-- statement:
--   Definitions and structural lemmas for General Linear Group Char Eq One Of Det Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GeneralLinearGroupCharEqOneOfDetEqOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open Matrix
section DetOneChar
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
  {A : Type} [CommGroup A]
def ddCharUnip (N : Matrix n n R) (hN : N * N = 0) : GL n R :=
  ⟨1 + N, 1 - N, by simp [add_mul, mul_sub, hN], by simp [sub_mul, mul_add, hN]⟩
def ddCharDiag : (n → Rˣ) →* GL n R :=
  (Units.map (diagonalRingHom n R).toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom
theorem ddChar_vecMulVec_sq {x y : n → R} (h : y ⬝ᵥ x = 0) :
    vecMulVec x y * vecMulVec x y = 0 := by
  ext i j
  have h' : ∑ k, y k * x k = 0 := h
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.zero_apply]
  calc ∑ k, x i * y k * (x k * y j) = x i * y j * ∑ k, y k * x k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = 0 := by rw [h', mul_zero]
end DetOneChar
end GlobalTheory


