-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenCol
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenCol
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:44.317247+00:00
-- url     : https://prove2.me/theorems/688f9be3-8feb-4425-b4b5-bb089ae3ca89
-- title:
--   Gen Col
-- statement:
--   Definitions and structural lemmas for Gen Col, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SymplecticGenerators/SymplecticCharacters/GenCol.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}
def ColsFixed (k : ℕ) (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) : Prop :=
  ∀ i : Fin g, (i : ℕ) < k →
    (∀ r, M r (Sum.inl i) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl i)) ∧
    (∀ r, M r (Sum.inr i) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inr i))
theorem vecMulVec_sq {u v : Fin g → ℤ} (h : v ⬝ᵥ u = 0) : vecMulVec u v * vecMulVec u v = 0 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
  have e : ∑ l, u a * v l * (u l * v b) = u a * v b * (v ⬝ᵥ u) := by
    rw [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [e, h, mul_zero]
def rkU (u v : Fin g → ℤ) (h : v ⬝ᵥ u = 0) : (Matrix (Fin g) (Fin g) ℤ)ˣ where
  val := 1 + vecMulVec u v
  inv := 1 - vecMulVec u v
  val_inv := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, vecMulVec_sq h]; abel
  inv_val := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, vecMulVec_sq h]; abel
end ReciprocityTheory.ChartRestriction.G.Key.Chi


