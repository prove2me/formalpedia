-- Prove2me | Definitions.Def_BMPV1173_Verification_Problems
-- name    : BMPV1173_Verification_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T23:02:51.184195+00:00
-- url     : https://prove2.me/theorems/87d6ef96-4f3e-4f24-b12f-e399ad3f011b
-- title:
--   Boolean matrix verification, single-list orthogonality, and triangle predicates
-- statement:
--   Defines square Boolean input matrices, their OR-of-AND product, verification and its two entrywise inequalities. Orthogonal Vectors uses a single indexed list and distinct indices, including repeated equal vectors. Triangle inputs are symmetric with zero diagonal. All input coordinates are individual bits; a selector distinguishes the three verification matrices.
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, Definitions 2.1 and 2.4; §2.1, printed pp.13–14 = PDF pp.13–14.

import Definitions.Def_QAlgorithms_Defs_Query
import Mathlib

/-! Operational problems from Gilani–Le Gall–Zhou, STOC 2027 submission #1173,
§2.1, printed/PDF pp.13–14. All oracle answers are single bits. -/
namespace BMPV1173.Verification

abbrev MatrixIndex (n : ℕ) := Fin n × Fin n
abbrev VerificationIndex (n : ℕ) := Fin 3 × MatrixIndex n
abbrev VerificationInput (n : ℕ) := VerificationIndex n → Bool
abbrev VectorInput (n : ℕ) := MatrixIndex n → Bool

noncomputable def booleanProduct {n : ℕ} (x : VerificationInput n) (i j : Fin n) : Bool := by
  classical
  exact decide (∃ k : Fin n, x (0, i, k) = true ∧ x (1, k, j) = true)

noncomputable def bmpv {n : ℕ} (x : VerificationInput n) : Bool := by
  classical
  exact decide (∀ i j : Fin n, booleanProduct x i j = x (2, i, j))

noncomputable def bmpvLE {n : ℕ} (x : VerificationInput n) : Bool := by
  classical
  exact decide (∀ i j : Fin n, booleanProduct x i j = true → x (2, i, j) = true)

noncomputable def bmpvGE {n : ℕ} (x : VerificationInput n) : Bool := by
  classical
  exact decide (∀ i j : Fin n, x (2, i, j) = true → booleanProduct x i j = true)

noncomputable def ov {n : ℕ} (x : VectorInput n) : Bool := by
  classical
  exact decide (∃ i j : Fin n, i ≠ j ∧ ∀ k : Fin n,
    ¬ (x (i, k) = true ∧ x (j, k) = true))

def SimpleGraphInput {n : ℕ} (x : MatrixIndex n → Bool) : Prop :=
  (∀ i, x (i, i) = false) ∧ ∀ i j, x (i, j) = x (j, i)

noncomputable def triangle {n : ℕ} (x : MatrixIndex n → Bool) : Bool := by
  classical
  exact decide (∃ i j k : Fin n, i ≠ j ∧ j ≠ k ∧ k ≠ i ∧
    x (i, j) = true ∧ x (j, k) = true ∧ x (k, i) = true)

end BMPV1173.Verification


