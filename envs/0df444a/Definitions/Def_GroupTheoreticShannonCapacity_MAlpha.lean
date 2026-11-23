-- Prove2me | Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
-- name    : GroupTheoreticShannonCapacity_MAlpha
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:26:07.980801+00:00
-- url     : https://prove2.me/theorems/4bdea4d0-e16c-40d4-97a9-9b8a331bdb8d
-- title:
--   MAlpha
-- statement:
--   Definitions and structural lemmas for MAlpha, from jzuiddam/GroupTheoreticShannonCapacity contributors (see pinned LICENSE and source headers)'s pinned Shannon capacity limits from lattice packings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MAlpha.lean

import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
set_option autoImplicit true
namespace GroupTheoreticShannonCapacity.MAlpha
open Matrix
def Mα (n : ℕ) (α : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) < (j : ℕ) then α
    else if (i : ℕ) > (j : ℕ) then -1
    else 0
def Rα (n : ℕ) (α : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if i.val = 0 ∧ j.val = n - 1 then -α
    else if i.val = j.val + 1 then 1
    else 0
def Dα (n : ℕ) (α : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun i => α ^ (i.val : ℕ)
section DetLemmas
end DetLemmas
section DetLemmas2
end DetLemmas2
section ConjugationLemmas
end ConjugationLemmas
section Tests
example : ∀ x y α : ℝ, (x • Rα 2 α + y • 1).det = (-x)^2 * α + y^2 := by
  intro x y α
  simp only [Rα, Matrix.det_fin_two, Matrix.smul_apply, Matrix.add_apply,
             Matrix.one_apply, Matrix.of_apply, smul_eq_mul]
  -- The matrix entries simplify: (0,0)=y, (0,1)=-xα, (1,0)=x, (1,1)=y
  -- det = y*y - (-xα)*x = y² + x²α
  norm_num [Fin.isValue]
  ring
example : Rα 2 (1 : ℝ) = !![0, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rα, Matrix.of_apply]
end Tests
end GroupTheoreticShannonCapacity.MAlpha


