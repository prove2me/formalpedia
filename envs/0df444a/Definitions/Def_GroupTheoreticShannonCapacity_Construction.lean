-- Prove2me | Definitions.Def_GroupTheoreticShannonCapacity_Construction
-- name    : GroupTheoreticShannonCapacity_Construction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:26:38.24081+00:00
-- url     : https://prove2.me/theorems/864a839e-362f-42b6-ae3b-092939d912da
-- title:
--   Construction
-- statement:
--   Definitions and structural lemmas for Construction, from jzuiddam/GroupTheoreticShannonCapacity contributors (see pinned LICENSE and source headers)'s pinned Shannon capacity limits from lattice packings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
set_option autoImplicit true
namespace GroupTheoreticShannonCapacity.Construction
open Matrix
def a (n : ℕ) (k b r s : ℤ) : ℤ := k * b^n + s * b + r
def aReal (n : ℕ) (k b r s : ℝ) : ℝ := k * b^n + s * b + r
noncomputable def p (n : ℕ) (k b r s : ℤ) : ℚ :=
  (s^n * r + k * (a n k b r s)^n) / (r + k * b^n)
noncomputable def q (n : ℕ) (k b r s : ℤ) : ℚ :=
  (s^(n-1) * r + k * b * (a n k b r s)^(n-1)) / (r + k * b^n)
def X_entry (n : ℕ) (k b r s : ℤ) (i j : Fin n) : ℚ :=
  let a' := a n k b r s
  if (i : ℕ) < (j : ℕ) then r * a'^((j : ℕ) - (i : ℕ) - 1) * s^(n - ((j : ℕ) - (i : ℕ) + 1))
  else if (i : ℕ) > (j : ℕ) then -k * a'^(n - ((i : ℕ) - (j : ℕ) + 1)) * s^((i : ℕ) - (j : ℕ) - 1)
  else 0
def Y_entry (n : ℕ) (k b r : ℤ) (i j : Fin n) : ℚ :=
  if (i : ℕ) < (j : ℕ) then -r * b^((j : ℕ) - (i : ℕ) - 1)
  else if (i : ℕ) > (j : ℕ) then k * b^(n - ((i : ℕ) - (j : ℕ) + 1))
  else 0
noncomputable def matrixX (n : ℕ) (k b r s : ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of (X_entry n k b r s)
noncomputable def matrixY (n : ℕ) (k b r _s : ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of (Y_entry n k b r)
noncomputable def X_entry_real (n : ℕ) (k b r s : ℝ) (i j : Fin n) : ℝ :=
  let a' := aReal n k b r s
  if (i : ℕ) < (j : ℕ) then r * a'^((j : ℕ) - (i : ℕ) - 1) * s^(n - ((j : ℕ) - (i : ℕ) + 1))
  else if (i : ℕ) > (j : ℕ) then -k * a'^(n - ((i : ℕ) - (j : ℕ) + 1)) * s^((i : ℕ) - (j : ℕ) - 1)
  else 0
noncomputable def matrixX_real (n : ℕ) (k b r s : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (X_entry_real n k b r s)
noncomputable def diagPow (n : ℕ) (β : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => β ^ (i.val : ℕ)
noncomputable def matrixA (n : ℕ) (k b r s : ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  q n k b r s • 1 + matrixX n k b r s
noncomputable def matrixB (n : ℕ) (k b r s : ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  ((a n k b r s - r) / b) • 1 + matrixY n k b r s
section Tests
example : a 2 1 2 1 0 = 5 := by decide
example : p 2 1 2 1 0 = 5 := by
  simp only [p, a]
  norm_num
example : q 2 1 2 1 0 = 2 := by
  simp only [q, a]
  norm_num
example : p 2 1 2 1 0 = q 2 1 2 1 0 * 0 + 1 * (a 2 1 2 1 0)^(2-1) := by
  simp only [p, q, a]
  norm_num
example : p 2 1 2 1 0 * 2 = q 2 1 2 1 0 * (a 2 1 2 1 0) - 1 * 0^(2-1) := by
  simp only [p, q, a]
  norm_num
end Tests
end GroupTheoreticShannonCapacity.Construction


