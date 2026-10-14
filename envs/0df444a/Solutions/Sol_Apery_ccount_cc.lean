-- Prove2me | solution 1 for Apery.ccount_cc
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T17:10:52.746463+00:00
-- url     : https://prove2.me/submissions/bda7055f-b05f-4290-9929-34e5a1e7a4f9

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# The nine continuous interval counts (source `Apery/Growth/TableGen.lean`)

This file proves the platform theorem `Apery.ccount_cc`, the bundle of the nine explicit
values of `ccount` for fractional parts in `[0, 1)`, used by every piece of the inner/outer
tables. Faithful port of mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
`Apery/Growth/TableGen.lean` (`cc00`..`cc22`).
-/

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

set_option autoImplicit false

section Port0
/-!
# The nine continuous interval counts (source `Apery/Growth/TableGen.lean`, `cc00`..`cc22`)

The bundle of the nine explicit values of `ccount` for fractional parts in `[0, 1)`:

`ccount f g 0 0 = 1/2`, `ccount f g 0 1 = min g (1/2)`, `ccount f g 0 2 = max 0 (g - 1/2)`,
`ccount f g 1 0 = min f (1/2)`, `ccount f g 2 0 = max 0 (f - 1/2)`,
`ccount f g 1 1 = min (min f g) (1/2)`, `ccount f g 1 2 = max 0 (min f (1/2) + g - 1)`,
`ccount f g 2 1 = max 0 (min g (1/2) + f - 1)`, `ccount f g 2 2 = max 0 (min f g - 1/2)`,

used by every piece of the inner/outer tables. Faithful port of mo271/Zeta5 @
7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, `Apery/Growth/TableGen.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open Finset

namespace Apery

section
variable {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1)

include hf0 hf1 hg0 hg1 in
lemma cc00 : ccount f g 0 0 = 1 / 2 := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc01 : ccount f g 0 1 = min g (1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc02 : ccount f g 0 2 = max 0 (g - 1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc10 : ccount f g 1 0 = min f (1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc20 : ccount f g 2 0 = max 0 (f - 1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc11 : ccount f g 1 1 = min (min f g) (1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc12 : ccount f g 1 2 = max 0 (min f (1 / 2) + g - 1) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc21 : ccount f g 2 1 = max 0 (min g (1 / 2) + f - 1) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

include hf0 hf1 hg0 hg1 in
lemma cc22 : ccount f g 2 2 = max 0 (min f g - 1 / 2) := by
  simp only [ccount, cvLo, cvHi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [max_def, min_def]
  split_ifs <;> linarith

end

theorem ccount_cc {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1) :
    ccount f g 0 0 = 1 / 2 ∧
    ccount f g 0 1 = min g (1 / 2) ∧
    ccount f g 0 2 = max 0 (g - 1 / 2) ∧
    ccount f g 1 0 = min f (1 / 2) ∧
    ccount f g 2 0 = max 0 (f - 1 / 2) ∧
    ccount f g 1 1 = min (min f g) (1 / 2) ∧
    ccount f g 1 2 = max 0 (min f (1 / 2) + g - 1) ∧
    ccount f g 2 1 = max 0 (min g (1 / 2) + f - 1) ∧
    ccount f g 2 2 = max 0 (min f g - 1 / 2) :=
  ⟨cc00 hf0 hf1 hg0 hg1, cc01 hf0 hf1 hg0 hg1, cc02 hf0 hf1 hg0 hg1,
   cc10 hf0 hf1 hg0 hg1, cc20 hf0 hf1 hg0 hg1, cc11 hf0 hf1 hg0 hg1,
   cc12 hf0 hf1 hg0 hg1, cc21 hf0 hf1 hg0 hg1, cc22 hf0 hf1 hg0 hg1⟩

end Apery

#check @Apery.ccount_cc
end Port0


open Finset in
/-- The platform target `Apery.ccount_cc`, restated at top level as `solution`. -/
theorem solution {f g : ℝ} (hf0 : 0 ≤ f) (hf1 : f < 1) (hg0 : 0 ≤ g) (hg1 : g < 1) :
    Apery.ccount f g 0 0 = 1 / 2 ∧
    Apery.ccount f g 0 1 = min g (1 / 2) ∧
    Apery.ccount f g 0 2 = max 0 (g - 1 / 2) ∧
    Apery.ccount f g 1 0 = min f (1 / 2) ∧
    Apery.ccount f g 2 0 = max 0 (f - 1 / 2) ∧
    Apery.ccount f g 1 1 = min (min f g) (1 / 2) ∧
    Apery.ccount f g 1 2 = max 0 (min f (1 / 2) + g - 1) ∧
    Apery.ccount f g 2 1 = max 0 (min g (1 / 2) + f - 1) ∧
    Apery.ccount f g 2 2 = max 0 (min f g - 1 / 2) :=
  Apery.ccount_cc hf0 hf1 hg0 hg1
