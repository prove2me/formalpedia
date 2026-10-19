-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_InputRouting
-- name    : MIPRE_Foundations_SAT_InputRouting
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:57:45.833973+00:00
-- url     : https://prove2.me/theorems/28110e43-7523-4f15-aab8-143c7fc877f4
-- title:
--   Definitions of InputRouting: Routing repeated input reads through their preceding copies `Circuit.WellFormed` bounds gate fan-out, but permits…
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.InputRouting` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Routing repeated input reads through their preceding copies. `Circuit.WellFormed` bounds gate fan-out, but permits arbitrarily many gates to read the same external input. For bounded-degree consistency polynomials, the first such gate reads the external variable and each later one reads the preceding input gate's variable. This changes neither the variables nor the Boolean gate values. Each variable supplies at most one of these copy links.
--
--   **Definitions** (3): `MIPRE.SAT.Circuit.RoutedConsistent` (Consistency equations after replacing repeated external reads by copy links.); `MIPRE.SAT.Circuit.inputOwner` (One plus the last gate reading input `i` before gate `k`, or zero if none.); `MIPRE.SAT.Circuit.inputRef` (The input-copy link: external input on the first read, previous gate thereafter.).
--
--   **Embedded lemmas** (7): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `inputOwner_after`, `inputOwner_le`, `inputOwner_mono`, `inputOwner_spec`, `inputRef_cases`, `inputRef_ne_of_lt`, `inputRef_value`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.InputRouting` (`MIPRE/Foundations/SAT/InputRouting.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 5 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/InputRouting.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/InputRouting.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Theorems.Thm_MIPRE_SAT_Circuit_valueAt_eq

/-!
# Routing repeated input reads through their preceding copies

`Circuit.WellFormed` bounds gate fan-out, but permits arbitrarily many gates to
read the same external input. For bounded-degree consistency polynomials, the
first such gate reads the external variable and each later one reads the
preceding input gate's variable. This changes neither the variables nor the
Boolean gate values. Each variable supplies at most one of these copy links.
-/

namespace MIPRE.SAT.Circuit

/-- One plus the last gate reading input `i` before gate `k`, or zero if none. -/
def inputOwner (C : Circuit) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, i => if C.gates.getD k (.const false) = .input i then k + 1 else inputOwner C k i

theorem inputOwner_le (C : Circuit) (k i : ℕ) : C.inputOwner k i ≤ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [inputOwner]; split <;> omega

theorem inputOwner_mono (C : Circuit) (i : ℕ) : Monotone (fun k => C.inputOwner k i) := by
  apply monotone_nat_of_le_succ
  intro k
  simp only [inputOwner]
  split
  · have := inputOwner_le C k i; omega
  · exact le_rfl

theorem inputOwner_spec (C : Circuit) (k i : ℕ) (h : C.inputOwner k i ≠ 0) :
    C.gates.getD (C.inputOwner k i - 1) (.const false) = .input i := by
  induction k with
  | zero => exact False.elim (h rfl)
  | succ k ih =>
    by_cases hg : C.gates.getD k (.const false) = .input i
    · simp only [inputOwner, if_pos hg, Nat.add_sub_cancel]
      exact hg
    · simp only [inputOwner, if_neg hg] at h ⊢
      exact ih h

theorem inputOwner_after (C : Circuit) {a b i : ℕ} (hab : a < b)
    (ha : C.gates.getD a (.const false) = .input i) : a + 1 ≤ C.inputOwner b i := by
  have h := inputOwner_mono C i (show a + 1 ≤ b by omega)
  change C.inputOwner (a + 1) i ≤ C.inputOwner b i at h
  rw [inputOwner, if_pos ha] at h
  exact h

/-- The input-copy link: external input on the first read, previous gate thereafter. -/
def inputRef (C : Circuit) (k i : ℕ) : ℕ ⊕ ℕ :=
  if C.inputOwner k i = 0 then .inl i else .inr (C.inputOwner k i - 1)

theorem inputRef_ne_of_lt (C : Circuit) {a b i j : ℕ} (hab : a < b)
    (ha : C.gates.getD a (.const false) = .input i)
    (he : C.inputRef a i = C.inputRef b j) : False := by
  by_cases h₁ : C.inputOwner a i = 0 <;> by_cases h₂ : C.inputOwner b j = 0
  · simp only [inputRef, h₁, h₂, if_true, Sum.inl.injEq] at he
    subst j
    have := inputOwner_after C hab ha
    omega
  · simp [inputRef, h₁, h₂] at he
  · simp [inputRef, h₁, h₂] at he
  · simp only [inputRef, h₁, h₂, if_false, Sum.inr.injEq] at he
    have howner : C.inputOwner a i = C.inputOwner b j := by omega
    have hi := inputOwner_spec C a i h₁
    have hj := inputOwner_spec C b j h₂
    rw [howner, hj] at hi
    have hij : i = j := by injection hi with h; exact h.symm
    subst j
    have hl := inputOwner_le C a i
    have hr := inputOwner_after C hab ha
    omega

/-- A copy link points to an input variable or to a strictly earlier gate. -/
theorem inputRef_cases (C : Circuit) (k i : ℕ) :
    C.inputRef k i = .inl i ∨
      ∃ u < k, C.inputRef k i = .inr u ∧ C.gates.getD u (.const false) = .input i := by
  by_cases h : C.inputOwner k i = 0
  · exact Or.inl (by simp [inputRef, h])
  · refine Or.inr ⟨C.inputOwner k i - 1, ?_, ?_, inputOwner_spec C k i h⟩
    · have := inputOwner_le C k i; omega
    · simp [inputRef, h]

/-- Consistency equations after replacing repeated external reads by copy links. -/
def RoutedConsistent (C : Circuit) (x w : ℕ → Bool) : Prop :=
  ∀ k < C.size, w k = (C.gates.getD k (.const false)).eval
    (fun i => Sum.elim x w (C.inputRef k i)) (List.ofFn fun j : Fin k => w j)

theorem inputRef_value (C : Circuit) (x w : ℕ → Bool) (k i : ℕ)
    (hw : ∀ u < k, w u = C.valueAt x u) : Sum.elim x w (C.inputRef k i) = x i := by
  rcases inputRef_cases C k i with he | ⟨u, hu, he, hg⟩
  · rw [he]; rfl
  · rw [he]
    change w u = x i
    rw [hw u hu, valueAt_eq, hg]
    rfl

end MIPRE.SAT.Circuit


