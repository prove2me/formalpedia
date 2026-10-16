-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Lists
-- name    : MIPRE_Foundations_Halting_Lists
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:34:23.007093+00:00
-- url     : https://prove2.me/theorems/7c546b1a-878e-483d-aae6-6736fae63845
-- title:
--   Bounded walks over lists in the ambient model: bit-list equality and the canonicity check
-- statement:
--   Let `Data` be the binary trees of the ambient model, `Prog` its programs, `Eval env p r t` its timed semantics, `Data.ofNat n` the unary numeral and `Data.ofBool` the bit encoding (`false ↦ nil`, `true ↦ cons nil nil`). The bundle holds list walks of the wrapper decider's format checks, each under a budget so that the cost is the budget times the input size.
--
--   Functions (`MIPRE.Cost.Data`). `spine : Data → ℕ` is the length of the right spine (`spine nil = 0`, `spine (cons _ r) = spine r + 1`). `bitOf : Data → Bool` reads `nil` as `false`, any `cons` as `true`. `eqBits : Data → Data → Bool`: `eqBits nil nil = true`, `eqBits (cons h₁ l₁) (cons h₂ l₂) = (bitOf h₁ == bitOf h₂) && eqBits l₁ l₂`, `false` otherwise. `canonWalk : Data → Bool → Bool` walks a list with a flag `last`: at `nil` it returns `last`; `nil` sets the flag to `false`, `cons nil nil` to `true`, any other element returns `false`.
--
--   Programs (`MIPRE.Cost.Prog`). `eqBitsBody` is the loop body on the state `cons l₁ l₂`, `eqBitsProg := .loop eqBitsBody`. `canonBody` is the body of the canonicity walk on the state `cons rest last`, and `normBinProg := .let_ (.let_ (.cons (.var 0) (.cons .nil .nil)) (.loop canonBody)) (.elim 0 .nil (.var 3))` runs it from `last = true`, returning the input if it accepts and `nil` otherwise (specification `Data.normBin`). `eqBitsProg_runs`: for `l₁ l₂ : Data`, `env` and $S$ with `l₁.size + l₂.size ≤ S`,
--
--   $$\exists\, t \le (\mathrm{spine}\,l_1 + 1)\,(S + 21),\qquad \mathrm{Eval}\ (\mathtt{cons}\ l_1\ l_2 :: \mathrm{env})\ \mathrm{eqBitsProg}\ \big(\mathrm{encode}\,(\mathrm{eqBits}\ l_1\ l_2)\big)\ t .$$
--
--   Other lemmas: `spine_nil`, `spine_cons`, `spine_ofNat`, `spine_le_size`, `bitOf_ofBool`, `eqBits_ofNat` (on unary numerals, equality of the numbers), the one-iteration lemmas `eqBitsBody_nil_nil`, `eqBitsBody_nil_cons`, `eqBitsBody_cons_nil` (cost at most $20$) and `eqBitsBody_cons_cons` (cost at most `l₁.size + l₂.size + 20`), `eqBitsBody_wellScoped`, `eqBitsProg_wellScoped`.
--
--   **Formalization Note**. Every walk copies the remainder of the lists at each step, which the ambient model charges, so bounds have the shape $(\text{budget}+1)(S+c)$. The wrapper applies `eqBits` to unary numerals. The module's bit-walk program for the length checks and the run lemma of `normBinProg` are not in this bundle. `canonWalk` and `canonBody` are the mathematical and the ambient form of one walk, started with `true` (the empty string is canonical).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Lists.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Lists.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B

/-!
# Bounded walks over lists, in the ambient model

The programs with which the wrapper decider of `Halting/Wrapper.lean` performs the paper's
format checks: the questions must be bit strings of the sampler's length, the answers bit
strings within the answer-length budget, and equal questions must carry equal answers. All of
them walk their input under a *budget*, so that their cost is the budget times the size of the
input — the shape `T · (|input| + 1)` of `Decider.TimeBoundAt` — rather than a power of it.

* `Prog.bitWalkProg`: on `cons l u`, walk `l` against the budget `u` (a list, typically a unary
  numeral), checking that each element passed is a bit; the result is `nil` on a non-bit
  element, and otherwise the pair of what remains of `l` and of `u` (`Data.bitWalk`). Both
  format checks read off it: `|l| = |u|` is the result `cons nil nil`, `|l| ≤ |u|` a result
  `cons nil _`.
* `Prog.eqBitsProg`: equality of two bit lists (`Data.eqBits`).
* `Prog.normBinProg`: the normalization `Data.normBin` of a parameter, by a walk recording the
  last bit seen (`Data.canonWalk`).

Every walk copies the remainder of the lists at each step, which is what the ambient model
charges; the cost bounds are `(budget + 1) · (S + c)` for `S` the size of the input.
-/

namespace MIPRE.Cost

namespace Data

/-- The length of the right spine: the length of a list. -/
def spine : Data → ℕ
  | nil => 0
  | cons _ r => spine r + 1

@[simp] theorem spine_nil : spine nil = 0 := rfl
@[simp] theorem spine_cons (a r : Data) : spine (cons a r) = spine r + 1 := rfl

theorem spine_ofNat (n : ℕ) : spine (ofNat n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ofNat, ih]

theorem spine_le_size (d : Data) : spine d ≤ d.size := by
  induction d with
  | nil => simp
  | cons a r _ ih => have := size_pos a; simp only [spine_cons, size_cons]; omega

/-- The bit an element denotes: `nil` is `false`, anything else `true`. -/
def bitOf : Data → Bool
  | nil => false
  | cons _ _ => true

@[simp] theorem bitOf_ofBool (b : Bool) : bitOf (ofBool b) = b := by cases b <;> rfl

/-- Equality of two bit lists, element by element. -/
def eqBits : Data → Data → Bool
  | nil, nil => true
  | cons h₁ l₁, cons h₂ l₂ => (bitOf h₁ == bitOf h₂) && eqBits l₁ l₂
  | _, _ => false

/-- On unary numerals, `eqBits` is equality of the numbers: every element is `nil`, so the
walk compares only the lengths. -/
theorem eqBits_ofNat (a b : ℕ) : eqBits (ofNat a) (ofNat b) = decide (a = b) := by
  induction a generalizing b with
  | zero => cases b <;> simp [eqBits, ofNat]
  | succ a ih =>
    cases b with
    | zero => simp [eqBits, ofNat]
    | succ b => simp [eqBits, ofNat, ih, bitOf]

/-- The walk of the normalization: `last` records whether the string so far is empty or ends
in `true`. -/
def canonWalk : Data → Bool → Bool
  | nil, last => last
  | cons nil r, _ => canonWalk r false
  | cons (cons nil nil) r, _ => canonWalk r true
  | cons _ _, _ => false

end Data

namespace Prog

open Data

/-! ## The bounded bit walk -/

/-! ## Equality of bit lists -/

/-- Body of `eqBitsProg`, on the state `cons l₁ l₂`. -/
def eqBitsBody : Prog :=
  .elim 0 .nil
    (.elim 0 (.elim 1 (.cons .nil (.cons .nil .nil)) (.cons .nil .nil))
      (.elim 3 (.cons .nil .nil)
        (.elim 2 (.elim 0 (.cons (.cons .nil .nil) (.cons (.var 3) (.var 1))) (.cons .nil .nil))
          (.elim 2 (.cons .nil .nil) (.cons (.cons .nil .nil) (.cons (.var 7) (.var 5)))))))

/-- Equality of two bit lists: on `cons l₁ l₂`, compute `encode (eqBits l₁ l₂)`. -/
def eqBitsProg : Prog := .loop eqBitsBody

theorem eqBitsBody_wellScoped : eqBitsBody.WellScoped 1 := by
  simp [eqBitsBody, WellScoped]

theorem eqBitsProg_wellScoped : eqBitsProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, eqBitsBody_wellScoped⟩

theorem eqBitsBody_nil_nil  :
    ∃ t ≤ 20, Eval [Data.cons Data.nil Data.nil] eqBitsBody (Data.cons Data.nil (encode true)) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.nil) (b := Data.nil) (by simp)
    (Eval.elim_nil (i := 0) (by simp)
    (Eval.elim_nil (i := 1) (by simp)
    (Eval.cons (Eval.nil _) (Eval.cons (Eval.nil _) (Eval.nil _)))))⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)

theorem eqBitsBody_nil_cons (h₂ l₂ : Data) :
    ∃ t ≤ 20, Eval [Data.cons Data.nil (Data.cons h₂ l₂)] eqBitsBody (Data.cons Data.nil (encode false)) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.nil) (b := Data.cons h₂ l₂) (by simp)
    (Eval.elim_nil (i := 0) (by simp)
    (Eval.elim_cons (i := 1) (a := h₂) (b := l₂) (by simp)
    (Eval.cons (Eval.nil _) (Eval.nil _))))⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)

theorem eqBitsBody_cons_nil (h₁ l₁ : Data) :
    ∃ t ≤ 20, Eval [Data.cons (Data.cons h₁ l₁) Data.nil] eqBitsBody (Data.cons Data.nil (encode false)) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons h₁ l₁) (b := Data.nil) (by simp)
    (Eval.elim_cons (i := 0) (a := h₁) (b := l₁) (by simp)
    (Eval.elim_nil (i := 3) (by simp)
    (Eval.cons (Eval.nil _) (Eval.nil _))))⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)

theorem eqBitsBody_cons_cons (h₁ l₁ h₂ l₂ : Data) :
    ∃ t ≤ l₁.size + l₂.size + 20,
      Eval [Data.cons (Data.cons h₁ l₁) (Data.cons h₂ l₂)] eqBitsBody
        (if bitOf h₁ = bitOf h₂ then Data.cons (Data.cons Data.nil Data.nil) (Data.cons l₁ l₂)
          else Data.cons Data.nil (encode false)) t := by
  rcases h₁ with _ | ⟨a1, a2⟩ <;> rcases h₂ with _ | ⟨b1, b2⟩
  · simp only [bitOf, if_true]
    refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons Data.nil l₁) (b := Data.cons Data.nil l₂) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.nil) (b := l₁) (by simp)
      (Eval.elim_cons (i := 3) (a := Data.nil) (b := l₂) (by simp)
      (Eval.elim_nil (i := 2) (by simp)
      (Eval.elim_nil (i := 0) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 3) (v := l₁) (by simp)) (Eval.var_of_get (i := 1) (v := l₂) (by simp))))))))⟩
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)
  · simp only [bitOf, Bool.false_eq_true, if_false]
    refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons Data.nil l₁) (b := Data.cons (Data.cons b1 b2) l₂) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.nil) (b := l₁) (by simp)
      (Eval.elim_cons (i := 3) (a := Data.cons b1 b2) (b := l₂) (by simp)
      (Eval.elim_nil (i := 2) (by simp)
      (Eval.elim_cons (i := 0) (a := b1) (b := b2) (by simp)
      (Eval.cons (Eval.nil _) (Eval.nil _))))))⟩
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)
  · simp only [bitOf, Bool.true_eq_false, if_false]
    refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons (Data.cons a1 a2) l₁) (b := Data.cons Data.nil l₂) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons a1 a2) (b := l₁) (by simp)
      (Eval.elim_cons (i := 3) (a := Data.nil) (b := l₂) (by simp)
      (Eval.elim_cons (i := 2) (a := a1) (b := a2) (by simp)
      (Eval.elim_nil (i := 2) (by simp)
      (Eval.cons (Eval.nil _) (Eval.nil _))))))⟩
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)
  · simp only [bitOf, if_true]
    refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := Data.cons (Data.cons a1 a2) l₁) (b := Data.cons (Data.cons b1 b2) l₂) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons a1 a2) (b := l₁) (by simp)
      (Eval.elim_cons (i := 3) (a := Data.cons b1 b2) (b := l₂) (by simp)
      (Eval.elim_cons (i := 2) (a := a1) (b := a2) (by simp)
      (Eval.elim_cons (i := 2) (a := b1) (b := b2) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 7) (v := l₁) (by simp)) (Eval.var_of_get (i := 5) (v := l₂) (by simp))))))))⟩
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)

/-- `eqBitsProg` computes `eqBits l₁ l₂`, in time `(|l₁| + 1) · (S + 21)` for `S` dominating
the sizes. -/
theorem eqBitsProg_runs (l₁ l₂ : Data) (env : Env) (S : ℕ) (hS : l₁.size + l₂.size ≤ S) :
    ∃ t ≤ (l₁.spine + 1) * (S + 21),
      Eval (Data.cons l₁ l₂ :: env) eqBitsProg (encode (eqBits l₁ l₂)) t := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil =>
      obtain ⟨t, ht, hrun⟩ := eqBitsBody_nil_nil
      have := Eval.loop_stop (Eval.append_of_wellScoped hrun eqBitsBody_wellScoped env)
      exact ⟨t + 1, by simp only [spine_nil]; omega, by simpa [eqBits, eqBitsProg] using this⟩
    | cons h₂ l₂ =>
      obtain ⟨t, ht, hrun⟩ := eqBitsBody_nil_cons h₂ l₂
      have := Eval.loop_stop (Eval.append_of_wellScoped hrun eqBitsBody_wellScoped env)
      exact ⟨t + 1, by simp only [spine_nil]; omega, by simpa [eqBits, eqBitsProg] using this⟩
  | cons h₁ l₁ _ ih =>
    cases l₂ with
    | nil =>
      obtain ⟨t, ht, hrun⟩ := eqBitsBody_cons_nil h₁ l₁
      have hstop := Eval.loop_stop (Eval.append_of_wellScoped hrun eqBitsBody_wellScoped env)
      refine ⟨t + 1, ?_, by simpa [eqBits, eqBitsProg] using hstop⟩
      have : S + 21 ≤ (spine (Data.cons h₁ l₁) + 1) * (S + 21) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    | cons h₂ l₂ =>
      obtain ⟨t, ht, hrun⟩ := eqBitsBody_cons_cons h₁ l₁ h₂ l₂
      by_cases hb : bitOf h₁ = bitOf h₂
      · rw [if_pos hb] at hrun
        have hS' : l₁.size + l₂.size ≤ S := by
          simp only [size_cons] at hS; have := size_pos h₁; have := size_pos h₂; omega
        obtain ⟨t', ht', hrun'⟩ := ih l₂ hS'
        refine ⟨t + t' + 1, ?_, ?_⟩
        · have h2 : (spine (Data.cons h₁ l₁) + 1) * (S + 21) =
              (l₁.spine + 1) * (S + 21) + (S + 21) := by
            simp only [spine_cons]; ring
          simp only [size_cons] at hS
          omega
        · have := Eval.loop_step (Eval.append_of_wellScoped hrun eqBitsBody_wellScoped env) hrun'
          simpa [eqBits, hb, eqBitsProg] using this
      · rw [if_neg hb] at hrun
        have hbeq : (bitOf h₁ == bitOf h₂) = false := beq_eq_false_iff_ne.2 hb
        have hstop := Eval.loop_stop (Eval.append_of_wellScoped hrun eqBitsBody_wellScoped env)
        refine ⟨t + 1, ?_, by simpa [eqBits, hbeq, eqBitsProg] using hstop⟩
        have : S + 21 ≤ (spine (Data.cons h₁ l₁) + 1) * (S + 21) :=
          Nat.le_mul_of_pos_left _ (by omega)
        simp only [size_cons] at hS
        omega

/-! ## Normalization of the parameter -/

/-- Body of the canonicity walk, on the state `cons rest last`. -/
def canonBody : Prog :=
  .elim 0 .nil
    (.elim 0 (.cons .nil (.var 1))
      (.elim 0 (.cons (.cons .nil .nil) (.cons (.var 1) .nil))
        (.elim 0 (.elim 1 (.cons (.cons .nil .nil) (.cons (.var 3) (.cons .nil .nil)))
            (.cons .nil .nil))
          (.cons .nil .nil))))

/-- `normBinProg` on `d` computes `normBin d`: the input itself if it is a canonical binary
numeral, `nil` otherwise. -/
def normBinProg : Prog :=
  .let_ (.let_ (.cons (.var 0) (.cons .nil .nil)) (.loop canonBody)) (.elim 0 .nil (.var 3))

end Prog

end MIPRE.Cost


