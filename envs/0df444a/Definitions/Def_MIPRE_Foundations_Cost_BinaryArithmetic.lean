-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
-- name    : MIPRE_Foundations_Cost_BinaryArithmetic
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:45:51.11939+00:00
-- url     : https://prove2.me/theorems/80ef1d4c-98f7-49d6-b9e7-181d569a06d1
-- title:
--   Canonical binary arithmetic in polynomial time: digit prepending, value normalization, predecessor and unary offsets
-- statement:
--   Let `BitStr = List Bool` be the binary numerals, least significant bit first, `bitsVal l = l.foldr Nat.bit 0` the value of a string (canonical or not), `Nat.bit b n = 2n + b`, `Unary = List Unit`, `PolyTimeFun α β` the polynomial-time functions, `inc` the polynomial-time successor and `decProg` the decrement program of earlier bundles. Names are in `MIPRE.Cost`.
--
--   `PolyTimeFun.natBit : PolyTimeFun (Bool × ℕ) ℕ` is `(b, n) ↦ Nat.bit b n` (a digit prepended, `(false, 0) ↦ 0`). `PolyTimeFun.bitsValue : PolyTimeFun BitStr ℕ` is `l ↦ bitsVal l`, a fold of `natBit` over the reversed string from $0$. `decBits : BitStr → BitStr` is the borrow (`[] ↦ []`, `true :: l ↦ false :: l`, `false :: l ↦ true :: decBits l`). `PolyTimeFun.predBits : PolyTimeFun ℕ BitStr` is `n ↦ decBits n.bits`, with code `.elim 0 .nil (.let_ (.var 2) decProg)` and bound `(X + 2) * (10 * X + 60) + X + 3`. `PolyTimeFun.predN : PolyTimeFun ℕ ℕ` is `n ↦ n - 1` (`bitsValue` after `predBits`). `PolyTimeFun.addUnary : PolyTimeFun (ℕ × Unary) ℕ` is `(n, u) ↦ n + u.length` (a fold of `inc`) and `PolyTimeFun.subUnary` is `(n, u) ↦ n - u.length` (a fold of `predN` under the Cobham bound `C 4 * X + 1`). The borrow satisfies
--
--   $$\mathrm{bitsVal}\,\big(\mathrm{decBits}\,(\mathrm{bits}\ n)\big) = n - 1 \qquad (\text{truncated subtraction on } \mathbb{N}).$$
--
--   Lemmas: `natBit_apply`, `esize_natBit_le` (`esize (Nat.bit b n) ≤ esize n + 4`), `bitsValue_apply`, `decBits_split`, `bitsVal_decBits`, `predBits_apply`, `predN_apply`, `addUnary_apply`, `subUnary_apply`, and three private helpers (the split of the bits of a nonzero number, and the fold identities for adding and subtracting a length).
--
--   The parameter algorithms of the answer-reduction padding use binary integers even when their values far exceed the available work space; these programs manipulate digits directly and never expand a value to unary (blueprint `lem:pcp-padding-programs`).
--
--   **Formalization Note**. The output of `predBits` need not be canonical (`decProg`'s output on a nonzero number, `[]` at $0$); `bitsValue` normalizes it. `natBit` is built by `cast` from a program branching on the digit and on whether the bits of `n` are empty. Subtraction on `ℕ` saturates at $0$; `subUnary`'s intermediate values stay bounded by the initial integer. Definitions carrying a `Polynomial ℕ` are noncomputable.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/BinaryArithmetic.lean; blueprint lem:pcp-padding-programs

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/BinaryArithmetic.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Theorems.Thm_MIPRE_Cost_Prog_decProg_runs

/-!
# Canonical binary arithmetic

The parameter algorithms use binary integers, even when their values are much
larger than the available work space. These programs manipulate binary digits
directly. In particular, converting a bit string to a natural number normalizes
its encoding without expanding its value to unary.
-/

namespace MIPRE.Cost

open PolyTimeFun Polynomial

/-- Prepend a digit, suppressing the noncanonical representation of zero. -/
noncomputable def PolyTimeFun.natBit : PolyTimeFun (Bool × ℕ) ℕ :=
  let raw := ite fst (cons (const true) (natBits.comp snd))
    ((casesList (const []) (cons (const false) (natBits.comp fst))).comp
      (snd.pair (natBits.comp snd)))
  cast raw (fun p => Nat.bit p.1 p.2) (by
    rintro ⟨b, n⟩
    change encode (Nat.bit b n).bits = encode (raw (b, n))
    cases b with
    | true => simp [raw, Nat.bit_val]
    | false =>
      by_cases hn : n = 0
      · subst n; rfl
      · have hne : n.bits ≠ [] := by
          intro h
          have := bitsVal_bits n
          rw [h] at this
          exact hn this.symm
        cases hbits : n.bits with
        | nil => exact False.elim (hne hbits)
        | cons b bs => simp [raw, Nat.bit_val, Nat.bit0_bits n hn, hbits])

@[simp] theorem PolyTimeFun.natBit_apply (p : Bool × ℕ) : natBit p = Nat.bit p.1 p.2 := rfl

theorem esize_natBit_le (b : Bool) (n : ℕ) : esize (Nat.bit b n) ≤ esize n + 4 := by
  by_cases hn : n = 0
  · subst n; cases b <;> decide
  · change esize (Nat.bit b n).bits ≤ esize n.bits + 4
    rw [Nat.bits_append_bit n b (by simp [hn])]
    cases b <;> simp only [esize_true_cons, esize_false_cons] <;> omega

/-- Read and normalize an arbitrary little-endian bit string. -/
noncomputable def PolyTimeFun.bitsValue : PolyTimeFun BitStr ℕ :=
  let step := natBit.comp (snd.pair fst)
  congr ((foldlAdd step (C 4) (by
    intro n b
    simpa [step] using esize_natBit_le b n)).comp (reverse.pair (const 0)))
    bitsVal (by
      intro l
      change l.reverse.foldl (fun n b => Nat.bit b n) 0 = l.foldr Nat.bit 0
      exact List.foldl_reverse)

@[simp] theorem PolyTimeFun.bitsValue_apply (l : BitStr) : bitsValue l = bitsVal l := rfl

/-- Binary borrow, used on the nonzero canonical representation. -/
def decBits : BitStr → BitStr
  | [] => []
  | true :: l => false :: l
  | false :: l => true :: decBits l

theorem decBits_split (j : ℕ) (rest : BitStr) :
    decBits (List.replicate j false ++ true :: rest) =
      List.replicate j true ++ false :: rest := by
  induction j with
  | zero => rfl
  | succ j ih => simp [List.replicate_succ, decBits, ih]

theorem split_bits_of_ne_zero (n : ℕ) (hn : n ≠ 0) :
    ∃ j rest, n.bits = List.replicate j false ++ true :: rest := by
  apply exists_split_of_any
  by_contra h
  have hz : n.bits.any id = false := by cases h' : n.bits.any id <;> simp_all
  have hv := (bitsVal_eq_zero_iff _).mpr hz
  rw [bitsVal_bits] at hv
  exact hn hv

theorem bitsVal_decBits (n : ℕ) : bitsVal (decBits n.bits) = n - 1 := by
  by_cases hn : n = 0
  · subst n; rfl
  · obtain ⟨j, rest, he⟩ := split_bits_of_ne_zero n hn
    have hv := bitsVal_replicate_true_append j rest
    rw [← he, bitsVal_bits] at hv
    rw [he, decBits_split]
    omega

/-- The existing borrow machine, with its missing zero case supplied. Its
output need not be canonical; `bitsValue` subsequently normalizes it. -/
noncomputable def PolyTimeFun.predBits : PolyTimeFun ℕ BitStr where
  toFun n := decBits n.bits
  code := .elim 0 .nil (.let_ (.var 2) Prog.decProg)
  closed := by
    simp only [Prog.WellScoped]
    exact ⟨by omega, trivial, by omega, Prog.decProg_wellScoped.mono (by omega) _⟩
  timeBound := (X + 2) * (10 * X + 60) + X + 3
  computes n := by
    by_cases hn : n = 0
    · subst n
      exact ⟨2, by simp, Eval.elim_nil (by rfl) (Eval.nil _)⟩
    · obtain ⟨j, rest, he⟩ := split_bits_of_ne_zero n hn
      obtain ⟨t, ht, hr⟩ := Prog.decProg_runs j rest
      have hr' : Prog.decProg.Runs (encode n) (encode (decBits n.bits)) t := by
        change Prog.decProg.Runs (encode n.bits) _ t
        rw [he, decBits_split]
        exact hr
      have hnenc : ∃ a b, (encode n : Data) = .cons a b := by
        have hne : n.bits ≠ [] := by simp [he]
        cases hb : n.bits with
        | nil => exact False.elim (hne hb)
        | cons b bs => exact ⟨Data.ofBool b, encode bs, by change encode n.bits = _; rw [hb]; rfl⟩
      obtain ⟨a, b, henc⟩ := hnenc
      refine ⟨esize n + 1 + t + 1 + 1, ?_, ?_⟩
      · have hs : esize n = 2 * j + (encode rest).size + 4 := by
          change (encode n.bits).size = _
          rw [he, size_encode_replicate_false_append]
        have hj : j ≤ esize n := by omega
        rw [← hs] at ht
        have ht' := ht.trans (Nat.mul_le_mul_right (10 * esize n + 60) (by omega : j + 2 ≤ esize n + 2))
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
        omega
      · exact Eval.elim_cons (by simpa using henc)
          (Eval.let_ (Eval.var_of_get (i := 2) (v := encode n) (by rfl))
            (Eval.append_of_wellScoped hr' Prog.decProg_wellScoped [a, b, encode n]))

@[simp] theorem PolyTimeFun.predBits_apply (n : ℕ) : predBits n = decBits n.bits := rfl

/-- Saturating predecessor of a binary integer. -/
noncomputable def PolyTimeFun.predN : PolyTimeFun ℕ ℕ :=
  congr (bitsValue.comp predBits) (fun n => n - 1) (by intro n; exact bitsVal_decBits n)

@[simp] theorem PolyTimeFun.predN_apply (n : ℕ) : predN n = n - 1 := rfl

theorem fold_addUnary (u : Unary) (n : ℕ) :
    u.foldl (fun k _ => k + 1) n = n + u.length := by
  induction u generalizing n with
  | nil => simp
  | cons a u ih => simp [ih]; omega

/-- Add a unary offset to a binary integer. -/
noncomputable def PolyTimeFun.addUnary : PolyTimeFun (ℕ × Unary) ℕ :=
  congr ((foldlAdd (inc.comp fst) (C 4) (by
    intro n u
    simpa using esize_succ_le n)).comp (snd.pair fst))
    (fun p => p.1 + p.2.length) (by intro p; exact fold_addUnary p.2 p.1)

@[simp] theorem PolyTimeFun.addUnary_apply (p : ℕ × Unary) :
    addUnary p = p.1 + p.2.length := rfl

theorem fold_subUnary (u : Unary) (n : ℕ) :
    u.foldl (fun k _ => k - 1) n = n - u.length := by
  induction u generalizing n with
  | nil => simp
  | cons a u ih => simp [ih]; omega

/-- Subtract a unary offset from a binary integer, saturating at zero. The
intermediate values are bounded by the initial integer, in binary size. -/
noncomputable def PolyTimeFun.subUnary : PolyTimeFun (ℕ × Unary) ℕ :=
  let step : PolyTimeFun (ℕ × Unit) ℕ := predN.comp fst
  congr ((foldl step (C 4 * X + 1) (by
    intro l n pre post h
    change esize (pre.foldl (fun k _ => k - 1) n) ≤ _
    rw [fold_subUnary]
    have hs := esize_nat_le (n - pre.length)
    have hm := Nat.size_le_size (Nat.sub_le n pre.length)
    have hn := size_le_esize_nat n
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_one, esize_prod]
    omega)).comp (snd.pair fst))
    (fun p => p.1 - p.2.length) (by intro p; exact fold_subUnary p.2 p.1)

@[simp] theorem PolyTimeFun.subUnary_apply (p : ℕ × Unary) :
    subUnary p = p.1 - p.2.length := rfl

end MIPRE.Cost


