-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Arith
-- name    : MIPRE_Foundations_Halting_Arith
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:35:50.40786+00:00
-- url     : https://prove2.me/theorems/a1f99f09-880a-4580-9059-6fcafa9d02cf
-- title:
--   Arithmetic in the ambient model: binary increment, binary-to-unary conversion and Horner coefficient lists
-- statement:
--   Let `BitStr = List Bool` be the binary numerals, least significant bit first, `encode n` the encoding of `n.bits`, `Data.ofNat n` the unary numeral, `p.Runs x r t` the timed run relation, and `revOntoProg`, `revProg`, `callVar` the reversal programs and call combinator of earlier bundles.
--
--   Increment (`MIPRE.Cost`). `Data.inc : BitStr → BitStr` is the successor (`[] ↦ [true]`, `false :: l ↦ true :: l`, `true :: l ↦ false :: inc l`); `Data.incAcc : BitStr → BitStr → BitStr × BitStr` is its first phase with an accumulator, `(rest, acc) ↦ (acc', rest')` with `acc'.reverse ++ rest' = acc.reverse ++ inc rest`. `Prog.incBody` is the loop body of that phase on the state `cons rest acc`, and `Prog.incProg := .let_ (.cons (.var 0) .nil) (.let_ (.loop incBody) revOntoProg)`.
--
--   Binary to unary. `Data.msbFold : List Bool → ℕ → ℕ` is the fold $k \mapsto 2k + b$ over the bits, most significant first. `Prog.toUnaryBody` is the body on the state `cons rest acc` (double the unary `acc` with `revOntoProg`, add the next bit) and `Prog.toUnaryProg := .let_ (callVar 0 revProg) (.let_ (.cons (.var 0) .nil) (.loop toUnaryBody))`; `toUnaryProg_runs` states, for every $n$,
--
--   $$\exists\, t \le (\mathrm{size}\,n + 2)\big((n+1)(4n+14) + 7\,\mathrm{esize}\,n + 8n + 90\big),\qquad \mathrm{toUnaryProg}.\mathrm{Runs}\ (\mathrm{encode}\ n)\ (\mathrm{ofNat}\ n)\ t .$$
--
--   Polynomials. `Data.polyEval : List ℕ → ℕ → ℕ` is Horner evaluation (`polyEval [] m = 0`, `polyEval (c :: cs) m = c + m * polyEval cs m`) and `hornerCoeffs (p : Polynomial ℕ) := (List.range (p.natDegree + 1)).map p.coeff`, the coefficients least significant first, padded to `natDegree + 1` entries.
--
--   Lemmas: `msbFold_append_singleton`, `msbFold_reverse`, `msbFold_le`, `polyEval_range_map`, `polyEval_hornerCoeffs` (`polyEval (hornerCoeffs p) m = p.eval m`), `size_encode_append`, `size_encode_reverse`, `double_runs`, `toUnaryBody_nil`, `toUnaryBody_step`, `toUnaryLoop_runs`, `toUnaryBody_wellScoped`, `toUnaryProg_wellScoped`, `primrec_polyEval`, `primrec_poly_eval`.
--
--   **Formalization Note**. Costs are polynomial in the values, since unary numerals are as long as the values they denote. `hornerCoeffs` is noncomputable (`Polynomial ℕ`) and differs from Mathlib's big-endian, unpadded `Polynomial.coeffList`. The run lemma of `incProg` (docstring: the bits of $n$ to the bits of $n+1$), the module's multiplication and polynomial programs and `Data.inc_bits` are not in this bundle.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Arith.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Arith.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Linarith
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
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Theorems.Thm_MIPRE_Cost_Prog_revOntoProg_runs

/-!
# Arithmetic in the ambient model: increment, unary conversion, multiplication, polynomials

The arithmetic the wrapper decider (`Halting/Wrapper.lean`) and the compressor's decider
(`Halting/Compressor.lean`) need, each with its cost:

* `Prog.incProg`: the successor of a canonical binary numeral (`Data.inc`, with
  `Data.inc_bits : inc n.bits = (n + 1).bits`), used to enumerate the bit queries;
* `Prog.toUnaryProg`: a binary numeral to unary (`encode n ↦ ofNat n`), by the fold
  `k ↦ 2k + b` over the bits from the most significant one, doubling the unary accumulator with
  `revOntoProg`;
* `Prog.mulProg`: multiplication of unary numerals, by repeated `addProg`;
* `Prog.polyProg cs`: the Horner evaluation `c₀ + m (c₁ + m (…))` of a polynomial given by its
  coefficient list, on a unary input; `hornerCoeffs` and `Data.polyEval_hornerCoeffs` connect it
  to `Polynomial.eval`, so that the wrapper can compute the paper's `poly(n, λ)` bounds.

Costs are polynomial in the *values* (the unary numerals are as long as the values); the
polynomial evaluation is bounded by an explicit `Polynomial ℕ` in the argument
(`Prog.polyProg_runs`), which is what the time accounting downstream composes.
-/

namespace MIPRE.Cost

open Polynomial

namespace Data

/-! ## The successor of a binary numeral -/

/-- The successor of a binary numeral, least significant bit first. -/
def inc : BitStr → BitStr
  | [] => [true]
  | false :: l => true :: l
  | true :: l => false :: inc l

/-- The first phase of the increment: `(rest, acc) ↦ (acc', rest')` with
`acc'.reverse ++ rest' = acc.reverse ++ inc rest`. -/
def incAcc : BitStr → BitStr → BitStr × BitStr
  | [], acc => (true :: acc, [])
  | false :: r, acc => (true :: acc, r)
  | true :: r, acc => incAcc r (false :: acc)

theorem size_encode_append (l₁ l₂ : BitStr) :
    (encode (l₁ ++ l₂) : Data).size + 1 = (encode l₁ : Data).size + (encode l₂ : Data).size := by
  induction l₁ with
  | nil => simp only [List.nil_append, encode_bitStr_nil, Data.size_nil]; omega
  | cons b l ih =>
    simp only [List.cons_append, encode_bitStr_cons, Data.size_cons] at ih ⊢
    omega

theorem size_encode_reverse (l : BitStr) : (encode l.reverse : Data).size = (encode l : Data).size := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have := size_encode_append l.reverse [b]
    simp only [List.reverse_cons, encode_bitStr_cons, encode_bitStr_nil, Data.size_cons,
      Data.size_nil] at this ⊢
    omega

/-! ## Binary to unary -/

/-- The fold `k ↦ 2k + b` over bits, most significant first. -/
def msbFold : List Bool → ℕ → ℕ
  | [], k => k
  | b :: r, k => msbFold r (2 * k + b.toNat)

theorem msbFold_append_singleton (l : List Bool) (b : Bool) (k : ℕ) :
    msbFold (l ++ [b]) k = 2 * msbFold l k + b.toNat := by
  induction l generalizing k with
  | nil => rfl
  | cons c l ih => simp [msbFold, ih]

theorem msbFold_reverse (l : BitStr) (k : ℕ) :
    msbFold l.reverse k = k * 2 ^ l.length + bitsVal l := by
  induction l generalizing k with
  | nil => simp [msbFold]
  | cons b l ih =>
    rw [List.reverse_cons, msbFold_append_singleton, ih, bitsVal_cons, List.length_cons,
      pow_succ, Nat.bit]
    cases b <;> simp <;> ring

theorem msbFold_le (l : List Bool) (k : ℕ) : k ≤ msbFold l k := by
  induction l generalizing k with
  | nil => exact le_rfl
  | cons b l ih => exact le_trans (by omega) (ih (2 * k + b.toNat))

/-! ## Polynomials by their coefficients -/

/-- Horner evaluation of a coefficient list: `polyEval [c₀, c₁, …] m = c₀ + m (c₁ + m (…))`. -/
def polyEval : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: cs, m => c + m * polyEval cs m

theorem polyEval_range_map (f : ℕ → ℕ) (k m : ℕ) :
    polyEval ((List.range k).map f) m = ∑ i ∈ Finset.range k, f i * m ^ i := by
  induction k generalizing f with
  | zero => simp [polyEval]
  | succ k ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, polyEval, ih, Finset.sum_range_succ',
      Finset.mul_sum]
    simp only [Function.comp_def, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

end Data

/-- The coefficient list of a polynomial over `ℕ`, least significant first and padded to
`natDegree + 1` entries: the form Horner evaluation consumes (`Data.polyEval`). Mathlib's
`Polynomial.coeffList` is the big-endian list without the padding. -/
noncomputable def hornerCoeffs (p : Polynomial ℕ) : List ℕ :=
  (List.range (p.natDegree + 1)).map p.coeff

theorem Data.polyEval_hornerCoeffs (p : Polynomial ℕ) (m : ℕ) :
    Data.polyEval (hornerCoeffs p) m = p.eval m := by
  rw [hornerCoeffs, Data.polyEval_range_map, Polynomial.eval_eq_sum_range]

namespace Prog

open Data

/-! ## The increment program -/

/-- Body of the first phase of `incProg`, on the state `cons rest acc`: at the end or at a
`false` bit, stop with `(true :: acc, rest)`; at a `true` bit, move a `false` onto `acc`. -/
def incBody : Prog :=
  .elim 0 .nil
    (.elim 0 (.cons .nil (.cons (.cons (.cons .nil .nil) (.var 1)) .nil))
      (.elim 0 (.cons .nil (.cons (.cons (.cons .nil .nil) (.var 3)) (.var 1)))
        (.cons (.cons .nil .nil) (.cons (.var 3) (.cons .nil (.var 5))))))

/-- `incProg` on the bits of `n` computes the bits of `n + 1`. -/
def incProg : Prog := .let_ (.cons (.var 0) .nil) (.let_ (.loop incBody) revOntoProg)

/-! ## Binary to unary -/

/-- Body of `toUnaryProg`, on the state `cons rest acc` (`rest` the remaining bits, most
significant first; `acc` a unary numeral): double `acc` and add the next bit. -/
def toUnaryBody : Prog :=
  .elim 0 .nil
    (.elim 0 (.cons .nil (.var 1))
      (.let_ (.let_ (.cons (.var 3) (.var 3)) revOntoProg)
        (.elim 1 (.cons (.cons .nil .nil) (.cons (.var 2) (.var 0)))
          (.cons (.cons .nil .nil) (.cons (.var 4) (.cons .nil (.var 2)))))))

/-- `toUnaryProg` on `encode n` computes `ofNat n`. -/
def toUnaryProg : Prog :=
  .let_ (callVar 0 revProg) (.let_ (.cons (.var 0) .nil) (.loop toUnaryBody))

theorem toUnaryBody_wellScoped : toUnaryBody.WellScoped 1 := by
  simp [toUnaryBody, WellScoped, revOntoProg, revOntoBody]

theorem toUnaryProg_wellScoped : toUnaryProg.WellScoped 1 := by
  simp [toUnaryProg, WellScoped, callVar, revProg, revOntoProg, revOntoBody, toUnaryBody]

theorem toUnaryBody_nil (k : ℕ) :
    ∃ t ≤ 2 * k + 20, Eval [Data.cons (encode ([] : BitStr)) (ofNat k)] toUnaryBody
      (Data.cons Data.nil (ofNat k)) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode ([] : BitStr)) (b := ofNat k) (by simp)
    (Eval.elim_nil (i := 0) (by simp [encode_bitStr_nil])
      (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := ofNat k) (by simp))))⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool, MIPRE.Cost.encode_bitStr_nil, Bool.toNat_false, Bool.toNat_true]) <;> omega)

/-- The doubling of a unary numeral by `revOntoProg`. -/
theorem double_runs (k : ℕ) (env : Env) :
    ∃ t ≤ (k + 1) * (4 * k + 14),
      Eval (Data.cons (ofNat k) (ofNat k) :: env) revOntoProg (ofNat (2 * k)) t := by
  obtain ⟨t, ht, h⟩ := revOntoProg_runs (List.replicate k Data.nil) (List.replicate k Data.nil) env
    (4 * k + 2) (by simp only [← ofNat_eq_list_replicate, Data.size_ofNat]; omega)
  refine ⟨t, ?_, ?_⟩
  · simpa [List.length_replicate] using ht
  · simp only [← ofNat_eq_list_replicate] at h
    rw [List.reverse_replicate, List.replicate_append_replicate, ← ofNat_eq_list_replicate] at h
    rw [show 2 * k = k + k by ring]
    exact h

theorem toUnaryBody_step (b : Bool) (r : BitStr) (k : ℕ) :
    ∃ t ≤ (k + 1) * (4 * k + 14) + (encode r : Data).size + 8 * k + 64,
      Eval [Data.cons (encode (b :: r)) (ofNat k)] toUnaryBody
        (Data.cons (Data.cons Data.nil Data.nil) (Data.cons (encode r) (ofNat (2 * k + b.toNat)))) t := by
  obtain ⟨t₀, ht₀, hd⟩ := double_runs k
    [ofBool b, encode r, encode (b :: r), ofNat k, Data.cons (encode (b :: r)) (ofNat k)]
  have hpair : Eval [ofBool b, encode r, encode (b :: r), ofNat k, Data.cons (encode (b :: r)) (ofNat k)]
      (.cons (.var 3) (.var 3)) (Data.cons (ofNat k) (ofNat k)) ((ofNat k).size + 1 + ((ofNat k).size + 1) + 1) :=
    Eval.cons (Eval.var_of_get (i := 3) (v := ofNat k) (by simp))
      (Eval.var_of_get (i := 3) (v := ofNat k) (by simp))
  have hdbl := Eval.let_ hpair hd
  cases b
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode (false :: r)) (b := ofNat k) (by simp)
      (Eval.elim_cons (i := 0) (a := ofBool false) (b := encode r) (by simp [encode_bitStr_cons])
        (Eval.let_ hdbl (Eval.elim_nil (i := 1) (by simp [ofBool])
          (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
            (Eval.cons (Eval.var_of_get (i := 2) (v := encode r) (by simp))
              (Eval.var_of_get (i := 0) (v := ofNat (2 * k)) (by simp)))))))⟩
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool, MIPRE.Cost.encode_bitStr_nil, Bool.toNat_false, Bool.toNat_true]) <;> omega)
  · refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode (true :: r)) (b := ofNat k) (by simp)
      (Eval.elim_cons (i := 0) (a := ofBool true) (b := encode r) (by simp [encode_bitStr_cons])
        (Eval.let_ hdbl (Eval.elim_cons (i := 1) (a := Data.nil) (b := Data.nil) (by simp [ofBool])
          (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
            (Eval.cons (Eval.var_of_get (i := 4) (v := encode r) (by simp))
              (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 2) (v := ofNat (2 * k)) (by simp))))))))⟩
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool, MIPRE.Cost.encode_bitStr_nil, Bool.toNat_false, Bool.toNat_true]) <;> omega)

/-- The unary fold over the bits, most significant first: from `(rest, ofNat k)` to
`ofNat (msbFold rest k)`, in time `(|rest| + 1) · B` for `B` a bound depending on the final
value `N = msbFold rest k`. -/
theorem toUnaryLoop_runs (l : List Bool) (k : ℕ) (env : Env) (N : ℕ) (hN : msbFold l k = N)
    (S : ℕ) (hS : (encode l : Data).size ≤ S) :
    ∃ t ≤ (l.length + 1) * ((N + 1) * (4 * N + 14) + S + 8 * N + 65),
      Eval (Data.cons (encode l) (ofNat k) :: env) (.loop toUnaryBody) (ofNat N) t := by
  induction l generalizing k with
  | nil =>
    simp only [msbFold] at hN; subst hN
    obtain ⟨t, ht, hrun⟩ := toUnaryBody_nil k
    have hstop := Eval.loop_stop (Eval.append_of_wellScoped hrun toUnaryBody_wellScoped env)
    refine ⟨t + 1, ?_, hstop⟩
    simp only [List.length_nil, Nat.zero_add, Nat.one_mul]
    nlinarith
  | cons b l ih =>
    simp only [msbFold] at hN
    have hk : k ≤ N := hN ▸ (msbFold_le l (2 * k + b.toNat)).trans' (by omega)
    obtain ⟨t, ht, hrun⟩ := toUnaryBody_step b l k
    have hS' : (encode l : Data).size ≤ S := by
      simp only [encode_bitStr_cons, Data.size_cons] at hS; omega
    obtain ⟨t', ht', hrun'⟩ := ih (2 * k + b.toNat) hN hS'
    refine ⟨t + t' + 1, ?_, ?_⟩
    · have hB : (k + 1) * (4 * k + 14) ≤ (N + 1) * (4 * N + 14) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h2 : (l.length + 1 + 1) * ((N + 1) * (4 * N + 14) + S + 8 * N + 65) =
          (l.length + 1) * ((N + 1) * (4 * N + 14) + S + 8 * N + 65) +
            ((N + 1) * (4 * N + 14) + S + 8 * N + 65) := Nat.succ_mul _ _
      simp only [List.length_cons]
      omega
    · exact Eval.loop_step (Eval.append_of_wellScoped hrun toUnaryBody_wellScoped env) hrun'

/-- `toUnaryProg` converts a binary numeral to unary. -/
theorem toUnaryProg_runs (n : ℕ) :
    ∃ t ≤ (Nat.size n + 2) * ((n + 1) * (4 * n + 14) + 7 * esize n + 8 * n + 90),
      toUnaryProg.Runs (encode n) (ofNat n) t := by
  have hL : n.bits.length = Nat.size n := Nat.size_eq_bits_len n
  have hesz : (encode n.bits : Data).size = esize n := rfl
  have hrev : (encode n.bits.reverse : Data).size = esize n := by
    rw [size_encode_reverse]; exact hesz
  -- reversal
  obtain ⟨t₁, ht₁, h₁⟩ := revProg_runs (n.bits.map Data.ofBool)
  have h₁'' : revProg.Runs (encode n.bits) (encode n.bits.reverse) t₁ := by
    rw [encode_bitStr_eq_list, encode_bitStr_eq_list, List.map_reverse]
    exact h₁
  have h₁' : Eval [encode n] (callVar 0 revProg) (encode n.bits.reverse)
      ((encode n : Data).size + 1 + t₁ + 1) :=
    callVar_eval (env := [encode n]) (i := 0) revProg_wellScoped (v := encode n) (by simp) h₁''
  -- the fold
  obtain ⟨t₂, ht₂, h₂⟩ := toUnaryLoop_runs n.bits.reverse 0 [encode n.bits.reverse, encode n] n
    (by rw [msbFold_reverse, bitsVal_bits]; simp) (esize n) (le_of_eq hrev)
  have hpre := Eval.cons (Eval.var_of_get (env := [encode n.bits.reverse, encode n]) (i := 0)
    (v := encode n.bits.reverse) (by simp)) (Eval.nil [encode n.bits.reverse, encode n])
  have h₂' : Eval [Data.cons (encode n.bits.reverse) .nil, encode n.bits.reverse, encode n]
      (.loop toUnaryBody) (ofNat n) t₂ := by
    simpa [ofNat] using h₂
  refine ⟨_, ?_, Eval.let_ h₁' (Eval.let_ hpre h₂')⟩
  have hlen : n.bits.reverse.length = Nat.size n := by rw [List.length_reverse, hL]
  rw [hlen] at ht₂
  have hA : t₁ ≤ (Nat.size n + 2) * (esize n + 13) := by
    refine ht₁.trans ?_
    simp only [List.length_map, hL]
    rw [← encode_bitStr_eq_list, hesz]
  have key : (Nat.size n + 2) * (esize n + 13) +
      (Nat.size n + 1) * ((n + 1) * (4 * n + 14) + esize n + 8 * n + 65) + 2 * esize n + 10 ≤
      (Nat.size n + 2) * ((n + 1) * (4 * n + 14) + 7 * esize n + 8 * n + 90) := by
    nlinarith
  have hesz' : (encode n : Data).size = esize n := rfl
  rw [hrev, hesz']
  omega

/-! ## Multiplication of unary numerals -/

/-! ## Polynomials, by Horner's rule -/

end Prog

/-! ## Evaluating a fixed polynomial, primitively recursively

The answer-length budget of the tabulation is `bound.eval (n + λ)` for the fixed polynomial
`bound` of `MIPRE.GapCompression`, so `MIPRE.Halting.tab_computable` needs a polynomial's
evaluation to be primitive recursive in its argument. It goes through this file's own
`Data.polyEval` and `hornerCoeffs` rather than Mathlib's `Polynomial` API: the coefficient
list is fixed data, and Horner's rule on a fixed list is a fixed composition of `+` and `*`.
-/

theorem primrec_polyEval : ∀ L : List ℕ, Primrec (Data.polyEval L)
  | [] => (Primrec.const 0).of_eq fun _ => rfl
  | c :: cs =>
      (Primrec.nat_add.comp (Primrec.const c)
        (Primrec.nat_mul.comp Primrec.id (primrec_polyEval cs))).of_eq fun _ => rfl

theorem primrec_poly_eval (p : Polynomial ℕ) : Primrec fun m : ℕ => p.eval m :=
  (primrec_polyEval (hornerCoeffs p)).of_eq fun m => Data.polyEval_hornerCoeffs p m

end MIPRE.Cost


