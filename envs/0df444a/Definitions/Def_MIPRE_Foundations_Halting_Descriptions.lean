-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Descriptions
-- name    : MIPRE_Foundations_Halting_Descriptions
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:33:41.209305+00:00
-- url     : https://prove2.me/theorems/ed3c3941-a40b-41f6-9838-e4290c5d8a03
-- title:
--   Descriptions as bit strings: postorder serialization of data, the stack-machine reader and parameter normalization
-- statement:
--   Let `Data` be the binary trees of the ambient cost model (`nil`, `cons`) and `BitStr = List Bool`, least significant bit first, with `encode n` the encoding of `n.bits`. The strings of the compressibility criterion are descriptions, a parameter and a decider serialized as data; this bundle (`MIPRE.Cost.Data`) fixes how a datum travels as a bit string and how any bit string is read back.
--
--   Serialization. `toBitsPost : Data → BitStr` is postorder: `nil ↦ [false]`, `cons a b ↦ a.toBitsPost ++ b.toBitsPost ++ [true]`. `stackStep (s : List Data) (bit : Bool)` is one step of a stack machine: `false` pushes `nil`; `true` on a stack `b :: a :: s'` with at least two entries replaces the top two by `cons a b`, and leaves a shorter stack unchanged. `stackRun x s := x.foldl stackStep s`, and `parse x := (stackRun x []).headD nil` is the total reader (the top of the final stack, `nil` for an empty stack), with the round trip
--
--   $$\mathrm{parse}\,(\mathrm{toBitsPost}\ d) = d \qquad \text{for every } d : \mathsf{Data}.$$
--
--   Parameters. `isBit : Data → Bool` is true exactly on `nil` and `cons nil nil`. `isCanonBin d : Bool` decodes `d` as a bit string $l$ and returns whether $l = []$ or $l$ ends in `true` (`false` if `d` is not the encoding of a bit string). `normBin d := if isCanonBin d then d else nil` and `natOf d := (decode (normBin d) : Option ℕ).getD 0`: every datum names a parameter, canonical binary numerals themselves and everything else $0$.
--
--   Lemmas: `length_toBitsPost`, `stackStep_false`, `stackStep_true_cons_cons`, `stackRun_nil`, `stackRun_cons`, `stackRun_toBitsPost` (`stackRun (d.toBitsPost ++ rest) s = stackRun rest (d :: s)`), `parse_toBitsPost`, `isBit_ofBool`, `bits_getLast`, `isCanonBin_encode`, `bits_foldr_of_canon`, `normBin_encode`, `natOf_encode`, `size_eq_recD`, and `Primrec` lemmas for `stackStep`, `parse`, `isCanonBin`, `normBin`, decoding a natural number, `natOf` and `Data.size` (`primrec_size`).
--
--   **Formalization Note**. Postorder rather than the preorder `Data.toBits`, because a stack machine reads it back and a loop of the ambient model can run a stack machine, whereas a recursive-descent reader would need recursion; the ambient program is in another module, this bundle has the mathematics and the primitive recursive versions. Reader and normalization are total, so no validity condition on strings is needed. `primrec_size` makes the level $2^{K+1+\mathrm{esize}(e)}$ of the halting reduction computable.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Descriptions.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Descriptions.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
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
import Theorems.Thm_MIPRE_Cost_Data_primrec_recD

/-!
# Descriptions as bit strings: the postorder serialization of data

Blueprint `rem:compression-abstract`, item 1: the strings of the compressibility criterion are
*descriptions*, pairs `(λ, decider)` of a parameter and a decider program. This file fixes how
such a pair travels as a bit string.

A pair is data (`cons (encode λ) (encode decider)`), and data is serialized in **postorder**:
`nil ↦ 0`, `cons a b ↦ a · b · 1` (`Data.toBitsPost`). Postorder, rather than the preorder
`Data.toBits`, because it is read back by a *stack machine* (`Data.stackStep`): a `0` pushes
`nil`, a `1` pops two entries and pushes their pair. A loop of the ambient model can run a stack
machine on a bit string, whereas a recursive-descent reader would need recursion; the ambient
program is in `Halting/Lists.lean`, this file has the mathematics and the primitive recursive
versions.

* `Data.toBitsPost`, `Data.stackRun`, `Data.parse`: the serialization, the stack machine and
  the total reader (the top of the final stack, `nil` for an empty stack), with the round trip
  `Data.parse_toBitsPost`.
* `Data.normBin`: a total normalization of the parameter, the identity on canonical binary
  numerals (`encode n` for `n : ℕ`) and `nil` (`encode 0`) elsewhere; `Data.natOf` reads it.
  Every string thereby names a parameter and a decider (`descLam`, `descDecD`), and the
  wrapper decider of `Halting/Wrapper.lean` interprets the raw data the same way, so that no
  validity condition on strings is needed anywhere.

Each of these is also given in primitive recursive form, `Data.parse` and `Data.natOf` among
them, together with `Data.primrec_size`: the level at which the halting reduction runs is
`2 ^ (K + 1 + esize e)`, so the size of an encoding has to be computable.
-/

namespace MIPRE.Cost.Data

/-! ## Postorder serialization -/

/-- Postorder serialization of data: `nil ↦ 0`, `cons a b ↦ a · b · 1`. -/
def toBitsPost : Data → BitStr
  | nil => [false]
  | cons a b => a.toBitsPost ++ b.toBitsPost ++ [true]

@[simp] theorem length_toBitsPost (d : Data) : d.toBitsPost.length = d.size := by
  induction d with
  | nil => rfl
  | cons a b iha ihb =>
    simp only [toBitsPost, List.length_append, List.length_singleton, iha, ihb, size_cons]

/-- One step of the stack machine: a `0` pushes `nil`; a `1` pops `b` then `a` and pushes
`cons a b`, and does nothing on a stack with fewer than two entries. -/
def stackStep (s : List Data) (bit : Bool) : List Data :=
  if bit then
    if 2 ≤ s.length then cons (s.tail.head?.getD nil) (s.head?.getD nil) :: s.tail.tail else s
  else nil :: s

@[simp] theorem stackStep_false (s : List Data) : stackStep s false = nil :: s := rfl

@[simp] theorem stackStep_true_cons_cons (b a : Data) (s : List Data) :
    stackStep (b :: a :: s) true = cons a b :: s := by
  simp [stackStep]

/-- Running the stack machine over a bit string from a stack. -/
def stackRun (x : BitStr) (s : List Data) : List Data := x.foldl stackStep s

@[simp] theorem stackRun_nil (s : List Data) : stackRun [] s = s := rfl

@[simp] theorem stackRun_cons (bit : Bool) (x : BitStr) (s : List Data) :
    stackRun (bit :: x) s = stackRun x (stackStep s bit) := rfl

/-- The stack machine reads a serialization by pushing the datum. -/
theorem stackRun_toBitsPost (d : Data) (rest : BitStr) (s : List Data) :
    stackRun (d.toBitsPost ++ rest) s = stackRun rest (d :: s) := by
  induction d generalizing rest s with
  | nil => rfl
  | cons a b iha ihb =>
    simp only [toBitsPost, List.append_assoc, iha, ihb, List.singleton_append, stackRun_cons,
      stackStep_true_cons_cons]

/-- The total reader: the top of the final stack, `nil` for an empty stack. -/
def parse (x : BitStr) : Data := (stackRun x []).headD nil

@[simp] theorem parse_toBitsPost (d : Data) : parse d.toBitsPost = d := by
  have := stackRun_toBitsPost d [] []
  simp only [List.append_nil, stackRun_nil] at this
  simp [parse, this]

/-! ## Primitive recursiveness -/

theorem primrec_stackStep : Primrec₂ stackStep := by
  have hlen : PrimrecPred fun p : List Data × Bool => 2 ≤ p.1.length :=
    Primrec.nat_le.comp (Primrec.const 2) (Primrec.list_length.comp Primrec.fst)
  have hhead : Primrec fun p : List Data × Bool => p.1.head?.getD nil :=
    Primrec.option_getD.comp (Primrec.list_head?.comp Primrec.fst) (Primrec.const nil)
  have htail : Primrec fun p : List Data × Bool => p.1.tail := Primrec.list_tail.comp Primrec.fst
  have hhead2 : Primrec fun p : List Data × Bool => p.1.tail.head?.getD nil :=
    Primrec.option_getD.comp (Primrec.list_head?.comp htail) (Primrec.const nil)
  have htail2 : Primrec fun p : List Data × Bool => p.1.tail.tail := Primrec.list_tail.comp htail
  have hpush : Primrec fun p : List Data × Bool =>
      cons (p.1.tail.head?.getD nil) (p.1.head?.getD nil) :: p.1.tail.tail :=
    Primrec.list_cons.comp (primrec_cons.comp hhead2 hhead) htail2
  have hnil : Primrec fun p : List Data × Bool => (nil : Data) :: p.1 :=
    Primrec.list_cons.comp (Primrec.const nil) Primrec.fst
  exact (Primrec.cond Primrec.snd (Primrec.ite hlen hpush Primrec.fst) hnil).of_eq fun p => by
    obtain ⟨s, bit⟩ := p
    cases bit <;> simp [stackStep]

theorem primrec_parse : Primrec parse := by
  have h : Primrec fun x : BitStr => stackRun x [] :=
    (Primrec.list_foldl Primrec.id (Primrec.const []) (primrec_stackStep.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun x => rfl
  exact (Primrec.option_getD.comp (Primrec.list_head?.comp h) (Primrec.const nil)).of_eq fun x => by
    simp [parse, List.headD_eq_head?_getD]

/-! ## The parameter: canonical binary numerals -/

/-- A datum is a bit: `nil` or `cons nil nil`. -/
def isBit : Data → Bool
  | nil => true
  | cons nil nil => true
  | _ => false

@[simp] theorem isBit_ofBool (b : Bool) : isBit (ofBool b) = true := by cases b <;> rfl

/-- A datum is a canonical binary numeral: a list of bits, empty or ending in `true`. -/
def isCanonBin (d : Data) : Bool :=
  match (decode d : Option BitStr) with
  | some l => l = [] ∨ l.getLast? = some true
  | none => false

/-- `Nat.bits` is canonical: empty or ending in `true`. -/
theorem bits_getLast (n : ℕ) : n.bits = [] ∨ n.bits.getLast? = some true := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    right
    rcases ih with h | h
    · have hn0 : n = 0 := by
        have := Nat.foldr_bit_bits n
        rw [h] at this
        simpa using this.symm
      rw [h, hn hn0]
      rfl
    · rcases hb : n.bits with _ | ⟨c, l⟩
      · rw [hb] at h; simp at h
      · rw [hb] at h
        rw [List.getLast?_cons_cons]
        exact h

theorem isCanonBin_encode (n : ℕ) : isCanonBin (encode n) = true := by
  simp only [isCanonBin]
  show (match (decode (encode n.bits) : Option BitStr) with
    | some l => decide (l = [] ∨ l.getLast? = some true)
    | none => false) = true
  rw [SizedEncoding.decode_encode]
  simpa using bits_getLast n

/-- A canonical bit string is the binary expansion of the number it denotes. -/
theorem bits_foldr_of_canon (l : BitStr) (hl : l = [] ∨ l.getLast? = some true) :
    (l.foldr Nat.bit 0).bits = l := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rcases hl with h | h
    · cases h
    · have hl' : l = [] ∨ l.getLast? = some true := by
        rcases l with _ | ⟨c, l⟩
        · exact Or.inl rfl
        · right; rw [List.getLast?_cons_cons] at h; exact h
      have h0 : l.foldr Nat.bit 0 = 0 → b = true := by
        intro hzero
        rcases hl' with hnil | hlast
        · subst hnil
          simpa using h
        · exfalso
          have := ih (Or.inr hlast)
          rw [hzero, Nat.zero_bits] at this
          rw [← this] at hlast
          simp at hlast
      rw [List.foldr_cons, Nat.bits_append_bit _ _ h0, ih hl']

/-- Total normalization of a parameter: canonical binary numerals are kept, everything else
reads as `0`. -/
def normBin (d : Data) : Data := if isCanonBin d then d else nil

/-- The parameter a datum denotes, after normalization. -/
def natOf (d : Data) : ℕ := ((decode (normBin d) : Option ℕ)).getD 0

@[simp] theorem normBin_encode (n : ℕ) : normBin (encode n) = encode n := by
  simp [normBin, isCanonBin_encode]

@[simp] theorem natOf_encode (n : ℕ) : natOf (encode n) = n := by
  simp [natOf, SizedEncoding.decode_encode]

/-! ## How large a parameter a short string can denote

The bound a string of length `L` places on the number it denotes. Obligation O4 of the
halting reduction needs it: the answer budget the classes are read with at level `n` grows
with the described string's own compression parameter (`MIPRE.Halting.ansBound`), while the
compression theorem's completeness clause supplies strategies at a budget fixed by the
compressor's output, so the two can only be related through a bound on that parameter. -/

theorem primrec_isCanonBin : Primrec isCanonBin := by
  have hA : PrimrecPred fun l : BitStr => l = [] :=
    PrimrecRel.comp Primrec.eq Primrec.id (Primrec.const [])
  obtain ⟨instB, hB⟩ : PrimrecPred fun l : BitStr => l.reverse.head? = some true :=
    PrimrecRel.comp Primrec.eq (Primrec.list_head?.comp Primrec.list_reverse)
      (Primrec.const (some true))
  have h1 : Primrec fun l : BitStr => decide (l = [] ∨ l.getLast? = some true) := by
    refine (Primrec.ite hA (Primrec.const true) hB).of_eq fun l => ?_
    by_cases h : l = [] <;> by_cases h2 : l.getLast? = some true <;>
      simp [h, h2, List.head?_reverse]
  refine (Primrec.option_casesOn primrec_decode_bitStr (Primrec.const false)
    (h1.comp Primrec.snd).to₂).of_eq fun d => ?_
  simp only [isCanonBin]
  cases (decode d : Option BitStr) <;> rfl

theorem primrec_normBin : Primrec normBin := by
  have hc : PrimrecPred fun d : Data => isCanonBin d = true :=
    ⟨inferInstance, primrec_isCanonBin.of_eq fun d => by cases h : isCanonBin d <;> simp [h]⟩
  exact (Primrec.ite hc Primrec.id (Primrec.const nil)).of_eq fun d => rfl

theorem primrec_decode_nat : Primrec fun d : Data => (decode d : Option ℕ) := by
  have hbit : Primrec₂ fun (b : Bool) (n : ℕ) => Nat.bit b n := by
    refine (Primrec.cond Primrec.fst
      (Primrec.succ.comp (Primrec.nat_double.comp Primrec.snd))
      (Primrec.nat_double.comp Primrec.snd)).of_eq fun p => ?_
    obtain ⟨b, n⟩ := p
    cases b <;> simp [Nat.bit]
  have hfold : Primrec fun l : BitStr => l.foldr Nat.bit 0 :=
    (Primrec.list_foldr Primrec.id (Primrec.const 0)
      (hbit.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
      fun l => rfl
  exact (Primrec.option_map primrec_decode_bitStr (hfold.comp Primrec.snd).to₂).of_eq fun d => rfl

theorem primrec_natOf : Primrec natOf :=
  Primrec.option_getD.comp (primrec_decode_nat.comp primrec_normBin) (Primrec.const 0)

/-! ## The size of data -/

/-- The size of data is a tree recursion. -/
theorem size_eq_recD (d : Data) : d.size = recD 1 (fun _ _ ra rb => ra + rb + 1) d := by
  induction d with
  | nil => rfl
  | cons a b iha ihb => rw [size_cons, recD_cons, iha, ihb]

/-- The size of data is primitive recursive, hence so is `esize` of anything whose encoding
is: `Cost.esize a = (encode a).size`. The halting reduction needs it for the level
`2 ^ (K + 1 + esize e)` at which the recursion runs. -/
theorem primrec_size : Primrec Data.size :=
  (primrec_recD 1 _ (Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
    (Primrec.const 1))).of_eq fun d => (size_eq_recD d).symm

end MIPRE.Cost.Data


