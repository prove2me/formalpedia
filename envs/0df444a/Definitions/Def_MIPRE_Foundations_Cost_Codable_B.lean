-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Codable_B
-- name    : MIPRE_Foundations_Cost_Codable_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:21:18.193482+00:00
-- url     : https://prove2.me/theorems/c09051a0-fc7c-42e0-a7ad-6e6268b135f5
-- title:
--   Primitive recursive projections, decoders and the natural-number encoding on `Data` (codable addendum)
-- statement:
--   This bundle adds eighteen theorems, and no new definitions, to the already published bundle `MIPRE_Foundations_Cost_Codable`, which makes the data type `Data` of the ambient model a `Primcodable` type through Cantor pairing (`encodeNat`, `decodeNat`). By concept: (i) the constructor `cons` is `Primrec₂`; the projections `left`, `right` (`nil` on `nil`) are `Primrec`, with $\mathrm{encodeNat}(\mathrm{left}\,d)$ equal to $0$ when $\mathrm{encodeNat}\,d = 0$ and otherwise to the first component of $\mathrm{unpair}(\mathrm{encodeNat}\,d - 1)$, symmetrically for `right`; (ii) `unaryToNat` is `Primrec`, the chain indexing `getList` is `Primrec₂`, and $\mathrm{getList}\,(\mathrm{list}\,l)\,i = \mathrm{Env.get}\,l\,i$; (iii) `toBool?` equals the case split `nil ↦ some false`, `cons nil nil ↦ some true`, else `none`, and is `Primrec`; `toList? g` equals a tree recursion (`recD`) and is `Primrec` for every `Primrec` element decoder $g$; hence decoding `Data` into `Option BitStr` is `Primrec`; (iv) the encoding of naturals as data satisfies $\mathrm{encode}(0) = \mathrm{nil}$ and, for $n > 0$,
--
--   $$\mathrm{encode}(n) = \mathrm{cons}\big(b_n,\ \mathrm{encode}(\lfloor n/2 \rfloor)\big),\qquad b_n = \mathrm{cons}(\mathrm{nil},\mathrm{nil}) \text{ if } n \bmod 2 = 1,\quad b_n = \mathrm{nil} \text{ otherwise},$$
--
--   and $n \mapsto \mathrm{encode}(n) : \mathrm{Data}$ is `Primrec`; (v) exponentiation on $\mathbb{N}$ is `Primrec₂`, two `LawfulBEq` instances give the same `List.idxOf`, and the index of a bit string in a list of bit strings is `Primrec₂` at the instance `List.instBEq`. These lemmas are the interface through which the halting-problem form of the compression lemma reaches Mathlib's computability: every budgeted run of the tabulation feeds the machine an `encode (n, …)`.
--
--   **Formalization Note** `encodeNat_left`/`right` are stated with `Nat.unpair (Nat.pred (encodeNat d))`. `primrec_decode_bitStr` is `Primrec fun d : Data => (SizedEncoding.decode d : Option BitStr)`; `primrec_encode_nat` is `Primrec fun n : ℕ => (encode n : Data)`, `encode` being the `SizedEncoding` of naturals by their bit list `Nat.bits`. `primrec_idxOf_bitStr` is stated at `@List.idxOf BitStr List.instBEq`, and `List.idxOf_congr_inst` bridges it to the instance of Mathlib's `Primrec.list_idxOf`. `getList d n = left (right^[n] d)`; `Env.get` reads a list with `nil` beyond its end.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Codable.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Codable.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_Cost_Codable does not carry);
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
import Theorems.Thm_MIPRE_Cost_Data_primrec_recD

/-!
# `Data` as a primcodable type

`Data` is denumerable through Cantor pairing (`Data.encodeNat`/`Data.decodeNat`), hence
`Primcodable`, with primitive recursive constructor, projections, a tree-recursion
principle (`Data.primrec_recD`), unary numerals, list indexing and the decoders of bit
strings. This is the interface between the ambient model and Mathlib's computability
(`Cost/Partrec.lean`): everything the model manipulates is `Data` — programs included,
through `Prog.toData` — so no separate encoding of `Prog` is needed.
-/

namespace MIPRE.Cost

namespace Data

/-! ## `Data ≃ ℕ` -/

/-! ## Primitive recursive constructor and projections -/

theorem primrec_cons : Primrec₂ Data.cons := by
  refine Primrec₂.encode_iff.1 ?_
  refine (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst)
    (Primrec.encode.comp Primrec.snd))).of_eq ?_
  rintro ⟨a, b⟩
  rfl

theorem encodeNat_left (d : Data) : encodeNat (left d) =
    if encodeNat d = 0 then 0 else (Nat.unpair (Nat.pred (encodeNat d))).1 := by
  cases d <;> simp [Nat.unpair_pair]

theorem encodeNat_right (d : Data) : encodeNat (right d) =
    if encodeNat d = 0 then 0 else (Nat.unpair (Nat.pred (encodeNat d))).2 := by
  cases d <;> simp [Nat.unpair_pair]

theorem primrec_left : Primrec left := by
  refine Primrec.encode_iff.1 ?_
  refine (Primrec.ite (PrimrecRel.comp Primrec.eq Primrec.encode (Primrec.const 0))
    (Primrec.const 0)
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.pred.comp Primrec.encode)))).of_eq ?_
  intro d
  exact (encodeNat_left d).symm

theorem primrec_right : Primrec right := by
  refine Primrec.encode_iff.1 ?_
  refine (Primrec.ite (PrimrecRel.comp Primrec.eq Primrec.encode (Primrec.const 0))
    (Primrec.const 0)
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.pred.comp Primrec.encode)))).of_eq ?_
  intro d
  exact (encodeNat_right d).symm

/-! ## Tree recursion -/

/-! ## Unary numerals and list indexing -/

theorem primrec_unaryToNat : Primrec unaryToNat :=
  primrec_recD 0 _ (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))

theorem primrec_getList : Primrec₂ getList :=
  primrec_left.comp (Primrec.nat_iterate Primrec.snd Primrec.fst
    (primrec_right.comp Primrec.snd).to₂)

theorem getList_list (l : List Data) (i : ℕ) : getList (Data.list l) i = Env.get l i := by
  induction i generalizing l with
  | zero => cases l <;> rfl
  | succ i ih =>
    unfold getList
    rw [Function.iterate_succ_apply]
    cases l with
    | nil => simp [Function.iterate_fixed right_nil, Env.get_nil]
    | cons a l => simpa [getList, Function.iterate_succ_apply] using ih l

/-! ## Decoding bit strings -/

theorem toBool?_eq (d : Data) : toBool? d =
    if d = nil then some false else if d = cons nil nil then some true else none := by
  rcases d with _ | ⟨_ | ⟨a, b⟩, _ | ⟨c, e⟩⟩ <;> simp [toBool?]

theorem primrec_toBool? : Primrec toBool? :=
  (Primrec.ite (PrimrecRel.comp Primrec.eq Primrec.id (Primrec.const nil))
    (Primrec.const (some false))
    (Primrec.ite (PrimrecRel.comp Primrec.eq Primrec.id (Primrec.const (cons nil nil)))
      (Primrec.const (some true)) (Primrec.const none))).of_eq fun d => (toBool?_eq d).symm

theorem toList?_eq_recD {α : Type*} (g : Data → Option α) (d : Data) :
    toList? g d = recD (some []) (fun a _ _ rb => (g a).bind fun x => rb.map (x :: ·)) d := by
  induction d with
  | nil => rfl
  | cons a d _ ihd =>
    rw [recD_cons, ← ihd]
    simp only [toList?]
    cases g a <;> cases toList? g d <;> rfl

theorem primrec_toList? {α : Type*} [Primcodable α] {g : Data → Option α} (hg : Primrec g) :
    Primrec (toList? g) := by
  have hstep : Primrec fun p : (Data × Data) × Option (List α) × Option (List α) =>
      (g p.1.1).bind fun x => p.2.2.map (x :: ·) :=
    Primrec.option_bind (hg.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))
  exact (primrec_recD (some []) _ hstep).of_eq fun d => (toList?_eq_recD g d).symm

/-- Decoding bit strings from `Data` is primitive recursive. -/
theorem primrec_decode_bitStr :
    Primrec fun d : Data => (SizedEncoding.decode d : Option BitStr) :=
  primrec_toList? primrec_toBool?

/-! ## Encoding naturals

The companion of `primrec_decode_bitStr` in the other direction. A natural is encoded as the
bit string of `Nat.bits`, so its encoding satisfies the halving recursion below, and strong
recursion on `ℕ` turns that into a primitive recursive definition. Every budgeted run of the
tabulation feeds the machine an `encode (n, …)`, so this is on the critical path of
`MIPRE.Halting.tab_computable`. -/

/-- The binary encoding of a natural as data, in recursive form. -/
theorem encode_nat_rec (n : ℕ) : (encode n : Data) =
    if n = 0 then Data.nil
    else Data.cons (if n % 2 = 1 then Data.cons Data.nil Data.nil else Data.nil)
      (encode (n / 2) : Data) := by
  by_cases h : n = 0
  · subst h; rfl
  rw [if_neg h]
  show (encode n.bits : Data) = Data.cons _ (encode (n / 2).bits : Data)
  rcases Nat.even_or_odd n with he | ho
  · have h0 : n % 2 = 0 := Nat.even_iff.1 he
    have h2 : n = 2 * (n / 2) := by omega
    have hne : n / 2 ≠ 0 := by omega
    rw [if_neg (by omega)]
    conv_lhs => rw [h2]
    rw [Nat.bit0_bits _ hne]
    rfl
  · have h1 : n % 2 = 1 := Nat.odd_iff.1 ho
    have h2 : n = 2 * (n / 2) + 1 := by omega
    rw [if_pos h1]
    conv_lhs => rw [h2]
    rw [Nat.bit1_bits]
    rfl

/-- Encoding a natural as data is primitive recursive. -/
theorem primrec_encode_nat : Primrec fun n : ℕ => (encode n : Data) := by
  have hstep : Primrec₂ (fun (_ : Unit) (l : List Data) =>
      some (if l.length = 0 then Data.nil
        else Data.cons (if l.length % 2 = 1 then Data.cons Data.nil Data.nil else Data.nil)
          (l.getD (l.length / 2) Data.nil))) := by
    have hlen : Primrec fun p : Unit × List Data => p.2.length :=
      Primrec.list_length.comp Primrec.snd
    have body : Primrec fun p : Unit × List Data =>
        (if p.2.length = 0 then Data.nil
          else Data.cons (if p.2.length % 2 = 1 then Data.cons Data.nil Data.nil else Data.nil)
            (p.2.getD (p.2.length / 2) Data.nil)) := ?_
    · exact (Primrec.option_some.comp body).to₂
    refine Primrec.ite (Primrec.eq.comp hlen (Primrec.const 0)) (Primrec.const Data.nil) ?_
    refine primrec_cons.comp ?_ ?_
    · exact Primrec.ite
        (Primrec.eq.comp (Primrec.nat_mod.comp hlen (Primrec.const 2)) (Primrec.const 1))
        (Primrec.const (Data.cons Data.nil Data.nil)) (Primrec.const Data.nil)
    · exact (Primrec.list_getD Data.nil).comp Primrec.snd
        (Primrec.nat_div.comp hlen (Primrec.const 2))
  have H : ∀ (_ : Unit) (n : ℕ),
      (fun (_ : Unit) (l : List Data) =>
        some (if l.length = 0 then Data.nil
          else Data.cons (if l.length % 2 = 1 then Data.cons Data.nil Data.nil else Data.nil)
            (l.getD (l.length / 2) Data.nil))) ()
        ((List.range n).map fun m => (encode m : Data)) = some (encode n : Data) := by
    intro _ n
    simp only [List.length_map, List.length_range]
    by_cases h : n = 0
    · subst h; rfl
    rw [if_neg h]
    conv_rhs => rw [encode_nat_rec n, if_neg h]
    congr 2
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  exact (Primrec.nat_strong_rec (fun (_ : Unit) (n : ℕ) => (encode n : Data)) hstep H).comp
    (Primrec.const ()) Primrec.id

end Data

/-! ## Two small gaps in the ambient library -/

/-- Exponentiation is primitive recursive. Mathlib has `Nat.Primrec.pow` on the unpaired
form but no `Primrec₂` spelling. -/
theorem primrec_nat_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow

/-- Two `LawfulBEq` instances give the same `List.idxOf`. `List Bool` has its own `BEq`, while
Mathlib's `Primrec.list_idxOf` is stated at the one derived from `DecidableEq`; the two are
propositionally equal, but reducing them to a common normal form sends `whnf` a very long way
indeed, so the bridge is proved once, here, rather than left to unification. -/
theorem List.idxOf_congr_inst {α : Type*} (i1 i2 : BEq α) [@LawfulBEq α i1] [@LawfulBEq α i2]
    (a : α) (l : List α) : @List.idxOf α i1 a l = @List.idxOf α i2 a l := by
  show @List.findIdx α _ l = @List.findIdx α _ l
  congr 1
  funext b
  exact Bool.eq_iff_iff.2 (by rw [@beq_iff_eq α i1 _, @beq_iff_eq α i2 _])

/-- The index of a bit string in a list of bit strings, at the instance the enumerations of
`Halting/Enumerate.lean` actually elaborate to. -/
theorem primrec_idxOf_bitStr :
    Primrec₂ (fun (a : BitStr) (l : List BitStr) => @List.idxOf BitStr List.instBEq a l) :=
  Primrec.list_idxOf.of_eq fun a l => List.idxOf_congr_inst instBEqOfDecidableEq List.instBEq a l

end MIPRE.Cost


