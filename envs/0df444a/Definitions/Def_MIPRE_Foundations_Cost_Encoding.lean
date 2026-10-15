-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Encoding
-- name    : MIPRE_Foundations_Cost_Encoding
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-12T16:02:44.436734+00:00
-- url     : https://prove2.me/theorems/3c5cf47c-7fae-473c-a7bb-79aac7401587
-- title:
--   Size-aware encodings: bits, bit strings, binary numbers, pairs and programs as data
-- statement:
--   This bundle is the interface between ordinary types and the ambient model: how a value becomes a tree, and what its size is.
--
--   `MIPRE.Cost.SizedEncoding` $\alpha$ is a class packaging an encoding $\mathrm{encode} : \alpha \to \mathrm{Data}$ and a partial decoding $\mathrm{decode} : \mathrm{Data} \to \mathrm{Option}\ \alpha$ with $\mathrm{decode}(\mathrm{encode}\ a) = a$ for every $a$. `MIPRE.Cost.esize` $a = \mathrm{size}(\mathrm{encode}\ a)$ is the size of a value, which is also the length of its preorder serialization: an honest bit length up to a constant factor. All polynomial-time statements of the project are relative to these encodings. `MIPRE.Cost.BitStr` is the type of bit strings, $\{0,1\}^*$, as lists of Booleans.
--
--   The concrete encodings, in the order of the file: `MIPRE.Cost.Data.ofBool` encodes a bit as $\mathrm{false} \mapsto \mathtt{nil}$ and $\mathrm{true} \mapsto \mathtt{cons}(\mathtt{nil}, \mathtt{nil})$, with inverse `MIPRE.Cost.Data.toBool?`; `MIPRE.Cost.Data.ofList` $f$ encodes a list elementwise through $f$ as a $\mathtt{cons}$-chain ending in $\mathtt{nil}$, with inverse `MIPRE.Cost.Data.toList?` $g$. These give the instances `MIPRE.Cost.instSizedEncodingBool` and `MIPRE.Cost.instSizedEncodingBitStr`; a bit string of length $\ell$ has size between $2\ell + 1$ and $4\ell + 1$. `MIPRE.Cost.instSizedEncodingNat` encodes a natural number $n$ in **binary**, least significant bit first, as the bit string of its binary digits (Mathlib's `Nat.bits`), so that $\mathrm{esize}(n) \le 4\,|n| + 1$ where $|n|$ is the binary length of $n$; this is the encoding under which indices "$n$ in binary" enter succinct descriptions. `MIPRE.Cost.instSizedEncodingProd` encodes a pair as $\mathtt{cons}(\mathrm{encode}\ a, \mathrm{encode}\ b)$, so that sizes are additive with no separators:
--   $$\mathrm{esize}(a, b) = \mathrm{esize}(a) + \mathrm{esize}(b) + 1 .$$
--
--   Programs are their own descriptions: `MIPRE.Cost.Prog.toData` serializes a program as a tree whose root pairs a unary tag in $\{0, \dots, 6\}$ (for $\mathtt{var}$, $\mathtt{nil}$, $\mathtt{cons}$, $\mathtt{elim}$, $\mathtt{let}$, $\mathtt{loop}$, $\mathtt{const}$) with the encoded fields, `MIPRE.Cost.Prog.ofData` reads a program back, and `MIPRE.Cost.Prog.instSizedEncoding` makes this the encoding of programs. Thus, for a program $e$, the quantity "$|e|$" in the statements of the toolkit is literally $\mathrm{esize}(e) = \mathrm{size}(\mathrm{toData}\ e)$.
--
--   The lemmas proved in the bundle are the round-trip equations for bits, lists and programs; the length bounds $\mathrm{length}(l) \le \mathrm{size}(\mathrm{ofList}\ f\ l)$, $|x| \le \mathrm{esize}(x)$ for a bit string $x$, and $|n| \le \mathrm{esize}(n)$ for $n \in \mathbb{N}$ (with $|n|$ the binary length `Nat.size n`); the additivity of $\mathrm{esize}$ on pairs; and the identity that folding `Nat.bit` over the binary digits of $n$ recovers $n$.
--
--   **Formalization Note**. The bundle deliberately does not reuse Mathlib's `Encodable`/`Primcodable`, which encode into $\mathbb{N}$ through the quadratic Cantor pairing `Nat.pair`: iterated use of that pairing distorts lengths exponentially, whereas the tree encoding is length-additive. Numbers are encoded in binary rather than unary precisely so that reading the compression parameter $n$ costs $O(\log n)$, and programs occur as data through their tree serialization rather than through a numeric Gödel numbering, so the s-m-n operation of the toolkit is a syntactic operation of linear cost.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Encoding.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Encoding.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic

/-!
# Size-aware encodings

Interface between ordinary types and the ambient model: a `SizedEncoding α` renders
`a : α` as a value `encode a : Data`, and `esize a` is its size (the length of its
preorder serialization `Data.toBits`), an honest bit-length up to a constant factor.
All polynomial-time statements (`Cost.PolyTime`) are relative to these encodings.

Conventions:

* bits are `false ↦ nil` and `true ↦ cons nil nil`;
* lists are `cons`-chains ending in `nil`, so a bit string of length `n` has size between
  `2n + 1` and `4n + 1`;
* natural numbers are encoded in **binary** (LSB first, `Nat.bits`), so
  `esize n ≤ 4 · Nat.size n + 1`;
* pairs are `cons`: `esize (a, b) = esize a + esize b + 1` — length-additive pairing, with
  no separators;
* programs are their tree encoding `Prog.toData`, a length-faithful serialization (this,
  not any numeric Gödel numbering, is how programs occur as *data*).

This deliberately does **not** reuse Mathlib's `Encodable`/`Primcodable`: those encode into
`ℕ` via the quadratic pairing `Nat.pair`, whose iterated use distorts lengths exponentially.
-/

namespace MIPRE.Cost

/-- A size-faithful encoding of `α` as data, with `decode` inverting `encode`. -/
class SizedEncoding (α : Type*) where
  /-- Encoding of a value. -/
  encode : α → Data
  /-- Decoding; must invert `encode` (on well-formed data). -/
  decode : Data → Option α
  decode_encode : ∀ a, decode (encode a) = some a

export SizedEncoding (encode decode)

/-- The size of a value: the number of nodes of its encoding. -/
def esize {α : Type*} [SizedEncoding α] (a : α) : ℕ := (encode a).size

/-- Binary strings, the `{0,1}*` of the paper. -/
abbrev BitStr := List Bool

namespace Data

/-- Bits: `false ↦ nil`, `true ↦ cons nil nil`. -/
def ofBool : Bool → Data
  | false => nil
  | true => cons nil nil

/-- Reading a bit back. -/
def toBool? : Data → Option Bool
  | nil => some false
  | cons nil nil => some true
  | cons _ _ => none

@[simp] theorem toBool?_ofBool (b : Bool) : toBool? (ofBool b) = some b := by cases b <;> rfl

/-- Lists: `cons`-chains ending in `nil`. -/
def ofList {α : Type*} (f : α → Data) : List α → Data
  | [] => nil
  | a :: l => cons (f a) (ofList f l)

/-- Reading a list back, elementwise. -/
def toList? {α : Type*} (g : Data → Option α) : Data → Option (List α)
  | nil => some []
  | cons a d => do
    let x ← g a
    let l ← toList? g d
    pure (x :: l)

theorem toList?_ofList {α : Type*} {f : α → Data} {g : Data → Option α}
    (hfg : ∀ a, g (f a) = some a) (l : List α) : toList? g (ofList f l) = some l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ofList, toList?, hfg, ih]

theorem length_le_size_ofList {α : Type*} (f : α → Data) (l : List α) :
    l.length ≤ (ofList f l).size := by
  induction l with
  | nil => simp [ofList]
  | cons a l ih =>
    have := size_pos (f a)
    simp only [ofList, size_cons, List.length_cons]
    omega

end Data

instance : SizedEncoding Bool where
  encode := Data.ofBool
  decode := Data.toBool?
  decode_encode := Data.toBool?_ofBool

/-- Bit strings encode as lists of bits. -/
instance : SizedEncoding BitStr where
  encode := Data.ofList Data.ofBool
  decode := Data.toList? Data.toBool?
  decode_encode := Data.toList?_ofList Data.toBool?_ofBool

theorem length_le_esize_bitStr (x : BitStr) : x.length ≤ esize x :=
  Data.length_le_size_ofList _ x

/-- Folding `Nat.bit` over the binary digits of `n` recovers `n`. -/
theorem Nat.foldr_bit_bits (n : ℕ) : n.bits.foldr Nat.bit 0 = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [Nat.zero_bits]
  | bit b n hn ih => rw [Nat.bits_append_bit n b hn, List.foldr_cons, ih]

/-- Natural numbers encode in **binary** (LSB first): the bit string `n.bits`. This is the
encoding under which indices "`n` in binary" enter succinct descriptions (blueprint
`def:succinct`). -/
instance : SizedEncoding ℕ where
  encode n := encode n.bits
  decode d := (decode d : Option BitStr).map fun l => l.foldr Nat.bit 0
  decode_encode n := by simp [SizedEncoding.decode_encode, Nat.foldr_bit_bits]

theorem size_le_esize_nat (n : ℕ) : Nat.size n ≤ esize n := by
  have := length_le_esize_bitStr n.bits
  rw [Nat.size_eq_bits_len] at this
  exact this

/-- Length-additive pairing: `encode (a, b) = cons (encode a) (encode b)`. -/
instance instSizedEncodingProd {α β : Type*} [SizedEncoding α] [SizedEncoding β] :
    SizedEncoding (α × β) where
  encode p := .cons (encode p.1) (encode p.2)
  decode d :=
    match d with
    | .cons a b =>
      match (decode a : Option α), (decode b : Option β) with
      | some x, some y => some (x, y)
      | _, _ => none
    | .nil => none
  decode_encode p := by
    obtain ⟨a, b⟩ := p
    simp [SizedEncoding.decode_encode]

@[simp] theorem esize_prod {α β : Type*} [SizedEncoding α] [SizedEncoding β] (a : α) (b : β) :
    esize (a, b) = esize a + esize b + 1 := rfl

/-! ## Programs as data -/

namespace Prog

/-- Programs as data: a unary tag (`0`–`6`) paired with the fields. -/
def toData : Prog → Data
  | var i => .cons (.ofNat 0) (.ofNat i)
  | nil => .cons (.ofNat 1) .nil
  | cons h t => .cons (.ofNat 2) (.cons h.toData t.toData)
  | elim i n c => .cons (.ofNat 3) (.cons (.ofNat i) (.cons n.toData c.toData))
  | let_ e b => .cons (.ofNat 4) (.cons e.toData b.toData)
  | loop b => .cons (.ofNat 5) b.toData
  | const d => .cons (.ofNat 6) d

/-- Reading a program back from its data (`ofData_toData`). -/
def ofData : Data → Option Prog
  | .cons .nil i => (Data.toNat? i).map var
  | .cons (.cons .nil .nil) .nil => some nil
  | .cons (.cons .nil (.cons .nil .nil)) (.cons h t) => do
    pure (cons (← ofData h) (← ofData t))
  | .cons (.cons .nil (.cons .nil (.cons .nil .nil))) (.cons i (.cons n c)) => do
    pure (elim (← Data.toNat? i) (← ofData n) (← ofData c))
  | .cons (.cons .nil (.cons .nil (.cons .nil (.cons .nil .nil)))) (.cons e b) => do
    pure (let_ (← ofData e) (← ofData b))
  | .cons (.cons .nil (.cons .nil (.cons .nil (.cons .nil (.cons .nil .nil))))) b =>
    (ofData b).map loop
  | .cons (.cons .nil (.cons .nil (.cons .nil (.cons .nil (.cons .nil (.cons .nil .nil))))))
      d => some (const d)
  | _ => none

theorem ofData_toData : ∀ p : Prog, ofData p.toData = some p
  | var i => by simp [toData, ofData, Data.ofNat]
  | nil => by simp [toData, ofData, Data.ofNat]
  | const d => by simp [toData, ofData, Data.ofNat]
  | cons h t => by simp [toData, ofData, Data.ofNat, ofData_toData h, ofData_toData t]
  | elim i n c => by simp [toData, ofData, Data.ofNat, ofData_toData n, ofData_toData c]
  | let_ e b => by simp [toData, ofData, Data.ofNat, ofData_toData e, ofData_toData b]
  | loop b => by simp [toData, ofData, Data.ofNat, ofData_toData b]

instance : SizedEncoding Prog where
  encode := toData
  decode := ofData
  decode_encode := ofData_toData

end Prog

end MIPRE.Cost


