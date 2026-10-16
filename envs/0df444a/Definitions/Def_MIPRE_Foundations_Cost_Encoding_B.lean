-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
-- name    : MIPRE_Foundations_Cost_Encoding_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:04:36.975758+00:00
-- url     : https://prove2.me/theorems/903c91ad-c51e-45d6-84c7-cbdb21ef7a38
-- title:
--   Size bounds for the encodings of bits, bit strings, binary numbers, pairs and programs (addition to the published encoding bundle)
-- statement:
--   This bundle adds eight lemmas, and no new definitions, to the already published bundle `MIPRE_Foundations_Cost_Encoding`, the interface between ordinary types and the ambient cost model: a `SizedEncoding α` renders $a : \alpha$ as a tree $\mathrm{encode}(a)$ of type `Data`, and $\mathrm{esize}(a)$ is the number of nodes of that tree. Bits are `Data.ofBool` ($\mathrm{false} \mapsto \mathtt{nil}$, $\mathrm{true} \mapsto \mathtt{cons}(\mathtt{nil},\mathtt{nil})$), lists are `Data.ofList f` ($\mathtt{cons}$-chains ending in $\mathtt{nil}$), bit strings `BitStr` are lists of bits, a natural number is its string of binary digits `Nat.bits` (least significant bit first), a pair is a single $\mathtt{cons}$, and a program $p$ is its tree serialization `Prog.toData p`.
--
--   The lemmas added, for a type with a `SizedEncoding` and $a$ in it, a bit $b$, a list $l$, a bit string $x$, a natural number $n$ and a program $p$: `esize_pos`, $0 < \mathrm{esize}(a)$; `Data.size_ofBool`, $\mathrm{size}(\mathrm{ofBool}\ b) \le 3$; `Data.size_ofList_le`, if $\mathrm{size}(f(a)) \le B$ for all $a$ then $\mathrm{size}(\mathrm{ofList}\ f\ l) \le (B+1)\,|l| + 1$; `esize_bitStr_le`, $\mathrm{esize}(x) \le 4|x| + 1$; `esize_nat_le`, with $|n|$ the binary length `Nat.size n`,
--   $$\mathrm{esize}(n) \le 4\,|n| + 1;$$
--   `encode_prod`, $\mathrm{encode}(a, b) = \mathtt{cons}(\mathrm{encode}\ a, \mathrm{encode}\ b)$; `Prog.esize_eq_size_toData`, $\mathrm{esize}(p) = \mathrm{size}(\mathrm{toData}\ p)$; and `Prog.two_le_esize`, $2 \le \mathrm{esize}(p)$, because `toData` is a $\mathtt{cons}$ node whatever the constructor, so no program encodes to $\mathtt{nil}$.
--
--   These are the upper bounds that make the encodings honest bit lengths up to a constant factor, and the last one is load-bearing: as its docstring records, it is what forces $2 \le \lambda$ in the boundedness predicate of normal form verifiers (`Verifier.IsBounded`), and so what puts the index of the halting reduction inside the range where its time clauses say anything.
--
--   **Formalization Note**. All eight are theorems of `MIPRE/Foundations/Cost/Encoding.lean` about definitions that are already published; `encode_prod` and `esize_eq_size_toData` hold by `rfl`. Nothing in the published bundle is changed; this delta only adds the declarations that the bundles of this upload use (the sampler bundle, through `encode` and `esize`). The bounds are exactly as displayed, non-strict except $0 < \mathrm{esize}(a)$.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Encoding.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Encoding.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_Cost_Encoding does not carry);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding

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

export SizedEncoding (encode decode)

theorem esize_pos {α : Type*} [SizedEncoding α] (a : α) : 0 < esize a := Data.size_pos _

namespace Data

theorem size_ofBool (b : Bool) : (ofBool b).size ≤ 3 := by cases b <;> simp [ofBool]

theorem size_ofList_le {α : Type*} {f : α → Data} {B : ℕ} (hf : ∀ a, (f a).size ≤ B)
    (l : List α) : (ofList f l).size ≤ (B + 1) * l.length + 1 := by
  induction l with
  | nil => simp [ofList]
  | cons a l ih =>
    have := hf a
    simp only [ofList, size_cons, List.length_cons, Nat.mul_succ]
    omega

end Data

theorem esize_bitStr_le (x : BitStr) : esize x ≤ 4 * x.length + 1 :=
  Data.size_ofList_le Data.size_ofBool x

theorem esize_nat_le (n : ℕ) : esize n ≤ 4 * Nat.size n + 1 := by
  have := esize_bitStr_le n.bits
  rw [Nat.size_eq_bits_len] at this
  exact this

theorem encode_prod {α β : Type*} [SizedEncoding α] [SizedEncoding β] (a : α) (b : β) :
    encode (a, b) = .cons (encode a) (encode b) := rfl

/-! ## Programs as data -/

namespace Prog

theorem esize_eq_size_toData (p : Prog) : esize p = p.toData.size := rfl

/-- **Every program has size at least two.** `Prog.toData` is a `Data.cons` whatever the
constructor, so no program encodes to `nil`. Small, and load-bearing: it is what forces
`2 ≤ λ` in `Verifier.IsBounded` (`Verifier.IsBounded.two_le`), and so what puts the index of
the halting reduction inside the range where `IsBounded`'s time clauses say anything. -/
theorem two_le_esize (p : Prog) : 2 ≤ esize p := by
  cases p <;>
    simp only [esize_eq_size_toData, toData, Data.size_cons, Data.size_nil, Data.size_ofNat] <;>
    omega

end Prog

end MIPRE.Cost


