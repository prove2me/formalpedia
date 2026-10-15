-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Codable
-- name    : MIPRE_Foundations_Cost_Codable
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-12T16:10:52.77906+00:00
-- url     : https://prove2.me/theorems/b83ff2ca-1c74-4bd5-a72f-79483f1700aa
-- title:
--   Trees as a denumerable, primcodable type: Cantor coding, projections, tree recursion and list indexing
-- statement:
--   This bundle connects the ambient data type to Mathlib's computability theory, by making `Data` a `Primcodable` type and providing the first-order operations on trees from which the machine step on data is built.
--
--   `MIPRE.Cost.Data.encodeNat` codes a tree as a natural number through Cantor pairing: $\mathtt{nil} \mapsto 0$ and $\mathtt{cons}(a, b) \mapsto \langle \mathrm{encodeNat}\ a, \mathrm{encodeNat}\ b \rangle + 1$, where $\langle \cdot, \cdot \rangle$ is Mathlib's pairing `Nat.pair`. `MIPRE.Cost.Data.decodeNat` is its inverse, defined by well-founded recursion on the number: $0 \mapsto \mathtt{nil}$, and $n + 1 \mapsto \mathtt{cons}$ of the decodings of the two components of $n$. `MIPRE.Cost.Data.equivNat` is the resulting bijection $\mathrm{Data} \simeq \mathbb{N}$, and `MIPRE.Cost.Data.instDenumerable` the `Denumerable Data` instance it induces, from which Mathlib supplies `Encodable` and `Primcodable` instances.
--
--   `MIPRE.Cost.Data.left` and `MIPRE.Cost.Data.right` are the two projections of a node, both returning $\mathtt{nil}$ on $\mathtt{nil}$. `MIPRE.Cost.Data.recD` $\mathit{base}\ \mathit{step}$ is structural recursion on trees with a first-order result in a type $\sigma$:
--   $$\mathrm{recD}(\mathtt{nil}) = \mathit{base}, \qquad \mathrm{recD}(\mathtt{cons}(a, b)) = \mathit{step}\ a\ b\ (\mathrm{recD}\ a)\ (\mathrm{recD}\ b).$$
--   `MIPRE.Cost.Data.unaryToNat` reads a unary numeral: it is the length of the right spine of a tree, so that $\mathrm{unaryToNat}(\mathrm{ofNat}\ n) = n$. `MIPRE.Cost.Data.getList` $d\ n = \mathrm{left}(\mathrm{right}^{n}(d))$ is the $n$-th element of a $\mathtt{cons}$-chain ($\mathtt{nil}$ beyond its end), the operation by which the machine on data looks a variable up in an encoded environment.
--
--   The lemmas proved in the bundle are the recursion equations of `encodeNat` and `decodeNat`, the two inverse laws $\mathrm{decodeNat}(\mathrm{encodeNat}\ d) = d$ and $\mathrm{encodeNat}(\mathrm{decodeNat}\ n) = n$, the equations of the projections and of `recD` on the two constructors, and the equations of `unaryToNat`, including $\mathrm{unaryToNat}(\mathrm{ofNat}\ n) = n$.
--
--   **Formalization Note**. The Cantor coding serves only Mathlib's computability interface, to state that the machine step is primitive recursive and evaluation partial recursive; it plays no role in the cost model, whose sizes are those of the tree encoding, precisely because iterated `Nat.pair` distorts lengths exponentially. Everything the model manipulates is `Data`, programs included through `Prog.toData`, so no separate `Primcodable` instance for programs is needed. The step function of the machine on data is written with `left`, `right`, `cons`, `unaryToNat` and `getList` only, so that its primitive recursiveness follows from that of these operations (`Data.primrec_recD` and its companions, uploaded separately).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Codable.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Codable.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops

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

/-- `Data` as natural numbers through Cantor pairing: `nil ↦ 0`, `cons a b ↦ pair a b + 1`. -/
def encodeNat : Data → ℕ
  | nil => 0
  | cons a b => Nat.pair (encodeNat a) (encodeNat b) + 1

/-- The inverse of `encodeNat`. -/
def decodeNat : ℕ → Data
  | 0 => nil
  | n + 1 => cons (decodeNat (Nat.unpair n).1) (decodeNat (Nat.unpair n).2)
decreasing_by
  all_goals
    try simp_wf
    first
    | exact Nat.lt_succ_of_le (Nat.unpair_left_le _)
    | exact Nat.lt_succ_of_le (Nat.unpair_right_le _)

@[simp] theorem encodeNat_nil : encodeNat nil = 0 := rfl

@[simp] theorem encodeNat_cons (a b : Data) :
    encodeNat (cons a b) = Nat.pair (encodeNat a) (encodeNat b) + 1 := rfl

@[simp] theorem decodeNat_zero : decodeNat 0 = nil := by rw [decodeNat]

@[simp] theorem decodeNat_succ (n : ℕ) :
    decodeNat (n + 1) = cons (decodeNat (Nat.unpair n).1) (decodeNat (Nat.unpair n).2) := by
  rw [decodeNat]

@[simp] theorem decodeNat_encodeNat : ∀ d : Data, decodeNat (encodeNat d) = d
  | nil => by simp
  | cons a b => by
    rw [encodeNat_cons, decodeNat_succ, Nat.unpair_pair]
    simp [decodeNat_encodeNat a, decodeNat_encodeNat b]

@[simp] theorem encodeNat_decodeNat (n : ℕ) : encodeNat (decodeNat n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [decodeNat_succ, encodeNat_cons, ih _ (Nat.lt_succ_of_le (Nat.unpair_left_le n)),
        ih _ (Nat.lt_succ_of_le (Nat.unpair_right_le n)), Nat.pair_unpair]

/-- `Data ≃ ℕ`. -/
def equivNat : Data ≃ ℕ where
  toFun := encodeNat
  invFun := decodeNat
  left_inv := decodeNat_encodeNat
  right_inv := encodeNat_decodeNat

instance : Denumerable Data := Denumerable.mk' equivNat

/-! ## Primitive recursive constructor and projections -/

/-- The head of a pair (`nil` on `nil`). -/
def left : Data → Data
  | nil => nil
  | cons a _ => a

/-- The tail of a pair (`nil` on `nil`). -/
def right : Data → Data
  | nil => nil
  | cons _ b => b

@[simp] theorem left_nil : left nil = nil := rfl
@[simp] theorem left_cons (a b : Data) : left (cons a b) = a := rfl
@[simp] theorem right_nil : right nil = nil := rfl
@[simp] theorem right_cons (a b : Data) : right (cons a b) = b := rfl

/-! ## Tree recursion -/

/-- Structural recursion on `Data` with a first-order result. -/
def recD {σ : Type*} (base : σ) (step : Data → Data → σ → σ → σ) : Data → σ
  | nil => base
  | cons a b => step a b (recD base step a) (recD base step b)

@[simp] theorem recD_nil {σ : Type*} (base : σ) (step : Data → Data → σ → σ → σ) :
    recD base step nil = base := rfl

@[simp] theorem recD_cons {σ : Type*} (base : σ) (step : Data → Data → σ → σ → σ)
    (a b : Data) : recD base step (cons a b) = step a b (recD base step a) (recD base step b) :=
  rfl

/-! ## Unary numerals and list indexing -/

/-- The length of the right spine: reads a unary numeral (`unaryToNat (ofNat n) = n`). -/
def unaryToNat : Data → ℕ := recD 0 fun _ _ _ rb => rb + 1

@[simp] theorem unaryToNat_nil : unaryToNat nil = 0 := rfl

@[simp] theorem unaryToNat_cons (a b : Data) : unaryToNat (cons a b) = unaryToNat b + 1 := rfl

@[simp] theorem unaryToNat_ofNat (n : ℕ) : unaryToNat (Data.ofNat n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Data.ofNat, ih]

/-- The `n`-th element of a `cons`-chain (`nil` beyond the end). -/
def getList (d : Data) (n : ℕ) : Data := left (right^[n] d)

/-! ## Decoding bit strings -/

/-! ## Encoding naturals

The companion of `primrec_decode_bitStr` in the other direction. A natural is encoded as the
bit string of `Nat.bits`, so its encoding satisfies the halving recursion below, and strong
recursion on `ℕ` turns that into a primitive recursive definition. Every budgeted run of the
tabulation feeds the machine an `encode (n, …)`, so this is on the critical path of
`MIPRE.Halting.tab_computable`. -/

end Data

/-! ## Two small gaps in the ambient library -/

end MIPRE.Cost


