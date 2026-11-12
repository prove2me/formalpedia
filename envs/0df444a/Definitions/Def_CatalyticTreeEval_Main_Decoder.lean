-- Prove2me | Definitions.Def_CatalyticTreeEval_Main_Decoder
-- name    : CatalyticTreeEval_Main_Decoder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:27:15.929406+00:00
-- url     : https://prove2.me/theorems/dea0db93-7f53-40b1-ada7-45c36c8ed5b9
-- title:
--   Ring-valued decoders and charged term access
-- statement:
--   For a modulus $m$, a decoder with $k$ terms consists of shifts $b_j\in\mathbb Z/m\mathbb Z$ and functions $\varphi_j:\mathbb Z/m\mathbb Z\to\mathbb Z/m\mathbb Z$. For a set $A$ containing zero it satisfies
--
--   $$\sum_j\varphi_j(z+ab_j)=0\quad(a\in A\setminus\{0\},\ z\in\mathbb Z/m\mathbb Z),\qquad\sum_j\varphi_j(0)=1.$$
--
--   The normalization is only at zero. The term printer receives construction parameters, the term index and a residue, and outputs both the shift and the term value in fixed-width binary form. All printing work is charged by the raw machine semantics.
--
--   These functions take values in the composite residue ring itself. They are not field-valued decoding polynomials, and no normalization at other residues is added.
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Definitions 2.8 and 3.16, printed p. 18 (PDF p. 20); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_Matching

set_option autoImplicit false

namespace CatalyticTreeEval.Main

structure Decoder (m k : ℕ) where
  shift : Fin k → ZMod m
  term : Fin k → ZMod m → ZMod m

def IsDecoder {m k : ℕ} (A : Set (ZMod m)) (D : Decoder m k) : Prop :=
  0 ∈ A ∧
  (∀ a ∈ A, a ≠ 0 → ∀ z, ∑ j, D.term j (z + a * D.shift j) = 0) ∧
  ∑ j, D.term j 0 = 1

def decoderRequest (params : List Bool) (j z : ℕ) : List Bool :=
  listCode params ++ natsCode [j,z]

def DecoderAccess {m k : ℕ} (M : Machine) (params : List Bool)
    (D : Decoder m k) (space : ℝ) : Prop :=
  ∀ j z, Prints M (decoderRequest params j.val z.val)
    (bits (Nat.log 2 (m - 1) + 1) (D.shift j).val ++
     bits (Nat.log 2 (m - 1) + 1) (D.term j z).val) space

/-- Two scalar fields, with no repeated shift in the term-access output. -/
def decoderOutput {m k : ℕ} (D : Decoder m k) (j : Fin k) (z : ZMod m) : List Bool :=
  bits (Nat.log 2 (m - 1) + 1) (D.shift j).val ++
    bits (Nat.log 2 (m - 1) + 1) (D.term j z).val


end CatalyticTreeEval.Main


