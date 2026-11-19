-- Prove2me | Definitions.Def_DeletionCode_HeaderRecovery
-- name    : DeletionCode_HeaderRecovery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:06:59.644141+00:00
-- url     : https://prove2.me/theorems/bed78b71-bdcf-4d76-9f23-fd9d1e12cde3
-- title:
--   Header Recovery
-- statement:
--   Definitions and structural lemmas for Header Recovery, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/HeaderRecovery.lean

import Definitions.Def_DeletionCode_Windows
set_option autoImplicit true
namespace DeletionCode.HeaderRecovery
open Windows
inductive Orientation where
  | deletion
  | insertion
  deriving DecidableEq
structure Header where
  orientation : Orientation
  rho : ℕ
  bit : Bool
def windowLength (k : ℕ) : ℕ := 3 * (k + 1)
def editOffset (k : ℕ) : ℕ := windowLength k - 1
def longLength (k : ℕ) (h : Header) : ℕ := 2 * windowLength k - h.rho
def shortLength (k : ℕ) (h : Header) : ℕ := longLength k h - 1
def negativePath (k : ℕ) (h : Header) (long : Letters) : Letters :=
  match h.orientation with
  | .deletion => long
  | .insertion => deleteAt long (editOffset k)
def positivePath (k : ℕ) (h : Header) (long : Letters) : Letters :=
  match h.orientation with
  | .deletion => deleteAt long (editOffset k)
  | .insertion => long
def negativeLength (k : ℕ) (h : Header) : ℕ :=
  match h.orientation with
  | .deletion => longLength k h
  | .insertion => shortLength k h
def positiveLength (k : ℕ) (h : Header) : ℕ :=
  match h.orientation with
  | .deletion => shortLength k h
  | .insertion => longLength k h
def negativeExtra (k : ℕ) (h : Header) : ℕ := negativeLength k h - windowLength k
def rebuildPositive (k : ℕ) (h : Header) (negative : Letters) : Letters :=
  match h.orientation with
  | .deletion => deleteAt negative (editOffset k)
  | .insertion => insertAt negative (editOffset k) h.bit
structure Seed where
  offset : ℕ
  bits : Letters
def shortenSeed (ell k : ℕ) (seed : Seed) (extra : Bool) : Seed :=
  if seed.offset + k ≤ ell then seed
  else if ell < seed.offset then ⟨seed.offset - 1, seed.bits⟩
  else ⟨seed.offset, deletionSeed k (ell - seed.offset) extra seed.bits⟩
def lengthenSeed (ell k : ℕ) (seed : Seed) (bit : Bool) : Seed :=
  if seed.offset + k ≤ ell then seed
  else if ell ≤ seed.offset then ⟨seed.offset + 1, seed.bits⟩
  else ⟨seed.offset, insertionSeed (ell - seed.offset) bit seed.bits⟩
def transferPositiveSeed (k : ℕ) (h : Header) (seed : Seed) (extra : Bool) : Seed :=
  match h.orientation with
  | .deletion => lengthenSeed (editOffset k) k seed h.bit
  | .insertion => shortenSeed (editOffset k) k seed extra
def ExtensionMatches (k : ℕ) (h : Header) (long : Letters)
    (seed : Seed) (extra : Bool) : Prop :=
  h.orientation = .insertion → seed.offset ≤ editOffset k →
    editOffset k < seed.offset + k →
      extra = negativePath k h long (seed.offset + k - 1)
abbrev Bits (n : ℕ) := Fin n → Bool
def padBits {n : ℕ} (bits : Bits n) : Letters :=
  fun i => if hi : i < n then bits ⟨i, hi⟩ else false
def transferFinite (k : ℕ) (h : Header) (offset : ℕ)
    (bits : Bits k) (extra : Bool) : ℕ × Bits k :=
  let output := transferPositiveSeed k h ⟨offset, padBits bits⟩ extra
  (output.offset, fun i => output.bits i.val)
def rebuildPositiveFinite (k : ℕ) (h : Header)
    (negative : Bits (negativeLength k h)) : Bits (positiveLength k h) :=
  fun i => rebuildPositive k h (padBits negative) i.val
end DeletionCode.HeaderRecovery


