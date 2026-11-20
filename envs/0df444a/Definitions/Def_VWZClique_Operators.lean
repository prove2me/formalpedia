-- Prove2me | Definitions.Def_VWZClique_Operators
-- name    : VWZClique_Operators
-- status  : Definition
-- author  : @orz
-- created : 2026-11-20T00:58:46.74918+00:00
-- url     : https://prove2.me/theorems/5f7abc41-1e69-475d-8295-efbdd57affa6
-- title:
--   Partial swaps and product-basis entries
-- statement:
--   The mask fixes a quadruple on exceptional bits and enforces crossed equalities elsewhere. The four one-bit vectors and their tensor products determine the low-rank factors.
-- source:
--   V. Vassilevska Williams and O. Zamir, The k-Clique hypothesis is dead, for good (2026), Sections 3.2 and 4. https://zamir.prof/kclq.pdf

import Mathlib

namespace VWZClique
abbrev Bits (L : ℕ) := Fin L → Bool
abbrev PairBits (L : ℕ) := Bits L × Bits L
abbrev BasisLabel (L : ℕ) := Fin L → Fin 4
abbrev Mask (L : ℕ) := Fin L → Option (Bool × Bool × Bool × Bool)

def swapOK {L : ℕ} (m : Mask L) (x y : PairBits L) : Prop :=
  ∀ i, match m i with
  | none => x.1 i = y.2 i ∧ x.2 i = y.1 i
  | some r => (x.1 i, x.2 i, y.1 i, y.2 i) = r

def oneBit (j : Fin 4) (s u : Bool) : ℚ :=
  if j = 0 then (if !s && !u then 1 else 0)
  else if j = 1 then (if s && u then 1 else 0)
  else if s = u then 0
  else if j = 2 ∨ s = false then 1 else -1

def basisEntry {L : ℕ} (j : BasisLabel L) (x : PairBits L) : ℚ :=
  ∏ i, oneBit (j i) (x.1 i) (x.2 i)

open Classical in
noncomputable def swapEntry {L : ℕ} (m : Mask L) (x y : PairBits L) : ℚ :=
  if swapOK m x y then 1 else 0
end VWZClique


