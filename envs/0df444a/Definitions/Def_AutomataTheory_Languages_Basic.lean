-- Prove2me | Definitions.Def_AutomataTheory_Languages_Basic
-- name    : AutomataTheory_Languages_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:11:31.23483+00:00
-- url     : https://prove2.me/theorems/75fa5ee7-a864-4d57-b00d-20b85844c57c
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean

import Definitions.Def_AutomataTheory_Sequences_Segments
set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
section Languages
variable {A : Type}
def ConcatFin (L0 L1 : Set (List A)) : Set (List A) :=
  { al | ∃ al0 al1, al0 ∈ L0 ∧ al1 ∈ L1 ∧ al0 ++ al1 = al }
instance : Mul (Set (List A)) :=
  { mul := ConcatFin }
def ConcatInf (L0 : Set (List A)) (L1 : Set (Stream' A)) : Set (Stream' A) :=
  { as | ∃ al0 as1, al0 ∈ L0 ∧ as1 ∈ L1 ∧ al0 ++ₛ as1 = as }
instance : HMul (Set (List A)) (Set (Stream' A)) (Set (Stream' A)) :=
  { hMul := ConcatInf }
def IterFin (L : Set (List A)) : ℕ → Set (List A)
  | 0 => {[]}
  | n + 1 => (IterFin L n) * L
instance instIterFin : HPow (Set (List A)) (ℕ) (Set (List A)) :=
  { hPow := IterFin }
def IterStar (L : Set (List A)) : Set (List A) :=
  ⋃ n : ℕ, L ^ n
instance instIterStar : KStar (Set (List A)) :=
  { kstar := IterStar }
def IterOmega (L : Set (List A)) : Set (Stream' A) :=
  { as | ∃ φ : Stream' ℕ, StrictMono φ ∧ φ 0 = 0 ∧ ∀ m, as.extract (φ m) (φ (m + 1)) ∈ L }
@[notation_class]
class OmegaPower (α : Type) (β : outParam (Type)) where
  omegaPower : α → β
postfix:1024 "^ω" => OmegaPower.omegaPower
instance instIterOmega : OmegaPower (Set (List A)) (Set (Stream' A)) :=
  { omegaPower := IterOmega }
def OmegaLimit (L : Set (List A)) : Set (Stream' A) :=
  { as | ∃ᶠ m in atTop, as.extract 0 m ∈ L }
@[notation_class]
class OmegaLimitCls (α : Type) (β : outParam (Type)) where
  omegaLimit : α → β
postfix:1024 "↗ω" => OmegaLimitCls.omegaLimit
instance instOmegaLimit : OmegaLimitCls (Set (List A)) (Set (Stream' A)) :=
  { omegaLimit := OmegaLimit }
end Languages


