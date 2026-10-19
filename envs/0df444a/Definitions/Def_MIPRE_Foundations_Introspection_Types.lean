-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_Types
-- name    : MIPRE_Foundations_Introspection_Types
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:49:29.712377+00:00
-- url     : https://prove2.me/theorems/9aac654e-1579-4317-8aac-dd8e996cec7c
-- title:
--   Definitions of Types: The introspection question types The source's type set consists of the Pauli types and two copies of `Introspect`,…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.Types` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The introspection question types. The source's type set consists of the Pauli types and two copies of `Introspect`, `Sample`, `Read`, and `Hide₁, ..., Hideℓ`. The Pauli type is a parameter so the foundational construction can be instantiated with the concrete Pauli test without importing a Background module.
--
--   **Definitions** (14): `MIPRE.Introspection.AuxType` (The additional tests, before specifying the original player's role.); `MIPRE.Introspection.AuxType.equivOption` (Three fixed tests followed by the hiding levels.); `MIPRE.Introspection.AuxType.instSizedEncoding`; `MIPRE.Introspection.AuxType.ofNat` (Out-of-range hiding labels are rejected by the decoder.); `MIPRE.Introspection.AuxType.toNat` (The auxiliary type's binary code, with the three fixed tags first.); `MIPRE.Introspection.QuestionType` (Pauli types together with the introspection tests for the two original players.); `MIPRE.Introspection.QuestionType.hide`; `MIPRE.Introspection.QuestionType.instSizedEncoding`; `MIPRE.Introspection.QuestionType.introspect`; `MIPRE.Introspection.QuestionType.ofData`; `MIPRE.Introspection.QuestionType.pauli`; `MIPRE.Introspection.QuestionType.read`; `MIPRE.Introspection.QuestionType.sample`; `MIPRE.Introspection.QuestionType.toData` (A single bit distinguishes Pauli labels from role-tagged auxiliary labels.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `ofNat_toNat`, `ofData_toData`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.Types` (`MIPRE/Foundations/Introspection/Types.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 2 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/Types.lean; blueprint def:intro-verifier

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/Types.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B

/-! # The introspection question types

The source's type set consists of the Pauli types and two copies of
`Introspect`, `Sample`, `Read`, and `Hide₁, ..., Hideℓ`. The Pauli type is a
parameter so the foundational construction can be instantiated with the
concrete Pauli test without importing a Background module.
-/

namespace MIPRE.Introspection

/-- The additional tests, before specifying the original player's role. -/
inductive AuxType (ℓ : ℕ)
  | introspect
  | sample
  | read
  /-- `k : Fin ℓ` represents the paper's hiding level `k + 1`. -/
  | hide (k : Fin ℓ)
  deriving DecidableEq, Fintype

namespace AuxType

/-- Three fixed tests followed by the hiding levels. -/
def equivOption (ℓ : ℕ) : AuxType ℓ ≃ Option (Option (Option (Fin ℓ))) where
  toFun
    | .introspect => none
    | .sample => some none
    | .read => some (some none)
    | .hide k => some (some (some k))
  invFun
    | none => .introspect
    | some none => .sample
    | some (some none) => .read
    | some (some (some k)) => .hide k
  left_inv t := by cases t <;> rfl
  right_inv t := by rcases t with _ | (_ | (_ | k)) <;> rfl

/-- The auxiliary type's binary code, with the three fixed tags first. -/
def toNat {ℓ : ℕ} : AuxType ℓ → ℕ
  | .introspect => 0
  | .sample => 1
  | .read => 2
  | .hide k => k.val + 3

/-- Out-of-range hiding labels are rejected by the decoder. -/
def ofNat (ℓ : ℕ) : ℕ → Option (AuxType ℓ)
  | 0 => some .introspect
  | 1 => some .sample
  | 2 => some .read
  | k + 3 => if h : k < ℓ then some (.hide ⟨k, h⟩) else none

@[simp] theorem ofNat_toNat {ℓ : ℕ} (t : AuxType ℓ) : ofNat ℓ t.toNat = some t := by
  cases t with
  | introspect => rfl
  | sample => rfl
  | read => rfl
  | hide k => simp [toNat, ofNat, k.isLt]

instance {ℓ : ℕ} : Cost.SizedEncoding (AuxType ℓ) where
  encode t := Cost.encode t.toNat
  decode d := (Cost.decode d : Option ℕ).bind (ofNat ℓ)
  decode_encode t := by simp [Cost.SizedEncoding.decode_encode]

end AuxType

/-- Pauli types together with the introspection tests for the two original players. -/
abbrev QuestionType (PauliType : Type*) (ℓ : ℕ) := PauliType ⊕ (AuxType ℓ × Bool)

namespace QuestionType

variable {PauliType : Type*} {ℓ : ℕ}

abbrev pauli (p : PauliType) : QuestionType PauliType ℓ := .inl p
abbrev introspect (w : Bool) : QuestionType PauliType ℓ := .inr (.introspect, w)
abbrev sample (w : Bool) : QuestionType PauliType ℓ := .inr (.sample, w)
abbrev read (w : Bool) : QuestionType PauliType ℓ := .inr (.read, w)
abbrev hide (w : Bool) (k : Fin ℓ) : QuestionType PauliType ℓ := .inr (.hide k, w)

section Encoding

open Cost

variable [SizedEncoding PauliType]

/-- A single bit distinguishes Pauli labels from role-tagged auxiliary labels. -/
def toData : QuestionType PauliType ℓ → Data
  | .inl p => .cons (encode false) (encode p)
  | .inr t => .cons (encode true) (encode t)

def ofData : Data → Option (QuestionType PauliType ℓ)
  | .nil => none
  | .cons tag payload => (decode tag : Option Bool).bind fun b =>
      if b then (decode payload : Option (AuxType ℓ × Bool)).map Sum.inr
      else (decode payload : Option PauliType).map Sum.inl

@[simp] theorem ofData_toData (t : QuestionType PauliType ℓ) : ofData (toData t) = some t := by
  cases t <;> simp [toData, ofData, SizedEncoding.decode_encode]

instance : SizedEncoding (QuestionType PauliType ℓ) where
  encode := toData
  decode := ofData
  decode_encode := ofData_toData

end Encoding

end QuestionType
end MIPRE.Introspection


