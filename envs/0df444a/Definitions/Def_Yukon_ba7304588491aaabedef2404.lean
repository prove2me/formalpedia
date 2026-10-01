-- Prove2me | Definitions.Def_Yukon_ba7304588491aaabedef2404
-- name    : Yukon_ba7304588491aaabedef2404
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:22:49.661983+00:00
-- url     : https://prove2.me/theorems/00b2bc34-a0a7-4509-a319-d2b53c38c2bd
-- title:
--   YukonModule.ArkLib.OracleReduction.Prelude.part0
-- statement:
--   Source module ArkLib.OracleReduction.Prelude.
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/OracleReduction/Prelude.lean
--
--   yukon-proof-operation:f6e7c382225106c2e2ecc614ec9151244a0abb951680eeef882e0afc269e609a
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246ZjZlN2MzODIyMjUxMDZjMmUyZWNjNjE0ZWM5MTUxMjQ0YTBhYmI5NTE2ODBlZWVmODgyZTBhZmMyNjllNjA5YSIsImhhc2giOiI3MTNkOGNmOTA3NGZiOGY0OGI2MTAzZTFjZmJhOWNkZTA4N2FjNTQzYWRjYjc3Y2YzMThkYzYyZjRiN2Q1M2Q5Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9iYTczMDQ1ODg0OTFhYWFiZWRlZjI0MDQiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Batteries.Data.Vector.Lemmas
import Definitions.Def_Yukon_19e49f429e40ab4a8ab6f6e7



import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.FinEnum
import Init.Data.UInt.Lemmas
import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.List.Sym
import Init
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Finset.Card
import Mathlib.Data.Vector.Defs
import Mathlib.CategoryTheory.Monad.Types
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Batteries.Control.AlternativeMonad
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Batteries.Control.OptionT
import Mathlib.Data.PFunctor.Multivariate.Basic
import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Tactic.Common
import Mathlib.Init
import Lean.Message
import Batteries.Tactic.Lint.Basic
import Batteries.Tactic.Lint
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.MvPolynomial.Eval
set_option backward.isDefEq.respectTransparency.types false
/-!
  # Prelude for Interactive (Oracle) Reductions

  This file contains preliminary definitions and instances that is used in defining I(O)Rs.
-/

open OracleComp

-- -- Notation for sums (maybe not needed?)
-- @[inherit_doc] postfix:max "↪ₗ" => Sum.inl
-- @[inherit_doc] postfix:max "↪ᵣ" => Sum.inr

/-- `⊕ᵥ` is notation for `Sum.rec`, the dependent elimination of `Sum.

This sends `(a : α) → γ (.inl a)` and `(b : β) → γ (.inr b)` to `(a : α ⊕ β) → γ a`. -/
infixr:35 " ⊕ᵥ " => Sum.rec

-- Figure out where to put this instance
instance instDecidableEqOption {α : Type*} [DecidableEq α] :
    DecidableEq (Option α) := inferInstance

/-- `VCVCompabible` is a type class for types that are finite, inhabited, and have decidable
  equality. These instances are needed when the type is used as the range of some `OracleSpec`. -/
class VCVCompatible (α : Type*) extends Fintype α, Inhabited α where
  [type_decidableEq' : DecidableEq α]

instance  _root_.instDecidableEqOfVCVCompatible {α : Type*} [VCVCompatible α] : DecidableEq α := VCVCompatible.type_decidableEq'

-- TODO: port first to batteries, second to mathlib

@[simp]
theorem Vector.ofFn_get {α : Type*} {n : ℕ} (v : Vector α n) : Vector.ofFn (Vector.get v) = v := by
  ext
  simp [getElem]

def Equiv.rootVectorEquivFin {α : Type*} {n : ℕ} : Vector α n ≃ (Fin n → α) :=
  ⟨Vector.get, Vector.ofFn, Vector.ofFn_get, fun f => funext <| Vector.get_ofFn f⟩

instance Vector.instFintype {α : Type*} {n : ℕ} [VCVCompatible α] : Fintype (Vector α n) :=
  Fintype.ofEquiv _ (Equiv.rootVectorEquivFin).symm

instance  _root_.instVCVCompatibleForallFin {α : Type*} {n : ℕ} [VCVCompatible α] : VCVCompatible (Fin n → α) where

instance  _root_.instVCVCompatibleVector {α : Type*} {n : ℕ} [VCVCompatible α] : VCVCompatible (Vector α n) where

/-- `Sampleable` extends `VCVCompabible` with `SampleableType` -/
class Sampleable (α : Type) extends VCVCompatible α, SampleableType α

instance  _root_.instDecidableEqOfSampleable {α : Type} [Sampleable α] : DecidableEq α := inferInstance

/-- Enum type for the direction of a round in a protocol specification. It is either `.P_to_V`
(the prover sends a message to the verifier) or `.V_to_P` (the verifier sends a challenge to the
prover). -/
inductive Direction where
  | P_to_V  -- Message
  | V_to_P -- Challenge
deriving DecidableEq, Inhabited, Repr

namespace Direction

/-- Equivalence between `Direction` and `Fin 2`, sending `V_to_P` to `0` and `P_to_V` to `1`
(the choice is essentially arbitrary). -/
def equivFin2 : Direction ≃ Fin 2 where
  toFun := fun dir => match dir with | .V_to_P => ⟨0, by decide⟩ | .P_to_V => ⟨1, by decide⟩
  invFun := fun n => match n with | ⟨0, _⟩ => .V_to_P | ⟨1, _⟩ => .P_to_V
  left_inv := fun dir => match dir with | .P_to_V => rfl | .V_to_P => rfl
  right_inv := fun n => match n with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl

/-- Equivalence between `Direction` and `Bool`, sending `V_to_P` to `false` and `P_to_V` to `true`
(the choice is essentially arbitrary). -/
def equivBool : Direction ≃ Bool where
  toFun := fun dir => match dir with | .V_to_P => false | .P_to_V => true
  invFun := fun b => match b with | false => .V_to_P | true => .P_to_V
  left_inv := fun dir => match dir with | .P_to_V => rfl | .V_to_P => rfl
  right_inv := fun b => match b with | false => rfl | true => rfl

/-- This allows us to write `0` for `.V_to_P` and `1` for `.P_to_V`. -/
instance  _root_.Direction.instCoeFinOfNatNat : Coe (Fin 2) Direction := ⟨equivFin2.invFun⟩

instance  _root_.Direction.instCoeBool : Coe Bool Direction := ⟨equivBool.invFun⟩

@[simp]
lemma not_P_to_V_eq_V_to_P {x : Direction} (h : x ≠ .V_to_P) : x = .P_to_V := by
  cases x <;> simp_all

@[simp]
lemma not_V_to_P_eq_P_to_V {x : Direction} (h : x ≠ .P_to_V) : x = .V_to_P := by
  cases x <;> simp_all

end Direction

section Relation

-- TODO: use mathlib's `Rel` which will be `Set`-based in the next update

/-- The associated language `Set α` for a relation `Set (α × β)`. -/
@[reducible]
def Set.language {α β} (rel : Set (α × β)) : Set α :=
  Prod.fst '' rel

@[simp]
theorem Set.mem_language_iff {α β} (rel : Set (α × β)) (stmt : α) :
    stmt ∈ rel.language ↔ ∃ wit, (stmt, wit) ∈ rel := by
  simp [language]

@[simp]
theorem Set.not_mem_language_iff {α β} (rel : Set (α × β)) (stmt : α) :
    stmt ∉ rel.language ↔ ∀ wit, (stmt, wit) ∉ rel := by
  simp [language]

/-- The trivial relation on Boolean statement and unit witness, which outputs the Boolean (i.e.
  accepts or rejects). -/
def acceptRejectRel : Set (Bool × Unit) :=
  { (true, ()) }

/-- The trivial relation on Boolean statement, no oracle statements, and unit witness. -/
def acceptRejectOracleRel : Set ((Bool × (∀ _ : Empty, Unit)) × Unit) :=
  { ((true, isEmptyElim), ()) }

@[simp]
theorem acceptRejectRel_language : acceptRejectRel.language = { true } := by
  unfold Set.language acceptRejectRel; simp

@[simp]
theorem acceptRejectOracleRel_language :
    acceptRejectOracleRel.language = { (true, isEmptyElim) } := by
  unfold Set.language acceptRejectOracleRel; simp

end Relation


