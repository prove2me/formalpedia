-- Prove2me | Definitions.Def_MazurTransfer_OriginalThirteenthCharacterRealFieldData20261019
-- name    : MazurTransfer_OriginalThirteenthCharacterRealFieldData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-20T20:33:10.347707+00:00
-- url     : https://prove2.me/theorems/4e5c33f7-2977-4193-ae98-f7aa3a620af2
-- title:
--   Original real generator and thirteenth character field
-- statement:
--   Retain the original generator z plus its inverse and the field it generates over the rationals in the same algebraic closure. Both complete constructor types and whole values, and all three original scoped certificate types, are checked independently. Named downstream consumer: the actual selected reflected-character degree-six field and uniform finite-level character argument.
-- source:
--   MazurTheorem ThirteenCharacterRealField by Vas and contributors; original constructor interface with complete original type and whole-value audits, preserving per-file Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the kernel of the GIVEN conjugate order-six thirteenth
character fixes exactly the real generator z + z inverse. Over the fixed
algebraic closure this is the fixing subgroup of an explicit number field.
Named downstream consumer: the degree-six field comparison and arithmetic Selmer/character bounds for the
SAME actual reflected-character kernel, without a replacement field.
-/
import Definitions.Def_MazurTransfer_ThirteenToNineteenOriginalCharacterDataAndConstructorCertificates20261018
import Mathlib

noncomputable section
namespace MazurTransfer.ThirteenCharacterRealField
open ThirteenToNineteenCharacters
local instance instFactPrimeOfNatNat_thirteenCharacterRealField : Fact (Nat.Prime 13) := ⟨by decide⟩
local instance instFactPrimeOfNatNat_thirteenCharacterRealField_1 : Fact (Nat.Prime 19) := ⟨by decide⟩





variable {K : Type} [Field K] [CharZero K] [Normal ℚ K]
variable (z : K) (hz : IsPrimitiveRoot z 13)





def realGenerator : K := z + z⁻¹





local notation "F" => AlgebraicClosure ℚ
local instance instIsAlgClosureRatAlgebraicClosure_thirteenCharacterRealField : IsAlgClosure ℚ F := by
  have he : (DivisionRing.toRatAlgebra : Algebra ℚ F) =
      @AlgebraicClosure.instAlgebra ℚ inferInstance ℚ inferInstance (Algebra.id ℚ) := Subsingleton.elim _ _
  rw [he]
  infer_instance

def realField (z : F) : IntermediateField ℚ F := IntermediateField.adjoin ℚ {realGenerator z}







end MazurTransfer.ThirteenCharacterRealField
#print axioms MazurTransfer.ThirteenCharacterRealField.realGenerator
#print axioms MazurTransfer.ThirteenCharacterRealField.realField


