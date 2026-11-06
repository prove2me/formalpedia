-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_RayQuotient
-- name    : OAI_NumberTheory_DirichletL_RayQuotient
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:00:25.843202+00:00
-- url     : https://prove2.me/theorems/4785e90e-6cd2-434f-b783-01897f25a7dd
-- title:
--   Ray Quotient
-- statement:
--   Definitions and structural lemmas for Ray Quotient, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayQuotient.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
set_option autoImplicit false
namespace OAI
namespace SevenEighths.RayQuotient
open SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
    (H : Subgroup (A ⧸ M)ˣ) (hH : globalUnits M ≤ H)
abbrev Characters := characters H
abbrev classNumber := Nat.card ((A ⧸ M)ˣ ⧸ H)
include hH
theorem character_unitInvariant (χ : Characters M H) :
    IdealCharacter.UnitInvariant M χ := by
  intro u
  exact (mem_characters_iff H χ).mp χ.property _ (hH ⟨u, rfl⟩)
def toFullRay : Characters M H →* rayCharacters M where
  toFun χ := ⟨χ, (mem_rayCharacters_iff M χ).mpr (character_unitInvariant M H hH χ)⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
variable [IsDomain A] [IsPrincipalIdealRing A]
def idealCharacter (χ : Characters M H) : Ideal A →*₀ ℂ :=
  IdealCharacter.ofResidue M χ (character_unitInvariant M H hH χ)
def identityClass : Set (Ideal A) :=
  {I | I ≠ ⊥ ∧ ∃ a : A, Ideal.span ({a} : Set A) = I ∧
    inUnitSubgroup H (Ideal.Quotient.mk M a)}
end
end SevenEighths.RayQuotient
end OAI


