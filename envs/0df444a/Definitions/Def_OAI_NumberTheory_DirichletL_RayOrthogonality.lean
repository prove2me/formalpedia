-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_RayOrthogonality
-- name    : OAI_NumberTheory_DirichletL_RayOrthogonality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T04:59:29.571348+00:00
-- url     : https://prove2.me/theorems/96ebeb69-841c-48a7-8346-1d3a64afe83b
-- title:
--   Ray Orthogonality
-- statement:
--   Definitions and structural lemmas for Ray Orthogonality, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/RayOrthogonality.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_IdealCharacter
import Mathlib.NumberTheory.MulChar.Duality
set_option autoImplicit false
namespace OAI
namespace SevenEighths.RayOrthogonality
open scoped Classical
noncomputable section
section FiniteMonoid
variable {R : Type*} [CommMonoid R] [Finite R]
def characters (H : Subgroup Rˣ) : Subgroup (MulChar R ℂ) :=
  (MulChar.subgroupOrderIsoSubgroupMulChar R ℂ H).ofDual
instance (H : Subgroup Rˣ) : Fintype (characters H) := Fintype.ofFinite _
theorem mem_characters_iff (H : Subgroup Rˣ) (χ : MulChar R ℂ) :
    χ ∈ characters H ↔ ∀ u ∈ H, χ u = 1 :=
  MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff
def inUnitSubgroup (H : Subgroup Rˣ) (r : R) : Prop :=
  ∃ u : Rˣ, (u : R) = r ∧ u ∈ H
end FiniteMonoid
section Residues
variable {A : Type*} [CommRing A] (M : Ideal A) [Finite (A ⧸ M)]
def globalUnits : Subgroup (A ⧸ M)ˣ :=
  (Units.map (Ideal.Quotient.mk M).toMonoidHom).range
abbrev rayCharacters := characters (globalUnits M)
theorem mem_rayCharacters_iff (χ : MulChar (A ⧸ M) ℂ) :
    χ ∈ rayCharacters M ↔ IdealCharacter.UnitInvariant M χ := by
  rw [mem_characters_iff]
  constructor
  · intro h u
    exact h _ ⟨u, rfl⟩
  · intro h u hu
    obtain ⟨v, rfl⟩ := hu
    exact h v
def principalResidue (r : A ⧸ M) : Prop :=
  ∃ u : Aˣ, Ideal.Quotient.mk M u = r
abbrev rayCard : ℕ := Nat.card ((A ⧸ M)ˣ ⧸ globalUnits M)
section PrincipalIdeals
variable [IsDomain A] [IsPrincipalIdealRing A]
def idealCharacter (χ : rayCharacters M) : Ideal A →*₀ ℂ :=
  IdealCharacter.ofResidue M χ ((mem_rayCharacters_iff M χ).mp χ.property)
def principalIdeals : Set (Ideal A) :=
  {I | I ≠ ⊥ ∧ ∃ a : A, Ideal.span ({a} : Set A) = I ∧
    principalResidue M (Ideal.Quotient.mk M a)}
end PrincipalIdeals
end Residues
end
end SevenEighths.RayOrthogonality
end OAI


