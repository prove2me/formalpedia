-- Prove2me | Definitions.Def_MazurTransfer_OriginalContinuousUnitRootCohomologyData20261019
-- name    : MazurTransfer_OriginalContinuousUnitRootCohomologyData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-20T23:20:21.377089+00:00
-- url     : https://prove2.me/theorems/1dfd9345-2d95-4718-be0c-513060235ecf
-- title:
--   Original unit-root cocycle subgroup and continuous H1 condition
-- statement:
--   Retain the same original literal mu19 coefficient values, unit-root predicate, cocycle subgroup, class subgroup and F19 submodule. The intrinsic coefficient multiplication and inversion certificates supply the same subgroup construction laws. Eight complete original types, six whole constructor values, both scoped provider types and their whole values, seven context types and four whole values, and every generated structural proof type are checked independently. Named downstream consumer: the actual selected pi Kummer unit condition at nineteen and its original Selmer subspace.
-- source:
--   MazurTheorem ContinuousUnitRootCohomology by Vas and contributors; original constructor interface with complete original type and whole-value audits, preserving per-file Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: unit-root representatives define a subgroup of the
EXISTING continuous cocycles and an F19 submodule of their EXISTING H1.
Coefficient representations and arithmetic automorphisms remain GIVEN.
The intrinsic coefficient multiplication and inversion certificates supply the same subgroup construction laws.
Named downstream consumer: the actual selected pi Kummer image at nineteen
and the conjugate character after compatible unramified splitting.
-/
import Definitions.Def_MazurTransfer_NineteenRootsGaloisRepresentationOriginalData20261018
import Definitions.Def_MazurTransfer_ContinuousCoefficientExponentF19ModuleData

noncomputable section
namespace MazurTransfer.ContinuousUnitRootCohomology
open NineteenRootsGaloisRepresentation RepresentationDiscreteCoefficients
open ContinuousFirstCohomologyPresentation ContinuousCoefficientExponentAndContinuity
variable (R K Γ : Type) [CommRing R] [Field K] [CharZero K] [Algebra R K]
  [Group Γ] [TopologicalSpace Γ]
local instance instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_continuousUnitRootCohomology : Module (ZMod 19) (Additive (Roots K)) := rootsZModModule K
variable (τ : Representation (ZMod 19) Γ (Additive (Roots K)))
variable (ι : Γ →* (K ≃ₐ[ℚ] K))

def coefficientUnit : Coefficient τ →* Kˣ where
  toFun x := x.val.toMul.val
  map_one' := rfl
  map_mul' _ _ := rfl

def coefficientValue (x : Coefficient τ) : K := (coefficientUnit K Γ τ x : K)

theorem coefficientValue_mul (x y : Coefficient τ) :
    coefficientValue K Γ τ (x * y) = coefficientValue K Γ τ x * coefficientValue K Γ τ y := rfl

theorem coefficientValue_inv (x : Coefficient τ) :
    coefficientValue K Γ τ x⁻¹ = (coefficientValue K Γ τ x)⁻¹ := by
  simp only [coefficientValue, map_inv, Units.val_inv_eq_inv_val]

def HasUnitRoot (z : continuousCocycles Γ (Coefficient τ)) : Prop :=
  ∃ (u : Rˣ) (β : K), β ≠ 0 ∧ β ^ 19 = algebraMap R K (u : R) ∧
    ∀ g : Γ, ι g β = coefficientValue K Γ τ (Additive.toMul (z.val g)) * β

def unitCocycles : AddSubgroup (continuousCocycles Γ (Coefficient τ)) where
  carrier := HasUnitRoot R K Γ τ ι
  zero_mem' := by
    refine ⟨1, 1, one_ne_zero, ?_, ?_⟩
    · simp
    · intro g
      change ι g 1 = (1 : K) * 1
      simp
  add_mem' := by
    rintro z w ⟨u, β, hβ, hp, hσ⟩ ⟨v, γ, hγ, hq, hτ⟩
    refine ⟨u * v, β * γ, mul_ne_zero hβ hγ, ?_, ?_⟩
    · simp only [mul_pow, hp, hq, Units.val_mul, map_mul]
    · intro g
      change ι g (β * γ) = coefficientValue K Γ τ
        ((Additive.toMul (z.val g) : Coefficient τ) * (Additive.toMul (w.val g) : Coefficient τ)) * (β * γ)
      rw [map_mul (ι g), hσ g, hτ g, coefficientValue_mul]
      ring
  neg_mem' := by
    rintro z ⟨u, β, hβ, hp, hσ⟩
    refine ⟨u⁻¹, β⁻¹, inv_ne_zero hβ, ?_, ?_⟩
    · rw [inv_pow, hp, map_units_inv]
    · intro g
      change ι g (β⁻¹) = coefficientValue K Γ τ ((Additive.toMul (z.val g) : Coefficient τ)⁻¹) * β⁻¹
      rw [coefficientValue_inv, map_inv₀ (ι g), hσ g, mul_inv_rev, mul_comm]

def unitClasses : AddSubgroup (H1 Γ (Coefficient τ)) :=
  (unitCocycles R K Γ τ ι).map (classMap Γ (Coefficient τ))

local instance instModuleZModOfNatNatH1CoefficientAdditiveSubtypeUnitsMemSubgroupRoots_continuousUnitRootCohomology : Module (ZMod 19) (H1 Γ (Coefficient τ)) := coefficientH1ZModModule τ

def unitCondition : Submodule (ZMod 19) (H1 Γ (Coefficient τ)) :=
  AddSubgroup.toZModSubmodule 19 (unitClasses R K Γ τ ι)





end MazurTransfer.ContinuousUnitRootCohomology
#print axioms MazurTransfer.ContinuousUnitRootCohomology.coefficientUnit
#print axioms MazurTransfer.ContinuousUnitRootCohomology.coefficientValue
#print axioms MazurTransfer.ContinuousUnitRootCohomology.coefficientValue_mul
#print axioms MazurTransfer.ContinuousUnitRootCohomology.coefficientValue_inv
#print axioms MazurTransfer.ContinuousUnitRootCohomology.HasUnitRoot
#print axioms MazurTransfer.ContinuousUnitRootCohomology.unitCocycles
#print axioms MazurTransfer.ContinuousUnitRootCohomology.unitClasses
#print axioms MazurTransfer.ContinuousUnitRootCohomology.unitCondition
#print axioms MazurTransfer.ContinuousUnitRootCohomology.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_continuousUnitRootCohomology
#print axioms MazurTransfer.ContinuousUnitRootCohomology.instModuleZModOfNatNatH1CoefficientAdditiveSubtypeUnitsMemSubgroupRoots_continuousUnitRootCohomology


