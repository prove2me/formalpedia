-- Prove2me | solution 1 for AlgebraicGeometry.eq_of_stalk_le_valuationSubring_of_maximalIdeal_le_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/a741fc1d-77e7-59b8-be36-25cd139718dd

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_eq_of_stalk_le_valuationSubring_of_maximalIdeal_le_of_isSeparated

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CenterUniqueBody

variable {X : Scheme.{0}} [IsIntegral X] (𝒪v : ValuationSubring X.functionField)

noncomputable def locMap (x : X) (h : ∀ g : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField g ∈ 𝒪v) :
    X.presheaf.stalk x →+* 𝒪v :=
  (algebraMap (X.presheaf.stalk x) X.functionField).codRestrict 𝒪v h

theorem locMap_coe (x : X) (h : ∀ g : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField g ∈ 𝒪v)
    (g : X.presheaf.stalk x) : (locMap 𝒪v x h g : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField g := rfl

theorem algebraMap_comp_locMap (x : X) (h : ∀ g : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField g ∈ 𝒪v) :
    (algebraMap 𝒪v X.functionField).comp (locMap 𝒪v x h) = algebraMap (X.presheaf.stalk x) X.functionField :=
  RingHom.ext fun _ => rfl

theorem isLocalHom_locMap (x : X) (h : ∀ g : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField g ∈ 𝒪v)
    (h' : ∀ g : X.presheaf.stalk x, g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) →
      algebraMap (X.presheaf.stalk x) X.functionField g ∈ 𝒪v.nonunits) :
    IsLocalHom (locMap 𝒪v x h) := by
  refine ((IsLocalRing.local_hom_TFAE (locMap 𝒪v x h)).out 3 0).mp ?_
  intro g hg
  rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  exact h' g hg

noncomputable def lift (x : X) (h : ∀ g : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField g ∈ 𝒪v) :
    Spec (CommRingCat.of 𝒪v) ⟶ X :=
  Spec.map (CommRingCat.ofHom (locMap 𝒪v x h)) ≫ X.fromSpecStalk x

theorem algebraMap_stalk_eq (x : X) :
    algebraMap (X.presheaf.stalk x) X.functionField =
      (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ x))).hom := rfl

theorem generic_comp_lift (x : X) (h : ∀ g : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField g ∈ 𝒪v) :
    Spec.map (CommRingCat.ofHom (algebraMap 𝒪v X.functionField)) ≫ lift 𝒪v x h =
      X.fromSpecStalk (genericPoint X) := by
  rw [lift, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, algebraMap_comp_locMap, algebraMap_stalk_eq,
    CommRingCat.ofHom_hom]
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk _

theorem lift_closedPoint (x : X) (h : ∀ g : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField g ∈ 𝒪v)
    (h' : ∀ g : X.presheaf.stalk x, g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) →
      algebraMap (X.presheaf.stalk x) X.functionField g ∈ 𝒪v.nonunits) :
    lift 𝒪v x h (IsLocalRing.closedPoint 𝒪v) = x := by
  haveI : IsLocalHom (CommRingCat.ofHom (locMap 𝒪v x h)).hom := isLocalHom_locMap 𝒪v x h h'
  rw [lift, Scheme.Hom.comp_apply, AlgebraicGeometry.Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

end CenterUniqueBody

open CenterUniqueBody in
theorem solution
    {X : Scheme.{0}} [IsIntegral X] [X.IsSeparated]
    (𝒪v : ValuationSubring X.functionField) (x₁ x₂ : X)
    (h₁ : ∀ g : X.presheaf.stalk x₁, algebraMap (X.presheaf.stalk x₁) X.functionField g ∈ 𝒪v)
    (h₁' : ∀ g : X.presheaf.stalk x₁, g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x₁) →
      algebraMap (X.presheaf.stalk x₁) X.functionField g ∈ 𝒪v.nonunits)
    (h₂ : ∀ g : X.presheaf.stalk x₂, algebraMap (X.presheaf.stalk x₂) X.functionField g ∈ 𝒪v)
    (h₂' : ∀ g : X.presheaf.stalk x₂, g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x₂) →
      algebraMap (X.presheaf.stalk x₂) X.functionField g ∈ 𝒪v.nonunits) :
    x₁ = x₂ := by

  let S : ValuativeCommSq (terminal.from X) :=
    { R := 𝒪v
      K := X.functionField
      i₁ := X.fromSpecStalk (genericPoint X)
      i₂ := terminal.from _
      commSq := ⟨terminal.hom_ext _ _⟩ }
  have hsub : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion (terminal.from X) S
  let l₁ : S.commSq.LiftStruct := ⟨lift 𝒪v x₁ h₁, generic_comp_lift 𝒪v x₁ h₁, terminal.hom_ext _ _⟩
  let l₂ : S.commSq.LiftStruct := ⟨lift 𝒪v x₂ h₂, generic_comp_lift 𝒪v x₂ h₂, terminal.hom_ext _ _⟩
  have hl : lift 𝒪v x₁ h₁ = lift 𝒪v x₂ h₂ := congrArg CommSq.LiftStruct.l (hsub.elim l₁ l₂)
  rw [← lift_closedPoint 𝒪v x₁ h₁ h₁', ← lift_closedPoint 𝒪v x₂ h₂ h₂', hl]

end S_AlgebraicGeometry_eq_of_stalk_le_valuationSubring_of_maximalIdeal_le_of_isSeparated
end P2MW
export P2MW.S_AlgebraicGeometry_eq_of_stalk_le_valuationSubring_of_maximalIdeal_le_of_isSeparated (solution)
