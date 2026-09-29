-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.eq_of_forall_mem_valuationSubring_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/661727d1-d8c6-5b0a-a91b-30b430949610

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_eq_of_forall_mem_valuationSubring_of_isSeparated

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

namespace M3aVCU

lemma spec_hom_ext_of_injective {O V K : CommRingCat.{u}} (ι : V ⟶ K)
    (hι : Function.Injective ι.hom) (g₁ g₂ : Spec V ⟶ Spec O)
    (h : Spec.map ι ≫ g₁ = Spec.map ι ≫ g₂) : g₁ = g₂ := by
  obtain ⟨φ₁, rfl⟩ := Spec.map_surjective g₁
  obtain ⟨φ₂, rfl⟩ := Spec.map_surjective g₂
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have h' : φ₁ ≫ ι = φ₂ ≫ ι := Spec.map_injective h
  congr 1
  ext a
  apply hι
  have := congrArg (fun g => (CommRingCat.Hom.hom g) a) h'
  simpa using this

lemma exists_lift {X : Scheme.{u}} [IsIntegral X] (V : ValuationSubring X.functionField) (c : X)
    (hc : ∀ s : X.presheaf.stalk c, algebraMap (X.presheaf.stalk c) X.functionField s ∈ V)
    (hc' : ∀ s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk c),
      algebraMap (X.presheaf.stalk c) X.functionField s ∈ V.nonunits) :
    ∃ l : Spec (CommRingCat.of V) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ l =
        X.fromSpecStalk (genericPoint X) ∧
      l.base (closedPoint V) = c := by
  classical

  let ρ : X.presheaf.stalk c →+* V :=
    (algebraMap (X.presheaf.stalk c) X.functionField).codRestrict V.toSubring hc
  have hρ : ∀ s, ((ρ s : V) : X.functionField) = algebraMap (X.presheaf.stalk c) X.functionField s :=
    fun s => rfl
  haveI : IsLocalHom ρ := by
    constructor
    intro s hs
    by_contra hns
    have hmem : s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk c) := hns
    have h1 := hc' s hmem
    rw [← hρ, ValuationSubring.coe_mem_nonunits_iff] at h1
    exact h1 hs
  haveI : IsLocalHom (CommRingCat.ofHom ρ).hom := ‹IsLocalHom ρ›
  refine ⟨Spec.map (CommRingCat.ofHom ρ) ≫ X.fromSpecStalk c, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp]
    have hcomp : CommRingCat.ofHom ρ ≫ CommRingCat.ofHom (algebraMap V X.functionField) =
        X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ c)) := by
      ext s
      change ((ρ s : V) : X.functionField) = _
      rw [hρ, RingHom.algebraMap_toAlgebra]
    rw [hcomp, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  · rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

end M3aVCU

open M3aVCU in
theorem solution
    {O : Type u} [CommRing O] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of O)) [IsSeparated f]
    (V : ValuationSubring X.functionField) (c₁ c₂ : X)
    (h₁ : ∀ s : X.presheaf.stalk c₁, algebraMap (X.presheaf.stalk c₁) X.functionField s ∈ V)
    (h₁' : ∀ s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk c₁),
      algebraMap (X.presheaf.stalk c₁) X.functionField s ∈ V.nonunits)
    (h₂ : ∀ s : X.presheaf.stalk c₂, algebraMap (X.presheaf.stalk c₂) X.functionField s ∈ V)
    (h₂' : ∀ s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk c₂),
      algebraMap (X.presheaf.stalk c₂) X.functionField s ∈ V.nonunits) :
    c₁ = c₂ := by
  classical
  obtain ⟨l₁, hl₁, hc₁⟩ := exists_lift V c₁ h₁ h₁'
  obtain ⟨l₂, hl₂, hc₂⟩ := exists_lift V c₂ h₂ h₂'

  have e₁ := congrArg (· ≫ f) hl₁
  have e₂ := congrArg (· ≫ f) hl₂
  simp only [Category.assoc] at e₁ e₂
  let S : ValuativeCommSq f :=
    { R := V
      K := X.functionField
      i₁ := X.fromSpecStalk (genericPoint X)
      i₂ := l₁ ≫ f
      commSq := ⟨e₁.symm⟩ }
  have hsub : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion f S
  have h12 : l₂ ≫ f = l₁ ≫ f := by
    refine spec_hom_ext_of_injective _ ?_ _ _ (e₂.trans e₁.symm)
    intro a b hab
    exact Subtype.ext hab
  let L₁ : S.commSq.LiftStruct := ⟨l₁, hl₁, rfl⟩
  let L₂ : S.commSq.LiftStruct := ⟨l₂, hl₂, h12⟩
  have hL : L₁ = L₂ := Subsingleton.elim _ _
  have hl : l₁ = l₂ := congrArg CommSq.LiftStruct.l hL
  rw [← hc₁, ← hc₂, hl]

end S_AlgebraicGeometry_Scheme_eq_of_forall_mem_valuationSubring_of_isSeparated
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_eq_of_forall_mem_valuationSubring_of_isSeparated (solution)
