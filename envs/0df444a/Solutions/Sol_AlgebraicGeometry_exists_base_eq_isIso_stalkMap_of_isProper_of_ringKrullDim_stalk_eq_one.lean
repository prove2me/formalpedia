-- Prove2me | solution 1 for AlgebraicGeometry.exists_base_eq_isIso_stalkMap_of_isProper_of_ringKrullDim_stalk_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/832389d8-b9af-587a-8e69-ae38d121b23a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_base_eq_isIso_stalkMap_of_isProper_of_ringKrullDim_stalk_eq_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

set_option maxHeartbeats 1600000 in
theorem solution
    {k : Type u} [Field k] {P' P : Scheme.{u}} (p : P ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    [IsIntegral P] [IsIntegral P'] (π : P' ⟶ P) [IsProper π]
    (W : P.Opens) (hW : (W : Set P).Nonempty) [IsIso (π ∣_ W)]
    (w : P) (hw₁ : ringKrullDim (P.presheaf.stalk w) = 1) (hwn : IsIntegrallyClosed (P.presheaf.stalk w)) :
    ∃ w' : P', π.base w' = w ∧ IsIso (π.stalkMap w') := by
  classical

  have hLN : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  haveI hDom : IsDomain (P.presheaf.stalk w) := inferInstance
  haveI hFR : IsFractionRing (P.presheaf.stalk w) P.functionField := inferInstance
  have hK1 : Ring.KrullDimLE 1 (P.presheaf.stalk w) := Ring.krullDimLE_iff.mpr (by simp [hw₁])
  have h4 : IsIntegrallyClosed (P.presheaf.stalk w) ∧ ∀ Q : Ideal (P.presheaf.stalk w), Q ≠ ⊥ →
      Q.IsPrime → Q = IsLocalRing.maximalIdeal (P.presheaf.stalk w) :=
    ⟨hwn, fun Q hQ hQ' => IsLocalRing.eq_maximalIdeal
      ((Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hK1) Q hQ hQ')⟩
  haveI hVal : ValuationRing (P.presheaf.stalk w) :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (P.presheaf.stalk w)).out 3 1).mp h4

  obtain ⟨x, hx⟩ := hW
  haveI hVne : Nonempty (π ⁻¹ᵁ W) := ⟨(inv (π ∣_ W)).base ⟨x, hx⟩⟩
  let η : ↥(π ⁻¹ᵁ W) := genericPoint (π ⁻¹ᵁ W)
  have hη : (π ⁻¹ᵁ W).ι.base η = genericPoint P' := genericPoint_eq_of_isOpenImmersion _
  have hg : (π ⁻¹ᵁ W).ι ≫ π = (π ∣_ W) ≫ W.ι := (morphismRestrict_ι π W).symm
  have hgen : π.base (genericPoint P') = genericPoint P := by
    rw [← hη, ← Scheme.Hom.comp_apply, hg]
    exact genericPoint_eq_of_isOpenImmersion _
  have hiso₁ : IsIso (((π ⁻¹ᵁ W).ι ≫ π).stalkMap η) := by
    rw [hg]; infer_instance
  have hiso₂ : IsIso (π.stalkMap ((π ⁻¹ᵁ W).ι.base η)) := by
    rw [Scheme.Hom.stalkMap_comp] at hiso₁
    have : π.stalkMap ((π ⁻¹ᵁ W).ι.base η) =
        (π.stalkMap ((π ⁻¹ᵁ W).ι.base η) ≫ (π ⁻¹ᵁ W).ι.stalkMap η) ≫
          inv ((π ⁻¹ᵁ W).ι.stalkMap η) := by
      simp
    rw [this]
    exact IsIso.comp_isIso' hiso₁ inferInstance
  have hiso : IsIso (π.stalkMap (genericPoint P')) := by rwa [hη] at hiso₂

  set e' : P'.presheaf.stalk (genericPoint P') ⟶ P.functionField :=
    inv (π.stalkMap (genericPoint P')) ≫ (P.presheaf.stalkCongr (.of_eq hgen)).hom with he'def
  have he' : IsIso e' := by rw [he'def]; infer_instance
  set i₁ : Spec P.functionField ⟶ P' := Spec.map e' ≫ P'.fromSpecStalk (genericPoint P') with hi₁def
  have hcomp : π.stalkMap (genericPoint P') ≫ e' = (P.presheaf.stalkCongr (.of_eq hgen)).hom := by
    rw [he'def]; simp
  have hL : i₁ ≫ π = P.fromSpecStalk (genericPoint P) := by
    rw [hi₁def, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc, hcomp,
      TopCat.Presheaf.stalkCongr_hom, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hRt : Spec.map (CommRingCat.ofHom (algebraMap (P.presheaf.stalk w) P.functionField)) ≫ P.fromSpecStalk w =
      P.fromSpecStalk (genericPoint P) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes w)
  have hsq : CommSq i₁ (Spec.map (CommRingCat.ofHom (algebraMap (P.presheaf.stalk w) P.functionField))) π (P.fromSpecStalk w) :=
    ⟨hL.trans hRt.symm⟩

  have hUC : UniversallyClosed π := inferInstance
  rw [UniversallyClosed.eq_valuativeCriterion] at hUC
  obtain ⟨hEx, -⟩ := hUC
  obtain ⟨⟨l, hl₁, hl₂⟩⟩ :=
    (hEx { R := (P.presheaf.stalk w : Type u), commRing := inferInstance, domain := hDom,
            valuationRing := hVal, K := (P.functionField : Type u), field := inferInstance,
            algebra := inferInstance, isFractionRing := hFR,
            i₁ := i₁, i₂ := P.fromSpecStalk w, commSq := hsq }).exists_lift
  change Spec.map (CommRingCat.ofHom (algebraMap (P.presheaf.stalk w) P.functionField)) ≫ l = i₁ at hl₁
  change l ≫ π = P.fromSpecStalk w at hl₂

  refine ⟨l.base (IsLocalRing.closedPoint (P.presheaf.stalk w)), ?_, ?_⟩
  · have h := Scheme.Hom.comp_apply l π (IsLocalRing.closedPoint (P.presheaf.stalk w))
    rw [hl₂] at h
    rw [← h]
    exact Scheme.fromSpecStalk_closedPoint

  · have hθ' : ∀ g : Spec (P.presheaf.stalk w) ⟶ P, g = P.fromSpecStalk w →
        IsIso (Scheme.stalkClosedPointTo g) := by
      rintro g rfl
      rw [Scheme.stalkClosedPointTo_fromSpecStalk]
      infer_instance
    have hθ := hθ' (l ≫ π) hl₂
    rw [Scheme.stalkClosedPointTo_comp] at hθ

    set φ := Scheme.stalkClosedPointTo l with hφ
    have hθ₂ : IsIso (π.stalkMap (l.base (IsLocalRing.closedPoint (P.presheaf.stalk w))) ≫ φ) := hθ
    have hlF : Spec.map φ ≫ P'.fromSpecStalk _ = l := by
      rw [hφ]; exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk l
    have hξw : genericPoint P' ⤳ l.base (IsLocalRing.closedPoint (P.presheaf.stalk w)) :=
      genericPoint_specializes _
    have key : φ ≫ CommRingCat.ofHom (algebraMap (P.presheaf.stalk w) P.functionField) =
        P'.presheaf.stalkSpecializes hξw ≫ e' := by
      apply Spec.map_injective
      rw [← cancel_mono (P'.fromSpecStalk (l.base (IsLocalRing.closedPoint (P.presheaf.stalk w))))]
      rw [Spec.map_comp_assoc, hlF, hl₁, Spec.map_comp_assoc,
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk, hi₁def]
    have hinj : Function.Injective φ.hom := by
      have h2 : Function.Injective
          (φ ≫ CommRingCat.ofHom (algebraMap (P.presheaf.stalk w) P.functionField)).hom := by
        rw [key, CommRingCat.hom_comp, RingHom.coe_comp]
        exact (asIso e').commRingCatIsoToRingEquiv.injective.comp
          (IsFractionRing.injective (P'.presheaf.stalk _) P'.functionField)
      rw [CommRingCat.hom_comp, RingHom.coe_comp] at h2
      exact h2.of_comp
    have hsurj : Function.Surjective φ.hom := by
      have hb' : Function.Surjective
          (π.stalkMap (l.base (IsLocalRing.closedPoint (P.presheaf.stalk w))) ≫ φ).hom :=
        (@asIso _ _ _ _ _ hθ₂).commRingCatIsoToRingEquiv.surjective
      rw [CommRingCat.hom_comp, RingHom.coe_comp] at hb'
      exact hb'.of_comp
    have hφiso : IsIso φ := (ConcreteCategory.isIso_iff_bijective φ).mpr ⟨hinj, hsurj⟩
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ (π.stalkMap _) φ hφiso hθ₂

end S_AlgebraicGeometry_exists_base_eq_isIso_stalkMap_of_isProper_of_ringKrullDim_stalk_eq_one
end P2MW
export P2MW.S_AlgebraicGeometry_exists_base_eq_isIso_stalkMap_of_isProper_of_ringKrullDim_stalk_eq_one (solution)
