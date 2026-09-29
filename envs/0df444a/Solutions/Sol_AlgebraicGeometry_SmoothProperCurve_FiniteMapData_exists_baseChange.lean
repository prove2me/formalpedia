-- Prove2me | solution 1 for AlgebraicGeometry.SmoothProperCurve.FiniteMapData.exists_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/9ff3102b-41e0-5de5-b627-da022565c10d

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange.AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange.AlgebraicGeometry.SmoothProperCurve NeronModelInfra TensorProduct"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd pullbackRestrictIsoRestrict_hom_morphismRestrict_assoc Scheme.Hom Scheme.Γ Scheme.Hom.preimage_inf morphismRestrict_appTop IsAffineOpen.fromSpec_top Scheme.preimage_basicOpen IsAffineOpen.isoSpec_hom IsAffineOpen.SpecMap_appLE_fromSpec Spec IsIntegral Scheme.Hom.id_appTop Spec.map Scheme pullbackSpecIso Scheme.Opens.toSpecΓ_appTop Scheme.Hom.appTop Scheme.Γ_map_op Scheme.isoSpec_Spec_inv pullbackRestrictIsoRestrict_inv_fst_assoc Scheme.Hom.comp_appTop Scheme.Hom.naturality_assoc isAffineOpen_top Etale IsAffineOpen.isoSpec_inv_ι_assoc pullbackSpecIso_hom_fst IsAffineOpen Scheme.Hom.preimage_sup pullbackRestrictIsoRestrict Scheme.Opens Scheme.Opens.ι_image_top Scheme.ΓSpecIso_naturality Scheme.Opens.ι_appTop Scheme.Pullback.exists_preimage_pullback Scheme.Hom.appLE Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.isAffineHom_fst SmoothProperCurve.FiniteMapData"
namespace SmoothProperCurve
p2m_export "AlgebraicGeometry.SmoothProperCurve" "specMap baseChange sectionBaseChange sectionBaseChange_coe_fst sectionBaseChange_coe_snd FiniteMapData"
p2m_open "AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry"

section

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (R' : Type u) [CommRing R'] [Algebra R R']

theorem isPullback_sectionBaseChange :
    IsPullback (sectionBaseChange R' ε).1 (specMap R R') (pullback.fst c (specMap R R')) ε.1 := by
  refine IsPullback.of_isLimit' ⟨sectionBaseChange_coe_fst R' ε⟩ ?_

  have hsnd : ∀ s : PullbackCone (pullback.fst c (specMap R R')) ε.1,
      s.snd = s.fst ≫ pullback.snd c (specMap R R') ≫ specMap R R' := fun s => by
    calc s.snd = s.snd ≫ ε.1 ≫ c := by rw [ε.2, Category.comp_id]
      _ = s.fst ≫ pullback.fst c (specMap R R') ≫ c := by rw [← Category.assoc, ← s.condition, Category.assoc]
      _ = s.fst ≫ pullback.snd c (specMap R R') ≫ specMap R R' := by rw [pullback.condition]
  refine PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ pullback.snd c (specMap R R')) ?_ ?_ ?_
  · intro s
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, sectionBaseChange_coe_fst, ← Category.assoc (pullback.snd _ _),
        ← Category.assoc, ← hsnd, s.condition]
    · rw [Category.assoc, Category.assoc, sectionBaseChange_coe_snd, Category.comp_id]
  · intro s
    rw [Category.assoc, ← hsnd]
  · intro s m h₁ h₂
    change m = s.fst ≫ pullback.snd c (specMap R R')
    rw [← h₁, Category.assoc, sectionBaseChange_coe_snd, Category.comp_id]

theorem range_sectionBaseChange :
    Set.range (sectionBaseChange R' ε).1.base =
      (pullback.fst c (specMap R R')).base ⁻¹' Set.range ε.1.base := by
  have H := isPullback_sectionBaseChange ε R'
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨(specMap R R').base y, ?_⟩
    change (specMap R R' ≫ ε.1).base y = ((sectionBaseChange R' ε).1 ≫ pullback.fst c (specMap R R')).base y
    rw [sectionBaseChange_coe_fst]
  · rintro ⟨z, hz⟩
    obtain ⟨w, hw₁, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.fst c (specMap R R')) (g := ε.1)
      x z hz.symm
    refine ⟨H.isoPullback.inv.base w, ?_⟩
    change (H.isoPullback.inv ≫ (sectionBaseChange R' ε).1).base w = x
    rw [H.isoPullback_inv_fst]
    exact hw₁

end

namespace FiniteMapData
p2m_export "AlgebraicGeometry.SmoothProperCurve.FiniteMapData" "LevelSetsGenericallyEtale mk finite_f U f sup_eq_top m V isAffineOpen_U inf_eq_basicOpen_g isAffineOpen_V finite_g g inf_eq_basicOpen mem_U_iff levelSet_free res_f_mul_res_g"
p2m_open "AlgebraicGeometry.SmoothProperCurve.FiniteMapData"

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} (𝔉 : FiniteMapData c ε)
  (R' : Type u) [CommRing R'] [Algebra R R']

private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.isAffineOpen_preimage_U : IsAffineOpen ((pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.U) :=
  haveI := Scheme.TwoAffineOpenCover.isAffineHom_fst c R'
  𝔉.isAffineOpen_U.preimage _

p2m_export "AlgebraicGeometry.SmoothProperCurve.FiniteMapData" "isAffineOpen_preimage_U"
private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.isAffineOpen_preimage_V : IsAffineOpen ((pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.V) :=
  haveI := Scheme.TwoAffineOpenCover.isAffineHom_fst c R'
  𝔉.isAffineOpen_V.preimage _

p2m_export "AlgebraicGeometry.SmoothProperCurve.FiniteMapData" "isAffineOpen_preimage_V"
private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.preimage_U_sup_preimage_V :
    (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.U ⊔ (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.V = ⊤ := by
  rw [← Scheme.Hom.preimage_sup, 𝔉.sup_eq_top]
  rfl

p2m_export "AlgebraicGeometry.SmoothProperCurve.FiniteMapData" "preimage_U_sup_preimage_V"
private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mem_preimage_U_iff (x : ↑(pullback c (specMap R R'))) :
    x ∈ (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.U ↔ x ∉ Set.range (sectionBaseChange R' ε).1.base := by
  rw [range_sectionBaseChange ε R', Set.mem_preimage, ← 𝔉.mem_U_iff]
  rfl

p2m_export "AlgebraicGeometry.SmoothProperCurve.FiniteMapData" "mem_preimage_U_iff"
private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.preimage_U_inf_preimage_V_eq_basicOpen_f :
    (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.U ⊓ (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.V =
      (pullback c (specMap R R')).basicOpen (((pullback.fst c (specMap R R')).app 𝔉.U).hom 𝔉.f) := by
  rw [← Scheme.Hom.preimage_inf, 𝔉.inf_eq_basicOpen, Scheme.preimage_basicOpen]

p2m_export "AlgebraicGeometry.SmoothProperCurve.FiniteMapData" "preimage_U_inf_preimage_V_eq_basicOpen_f"
private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.preimage_U_inf_preimage_V_eq_basicOpen_g :
    (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.U ⊓ (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.V =
      (pullback c (specMap R R')).basicOpen (((pullback.fst c (specMap R R')).app 𝔉.V).hom 𝔉.g) := by
  rw [← Scheme.Hom.preimage_inf, 𝔉.inf_eq_basicOpen_g, Scheme.preimage_basicOpen]

p2m_export "AlgebraicGeometry.SmoothProperCurve.FiniteMapData" "preimage_U_inf_preimage_V_eq_basicOpen_g"

private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.res_app_f_mul_res_app_g :
    ((pullback c (specMap R R')).presheaf.map (homOfLE (inf_le_left :
        (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.U ⊓ (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.V ≤
          (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.U)).op).hom
        (((pullback.fst c (specMap R R')).app 𝔉.U).hom 𝔉.f) *
      ((pullback c (specMap R R')).presheaf.map (homOfLE (inf_le_right :
        (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.U ⊓ (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.V ≤
          (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.V)).op).hom
        (((pullback.fst c (specMap R R')).app 𝔉.V).hom 𝔉.g) = 1 := by
  set p := pullback.fst c (specMap R R') with hp

  have nat : ∀ {U U' : C.Opens} (i : U' ≤ U) (a : Γ(C, U)),
      ((pullback c (specMap R R')).presheaf.map (homOfLE (show p ⁻¹ᵁ U' ≤ p ⁻¹ᵁ U from
        fun x hx => i hx)).op).hom ((p.app U).hom a) = (p.app U').hom ((C.presheaf.map (homOfLE i).op).hom a) := by
    intro U U' i a
    have h := congrArg (fun φ => φ.hom a) (p.naturality (homOfLE i).op)
    exact h.symm
  have h₁ := nat (inf_le_left : 𝔉.U ⊓ 𝔉.V ≤ 𝔉.U) 𝔉.f
  have h₂ := nat (inf_le_right : 𝔉.U ⊓ 𝔉.V ≤ 𝔉.V) 𝔉.g

  change ((pullback c (specMap R R')).presheaf.map (homOfLE _).op).hom ((p.app 𝔉.U).hom 𝔉.f) *
    ((pullback c (specMap R R')).presheaf.map (homOfLE _).op).hom ((p.app 𝔉.V).hom 𝔉.g) = 1
  erw [h₁, h₂, ← map_mul, 𝔉.res_f_mul_res_g, map_one]
  rfl

p2m_export "AlgebraicGeometry.SmoothProperCurve.FiniteMapData" "res_app_f_mul_res_app_g"
end FiniteMapData

end AlgebraicGeometry.SmoothProperCurve

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd pullbackRestrictIsoRestrict_hom_morphismRestrict_assoc Scheme.Hom Scheme.Γ Scheme.Hom.preimage_inf morphismRestrict_appTop IsAffineOpen.fromSpec_top Scheme.preimage_basicOpen IsAffineOpen.isoSpec_hom IsAffineOpen.SpecMap_appLE_fromSpec Spec IsIntegral Scheme.Hom.id_appTop Spec.map Scheme pullbackSpecIso Scheme.Opens.toSpecΓ_appTop Scheme.Hom.appTop Scheme.Γ_map_op Scheme.isoSpec_Spec_inv pullbackRestrictIsoRestrict_inv_fst_assoc Scheme.Hom.comp_appTop Scheme.Hom.naturality_assoc isAffineOpen_top Etale IsAffineOpen.isoSpec_inv_ι_assoc pullbackSpecIso_hom_fst IsAffineOpen Scheme.Hom.preimage_sup pullbackRestrictIsoRestrict Scheme.Opens Scheme.Opens.ι_image_top Scheme.ΓSpecIso_naturality Scheme.Opens.ι_appTop Scheme.Pullback.exists_preimage_pullback Scheme.Hom.appLE Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.isAffineHom_fst SmoothProperCurve.FiniteMapData"
namespace AffineBaseChange
p2m_open "AlgebraicGeometry"

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (R' : Type u) [CommRing R'] [Algebra R R'] (U : C.Opens) (hU : IsAffineOpen U)
  [Algebra R Γ(C, U)]
  (halg : ∀ r : R, algebraMap R Γ(C, U) r = (c.appLE ⊤ U le_top) ((Scheme.ΓSpecIso (.of R)).inv r))

abbrev sm : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R R'))

abbrev p : pullback c (sm (R := R) R') ⟶ C := pullback.fst c (sm (R := R) R')

include halg in
lemma ofHom_algebraMap_eq :
    CommRingCat.ofHom (algebraMap R Γ(C, U)) = (Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ U le_top := by
  ext r
  exact halg r

include halg in

lemma specMap_algebraMap_eq :
    Spec.map (CommRingCat.ofHom (algebraMap R Γ(C, U))) = hU.isoSpec.inv ≫ U.ι ≫ c := by
  rw [ofHom_algebraMap_eq c U halg, Spec.map_comp, ← Scheme.isoSpec_Spec_inv,
    ← IsAffineOpen.fromSpec_top,
    IsAffineOpen.SpecMap_appLE_fromSpec c (isAffineOpen_top _) hU, IsAffineOpen.isoSpec_inv_ι_assoc]

def Φ : (↑((p c R') ⁻¹ᵁ U) : Scheme.{u}) ≅ Spec (CommRingCat.of (Γ(C, U) ⊗[R] R')) :=
  (pullbackRestrictIsoRestrict (p c R') U).symm ≪≫ pullbackSymmetry _ _ ≪≫
    pullbackRightPullbackFstIso c (sm (R := R) R') U.ι ≪≫
    asIso (pullback.map (U.ι ≫ c) (sm (R := R) R')
      (Spec.map (CommRingCat.ofHom (algebraMap R Γ(C, U)))) (sm (R := R) R')
      hU.isoSpec.hom (𝟙 _) (𝟙 _)
      (by rw [specMap_algebraMap_eq c U hU halg, Iso.hom_inv_id_assoc, Category.comp_id])
      (by rw [Category.comp_id, Category.id_comp])) ≪≫
    pullbackSpecIso R Γ(C, U) R'

lemma Φ_hom_comp_fst :
    (Φ c R' U hU halg).hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : Γ(C, U) →+* Γ(C, U) ⊗[R] R')) =
      ((p c R') ∣_ U) ≫ hU.isoSpec.hom := by
  simp only [Φ, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc, pullbackSpecIso_hom_fst,
    pullback.lift_fst, pullbackRightPullbackFstIso_hom_fst_assoc, pullbackSymmetry_hom_comp_fst_assoc]
  rw [Iso.inv_comp_eq, pullbackRestrictIsoRestrict_hom_morphismRestrict_assoc]

lemma Φ_hom_comp_snd :
    (Φ c R' U hU halg).hom ≫ Spec.map (CommRingCat.ofHom
      ((Algebra.TensorProduct.includeRight : R' →ₐ[R] Γ(C, U) ⊗[R] R') : R' →+* Γ(C, U) ⊗[R] R')) =
      ((p c R') ⁻¹ᵁ U).ι ≫ pullback.snd c (sm (R := R) R') := by
  simp only [Φ, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  rw [← pullbackSpecIso_inv_snd R Γ(C, U) R', Iso.hom_inv_id_assoc, pullback.lift_snd,
    Category.comp_id, pullbackRightPullbackFstIso_hom_snd, pullbackSymmetry_hom_comp_snd_assoc,
    pullbackRestrictIsoRestrict_inv_fst_assoc]

def ΓIso : Γ(pullback c (sm (R := R) R'), (p c R') ⁻¹ᵁ U) ≅ CommRingCat.of (Γ(C, U) ⊗[R] R') :=
  ((p c R') ⁻¹ᵁ U).topIso.symm ≪≫ (Scheme.Γ.mapIso (Φ c R' U hU halg).op).symm ≪≫
    Scheme.ΓSpecIso (.of (Γ(C, U) ⊗[R] R'))

lemma ΓIso_hom_eq : (ΓIso c R' U hU halg).hom =
    ((p c R') ⁻¹ᵁ U).topIso.inv ≫ (Φ c R' U hU halg).inv.appTop ≫
      (Scheme.ΓSpecIso (.of (Γ(C, U) ⊗[R] R'))).hom := by
  simp only [ΓIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.op_inv, Scheme.Γ_map_op]
  rfl

lemma Φ_hom_appTop_comp_inv_appTop :
    (Φ c R' U hU halg).hom.appTop ≫ (Φ c R' U hU halg).inv.appTop = 𝟙 _ := by
  rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]

lemma presheaf_map_comp_eq {X : Scheme.{u}} {A B D : X.Opens} (i : (Opposite.op A) ⟶ (Opposite.op B))
    (j : (Opposite.op B) ⟶ (Opposite.op D)) (k : (Opposite.op A) ⟶ (Opposite.op D)) :
    X.presheaf.map i ≫ X.presheaf.map j = X.presheaf.map k := by
  rw [← Functor.map_comp, Subsingleton.elim (i ≫ j) k]

lemma presheaf_map_eq_of_parallel {X : Scheme.{u}} {V W : X.Opens} (i j : (Opposite.op V) ⟶ (Opposite.op W)) :
    X.presheaf.map i = X.presheaf.map j := by
  rw [Subsingleton.elim i j]

lemma app_comp_ΓIso_hom :
    (p c R').app U ≫ (ΓIso c R' U hU halg).hom =
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Γ(C, U) →+* Γ(C, U) ⊗[R] R') := by
  have h := congrArg Scheme.Hom.appTop (Φ_hom_comp_fst c R' U hU halg)
  simp only [Scheme.Hom.comp_appTop, morphismRestrict_appTop] at h
  rw [IsAffineOpen.isoSpec_hom, Scheme.Opens.toSpecΓ_appTop, Category.assoc] at h

  have hn := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom : Γ(C, U) →+* Γ(C, U) ⊗[R] R'))
  rw [← Iso.eq_comp_inv] at hn
  rw [hn, Category.assoc, Category.assoc] at h

  have h' : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Γ(C, U) →+* Γ(C, U) ⊗[R] R') ≫
      (Scheme.ΓSpecIso (.of (Γ(C, U) ⊗[R] R'))).inv ≫ (Φ c R' U hU halg).hom.appTop =
      U.topIso.inv ≫ (p c R').app (U.ι ''ᵁ ⊤) ≫ (pullback c (sm (R := R) R')).presheaf.map
        (eqToHom (show ((p c R') ⁻¹ᵁ U).ι ''ᵁ ⊤ = (p c R') ⁻¹ᵁ (U.ι ''ᵁ ⊤) by
          rw [Scheme.Opens.ι_image_top, Scheme.Opens.ι_image_top])).op := by
    rw [← cancel_epi (Scheme.ΓSpecIso (.of Γ(C, U))).hom]
    exact h
  rw [ΓIso_hom_eq]

  have aux : (p c R').app U ≫ ((p c R') ⁻¹ᵁ U).topIso.inv =
      U.topIso.inv ≫ (p c R').app (U.ι ''ᵁ ⊤) ≫ (pullback c (sm (R := R) R')).presheaf.map
        (eqToHom (show ((p c R') ⁻¹ᵁ U).ι ''ᵁ ⊤ = (p c R') ⁻¹ᵁ (U.ι ''ᵁ ⊤) by
          rw [Scheme.Opens.ι_image_top, Scheme.Opens.ι_image_top])).op := by
    rw [Scheme.Opens.topIso_inv, Scheme.Opens.topIso_inv]
    erw [Scheme.Hom.naturality_assoc]
    rw [← Functor.map_comp]
    exact congrArg (fun k => (p c R').app U ≫ k) (presheaf_map_eq_of_parallel _ _)
  rw [← Category.assoc, aux, ← h']
  simp only [Category.assoc]
  rw [reassoc_of% (Φ_hom_appTop_comp_inv_appTop c R' U hU halg), Iso.inv_hom_id,
    Category.comp_id]

lemma ΓIso_hom_app (a : Γ(C, U)) :
    (ΓIso c R' U hU halg).hom (((p c R').app U) a) = a ⊗ₜ[R] (1 : R') := by
  change ((p c R').app U ≫ (ΓIso c R' U hU halg).hom) a = _
  rw [app_comp_ΓIso_hom]
  rfl

lemma algebraMap_comp_ΓIso_hom :
    (Scheme.ΓSpecIso (.of R')).inv ≫ (pullback.snd c (sm (R := R) R')).appLE ⊤ ((p c R') ⁻¹ᵁ U) le_top ≫
      (ΓIso c R' U hU halg).hom =
      CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : R' →ₐ[R] Γ(C, U) ⊗[R] R') :
        R' →+* Γ(C, U) ⊗[R] R') := by
  have h := congrArg Scheme.Hom.appTop (Φ_hom_comp_snd c R' U hU halg)
  simp only [Scheme.Hom.comp_appTop] at h
  have hn := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
    ((Algebra.TensorProduct.includeRight : R' →ₐ[R] Γ(C, U) ⊗[R] R') : R' →+* Γ(C, U) ⊗[R] R'))
  rw [← Iso.eq_comp_inv] at hn
  rw [hn, Category.assoc, Category.assoc, ← Iso.eq_inv_comp] at h

  rw [ΓIso_hom_eq]

  have aux : (pullback.snd c (sm (R := R) R')).appLE ⊤ ((p c R') ⁻¹ᵁ U) le_top ≫
      ((p c R') ⁻¹ᵁ U).topIso.inv =
      (pullback.snd c (sm (R := R) R')).appTop ≫ ((p c R') ⁻¹ᵁ U).ι.appTop := by
    rw [Scheme.Hom.appLE, Scheme.Opens.topIso_inv, Scheme.Opens.ι_appTop, Category.assoc]
    exact congrArg (fun k => (pullback.snd c (sm (R := R) R')).appTop ≫ k)
      (presheaf_map_comp_eq _ _ _)
  rw [reassoc_of% aux, ← reassoc_of% h]
  try simp only [Category.assoc]
  rw [reassoc_of% (Φ_hom_appTop_comp_inv_appTop c R' U hU halg), Iso.inv_hom_id,
    Category.comp_id]

lemma ΓIso_hom_algebraMap' (r' : R') :
    (ΓIso c R' U hU halg).hom (((pullback.snd c (sm (R := R) R')).appLE ⊤ ((p c R') ⁻¹ᵁ U) le_top)
      ((Scheme.ΓSpecIso (.of R')).inv r')) = (1 : Γ(C, U)) ⊗ₜ[R] r' := by
  change ((Scheme.ΓSpecIso (.of R')).inv ≫ (pullback.snd c (sm (R := R) R')).appLE ⊤ ((p c R') ⁻¹ᵁ U)
    le_top ≫ (ΓIso c R' U hU halg).hom) r' = _
  rw [algebraMap_comp_ΓIso_hom]
  rfl

section algebra

variable [Algebra R' Γ(pullback c (sm (R := R) R'), (p c R') ⁻¹ᵁ U)]
  (halg' : ∀ r' : R', algebraMap R' Γ(pullback c (sm (R := R) R'), (p c R') ⁻¹ᵁ U) r' =
    ((pullback.snd c (sm (R := R) R')).appLE ⊤ ((p c R') ⁻¹ᵁ U) le_top)
      ((Scheme.ΓSpecIso (.of R')).inv r'))

def bcEquiv : Γ(pullback c (sm (R := R) R'), (p c R') ⁻¹ᵁ U) ≃ₐ[R'] R' ⊗[R] Γ(C, U) :=
  AlgEquiv.ofRingEquiv (f := ((ΓIso c R' U hU halg).commRingCatIsoToRingEquiv).trans
      (Algebra.TensorProduct.comm R Γ(C, U) R').toRingEquiv) (fun r' => by
    change Algebra.TensorProduct.comm R Γ(C, U) R'
      ((ΓIso c R' U hU halg).hom (algebraMap R' _ r')) = _
    rw [halg', ΓIso_hom_algebraMap', Algebra.TensorProduct.comm_tmul,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply])

lemma bcEquiv_app (a : Γ(C, U)) :
    bcEquiv c R' U hU halg halg' ((p c R').app U a) = (1 : R') ⊗ₜ[R] a := by
  change Algebra.TensorProduct.comm R Γ(C, U) R' ((ΓIso c R' U hU halg).hom ((p c R').app U a)) = _
  rw [ΓIso_hom_app, Algebra.TensorProduct.comm_tmul]

lemma bcEquiv_symm_tmul (r' : R') (a : Γ(C, U)) :
    (bcEquiv c R' U hU halg halg').symm (r' ⊗ₜ[R] a) =
      algebraMap R' _ r' * (p c R').app U a := by
  apply (bcEquiv c R' U hU halg halg').injective
  rw [AlgEquiv.apply_symm_apply, map_mul, AlgEquiv.commutes, bcEquiv_app,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

omit hU halg in

lemma finite_aeval_tensor {Γ₀ : Type u} [CommRing Γ₀] [Algebra R Γ₀] (f : Γ₀)
    (hf : (Polynomial.aeval f : Polynomial R →ₐ[R] Γ₀).toRingHom.Finite) :
    (Polynomial.aeval ((1 : R') ⊗ₜ[R] f) : Polynomial R' →ₐ[R'] R' ⊗[R] Γ₀).toRingHom.Finite := by
  classical
  letI alg₀ : Algebra (Polynomial R) Γ₀ := (Polynomial.aeval f : Polynomial R →ₐ[R] Γ₀).toRingHom.toAlgebra
  letI alg₁ : Algebra (Polynomial R') (R' ⊗[R] Γ₀) :=
    (Polynomial.aeval ((1 : R') ⊗ₜ[R] f) : Polynomial R' →ₐ[R'] R' ⊗[R] Γ₀).toRingHom.toAlgebra
  have hfin : Module.Finite (Polynomial R) Γ₀ := hf
  change Module.Finite (Polynomial R') (R' ⊗[R] Γ₀)
  obtain ⟨s, hs⟩ := hfin.fg_top
  refine ⟨⟨s.image (fun a => (1 : R') ⊗ₜ[R] a), ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul r' a =>
    have ha : a ∈ Submodule.span (Polynomial R) (s : Set Γ₀) := by rw [hs]; trivial
    refine Submodule.span_induction (p := fun a _ => r' ⊗ₜ[R] a ∈
      Submodule.span (Polynomial R') ((fun a => (1 : R') ⊗ₜ[R] a) '' (s : Set Γ₀))) ?_ ?_ ?_ ?_ ha
    · intro a has

      have : r' ⊗ₜ[R] a = (Polynomial.C r' : Polynomial R') • ((1 : R') ⊗ₜ[R] a) := by
        change _ = (Polynomial.aeval ((1 : R') ⊗ₜ[R] f) (Polynomial.C r')) * ((1 : R') ⊗ₜ[R] a)
        rw [Polynomial.aeval_C, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
          RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, has, rfl⟩)
    · simp
    · intro a b _ _ ha hb
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ ha hb
    · intro q a _ ha

      have : r' ⊗ₜ[R] (q • a) = (Polynomial.map (algebraMap R R') q : Polynomial R') • (r' ⊗ₜ[R] a) := by
        change r' ⊗ₜ[R] (Polynomial.aeval f q * a) =
          (Polynomial.aeval ((1 : R') ⊗ₜ[R] f) (Polynomial.map (algebraMap R R') q)) * (r' ⊗ₜ[R] a)
        rw [Polynomial.aeval_map_algebraMap,
          show (Polynomial.aeval ((1 : R') ⊗ₜ[R] f)) q = (1 : R') ⊗ₜ[R] (Polynomial.aeval f q) from by
            rw [← Algebra.TensorProduct.includeRight_apply, Polynomial.aeval_algHom_apply]; rfl,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [this]
      exact Submodule.smul_mem _ _ ha

include hU halg halg' in

lemma finite_aeval_bc (f : Γ(C, U))
    (hf : (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Finite) :
    (Polynomial.aeval ((p c R').app U f) :
      Polynomial R' →ₐ[R'] Γ(pullback c (sm (R := R) R'), (p c R') ⁻¹ᵁ U)).toRingHom.Finite := by
  have h1 := finite_aeval_tensor (R := R) R' f hf
  have h2 := RingHom.finite_respectsIso.1 _ (bcEquiv c R' U hU halg halg').symm.toRingEquiv h1
  have heq : (Polynomial.aeval ((p c R').app U f) : Polynomial R' →ₐ[R'] _) =
      ((bcEquiv c R' U hU halg halg').symm : R' ⊗[R] Γ(C, U) →ₐ[R'] _).comp
        (Polynomial.aeval ((1 : R') ⊗ₜ[R] f)) := by
    apply Polynomial.algHom_ext
    rw [Polynomial.aeval_X, AlgHom.comp_apply, Polynomial.aeval_X, AlgEquiv.coe_algHom,
      bcEquiv_symm_tmul, map_one, one_mul]
  rw [heq]
  exact h2

section levelset

variable (S : Type u) [CommRing S] [Algebra R' S] [Algebra R S] [IsScalarTower R R' S]

def θ : S ⊗[R'] Γ(pullback c (sm (R := R) R'), (p c R') ⁻¹ᵁ U) ≃ₐ[S] S ⊗[R] Γ(C, U) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) (bcEquiv c R' U hU halg halg')).trans
    (Algebra.TensorProduct.cancelBaseChange R R' S S Γ(C, U))

lemma θ_tmul (x : S) (y : Γ(pullback c (sm (R := R) R'), (p c R') ⁻¹ᵁ U)) :
    θ c R' U hU halg halg' S (x ⊗ₜ[R'] y) =
      Algebra.TensorProduct.cancelBaseChange R R' S S Γ(C, U) (x ⊗ₜ[R'] bcEquiv c R' U hU halg halg' y) :=
  rfl

lemma θ_one_tmul_app (f : Γ(C, U)) :
    θ c R' U hU halg halg' S ((1 : S) ⊗ₜ[R'] (p c R').app U f) = (1 : S) ⊗ₜ[R] f := by
  rw [θ_tmul, bcEquiv_app, Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]

lemma θ_tmul_one (s : S) :
    θ c R' U hU halg halg' S (s ⊗ₜ[R'] (1 : Γ(pullback c (sm (R := R) R'), (p c R') ⁻¹ᵁ U))) =
      s ⊗ₜ[R] (1 : Γ(C, U)) := by
  rw [θ_tmul, map_one, Algebra.TensorProduct.one_def, Algebra.TensorProduct.cancelBaseChange_tmul,
    one_smul]

lemma ideal_map_θ (f : Γ(C, U)) (s : S) :
    Ideal.map (θ c R' U hU halg halg' S)
      (Ideal.span {(1 : S) ⊗ₜ[R'] (p c R').app U f - s ⊗ₜ[R'] 1}) =
      Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))} := by
  rw [Ideal.map_span, Set.image_singleton]
  congr 2
  change θ c R' U hU halg halg' S _ = _
  rw [map_sub, θ_one_tmul_app, θ_tmul_one]

def levelSetEquiv (f : Γ(C, U)) (s : S) :
    (S ⊗[R'] Γ(pullback c (sm (R := R) R'), (p c R') ⁻¹ᵁ U) ⧸
      Ideal.span {(1 : S) ⊗ₜ[R'] (p c R').app U f - s ⊗ₜ[R'] 1}) ≃ₐ[S]
    (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) :=
  Ideal.quotientEquivAlg _ _ (θ c R' U hU halg halg' S) (ideal_map_θ c R' U hU halg halg' S f s).symm

include hU halg halg' in

lemma levelSet_transport (f : Γ(C, U)) (s : S) (m : ℕ)
    (h : Module.Finite S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) ∧
      Module.Free S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) ∧
      Module.finrank S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) = m) :
    Module.Finite S (S ⊗[R'] Γ(pullback c (sm (R := R) R'), (p c R') ⁻¹ᵁ U) ⧸
        Ideal.span {(1 : S) ⊗ₜ[R'] (p c R').app U f - s ⊗ₜ[R'] 1}) ∧
      Module.Free S (S ⊗[R'] Γ(pullback c (sm (R := R) R'), (p c R') ⁻¹ᵁ U) ⧸
        Ideal.span {(1 : S) ⊗ₜ[R'] (p c R').app U f - s ⊗ₜ[R'] 1}) ∧
      Module.finrank S (S ⊗[R'] Γ(pullback c (sm (R := R) R'), (p c R') ⁻¹ᵁ U) ⧸
        Ideal.span {(1 : S) ⊗ₜ[R'] (p c R').app U f - s ⊗ₜ[R'] 1}) = m := by
  obtain ⟨h1, h2, h3⟩ := h
  let e := (levelSetEquiv c R' U hU halg halg' S f s).toLinearEquiv
  exact ⟨Module.Finite.equiv e.symm, Module.Free.of_equiv e.symm, (LinearEquiv.finrank_eq e).trans h3⟩

include hU halg halg' in

lemma etale_transport (f : Γ(C, U)) (s : S)
    (h : Algebra.Etale S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))})) :
    Algebra.Etale S (S ⊗[R'] Γ(pullback c (sm (R := R) R'), (p c R') ⁻¹ᵁ U) ⧸
        Ideal.span {(1 : S) ⊗ₜ[R'] (p c R').app U f - s ⊗ₜ[R'] 1}) :=
  by
    haveI := h
    exact Algebra.Etale.of_equiv
      (A := S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))})
      (levelSetEquiv c R' U hU halg halg' S f s).symm

end levelset

end algebra

omit hU in
lemma isLocalHom_algebraMap_of_isIntegral {S : Type u} [CommRing S] [IsLocalRing R] [Algebra R' S]
    [Algebra R S] [IsScalarTower R R' S] [Algebra.IsIntegral R R'] [Nontrivial S]
    [IsLocalHom (algebraMap R' S)] : IsLocalHom (algebraMap R S) := by
  constructor
  intro r hr
  rw [IsScalarTower.algebraMap_apply R R' S] at hr
  have h1 : IsUnit (algebraMap R R' r) := IsLocalHom.map_nonunit _ hr
  by_contra hnu
  have hr' : r ∈ IsLocalRing.maximalIdeal R := hnu
  haveI : Nontrivial R' := (algebraMap R' S).domain_nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R'
  haveI := hm
  have hcomap : (m.comap (algebraMap R R')).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
  have hmax : m.comap (algebraMap R R') = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hcomap
  have hmem : algebraMap R R' r ∈ m := by rw [← Ideal.mem_comap, hmax]; exact hr'
  exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem h1)

end AlgebraicGeometry.AffineBaseChange

end

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Opens.topIso_inv pullbackSpecIso_inv_snd pullbackRestrictIsoRestrict_hom_morphismRestrict_assoc Scheme.Hom Scheme.Γ Scheme.Hom.preimage_inf morphismRestrict_appTop IsAffineOpen.fromSpec_top Scheme.preimage_basicOpen IsAffineOpen.isoSpec_hom IsAffineOpen.SpecMap_appLE_fromSpec Spec IsIntegral Scheme.Hom.id_appTop Spec.map Scheme pullbackSpecIso Scheme.Opens.toSpecΓ_appTop Scheme.Hom.appTop Scheme.Γ_map_op Scheme.isoSpec_Spec_inv pullbackRestrictIsoRestrict_inv_fst_assoc Scheme.Hom.comp_appTop Scheme.Hom.naturality_assoc isAffineOpen_top Etale IsAffineOpen.isoSpec_inv_ι_assoc pullbackSpecIso_hom_fst IsAffineOpen Scheme.Hom.preimage_sup pullbackRestrictIsoRestrict Scheme.Opens Scheme.Opens.ι_image_top Scheme.ΓSpecIso_naturality Scheme.Opens.ι_appTop Scheme.Pullback.exists_preimage_pullback Scheme.Hom.appLE Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.isAffineHom_fst SmoothProperCurve.FiniteMapData"
namespace SmoothProperCurve
p2m_export "AlgebraicGeometry.SmoothProperCurve" "specMap baseChange sectionBaseChange sectionBaseChange_coe_fst sectionBaseChange_coe_snd FiniteMapData"
namespace FiniteMapData
p2m_export "AlgebraicGeometry.SmoothProperCurve.FiniteMapData" "LevelSetsGenericallyEtale mk finite_f U f sup_eq_top m V isAffineOpen_U inf_eq_basicOpen_g isAffineOpen_V finite_g g inf_eq_basicOpen mem_U_iff levelSet_free res_f_mul_res_g"
p2m_open "AlgebraicGeometry.SmoothProperCurve.FiniteMapData AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry"

open AlgebraicGeometry.AffineBaseChange

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} (𝔉 : FiniteMapData c ε)
  (R' : Type u) [CommRing R'] [Algebra R R']

private noncomputable def _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.baseChangeData : FiniteMapData (baseChange R c R') (sectionBaseChange R' ε) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.V
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (baseChange R c R')
    ((pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.U)
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (baseChange R c R')
    ((pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.V)
  { U := (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.U
    V := (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.V
    f := ((pullback.fst c (specMap R R')).app 𝔉.U).hom 𝔉.f
    g := ((pullback.fst c (specMap R R')).app 𝔉.V).hom 𝔉.g
    m := 𝔉.m
    isAffineOpen_U := 𝔉.isAffineOpen_preimage_U R'
    isAffineOpen_V := 𝔉.isAffineOpen_preimage_V R'
    sup_eq_top := 𝔉.preimage_U_sup_preimage_V R'
    mem_U_iff := 𝔉.mem_preimage_U_iff R'
    inf_eq_basicOpen := 𝔉.preimage_U_inf_preimage_V_eq_basicOpen_f R'
    inf_eq_basicOpen_g := 𝔉.preimage_U_inf_preimage_V_eq_basicOpen_g R'
    res_f_mul_res_g := 𝔉.res_app_f_mul_res_app_g R'
    finite_f := finite_aeval_bc c R' 𝔉.U 𝔉.isAffineOpen_U (fun _ => rfl) (fun _ => rfl) 𝔉.f 𝔉.finite_f
    finite_g := finite_aeval_bc c R' 𝔉.V 𝔉.isAffineOpen_V (fun _ => rfl) (fun _ => rfl) 𝔉.g 𝔉.finite_g
    levelSet_free := fun S _ _ _ s => by
      letI : Algebra R S := ((algebraMap R' S).comp (algebraMap R R')).toAlgebra
      haveI : IsScalarTower R R' S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      exact levelSet_transport c R' 𝔉.U 𝔉.isAffineOpen_U (fun _ => rfl) (fun _ => rfl) S 𝔉.f s 𝔉.m
        (𝔉.levelSet_free S s) }

p2m_export "AlgebraicGeometry.SmoothProperCurve.FiniteMapData" "baseChangeData"
@[scoped simp] lemma baseChangeData_U : (𝔉.baseChangeData R').U = (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.U := rfl
@[scoped simp] lemma baseChangeData_V : (𝔉.baseChangeData R').V = (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.V := rfl
@[scoped simp] lemma baseChangeData_m : (𝔉.baseChangeData R').m = 𝔉.m := rfl
@[scoped simp] lemma baseChangeData_f :
    (𝔉.baseChangeData R').f = ((pullback.fst c (specMap R R')).app 𝔉.U).hom 𝔉.f := rfl

private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.levelSetsGenericallyEtale_baseChange (hloc : IsLocalRing R) (hfin : Module.Finite R R')
    (h : 𝔉.LevelSetsGenericallyEtale) : (𝔉.baseChangeData R').LevelSetsGenericallyEtale := by
  obtain ⟨D, ⟨i, hi⟩, hD⟩ := h
  refine ⟨D.map (algebraMap R R'), ⟨i, by rw [Polynomial.coeff_map]; exact hi.map _⟩, ?_⟩
  intro S _ _ _ _ s hs
  letI : Algebra R S := ((algebraMap R' S).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral R R' := Algebra.IsIntegral.of_finite R R'
  haveI : IsLocalHom (algebraMap R S) := isLocalHom_algebraMap_of_isIntegral (R := R) R'
  have hs' : IsUnit (Polynomial.aeval s D) := by rwa [Polynomial.aeval_map_algebraMap] at hs
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (baseChange R c R')
    ((pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.U)
  exact etale_transport c R' 𝔉.U 𝔉.isAffineOpen_U (fun _ => rfl) (fun _ => rfl) S 𝔉.f s (hD S s hs')

p2m_export "AlgebraicGeometry.SmoothProperCurve.FiniteMapData" "levelSetsGenericallyEtale_baseChange"
end AlgebraicGeometry.SmoothProperCurve.FiniteMapData
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange.AlgebraicGeometry P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange.AlgebraicGeometry.SmoothProperCurve P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange.AlgebraicGeometry.SmoothProperCurve.FiniteMapData"
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange.AlgebraicGeometry P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange.AlgebraicGeometry.SmoothProperCurve"
p2m_reactivate "P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange.AlgebraicGeometry"

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange.AlgebraicGeometry _root_.AlgebraicGeometry.SmoothProperCurve _root_.P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange.AlgebraicGeometry.SmoothProperCurve in
theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} (𝔉 : SmoothProperCurve.FiniteMapData c ε)
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    ∃ 𝔉' : SmoothProperCurve.FiniteMapData (baseChange R c R') (sectionBaseChange R' ε),
      𝔉'.U = (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.U ∧ 𝔉'.V = (pullback.fst c (specMap R R')) ⁻¹ᵁ 𝔉.V ∧
        𝔉'.m = 𝔉.m ∧
        (IsLocalRing R → Module.Finite R R' → 𝔉.LevelSetsGenericallyEtale → 𝔉'.LevelSetsGenericallyEtale) :=
  ⟨𝔉.baseChangeData R', rfl, rfl, rfl, 𝔉.levelSetsGenericallyEtale_baseChange R'⟩

end S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange (solution)
