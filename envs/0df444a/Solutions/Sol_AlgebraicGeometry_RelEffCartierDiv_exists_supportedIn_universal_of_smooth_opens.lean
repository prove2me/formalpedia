-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.exists_supportedIn_universal_of_smooth_opens
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/cf4a4ebc-d057-509b-8974-9d927ff97e65

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivRestrict
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_isUniversal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_universal_of_smooth_opens
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelEffCartierDiv

theorem solution
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] (U : 𝒞.Opens)
    [SmoothOfRelativeDimension 1 (U.ι ≫ f)]
    (hcov : ∀ (V : S.affineOpens) (F : Finset ↥U), (∀ x ∈ F, (U.ι ≫ f) x ∈ (V : S.Opens)) →
      ∃ W : (↑U : Scheme.{u}).Opens, IsAffineOpen W ∧ W ≤ (U.ι ≫ f) ⁻¹ᵁ (V : S.Opens) ∧ ∀ x ∈ F, x ∈ W)
    (r : ℕ) :
    ∃ (Y : Scheme.{u}) (y : Y ⟶ S) (Duniv : RelEffCartierDiv f r y), Duniv.SupportedIn U ∧
      ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S) (D : RelEffCartierDiv f r g), D.SupportedIn U →
        ∃! φ : {φ : T ⟶ Y // φ ≫ y = g}, PullsBackOver Duniv φ.1 φ.2 D := by

  have hUV : U ≤ f ⁻¹ᵁ (⊤ : S.Opens) := le_top
  let ι : (↑(⊤ : S.Opens) : Scheme.{u}) ⟶ S := (⊤ : S.Opens).ι
  haveI : IsIso ι := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    ext1
    rw [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Scheme.Opens.range_ι, TopologicalSpace.Opens.coe_top]
  let fU := f.resLE ⊤ U hUV
  have hfU : fU ≫ ι = U.ι ≫ f := Scheme.Hom.resLE_comp_ι f hUV

  haveI : SmoothOfRelativeDimension 1 fU := by
    have : fU = (U.ι ≫ f) ≫ inv ι := by rw [← hfU, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [this]
    exact (MorphismProperty.cancel_right_of_respectsIso (@SmoothOfRelativeDimension 1) _ _).mpr inferInstance
  haveI : IsSeparated fU := by
    have : fU = (U.ι ≫ f) ≫ inv ι := by rw [← hfU, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [this]; infer_instance

  have hcov' : ∀ (V : (↑(⊤ : S.Opens) : Scheme.{u}).affineOpens) (F : Finset ↥U),
      (∀ x ∈ F, fU x ∈ (V : (↑(⊤ : S.Opens) : Scheme.{u}).Opens)) →
      ∃ W : (↑U : Scheme.{u}).Opens, IsAffineOpen W ∧ W ≤ fU ⁻¹ᵁ (V : (↑(⊤ : S.Opens) : Scheme.{u}).Opens) ∧
        ∀ x ∈ F, x ∈ W := by
    intro V F hF
    obtain ⟨W, hW, hWV, hFW⟩ := hcov ⟨ι ''ᵁ (V : (↑(⊤ : S.Opens) : Scheme.{u}).Opens), V.2.image_of_isOpenImmersion ι⟩ F
      (fun x hx => by
        change (U.ι ≫ f) x ∈ ι ''ᵁ _
        rw [← hfU, Scheme.Hom.comp_apply]
        exact ⟨fU x, hF x hx, rfl⟩)
    refine ⟨W, hW, fun x hx => ?_, hFW⟩
    have h1 : (U.ι ≫ f) x ∈ ι ''ᵁ (V : (↑(⊤ : S.Opens) : Scheme.{u}).Opens) := hWV hx
    rw [← hfU, Scheme.Hom.comp_apply] at h1
    obtain ⟨v, hv, hveq⟩ := h1
    have : v = fU x := ι.isOpenEmbedding.injective hveq
    change fU x ∈ (V : (↑(⊤ : S.Opens) : Scheme.{u}).Opens)
    rw [← this]; exact hv

  obtain ⟨Y, yU, Duniv', hU'⟩ := RelEffCartierDiv.exists_isUniversal fU hcov' r
  refine ⟨Y, yU ≫ ι, extendAlong f r ⊤ U hUV yU (yU ≫ ι) rfl Duniv', extendAlong_supportedIn .., ?_⟩
  intro T g D hD

  let gV : T ⟶ ↑(⊤ : S.Opens) := IsOpenImmersion.lift ι g (by rw [Scheme.Opens.range_ι]; exact fun _ _ => trivial)
  have hg : gV ≫ ι = g := IsOpenImmersion.lift_fac _ _ _
  let D' := restrictAlong f r ⊤ U hUV gV g hg D hD
  let φ := hU'.lift D'
  have hφ : φ ≫ yU = gV := hU'.lift_comp D'
  have hφ' : φ ≫ yU ≫ ι = g := by rw [← Category.assoc, hφ, hg]
  have hpull : (extendAlong f r ⊤ U hUV yU (yU ≫ ι) rfl Duniv').pullbackAlong φ hφ' = D := by
    rw [← extendAlong_pullbackAlong f r ⊤ U hUV hg rfl Duniv' φ hφ hφ', hU'.pullbackAlong_lift,
      extendAlong_restrictAlong]
  refine ⟨⟨φ, hφ'⟩, ?_, ?_⟩
  · change PullsBackOver _ φ hφ' D
    rw [← hpull]
    exact pullsBackOver_pullbackAlong _ _ _
  · rintro ⟨ψ, hψ⟩ hP
    apply Subtype.ext
    change ψ = φ
    have hψV : ψ ≫ yU = gV := by
      rw [← cancel_mono ι, Category.assoc, hψ, hg]
    have hDeq : D = (extendAlong f r ⊤ U hUV yU (yU ≫ ι) rfl Duniv').pullbackAlong ψ hψ := hP.eq_pullbackAlong
    rw [← extendAlong_pullbackAlong f r ⊤ U hUV hg rfl Duniv' ψ hψV hψ] at hDeq

    have hD' : D' = Duniv'.pullbackAlong ψ hψV := by
      change restrictAlong f r ⊤ U hUV gV g hg D hD = _
      subst hDeq
      exact restrictAlong_extendAlong f r ⊤ U hUV gV g hg _
    exact hU'.eq_lift hψV (hD' ▸ pullsBackOver_pullbackAlong Duniv' ψ hψV)

end S_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_universal_of_smooth_opens
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_universal_of_smooth_opens (solution)
