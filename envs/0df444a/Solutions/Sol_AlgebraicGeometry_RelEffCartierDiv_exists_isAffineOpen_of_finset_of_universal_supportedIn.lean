-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.exists_isAffineOpen_of_finset_of_universal_supportedIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/ecf2f07d-2984-5474-927c-08775527f217

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivRestrict
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_exists_isAffineOpen_of_finset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_isAffineOpen_of_finset_of_universal_supportedIn
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
    (r : ℕ) {Y : Scheme.{u}} (y : Y ⟶ S) (Duniv : RelEffCartierDiv f r y) (hDunivU : Duniv.SupportedIn U)
    (huniv : ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S) (D : RelEffCartierDiv f r g), D.SupportedIn U →
      ∃! φ : {φ : T ⟶ Y // φ ≫ y = g}, PullsBackOver Duniv φ.1 φ.2 D)
    (V : S.affineOpens) (F : Finset Y) (hF : ∀ p ∈ F, y p ∈ (V : S.Opens)) :
    ∃ W : Y.Opens, IsAffineOpen W ∧ W ≤ y ⁻¹ᵁ (V : S.Opens) ∧ ∀ p ∈ F, p ∈ W := by

  have hUV : U ≤ f ⁻¹ᵁ (⊤ : S.Opens) := le_top
  let ι : (↑(⊤ : S.Opens) : Scheme.{u}) ⟶ S := (⊤ : S.Opens).ι
  haveI : IsIso ι := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    ext1
    rw [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Scheme.Opens.range_ι, TopologicalSpace.Opens.coe_top]
  let fU := f.resLE ⊤ U hUV
  have hfU : fU ≫ ι = U.ι ≫ f := Scheme.Hom.resLE_comp_ι f hUV
  have hfU' : fU = (U.ι ≫ f) ≫ inv ι := by rw [← hfU, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  haveI : SmoothOfRelativeDimension 1 fU := by
    rw [hfU']; exact (MorphismProperty.cancel_right_of_respectsIso (@SmoothOfRelativeDimension 1) _ _).mpr inferInstance
  haveI : IsSeparated fU := by rw [hfU']; infer_instance

  let yU : Y ⟶ ↑(⊤ : S.Opens) := IsOpenImmersion.lift ι y (by rw [Scheme.Opens.range_ι]; exact fun _ _ => trivial)
  have hy : yU ≫ ι = y := IsOpenImmersion.lift_fac _ _ _

  let D' : RelEffCartierDiv fU r yU := restrictAlong f r ⊤ U hUV yU y hy Duniv hDunivU
  have hU' : D'.IsUniversal := by
    intro T gV E

    let E𝒞 := extendAlong f r ⊤ U hUV gV (gV ≫ ι) rfl E
    have hE𝒞 : E𝒞.SupportedIn U := extendAlong_supportedIn f r ⊤ U hUV gV (gV ≫ ι) rfl E
    obtain ⟨⟨φ, hφ⟩, hP, huq⟩ := huniv (gV ≫ ι) E𝒞 hE𝒞
    have hφV : φ ≫ yU = gV := by rw [← cancel_mono ι, Category.assoc, hy, hφ]
    have key : ∀ {A B : RelEffCartierDiv f r (gV ≫ ι)} (hA : A.SupportedIn U) (hB : B.SupportedIn U), A = B →
        restrictAlong f r ⊤ U hUV gV (gV ≫ ι) rfl A hA = restrictAlong f r ⊤ U hUV gV (gV ≫ ι) rfl B hB := by
      rintro A B hA hB rfl; rfl
    refine ⟨⟨φ, hφV⟩, ?_, ?_⟩
    ·
      have h1 : Duniv.pullbackAlong φ hφ = E𝒞 := (hP.eq_pullbackAlong).symm
      have h2 : extendAlong f r ⊤ U hUV gV (gV ≫ ι) rfl (D'.pullbackAlong φ hφV) = E𝒞 := by
        rw [extendAlong_pullbackAlong f r ⊤ U hUV rfl hy D' φ hφV hφ]
        change (extendAlong f r ⊤ U hUV yU y hy (restrictAlong f r ⊤ U hUV yU y hy Duniv hDunivU)).pullbackAlong φ hφ = E𝒞
        rw [extendAlong_restrictAlong]; exact h1
      have h3 : D'.pullbackAlong φ hφV = E := by
        have hA := restrictAlong_extendAlong f r ⊤ U hUV gV (gV ≫ ι) rfl (D'.pullbackAlong φ hφV)
        have hB := restrictAlong_extendAlong f r ⊤ U hUV gV (gV ≫ ι) rfl E
        rw [← hA, ← hB]
        exact key _ _ h2
      rw [← h3]; exact pullsBackOver_pullbackAlong _ _ _
    · rintro ⟨ψ, hψ⟩ hPψ
      apply Subtype.ext
      change ψ = φ
      have hψ' : ψ ≫ y = gV ≫ ι := by rw [← hy, ← Category.assoc, hψ]
      have hE : E = D'.pullbackAlong ψ hψ := hPψ.eq_pullbackAlong
      have : PullsBackOver Duniv ψ hψ' E𝒞 := by
        have h4 : E𝒞 = Duniv.pullbackAlong ψ hψ' := by
          change extendAlong f r ⊤ U hUV gV (gV ≫ ι) rfl E = _
          rw [hE, extendAlong_pullbackAlong f r ⊤ U hUV rfl hy D' ψ hψ hψ']
          change (extendAlong f r ⊤ U hUV yU y hy (restrictAlong f r ⊤ U hUV yU y hy Duniv hDunivU)).pullbackAlong ψ hψ' = _
          rw [extendAlong_restrictAlong]
        rw [h4]; exact pullsBackOver_pullbackAlong _ _ _
      have := huq ⟨ψ, hψ'⟩ this
      exact congrArg Subtype.val this

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

  let V' : (↑(⊤ : S.Opens) : Scheme.{u}).affineOpens := ⟨ι ⁻¹ᵁ (V : S.Opens), V.2.preimage_of_isIso ι⟩
  have hF' : ∀ p ∈ F, yU p ∈ (V' : (↑(⊤ : S.Opens) : Scheme.{u}).Opens) := by
    intro p hp
    change ι (yU p) ∈ (V : S.Opens)
    rw [← Scheme.Hom.comp_apply, hy]; exact hF p hp
  obtain ⟨W, hW, hWV, hFW⟩ := hU'.exists_isAffineOpen_of_finset hcov' V' F hF'
  refine ⟨W, hW, fun p hp => ?_, hFW⟩
  have : yU p ∈ (V' : (↑(⊤ : S.Opens) : Scheme.{u}).Opens) := hWV hp
  change y p ∈ (V : S.Opens)
  rw [← hy, Scheme.Hom.comp_apply]; exact this

end S_AlgebraicGeometry_RelEffCartierDiv_exists_isAffineOpen_of_finset_of_universal_supportedIn
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_isAffineOpen_of_finset_of_universal_supportedIn (solution)
