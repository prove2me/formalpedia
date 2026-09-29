-- Prove2me | solution 1 for AlgebraicCurve.exists_mem_ord_eq_one_ord_residue_eq_one_of_smoothOfRelativeDimension_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e28cfe84-773c-54e8-a91d-f5f4d8ababf7

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_NeronModelInfra_existsUnique_schemeHomOver_comp_eq_of_isProper_valuationSubring
import Theorems.Thm_AlgebraicGeometry_exists_ker_stalkMap_eq_span_and_maximalIdeal_eq_of_section_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicGeometry_stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective
import Theorems.Thm_AlgebraicCurve_CurveModel_ord_placeOfPoint_ffEquiv_symm_algebraMap_eq_one_of_maximalIdeal_eq_span
import Theorems.Thm_AlgebraicGeometry_isOpenImmersion_specMap_subtype_of_liesOverPrime
import Theorems.Thm_AlgebraicGeometry_maximalIdeal_stalk_eq_span_stalkSpecializes_of_ker_stalkMap_eq_span
import Theorems.Thm_AlgebraicGeometry_eq_of_section_of_base_closedPoint_eq_of_ker_stalkMap_le
import Theorems.Thm_AlgebraicCurve_CurveModel_ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_mem_ord_eq_one_ord_residue_eq_one_of_smoothOfRelativeDimension_one
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve P2MW.S_AlgebraicCurve_exists_mem_ord_eq_one_ord_residue_eq_one_of_smoothOfRelativeDimension_one.AlgebraicCurve TopologicalSpace"

universe v w

namespace HeckeGC3a

end HeckeGC3a

namespace GC3aC4

theorem map_maximalIdeal_of_surjective {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] (hf : Function.Surjective f) :
    (IsLocalRing.maximalIdeal R).map f = IsLocalRing.maximalIdeal S := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (IsLocalHom.map_nonunit a hu)
  · intro b hb
    obtain ⟨a, rfl⟩ := hf b
    apply Ideal.mem_map_of_mem
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => (IsLocalRing.mem_maximalIdeal _).1 hb (hu.map f)
end GC3aC4

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "CurveModel CurveModel.pointEquivPlace_apply Place Place.ord_zero IsCurveOver CurveModel.ord_placeOfPoint_ffEquiv_symm_algebraMap_eq_one_of_maximalIdeal_eq_span" end AlgebraicCurve
p2m_open_scoped "AlgebraicCurve" in

theorem AlgebraicCurve.ord_red_residue_section_eq_one_of_maximalIdeal_eq_of_smoothOfRelativeDimension_one
    (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p)
    [hk : IsAlgClosed (IsLocalRing.ResidueField ↥O)]

    (X : Scheme.{0}) (π : X ⟶ Spec (CommRingCat.of ↥O)) [IsProper π] [SmoothOfRelativeDimension 1 π]
    [hXint : IsIntegral X]
    [hXk : IsIntegral (pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))]

    (F : Type v) [Field F] [Algebra (AlgebraicClosure ℚ) F] [IsCurveOver (AlgebraicClosure ℚ) F]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) F]
    (𝔐 : CurveModel (AlgebraicClosure ℚ) F)
    (e : 𝔐.C ⟶ pullback π (Spec.map (CommRingCat.ofHom O.subtype))) [IsIso e]
    (he : e ≫ pullback.snd π (Spec.map (CommRingCat.ofHom O.subtype)) = 𝔐.toBase)

    (K : Type w) [Field K] [Algebra (IsLocalRing.ResidueField ↥O) K]
    (𝔐k : CurveModel (IsLocalRing.ResidueField ↥O) K)
    (ek : 𝔐k.C ⟶ pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) [IsIso ek]
    (hek : ek ≫ pullback.snd π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))) = 𝔐k.toBase)

    (𝒪F : ValuationSubring F) (res : ↥𝒪F →+* K)
    (h𝒪F : ∀ f : F, f ∈ 𝒪F ↔
      ∃ (U : X.Opens)
        (hξ : (pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).base
                (genericPoint ↥(pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))) ∈ U)
        (_ : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ U))
        (s t : X.presheaf.obj (Opposite.op U)),
        IsUnit (X.presheaf.germ U _ hξ t) ∧
        f * 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom t)) =
          𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom s)))
    (hres : ∀ (U : X.Opens)
        (_ : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ U))
        (_ : Nonempty ((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) ⁻¹ᵁ U))
        (s : X.presheaf.obj (Opposite.op U))
        (hs : 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom s)) ∈ 𝒪F),
        res ⟨_, hs⟩ =
          𝔐k.ffEquiv.symm (𝔐k.C.germToFunctionField _
            (((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).app U).hom s)))
    (hsurj : Function.Surjective res) (hker : RingHom.ker res = IsLocalRing.maximalIdeal ↥𝒪F)

    (red : Place (AlgebraicClosure ℚ) F → Place (IsLocalRing.ResidueField ↥O) K)
    (hred : ∀ (P : Place (AlgebraicClosure ℚ) F) (Pt : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥O))) π),
      ((𝔐.pointEquivPlace.symm P).1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) =
        Spec.map (CommRingCat.ofHom O.subtype) ≫ Pt.1 →
      ((𝔐k.pointEquivPlace.symm (red P)).1 ≫ ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)) ≫ Pt.1)

    (P : Place (AlgebraicClosure ℚ) F) (Pt : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥O))) π)
    (hPt : Spec.map (CommRingCat.ofHom O.subtype) ≫ Pt.1 =
      (𝔐.pointEquivPlace.symm P).1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype)))
    (t : X.presheaf.stalk (Pt.1.base (IsLocalRing.closedPoint ↥O)))
    (hmaxt : IsLocalRing.maximalIdeal (X.presheaf.stalk (Pt.1.base (IsLocalRing.closedPoint ↥O))) =
      Ideal.span {t} ⊔ (IsLocalRing.maximalIdeal ↥O).map ((X.presheaf.germ ⊤ (Pt.1.base (IsLocalRing.closedPoint ↥O)) trivial).hom.comp
        (π.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥O)).inv.hom)))
    (U : X.Opens) (hxU : Pt.1.base (IsLocalRing.closedPoint ↥O) ∈ U) (u : X.presheaf.obj (Opposite.op U))
    (hu : (X.presheaf.germ U _ hxU).hom u = t)
    (hnek : Nonempty ((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) ⁻¹ᵁ U)) :
    (red P).ord (𝔐k.ffEquiv.symm (𝔐k.C.germToFunctionField _
      (((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).app U).hom u))) = 1 := by
  classical

  set G := ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))) with hGdef
  set zQ := 𝔐k.pointEquivPlace.symm (red P) with hzQdef
  have hzQP : 𝔐k.pointEquivPlace zQ = red P := by rw [hzQdef, Equiv.apply_symm_apply]
  have hk : zQ.1 ≫ G = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)) ≫ Pt.1 := hred P Pt hPt.symm
  set y : ↥𝔐k.C := zQ.1.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O)) with hydef
  have hGy : G.base y = Pt.1.base (IsLocalRing.closedPoint ↥O) := by
    show (zQ.1 ≫ G).base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O)) = _
    rw [hk]
    show Pt.1.base ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))).base
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O))) = _
    congr 1
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue ↥O)

  revert t hmaxt hxU hu
  generalize hx₀ : Pt.1.base (IsLocalRing.closedPoint ↥O) = x₀
  intro t hmaxt hxU hu
  rw [hx₀] at hGy
  subst hGy

  have hsq : IsPullback G 𝔐k.toBase π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))) := by
    have s1 : IsPullback ek (ek ≫ pullback.snd π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))
        (pullback.snd π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]⟩
    have s2 := IsPullback.of_hasPullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))
    have s := s1.paste_horiz s2
    rw [Category.id_comp, hek] at s
    exact s

  obtain ⟨hsurjS, hkerS⟩ :=
    AlgebraicGeometry.stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective
      (IsLocalRing.residue ↥O) IsLocalRing.residue_surjective π G 𝔐k.toBase hsq y
  rw [IsLocalRing.ker_residue] at hkerS

  set φ := (G.stalkMap y).hom with hφdef
  haveI : IsLocalHom φ := inferInstance
  set g := φ t with hgdef
  have hmaxy : IsLocalRing.maximalIdeal (𝔐k.C.presheaf.stalk y) = Ideal.span {g} := by
    rw [← GC3aC4.map_maximalIdeal_of_surjective φ hsurjS, hmaxt, Ideal.map_sup, Ideal.map_span, Set.image_singleton,
      Ideal.map_map, (Ideal.map_eq_bot_iff_le_ker _).2, sup_bot_eq]

    rw [RingHom.ker_eq_comap_bot, ← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, hkerS]
    exact Ideal.le_comap_map

  have hg : g = (𝔐k.C.presheaf.germ (G ⁻¹ᵁ U) y hxU).hom ((G.app U).hom u) := by
    rw [hgdef, hφdef, ← hu]
    exact Scheme.Hom.germ_stalkMap_apply G U y hxU u

  have hyc : y ∈ closedPoints ↥𝔐k.C := by
    have := (pointEquivClosedPoint 𝔐k.toBase zQ).2
    rwa [pointEquivClosedPoint_apply_coe] at this
  have hplace : 𝔐k.placeOfPoint ⟨y, hyc⟩ = red P := by
    rw [← hzQP, AlgebraicCurve.CurveModel.pointEquivPlace_apply]
    exact congrArg 𝔐k.placeOfPoint (Subtype.ext (pointEquivClosedPoint_apply_coe 𝔐k.toBase zQ).symm)

  have h1 := AlgebraicCurve.CurveModel.ord_placeOfPoint_ffEquiv_symm_algebraMap_eq_one_of_maximalIdeal_eq_span 𝔐k ⟨y, hyc⟩ g hmaxy
  rw [hplace, hg] at h1

  have hgerm : algebraMap (𝔐k.C.presheaf.stalk y) 𝔐k.C.functionField
      ((𝔐k.C.presheaf.germ (G ⁻¹ᵁ U) y hxU).hom ((G.app U).hom u)) =
      𝔐k.C.germToFunctionField (G ⁻¹ᵁ U) ((G.app U).hom u) :=
    TopCat.Presheaf.germ_stalkSpecializes_apply 𝔐k.C.presheaf (show y ∈ G ⁻¹ᵁ U from hxU) (genericPoint_specializes y) _
  rw [hgerm] at h1
  exact h1

namespace GC3aH1
private theorem _root_.GC3aH1.ord_eq_zero_of_isUnit_germ
    (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p)
    (X : Scheme.{0}) (π : X ⟶ Spec (CommRingCat.of ↥O))
    (F : Type v) [Field F] [Algebra (AlgebraicClosure ℚ) F] [IsCurveOver (AlgebraicClosure ℚ) F]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) F]
    (𝔐 : CurveModel (AlgebraicClosure ℚ) F)
    (e : 𝔐.C ⟶ pullback π (Spec.map (CommRingCat.ofHom O.subtype))) [IsIso e]
    (P' : Place (AlgebraicClosure ℚ) F) (Pt' : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥O))) π)
    (hPt' : Spec.map (CommRingCat.ofHom O.subtype) ≫ Pt'.1 =
      (𝔐.pointEquivPlace.symm P').1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype)))
    (U : X.Opens) (u : X.presheaf.obj (Opposite.op U))
    (hyU : Pt'.1.base (genericPoint ↥(Spec (CommRingCat.of ↥O))) ∈ U)
    (hunit : IsUnit ((X.presheaf.germ U _ hyU).hom u))
    (hneL : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ U)) :
    P'.ord (𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
      (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom u))) = 0 := by
  classical
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom O.subtype)) :=
    AlgebraicGeometry.isOpenImmersion_specMap_subtype_of_liesOverPrime O p hp hO
  set G' := e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype)) with hG'def
  haveI : IsOpenImmersion G' := inferInstance
  set zP := 𝔐.pointEquivPlace.symm P' with hzPdef
  have hzPP : 𝔐.pointEquivPlace zP = P' := by rw [hzPdef, Equiv.apply_symm_apply]
  set y' : ↥𝔐.C := zP.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) with hy'def

  have hgen : (Spec.map (CommRingCat.ofHom O.subtype)).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) =
      genericPoint ↥(Spec (CommRingCat.of ↥O)) := by
    apply IsGenericPoint.eq _ (genericPoint_spec _)
    rw [isGenericPoint_iff_specializes]
    intro q
    simp only [Set.mem_univ, iff_true]
    refine (PrimeSpectrum.le_iff_specializes
      (PrimeSpectrum.comap O.subtype (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) q).1 ?_
    intro a ha
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at ha
    have : (a : AlgebraicClosure ℚ) = 0 := by
      simpa [IsLocalRing.closedPoint] using ha
    have : a = 0 := Subtype.ext this
    rw [this]; exact q.asIdeal.zero_mem
  have hG'y : G'.base y' = Pt'.1.base (genericPoint ↥(Spec (CommRingCat.of ↥O))) := by
    rw [← hgen]
    show (zP.1 ≫ G').base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) =
      (Spec.map (CommRingCat.ofHom O.subtype) ≫ Pt'.1).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))
    rw [hG'def, hPt']
  have hyU' : G'.base y' ∈ U := by rw [hG'y]; exact hyU

  have hunit' : IsUnit ((X.presheaf.germ U (G'.base y') hyU').hom u) := by
    have key : ∀ (x₁ : ↥X) (hx₁ : x₁ ∈ U), x₁ = Pt'.1.base (genericPoint ↥(Spec (CommRingCat.of ↥O))) →
        IsUnit ((X.presheaf.germ U x₁ hx₁).hom u) := by
      rintro x₁ hx₁ rfl; exact hunit
    exact key _ hyU' hG'y
  set φ' := (G'.stalkMap y').hom with hφ'def
  have hg' : φ' ((X.presheaf.germ U (G'.base y') hyU').hom u) =
      (𝔐.C.presheaf.germ (G' ⁻¹ᵁ U) y' hyU').hom ((G'.app U).hom u) := by
    rw [hφ'def]; exact Scheme.Hom.germ_stalkMap_apply G' U y' hyU' u
  have hunit'' : IsUnit ((𝔐.C.presheaf.germ (G' ⁻¹ᵁ U) y' hyU').hom ((G'.app U).hom u)) := by
    rw [← hg']; exact hunit'.map φ'

  have hyc : y' ∈ closedPoints ↥𝔐.C := by
    have := (pointEquivClosedPoint 𝔐.toBase zP).2
    rwa [pointEquivClosedPoint_apply_coe] at this
  have hplace : 𝔐.placeOfPoint ⟨y', hyc⟩ = P' := by
    rw [← hzPP, AlgebraicCurve.CurveModel.pointEquivPlace_apply]
    exact congrArg 𝔐.placeOfPoint (Subtype.ext (pointEquivClosedPoint_apply_coe 𝔐.toBase zP).symm)

  set ρ : ↑(𝔐.C.presheaf.stalk y') →+* F :=
    (𝔐.ffEquiv.symm : 𝔐.C.functionField ≃+* F).toRingHom.comp (algebraMap (𝔐.C.presheaf.stalk y') 𝔐.C.functionField)
    with hρdef
  have hrange : ρ.range = P'.toValuationSubring.toSubring := by
    rw [← hplace]; exact 𝔐.range_stalk_eq ⟨y', hyc⟩
  have hgerm : algebraMap (𝔐.C.presheaf.stalk y') 𝔐.C.functionField
      ((𝔐.C.presheaf.germ (G' ⁻¹ᵁ U) y' hyU').hom ((G'.app U).hom u)) =
      𝔐.C.germToFunctionField (G' ⁻¹ᵁ U) ((G'.app U).hom u) :=
    TopCat.Presheaf.germ_stalkSpecializes_apply 𝔐.C.presheaf (show y' ∈ G' ⁻¹ᵁ U from hyU') (genericPoint_specializes y') _
  obtain ⟨w, hw⟩ := hunit''
  let wr : (ρ.range)ˣ := Units.map (ρ.rangeRestrict : ↑(𝔐.C.presheaf.stalk y') →* ρ.range) w
  let wv : (P'.toValuationSubring)ˣ := Units.map ((RingEquiv.subringCongr hrange).toRingHom : ρ.range →* _) wr
  have hval : ((wv : P'.toValuationSubring) : F) =
      𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _ ((G'.app U).hom u)) := by
    show ρ w = _
    rw [hw, hρdef, RingHom.comp_apply, hgerm]
    rfl
  rw [← hval]
  exact P'.ord_coe_unit wv

end GC3aH1
p2m_export "" "GC3aH1.ord_eq_zero_of_isUnit_germ"
namespace GC3aC5

private theorem _root_.GC3aC5.ord_eq_zero_of_isUnit_germ
    (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p)
    [hk : IsAlgClosed (IsLocalRing.ResidueField ↥O)]

    (X : Scheme.{0}) (π : X ⟶ Spec (CommRingCat.of ↥O)) [IsProper π] [SmoothOfRelativeDimension 1 π]
    [hXint : IsIntegral X]
    [hXk : IsIntegral (pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))]

    (F : Type v) [Field F] [Algebra (AlgebraicClosure ℚ) F] [IsCurveOver (AlgebraicClosure ℚ) F]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) F]
    (𝔐 : CurveModel (AlgebraicClosure ℚ) F)
    (e : 𝔐.C ⟶ pullback π (Spec.map (CommRingCat.ofHom O.subtype))) [IsIso e]
    (he : e ≫ pullback.snd π (Spec.map (CommRingCat.ofHom O.subtype)) = 𝔐.toBase)

    (K : Type w) [Field K] [Algebra (IsLocalRing.ResidueField ↥O) K]
    (𝔐k : CurveModel (IsLocalRing.ResidueField ↥O) K)
    (ek : 𝔐k.C ⟶ pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) [IsIso ek]
    (hek : ek ≫ pullback.snd π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))) = 𝔐k.toBase)

    (𝒪F : ValuationSubring F) (res : ↥𝒪F →+* K)
    (h𝒪F : ∀ f : F, f ∈ 𝒪F ↔
      ∃ (U : X.Opens)
        (hξ : (pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).base
                (genericPoint ↥(pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))) ∈ U)
        (_ : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ U))
        (s t : X.presheaf.obj (Opposite.op U)),
        IsUnit (X.presheaf.germ U _ hξ t) ∧
        f * 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom t)) =
          𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom s)))
    (hres : ∀ (U : X.Opens)
        (_ : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ U))
        (_ : Nonempty ((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) ⁻¹ᵁ U))
        (s : X.presheaf.obj (Opposite.op U))
        (hs : 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom s)) ∈ 𝒪F),
        res ⟨_, hs⟩ =
          𝔐k.ffEquiv.symm (𝔐k.C.germToFunctionField _
            (((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).app U).hom s)))
    (hsurj : Function.Surjective res) (hker : RingHom.ker res = IsLocalRing.maximalIdeal ↥𝒪F)

    (red : Place (AlgebraicClosure ℚ) F → Place (IsLocalRing.ResidueField ↥O) K)
    (hred : ∀ (P : Place (AlgebraicClosure ℚ) F) (Pt : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥O))) π),
      ((𝔐.pointEquivPlace.symm P).1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) =
        Spec.map (CommRingCat.ofHom O.subtype) ≫ Pt.1 →
      ((𝔐k.pointEquivPlace.symm (red P)).1 ≫ ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)) ≫ Pt.1)

    (U : X.Opens) (hneL : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ U))
    (u : X.presheaf.obj (Opposite.op U)) (P' : Place (AlgebraicClosure ℚ) F)
    (hy : ((𝔐.pointEquivPlace.symm P').1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).base
      (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ U)
    (hunit : IsUnit ((X.presheaf.germ U _ hy).hom u)) :
    P'.ord (𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
      (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom u))) = 0 := by
  classical

  have hcondπ : pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype)) ≫ π =
      pullback.snd π (Spec.map (CommRingCat.ofHom O.subtype)) ≫ Spec.map (CommRingCat.ofHom O.subtype) := pullback.condition
  obtain ⟨Pt', hPt', -⟩ := NeronModelInfra.existsUnique_schemeHomOver_comp_eq_of_isProper_valuationSubring O π (𝟙 _)
    ((𝔐.pointEquivPlace.symm P').1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) (by
      rw [Category.comp_id, Category.assoc, Category.assoc, hcondπ, ← Category.assoc, ← Category.assoc,
        show ((𝔐.pointEquivPlace.symm P').1 ≫ e) ≫ pullback.snd π (Spec.map (CommRingCat.ofHom O.subtype)) = 𝟙 _ by
          rw [Category.assoc, he]; exact (𝔐.pointEquivPlace.symm P').2, Category.id_comp])

  have hgen : (Spec.map (CommRingCat.ofHom O.subtype)).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) =
      genericPoint ↥(Spec (CommRingCat.of ↥O)) := by
    apply IsGenericPoint.eq _ (genericPoint_spec _)
    rw [isGenericPoint_iff_specializes]
    intro q
    simp only [Set.mem_univ, iff_true]
    refine (PrimeSpectrum.le_iff_specializes
      (PrimeSpectrum.comap O.subtype (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) q).1 ?_
    intro a ha
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at ha
    have : (a : AlgebraicClosure ℚ) = 0 := by
      simpa [IsLocalRing.closedPoint] using ha
    have : a = 0 := Subtype.ext this
    rw [this]; exact q.asIdeal.zero_mem
  have hpt : ((𝔐.pointEquivPlace.symm P').1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).base
        (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = Pt'.1.base (genericPoint ↥(Spec (CommRingCat.of ↥O))) := by
    rw [← hgen, ← hPt']; rfl
  have hyU : Pt'.1.base (genericPoint ↥(Spec (CommRingCat.of ↥O))) ∈ U := hpt ▸ hy
  have hunit' : IsUnit ((X.presheaf.germ U _ hyU).hom u) := by
    have key : ∀ (x₁ : ↥X) (hx₁ : x₁ ∈ U),
        x₁ = ((𝔐.pointEquivPlace.symm P').1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).base
          (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) → IsUnit ((X.presheaf.germ U x₁ hx₁).hom u) := by
      rintro x₁ hx₁ rfl; exact hunit
    exact key _ hyU hpt.symm
  exact GC3aH1.ord_eq_zero_of_isUnit_germ O p hp hO X π F 𝔐 e P' Pt' hPt' U u hyU hunit' hneL

end GC3aC5
p2m_export "" "GC3aC5.ord_eq_zero_of_isUnit_germ"

theorem GC3aC5.stalkSpecializes_genericPoint_closedPoint_injective
    (A : Type*) [CommRing A] [IsDomain A] [IsLocalRing A] :
    Function.Injective ((Spec (CommRingCat.of A)).presheaf.stalkSpecializes
      (genericPoint_specializes (IsLocalRing.closedPoint A))).hom :=
  IsFractionRing.injective
    ((Spec (CommRingCat.of A)).presheaf.stalk (IsLocalRing.closedPoint A))
    (Spec (CommRingCat.of A)).functionField

theorem GC3aC5.eq_of_germ_not_isUnit
    (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p)
    [hk : IsAlgClosed (IsLocalRing.ResidueField ↥O)]

    (X : Scheme.{0}) (π : X ⟶ Spec (CommRingCat.of ↥O)) [IsProper π] [SmoothOfRelativeDimension 1 π]
    [hXint : IsIntegral X]
    [hXk : IsIntegral (pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))]

    (F : Type v) [Field F] [Algebra (AlgebraicClosure ℚ) F] [IsCurveOver (AlgebraicClosure ℚ) F]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) F]
    (𝔐 : CurveModel (AlgebraicClosure ℚ) F)
    (e : 𝔐.C ⟶ pullback π (Spec.map (CommRingCat.ofHom O.subtype))) [IsIso e]
    (he : e ≫ pullback.snd π (Spec.map (CommRingCat.ofHom O.subtype)) = 𝔐.toBase)

    (K : Type w) [Field K] [Algebra (IsLocalRing.ResidueField ↥O) K]
    (𝔐k : CurveModel (IsLocalRing.ResidueField ↥O) K)
    (ek : 𝔐k.C ⟶ pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) [IsIso ek]
    (hek : ek ≫ pullback.snd π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))) = 𝔐k.toBase)

    (𝒪F : ValuationSubring F) (res : ↥𝒪F →+* K)
    (h𝒪F : ∀ f : F, f ∈ 𝒪F ↔
      ∃ (U : X.Opens)
        (hξ : (pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).base
                (genericPoint ↥(pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))) ∈ U)
        (_ : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ U))
        (s t : X.presheaf.obj (Opposite.op U)),
        IsUnit (X.presheaf.germ U _ hξ t) ∧
        f * 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom t)) =
          𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom s)))
    (hres : ∀ (U : X.Opens)
        (_ : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ U))
        (_ : Nonempty ((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) ⁻¹ᵁ U))
        (s : X.presheaf.obj (Opposite.op U))
        (hs : 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom s)) ∈ 𝒪F),
        res ⟨_, hs⟩ =
          𝔐k.ffEquiv.symm (𝔐k.C.germToFunctionField _
            (((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).app U).hom s)))
    (hsurj : Function.Surjective res) (hker : RingHom.ker res = IsLocalRing.maximalIdeal ↥𝒪F)

    (red : Place (AlgebraicClosure ℚ) F → Place (IsLocalRing.ResidueField ↥O) K)
    (hred : ∀ (P : Place (AlgebraicClosure ℚ) F) (Pt : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥O))) π),
      ((𝔐.pointEquivPlace.symm P).1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) =
        Spec.map (CommRingCat.ofHom O.subtype) ≫ Pt.1 →
      ((𝔐k.pointEquivPlace.symm (red P)).1 ≫ ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)) ≫ Pt.1)

    (P : Place (AlgebraicClosure ℚ) F) (Pt : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥O))) π)
    (hPt : Spec.map (CommRingCat.ofHom O.subtype) ≫ Pt.1 =
      (𝔐.pointEquivPlace.symm P).1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype)))
    (t : X.presheaf.stalk (Pt.1.base (IsLocalRing.closedPoint ↥O)))
    (hkert : RingHom.ker (Scheme.Hom.stalkMap Pt.1 (IsLocalRing.closedPoint ↥O)).hom = Ideal.span {t})
    (U : X.Opens) (hxU : Pt.1.base (IsLocalRing.closedPoint ↥O) ∈ U) (u : X.presheaf.obj (Opposite.op U))
    (hu : (X.presheaf.germ U _ hxU).hom u = t)

    (P' : Place (AlgebraicClosure ℚ) F) (Pt' : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥O))) π)
    (hPt' : Spec.map (CommRingCat.ofHom O.subtype) ≫ Pt'.1 =
      (𝔐.pointEquivPlace.symm P').1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype)))
    (hx' : Pt'.1.base (IsLocalRing.closedPoint ↥O) = Pt.1.base (IsLocalRing.closedPoint ↥O))
    (hy : ((𝔐.pointEquivPlace.symm P').1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).base
      (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ U)
    (hnu : ¬ IsUnit ((X.presheaf.germ U _ hy).hom u)) :
    P' = P := by
  classical

  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom O.subtype)) :=
    AlgebraicGeometry.isOpenImmersion_specMap_subtype_of_liesOverPrime O p hp hO
  haveI : IsOpenImmersion (pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) := inferInstance

  have hgen : (Spec.map (CommRingCat.ofHom O.subtype)).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) =
      genericPoint ↥(Spec (CommRingCat.of ↥O)) := by
    apply IsGenericPoint.eq _ (genericPoint_spec _)
    rw [isGenericPoint_iff_specializes]
    intro q
    simp only [Set.mem_univ, iff_true]
    refine (PrimeSpectrum.le_iff_specializes
      (PrimeSpectrum.comap O.subtype (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) q).1 ?_
    intro a ha
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at ha
    have : (a : AlgebraicClosure ℚ) = 0 := by
      simpa [IsLocalRing.closedPoint] using ha
    have : a = 0 := Subtype.ext this
    rw [this]; exact q.asIdeal.zero_mem

  revert hy hnu
  generalize hY : ((𝔐.pointEquivPlace.symm P').1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).base
      (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = y'
  intro hy hnu
  have hyeq : Pt'.1.base (genericPoint ↥(Spec (CommRingCat.of ↥O))) = y' := by
    rw [← hY, ← hPt', ← hgen]; rfl
  subst hyeq

  have hsO : genericPoint ↥(Spec (CommRingCat.of ↥O)) ⤳ IsLocalRing.closedPoint ↥O :=
    genericPoint_specializes (IsLocalRing.closedPoint ↥O)
  have h' : Pt'.1.base (genericPoint ↥(Spec (CommRingCat.of ↥O))) ⤳ Pt'.1.base (IsLocalRing.closedPoint ↥O) :=
    hsO.map Pt'.1.continuous
  have h'' : Pt'.1.base (genericPoint ↥(Spec (CommRingCat.of ↥O))) ⤳ Pt.1.base (IsLocalRing.closedPoint ↥O) := hx' ▸ h'

  have haux : ∀ w : X.presheaf.stalk (Pt'.1.base (IsLocalRing.closedPoint ↥O)),
      (X.presheaf.stalkSpecializes h').hom w ∈ IsLocalRing.maximalIdeal _ →
      (Pt'.1.stalkMap (IsLocalRing.closedPoint ↥O)).hom w = 0 := by
    intro w hw
    apply GC3aC5.stalkSpecializes_genericPoint_closedPoint_injective ↥O
    rw [map_zero]
    erw [← Scheme.Hom.stalkSpecializes_stalkMap_apply Pt'.1 (genericPoint ↥(Spec (CommRingCat.of ↥O)))
      (IsLocalRing.closedPoint ↥O) hsO w]
    have hF : IsLocalRing.maximalIdeal ((Spec (CommRingCat.of ↥O)).presheaf.stalk
        (genericPoint ↥(Spec (CommRingCat.of ↥O)))) = ⊥ :=
      IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField _)
    have hz := map_nonunit (Pt'.1.stalkMap (genericPoint ↥(Spec (CommRingCat.of ↥O)))).hom _ hw
    rw [hF, Ideal.mem_bot] at hz
    exact hz

  have hker' : ∀ (V : X.Opens) (hV : Pt.1.base (IsLocalRing.closedPoint ↥O) ∈ V) (s : X.presheaf.obj (Opposite.op V)),
      (Pt.1.stalkMap (IsLocalRing.closedPoint ↥O)).hom (X.presheaf.germ V (Pt.1.base (IsLocalRing.closedPoint ↥O)) hV s) = 0 →
      (Pt'.1.stalkMap (IsLocalRing.closedPoint ↥O)).hom
        (X.presheaf.germ V (Pt'.1.base (IsLocalRing.closedPoint ↥O)) (by rw [hx']; exact hV) s) = 0 := by
    intro V hV s hs
    apply haux
    erw [TopCat.Presheaf.germ_stalkSpecializes_apply]

    have hs' : (X.presheaf.germ V (Pt.1.base (IsLocalRing.closedPoint ↥O)) hV).hom s ∈ Ideal.span {t} := by
      rw [← hkert]; exact (RingHom.mem_ker).2 hs
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hs'

    have e1 : (X.presheaf.germ V (Pt'.1.base (genericPoint ↥(Spec (CommRingCat.of ↥O))))
          (h''.mem_open V.2 hV)).hom s =
        (X.presheaf.stalkSpecializes h'').hom ((X.presheaf.germ V (Pt.1.base (IsLocalRing.closedPoint ↥O)) hV).hom s) :=
      (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hV h'' s).symm
    erw [e1, ← ha, map_mul]
    apply Ideal.mul_mem_left
    rw [← hu]
    erw [TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hxU h'' u]
    exact (IsLocalRing.mem_maximalIdeal _).2 hnu

  have hPP : Pt.1 = Pt'.1 :=
    AlgebraicGeometry.eq_of_section_of_base_closedPoint_eq_of_ker_stalkMap_le π Pt.1 Pt'.1 Pt.2 Pt'.2 hx' hker'

  haveI : Mono (e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) := mono_comp _ _
  have hz : (𝔐.pointEquivPlace.symm P).1 = (𝔐.pointEquivPlace.symm P').1 := by
    rw [← cancel_mono (e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))), ← hPt, ← hPt', hPP]
  exact (𝔐.pointEquivPlace.symm.injective (Subtype.ext hz)).symm

theorem solution
    (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p)
    [hk : IsAlgClosed (IsLocalRing.ResidueField ↥O)]

    (X : Scheme.{0}) (π : X ⟶ Spec (CommRingCat.of ↥O)) [IsProper π] [SmoothOfRelativeDimension 1 π]
    [hXint : IsIntegral X]
    [hXk : IsIntegral (pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))]

    (F : Type v) [Field F] [Algebra (AlgebraicClosure ℚ) F] [IsCurveOver (AlgebraicClosure ℚ) F]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) F]
    (𝔐 : CurveModel (AlgebraicClosure ℚ) F)
    (e : 𝔐.C ⟶ pullback π (Spec.map (CommRingCat.ofHom O.subtype))) [IsIso e]
    (he : e ≫ pullback.snd π (Spec.map (CommRingCat.ofHom O.subtype)) = 𝔐.toBase)

    (K : Type w) [Field K] [Algebra (IsLocalRing.ResidueField ↥O) K]
    (𝔐k : CurveModel (IsLocalRing.ResidueField ↥O) K)
    (ek : 𝔐k.C ⟶ pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) [IsIso ek]
    (hek : ek ≫ pullback.snd π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))) = 𝔐k.toBase)

    (𝒪F : ValuationSubring F) (res : ↥𝒪F →+* K)
    (h𝒪F : ∀ f : F, f ∈ 𝒪F ↔
      ∃ (U : X.Opens)
        (hξ : (pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).base
                (genericPoint ↥(pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))) ∈ U)
        (_ : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ U))
        (s t : X.presheaf.obj (Opposite.op U)),
        IsUnit (X.presheaf.germ U _ hξ t) ∧
        f * 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom t)) =
          𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom s)))
    (hres : ∀ (U : X.Opens)
        (_ : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ U))
        (_ : Nonempty ((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) ⁻¹ᵁ U))
        (s : X.presheaf.obj (Opposite.op U))
        (hs : 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
              (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom s)) ∈ 𝒪F),
        res ⟨_, hs⟩ =
          𝔐k.ffEquiv.symm (𝔐k.C.germToFunctionField _
            (((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).app U).hom s)))
    (hsurj : Function.Surjective res) (hker : RingHom.ker res = IsLocalRing.maximalIdeal ↥𝒪F)

    (red : Place (AlgebraicClosure ℚ) F → Place (IsLocalRing.ResidueField ↥O) K)
    (hred : ∀ (P : Place (AlgebraicClosure ℚ) F) (Pt : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥O))) π),
      ((𝔐.pointEquivPlace.symm P).1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) =
        Spec.map (CommRingCat.ofHom O.subtype) ≫ Pt.1 →
      ((𝔐k.pointEquivPlace.symm (red P)).1 ≫ ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)) ≫ Pt.1) :
    ∀ P : Place (AlgebraicClosure ℚ) F, ∃ (u : F) (hu : u ∈ 𝒪F), u⁻¹ ∈ 𝒪F ∧ P.ord u = 1 ∧
      (∀ P' : Place (AlgebraicClosure ℚ) F, red P' = red P → P' ≠ P → P'.ord u = 0) ∧
      (red P).ord (res ⟨u, hu⟩) = 1 := by
  classical
  intro P

  have hcondπ : pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype)) ≫ π =
      pullback.snd π (Spec.map (CommRingCat.ofHom O.subtype)) ≫ Spec.map (CommRingCat.ofHom O.subtype) := pullback.condition
  obtain ⟨Pt, hPt, -⟩ := NeronModelInfra.existsUnique_schemeHomOver_comp_eq_of_isProper_valuationSubring O π (𝟙 _)
    ((𝔐.pointEquivPlace.symm P).1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) (by
      rw [Category.comp_id, Category.assoc, Category.assoc, hcondπ, ← Category.assoc, ← Category.assoc,
        show ((𝔐.pointEquivPlace.symm P).1 ≫ e) ≫ pullback.snd π (Spec.map (CommRingCat.ofHom O.subtype)) = 𝟙 _ by
          rw [Category.assoc, he]; exact (𝔐.pointEquivPlace.symm P).2, Category.id_comp])

  obtain ⟨t, hkert, hmaxt⟩ :=
    AlgebraicGeometry.exists_ker_stalkMap_eq_span_and_maximalIdeal_eq_of_section_of_smoothOfRelativeDimension_one π Pt.1 Pt.2

  obtain ⟨U, hxU, u, hu⟩ := X.presheaf.germ_exist (x := Pt.1.base (IsLocalRing.closedPoint ↥O)) t

  have hPtU : ∀ q : ↥(Spec (CommRingCat.of ↥O)), Pt.1.base q ∈ U := fun q =>
    ((IsLocalRing.specializes_closedPoint q).map Pt.1.base.hom.continuous).mem_open U.2 hxU

  have hkpt : ((𝔐k.pointEquivPlace.symm (red P)).1 ≫ ek ≫
      pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).base
        (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O)) = Pt.1.base (IsLocalRing.closedPoint ↥O) := by
    rw [hred P Pt hPt.symm]
    show Pt.1.base ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))).base
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O))) = _
    congr 1
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue ↥O)
  have hξU : (pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).base
      (genericPoint ↥(pullback π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))) ∈ U := by

    have hsp := (genericPoint_specializes (ek.base ((𝔐k.pointEquivPlace.symm (red P)).1.base
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O))))).map
      (pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).base.hom.continuous
    refine hsp.mem_open U.2 ?_
    show ((𝔐k.pointEquivPlace.symm (red P)).1 ≫ ek ≫
      pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).base _ ∈ U
    rw [hkpt]; exact hxU
  have hneL : Nonempty ((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) ⁻¹ᵁ U) := by
    refine ⟨⟨(𝔐.pointEquivPlace.symm P).1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)), ?_⟩⟩
    show ((𝔐.pointEquivPlace.symm P).1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).base _ ∈ U
    rw [← hPt]
    exact hPtU _
  have hnek : Nonempty ((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))) ⁻¹ᵁ U) := by
    refine ⟨⟨(𝔐k.pointEquivPlace.symm (red P)).1.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O)), ?_⟩⟩
    show ((𝔐k.pointEquivPlace.symm (red P)).1 ≫ ek ≫
      pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).base _ ∈ U
    rw [hkpt]; exact hxU

  haveI := hneL
  haveI := hnek
  let uF : F := 𝔐.ffEquiv.symm (𝔐.C.germToFunctionField _
      (((e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).app U).hom u))
  let uK : K := 𝔐k.ffEquiv.symm (𝔐k.C.germToFunctionField _
      (((ek ≫ pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))).app U).hom u))

  have huO : uF ∈ 𝒪F := by
    refine (h𝒪F uF).mpr ⟨U, hξU, hneL, u, 1, by rw [map_one]; exact isUnit_one, ?_⟩
    rw [map_one, map_one, map_one, mul_one]

  have hresu : res ⟨uF, huO⟩ = uK := hres U hneL hnek u huO

  have hordk : (red P).ord uK = 1 :=
    AlgebraicCurve.ord_red_residue_section_eq_one_of_maximalIdeal_eq_of_smoothOfRelativeDimension_one O p hp hO X π F 𝔐 e he K 𝔐k
      ek hek 𝒪F res h𝒪F hres hsurj hker red hred P Pt hPt t hmaxt U hxU u hu hnek

  have huinvO : uF⁻¹ ∈ 𝒪F := by
    have hne : res ⟨uF, huO⟩ ≠ 0 := by
      rw [hresu]; intro h0; rw [h0, Place.ord_zero] at hordk; exact zero_ne_one hordk
    have hunit : IsUnit (⟨uF, huO⟩ : ↥𝒪F) := by
      by_contra hnu
      exact hne ((RingHom.mem_ker).1 (hker.symm ▸ (IsLocalRing.mem_maximalIdeal _).2 hnu))
    obtain ⟨w, hw⟩ := hunit
    have h0 : uF ≠ 0 := fun h => hne (by
      have : (⟨uF, huO⟩ : ↥𝒪F) = 0 := Subtype.ext h
      rw [this, map_zero])
    have : ((w⁻¹ : (↥𝒪F)ˣ) : ↥𝒪F).1 = uF⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have := congrArg (fun z : ↥𝒪F => (z : F)) w.inv_mul
      simpa [hw] using this
    rw [← this]; exact Subtype.mem _

  have hordP : P.ord uF = 1 := by

    haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom O.subtype)) :=
      AlgebraicGeometry.isOpenImmersion_specMap_subtype_of_liesOverPrime O p hp hO
    haveI : IsOpenImmersion (pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) := inferInstance
    set G' := e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype)) with hG'def
    haveI : IsOpenImmersion G' := inferInstance
    set zP := 𝔐.pointEquivPlace.symm P with hzPdef
    have hzPP : 𝔐.pointEquivPlace zP = P := by rw [hzPdef, Equiv.apply_symm_apply]
    set y' : ↥𝔐.C := zP.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) with hy'def

    have hgen : (Spec.map (CommRingCat.ofHom O.subtype)).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) =
        genericPoint ↥(Spec (CommRingCat.of ↥O)) := by
      apply IsGenericPoint.eq _ (genericPoint_spec _)
      rw [isGenericPoint_iff_specializes]
      intro q
      simp only [Set.mem_univ, iff_true]
      refine (PrimeSpectrum.le_iff_specializes
        (PrimeSpectrum.comap O.subtype (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) q).1 ?_
      intro a ha
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at ha
      have : (a : AlgebraicClosure ℚ) = 0 := by
        simpa [IsLocalRing.closedPoint] using ha
      have : a = 0 := Subtype.ext this
      rw [this]; exact q.asIdeal.zero_mem
    have hG'y : G'.base y' = Pt.1.base (genericPoint ↥(Spec (CommRingCat.of ↥O))) := by
      rw [← hgen]
      show (zP.1 ≫ G').base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) =
        (Spec.map (CommRingCat.ofHom O.subtype) ≫ Pt.1).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))
      rw [hG'def, hPt]

    have hC3 := AlgebraicGeometry.maximalIdeal_stalk_eq_span_stalkSpecializes_of_ker_stalkMap_eq_span π Pt.1 Pt.2 t hkert

    have hspec : (X.presheaf.stalkSpecializes (((genericPoint_specializes (IsLocalRing.closedPoint ↥O)).map Pt.1.continuous) :
          Pt.1.base (genericPoint ↥(Spec (CommRingCat.of ↥O))) ⤳ Pt.1.base (IsLocalRing.closedPoint ↥O))).hom t =
        (X.presheaf.germ U (Pt.1.base (genericPoint ↥(Spec (CommRingCat.of ↥O))))
          ((((genericPoint_specializes (IsLocalRing.closedPoint ↥O)).map Pt.1.continuous)).mem_open U.2 hxU)).hom u := by
      rw [← hu]
      exact TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hxU _ u
    rw [hspec] at hC3

    have hyU : G'.base y' ∈ U := by rw [hG'y]; exact ((genericPoint_specializes (IsLocalRing.closedPoint ↥O)).map Pt.1.continuous).mem_open U.2 hxU
    have hmax' : IsLocalRing.maximalIdeal (X.presheaf.stalk (G'.base y')) =
        Ideal.span {(X.presheaf.germ U (G'.base y') hyU).hom u} := by
      revert hyU; rw [hG'y]; intro hyU; exact hC3

    set φ' := (G'.stalkMap y').hom with hφ'def
    haveI : IsLocalHom φ' := inferInstance
    have hφ'surj : Function.Surjective φ' := by
      have : IsIso (G'.stalkMap y') := inferInstance
      exact (ConcreteCategory.bijective_of_isIso (G'.stalkMap y')).2
    have hmaxy' : IsLocalRing.maximalIdeal (𝔐.C.presheaf.stalk y') =
        Ideal.span {φ' ((X.presheaf.germ U (G'.base y') hyU).hom u)} := by
      rw [← GC3aC4.map_maximalIdeal_of_surjective φ' hφ'surj, hmax', Ideal.map_span, Set.image_singleton]
    have hg' : φ' ((X.presheaf.germ U (G'.base y') hyU).hom u) = (𝔐.C.presheaf.germ (G' ⁻¹ᵁ U) y' hyU).hom ((G'.app U).hom u) := by
      rw [hφ'def]; exact Scheme.Hom.germ_stalkMap_apply G' U y' hyU u
    rw [hg'] at hmaxy'

    have hyc : y' ∈ closedPoints ↥𝔐.C := by
      have := (pointEquivClosedPoint 𝔐.toBase zP).2
      rwa [pointEquivClosedPoint_apply_coe] at this
    have hplace : 𝔐.placeOfPoint ⟨y', hyc⟩ = P := by
      rw [← hzPP, AlgebraicCurve.CurveModel.pointEquivPlace_apply]
      exact congrArg 𝔐.placeOfPoint (Subtype.ext (pointEquivClosedPoint_apply_coe 𝔐.toBase zP).symm)
    have h1 := AlgebraicCurve.CurveModel.ord_placeOfPoint_ffEquiv_symm_algebraMap_eq_one_of_maximalIdeal_eq_span 𝔐 ⟨y', hyc⟩ _ hmaxy'
    rw [hplace] at h1
    have hgerm : algebraMap (𝔐.C.presheaf.stalk y') 𝔐.C.functionField
        ((𝔐.C.presheaf.germ (G' ⁻¹ᵁ U) y' hyU).hom ((G'.app U).hom u)) =
        𝔐.C.germToFunctionField (G' ⁻¹ᵁ U) ((G'.app U).hom u) :=
      TopCat.Presheaf.germ_stalkSpecializes_apply 𝔐.C.presheaf (show y' ∈ G' ⁻¹ᵁ U from hyU) (genericPoint_specializes y') _
    rw [hgerm] at h1
    exact h1

  have hother : ∀ P' : Place (AlgebraicClosure ℚ) F, red P' = red P → P' ≠ P → P'.ord uF = 0 := by
    intro P' hredeq hne

    obtain ⟨Pt', hPt', -⟩ := NeronModelInfra.existsUnique_schemeHomOver_comp_eq_of_isProper_valuationSubring O π (𝟙 _)
      ((𝔐.pointEquivPlace.symm P').1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))) (by
        rw [Category.comp_id, Category.assoc, Category.assoc, hcondπ, ← Category.assoc, ← Category.assoc,
          show ((𝔐.pointEquivPlace.symm P').1 ≫ e) ≫ pullback.snd π (Spec.map (CommRingCat.ofHom O.subtype)) = 𝟙 _ by
            rw [Category.assoc, he]; exact (𝔐.pointEquivPlace.symm P').2, Category.id_comp])

    have hx' : Pt'.1.base (IsLocalRing.closedPoint ↥O) = Pt.1.base (IsLocalRing.closedPoint ↥O) := by
      have h12 : Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)) ≫ Pt'.1 =
          Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)) ≫ Pt.1 := by
        rw [← hred P' Pt' hPt'.symm, ← hred P Pt hPt.symm, hredeq]
      have hc : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))).base
          (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O)) = IsLocalRing.closedPoint ↥O :=
        IsLocalRing.comap_closedPoint (IsLocalRing.residue ↥O)
      have h3 : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)) ≫ Pt'.1).base
            (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O)) =
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)) ≫ Pt.1).base
            (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O)) := by rw [h12]
      change Pt'.1.base ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))).base
          (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O))) =
        Pt.1.base ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))).base
          (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥O))) at h3
      rwa [hc] at h3

    have hy' : ((𝔐.pointEquivPlace.symm P').1 ≫ e ≫ pullback.fst π (Spec.map (CommRingCat.ofHom O.subtype))).base
        (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ U := by
      rw [← hPt']
      show Pt'.1.base ((Spec.map (CommRingCat.ofHom O.subtype)).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) ∈ U
      have hxU' : Pt'.1.base (IsLocalRing.closedPoint ↥O) ∈ U := by rw [hx']; exact hxU
      exact ((IsLocalRing.specializes_closedPoint _).map Pt'.1.base.hom.continuous).mem_open U.2 hxU'
    by_cases hunit : IsUnit ((X.presheaf.germ U _ hy').hom u)
    ·
      exact GC3aC5.ord_eq_zero_of_isUnit_germ O p hp hO X π F 𝔐 e he K 𝔐k ek hek 𝒪F res h𝒪F hres hsurj hker red hred
        U hneL u P' hy' hunit
    ·
      exact absurd (GC3aC5.eq_of_germ_not_isUnit O p hp hO X π F 𝔐 e he K 𝔐k ek hek 𝒪F res h𝒪F hres hsurj hker red hred
        P Pt hPt t hkert U hxU u hu P' Pt' hPt' hx' hy' hunit) hne
  exact ⟨uF, huO, huinvO, hordP, hother, by rw [hresu]; exact hordk⟩

end S_AlgebraicCurve_exists_mem_ord_eq_one_ord_residue_eq_one_of_smoothOfRelativeDimension_one
end P2MW
export P2MW.S_AlgebraicCurve_exists_mem_ord_eq_one_ord_residue_eq_one_of_smoothOfRelativeDimension_one (solution)
