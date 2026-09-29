-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.isFinite_and_flat_and_locallyOfFinitePresentation_and_surjective_of_pointEquivPlace_comp_eq_restrictAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/81beb1d3-15be-5aad-84f0-f1a79382f5f5

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Theorems.Thm_AlgebraicCurve_CurveModel_infinite_place
import Theorems.Thm_AlgebraicGeometry_flat_and_finrank_eq_of_isFinite_of_surjective_of_ringKrullDim_le_one
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_isFinite_and_flat_and_locallyOfFinitePresentation_and_surjective_of_pointEquivPlace_comp_eq_restrictAlong
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C"
p2m_attr_erase "simp" "ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

noncomputable section

namespace FF17

open TopologicalSpace

theorem finite_of_isClosed_of_forall_isClosed_singleton {α : Type*} [TopologicalSpace α] [NoetherianSpace α] [QuasiSober α]
    (Z : Set α) (hZ : IsClosed Z) (hpt : ∀ z ∈ Z, IsClosed ({z} : Set α)) : Z.Finite := by
  obtain ⟨S, hSfin, hSclosed, hSirr, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine hSfin.sUnion fun t ht => (Set.finite_singleton (hSirr t ht).genericPoint).subset fun z hz => ?_
  have hgen := (hSirr t ht).isGenericPoint_genericPoint (hSclosed t ht)
  have hmem : (hSirr t ht).genericPoint ∈ t := hgen.mem
  have hcl := (hpt _ (Set.mem_sUnion_of_mem hmem ht)).closure_eq
  have hz' : z ∈ closure ({(hSirr t ht).genericPoint} : Set α) := by
    rw [hgen.def]; exact hz
  rwa [hcl] at hz'

theorem isClosed_singleton_base_of_isClosed {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType fX] [LocallyOfFiniteType fY]
    (g : X ⟶ Y) (hg : g ≫ fY = fX) (x : X) (hx : IsClosed ({x} : Set X)) : IsClosed ({g.base x} : Set Y) := by
  let p := (pointEquivClosedPoint fX).symm ⟨x, hx⟩
  have hp : p.1.base (IsLocalRing.closedPoint k) = x :=
    congrArg Subtype.val ((pointEquivClosedPoint fX).apply_symm_apply ⟨x, hx⟩)
  have hq : (p.1 ≫ g) ≫ fY = 𝟙 _ := by rw [Category.assoc, hg, p.2]
  have h2 := (pointEquivClosedPoint fY ⟨p.1 ≫ g, hq⟩).2
  change IsClosed ({g.base (p.1.base (IsLocalRing.closedPoint k))} : Set Y) at h2
  rwa [hp] at h2

end FF17

end

open FF17 in
theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {F : Type v} [Field F] [Algebra k F] [HasPrincipalDivisors k F] {F' : Type v} [Field F'] [Algebra k F'] [HasPrincipalDivisors k F']
    (M : CurveModel k F) (M' : CurveModel k F')
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral)
    (g : M'.C ⟶ M.C) (hg : g ≫ M.toBase = M'.toBase)
    (hgφ : ∀ x' : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _},
      M.pointEquivPlace ⟨x'.1 ≫ g, by rw [Category.assoc, hg]; exact x'.2⟩ = (M'.pointEquivPlace x').restrictAlong φ hφ) :
    IsFinite g ∧ Flat g ∧ LocallyOfFinitePresentation g ∧ Surjective g := by
  classical
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ

  haveI : IsProper g := by
    have : IsProper (g ≫ M.toBase) := by rw [hg]; infer_instance
    exact IsProper.of_comp g M.toBase
  haveI : IsLocallyNoetherian M'.C := LocallyOfFiniteType.isLocallyNoetherian M'.toBase
  haveI : IsLocallyNoetherian M.C := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  haveI : CompactSpace M'.C := by
    haveI h1 : QuasiCompact (Limits.terminal.from (Spec (CommRingCat.of k))) :=
      (compactSpace_iff_quasiCompact _).mp inferInstance
    have h2 : QuasiCompact (M'.toBase ≫ Limits.terminal.from _) := inferInstance
    rw [Limits.terminal.comp_from] at h2
    exact (compactSpace_iff_quasiCompact _).mpr h2
  haveI : IsNoetherian M'.C := {}

  have hres : ∀ y : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _},
      M.pointEquivPlace ⟨y.1 ≫ g, by rw [Category.assoc, hg]; exact y.2⟩ = (M'.pointEquivPlace y).restrict F := fun y => hgφ y

  have hbase : ∀ (y : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _}),
      ((pointEquivClosedPoint M.toBase) ⟨y.1 ≫ g, by rw [Category.assoc, hg]; exact y.2⟩).1 = g.base (y.1.base (IsLocalRing.closedPoint k)) := by
    intro y; simp [pointEquivClosedPoint]

  have hgen : g.base (genericPoint M'.C) = genericPoint M.C := by
    by_contra hne
    have hz : IsClosed ({g.base (genericPoint M'.C)} : Set M.C) :=
      AlgebraicCurve.isClosed_singleton_of_ne_genericPoint M.toBase _ hne
    have hall : ∀ x' : M'.C, g.base x' = g.base (genericPoint M'.C) := by
      intro x'
      have hs : g.base (genericPoint M'.C) ⤳ g.base x' :=
        ((genericPoint_spec M'.C).specializes (Set.mem_univ x')).map g.base.hom.continuous
      have := hs.mem_closure
      rw [hz.closure_eq, Set.mem_singleton_iff] at this
      exact this
    let z₀ : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _} :=
      (pointEquivClosedPoint M.toBase).symm ⟨g.base (genericPoint M'.C), hz⟩
    have hv : ∀ w : Place k F', w.restrict F = M.pointEquivPlace z₀ := by
      intro w
      let y := M'.pointEquivPlace.symm w
      have h1 := hres y
      rw [Equiv.apply_symm_apply] at h1
      rw [← h1]
      congr 1
      apply (pointEquivClosedPoint M.toBase).injective
      apply Subtype.ext
      rw [hbase y, hall]
      change _ = ((pointEquivClosedPoint M.toBase) ((pointEquivClosedPoint M.toBase).symm ⟨g.base (genericPoint M'.C), hz⟩)).1
      rw [Equiv.apply_symm_apply]
    have hfin : (Set.univ : Set (Place k F')).Finite :=
      (Place.restrict_fiber_finite (F' := F') (M.pointEquivPlace z₀)).subset fun w _ => hv w
    haveI := M'.infinite_place
    exact Set.infinite_univ hfin

  have hηnc : ¬ IsClosed ({genericPoint M.C} : Set M.C) := by
    intro hcl
    have huniv : (Set.univ : Set M.C) = {genericPoint M.C} := by
      rw [← (genericPoint_spec M.C).def, hcl.closure_eq]
    haveI := M.infinite_place
    have : (Set.univ : Set (Place k F)).Finite := by
      refine (Set.finite_singleton (M.pointEquivPlace ((pointEquivClosedPoint M.toBase).symm ⟨genericPoint M.C, hcl⟩))).subset ?_
      intro w _
      rw [Set.mem_singleton_iff]
      have hx := (pointEquivClosedPoint M.toBase (M.pointEquivPlace.symm w)).2

      have heq : (pointEquivClosedPoint M.toBase (M.pointEquivPlace.symm w)) = ⟨genericPoint M.C, hcl⟩ := by
        apply Subtype.ext
        have : ((pointEquivClosedPoint M.toBase (M.pointEquivPlace.symm w)).1 : M.C) ∈ (Set.univ : Set M.C) := Set.mem_univ _
        rwa [huniv, Set.mem_singleton_iff] at this
      have := congrArg (fun q => M.pointEquivPlace ((pointEquivClosedPoint M.toBase).symm q)) heq
      simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply] at this
      exact this
    exact Set.infinite_univ this

  haveI : LocallyQuasiFinite g := by
    rw [locallyQuasiFinite_iff_finite_preimage_singleton]
    intro z
    by_cases hzη : z = genericPoint M.C
    · subst hzη
      refine (Set.finite_singleton (genericPoint M'.C)).subset fun x hx => ?_
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
      rw [Set.mem_singleton_iff]
      by_contra hxη
      have hxc : IsClosed ({x} : Set M'.C) := AlgebraicCurve.isClosed_singleton_of_ne_genericPoint M'.toBase x hxη
      have := isClosed_singleton_base_of_isClosed M'.toBase M.toBase g hg x hxc
      rw [hx] at this
      exact hηnc this
    · have hzc : IsClosed ({z} : Set M.C) := AlgebraicCurve.isClosed_singleton_of_ne_genericPoint M.toBase z hzη
      refine finite_of_isClosed_of_forall_isClosed_singleton _ (hzc.preimage g.base.hom.continuous) ?_
      intro x hx
      refine AlgebraicCurve.isClosed_singleton_of_ne_genericPoint M'.toBase x fun hxη => hzη ?_
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
      rw [← hx, hxη, hgen]
  haveI hfinite : IsFinite g := IsFinite.of_isProper_of_locallyQuasiFinite g

  haveI hsurj : Surjective g := ⟨by
    have hcl : IsClosed (Set.range g.base) := g.isClosedMap.isClosed_range
    have h : closure ({genericPoint M.C} : Set M.C) ⊆ Set.range g.base :=
      hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨_, hgen⟩)
    rw [(genericPoint_spec M.C).def] at h
    exact fun y => h (Set.mem_univ y)⟩

  have hY : ∀ y : M.C, IsIntegrallyClosed (M.C.presheaf.stalk y) := by
    intro y
    have hFk : IsField Γ(Spec (CommRingCat.of k), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField k)
    letI : Field Γ(Spec (CommRingCat.of k), ⊤) := hFk.toField
    haveI : IsIntegrallyClosed Γ(Spec (CommRingCat.of k), ⊤) := inferInstance
    haveI : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
    exact (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase y).2
  have hdim : ∀ y : M.C, ringKrullDim (M.C.presheaf.stalk y) ≤ 1 := by
    intro y
    by_cases hyη : y = genericPoint M.C
    · subst hyη
      rw [ringKrullDim_eq_zero_of_field M.C.functionField]
      exact zero_le_one
    ·
      have hyc : IsClosed ({y} : Set M.C) := AlgebraicCurve.isClosed_singleton_of_ne_genericPoint M.toBase y hyη
      let ψ : M.C.presheaf.stalk y →+* F :=
        (M.ffEquiv.symm : M.C.functionField ≃+* F).toRingHom.comp (algebraMap (M.C.presheaf.stalk y) M.C.functionField)
      have hinj : Function.Injective ψ :=
        (M.ffEquiv.symm.injective).comp (IsFractionRing.injective (M.C.presheaf.stalk y) M.C.functionField)
      have hrange : ψ.range = (M.placeOfPoint ⟨y, hyc⟩).toValuationSubring.toSubring := M.range_stalk_eq ⟨y, hyc⟩
      have hbij : Function.Bijective ψ.rangeRestrict :=
        ⟨fun a b h => hinj (congrArg Subtype.val h), ψ.rangeRestrict_surjective⟩
      let e : M.C.presheaf.stalk y ≃+* ↥(M.placeOfPoint ⟨y, hyc⟩).toValuationSubring :=
        (RingEquiv.ofBijective ψ.rangeRestrict hbij).trans (RingEquiv.subringCongr hrange)
      haveI : Ring.DimensionLEOne (M.C.presheaf.stalk y) := Ring.DimensionLEOne.of_ringEquiv e
      exact Ring.krullDimLE_iff.mp inferInstance
  obtain ⟨U, hU, hηU⟩ := M.finset_subset_affineOpen {genericPoint M.C}
  haveI : Nonempty U := ⟨⟨_, hηU _ (Finset.mem_singleton_self _)⟩⟩
  obtain ⟨hlfp, hflat, -⟩ :=
    AlgebraicGeometry.flat_and_finrank_eq_of_isFinite_of_surjective_of_ringKrullDim_le_one g hY hdim U hU _ rfl
  exact ⟨hfinite, hflat, hlfp, hsurj⟩

end S_AlgebraicCurve_CurveModel_isFinite_and_flat_and_locallyOfFinitePresentation_and_surjective_of_pointEquivPlace_comp_eq_restrictAlong
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_isFinite_and_flat_and_locallyOfFinitePresentation_and_surjective_of_pointEquivPlace_comp_eq_restrictAlong (solution)
