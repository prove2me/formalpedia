-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_place_comap_eq_and_ord_eq_mul_ord_of_forall_smul_maximalIdeal_map_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/8f0f157e-8f49-5880-992d-5c7134be54c4

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_eq_toValuationSubring
import Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_of_ne_top
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap_eq_mul_ord_of_constant_extension
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_place_comap_eq_and_ord_eq_mul_ord_of_forall_smul_maximalIdeal_map_eq_pow
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_exists_place_comap_eq_and_ord_eq_mul_ord_of_forall_smul_maximalIdeal_map_eq_pow.AlgebraicCurve"
open scoped Pointwise

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.exists_comap_eq_toValuationSubring Place.exists_toValuationSubring_eq_comap_of_ne_top Place.ord_algebraMap_eq_mul_ord_of_constant_extension"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ord ord_coe_irreducible ord_unit_smul_zpow ne_top' algebraMap_mem' toValuationSubring exists_comap_eq_toValuationSubring exists_toValuationSubring_eq_comap_of_ne_top ord_algebraMap_eq_mul_ord_of_constant_extension"
namespace ConjugateCore
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

section OrdHelper
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem Place.ord_eq_of_span_eq_pow' (v : Place K F) {f : ↥v.toValuationSubring} {n : ℕ}
    (h : Ideal.span {f} = IsLocalRing.maximalIdeal ↥v.toValuationSubring ^ n) : v.ord (f : F) = n := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥v.toValuationSubring
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at h
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 h
  have h1 : (f : ↥v.toValuationSubring) = ϖ ^ n * ((u⁻¹ : (↥v.toValuationSubring)ˣ) : ↥v.toValuationSubring) := by
    rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  have h2 := congrArg (fun x : ↥v.toValuationSubring => (x : F)) h1
  simp only [SubmonoidClass.coe_pow, MulMemClass.coe_mul] at h2
  rw [h2, mul_comm, ← zpow_natCast, v.ord_unit_smul_zpow _ hϖ]

end OrdHelper

end AlgebraicCurve.Place.ConjugateCore

open AlgebraicCurve.Place.ConjugateCore in
theorem solution
    {κ k F 𝓕 F' : Type*} [Field κ] [Field k] [Field F] [Field 𝓕] [Field F']
    [Algebra κ k] [Algebra.IsAlgebraic κ k] [Algebra.IsSeparable κ k] [Algebra κ F] [Algebra k 𝓕] [Algebra k F']
    (G : Type*) [Group G] [Fintype G] [MulSemiringAction G F] [FaithfulSMul G F]
    (hGκ : ∀ (g : G) (c : κ), g • algebraMap κ F c = algebraMap κ F c)
    (P : ValuationSubring F) [IsDiscreteValuationRing ↥P] (hκP : ∀ c : κ, algebraMap κ F c ∈ P)
    (n : ℕ)

    [IsDiscreteValuationRing ↥(P.comap (FixedPoints.subfield G F).subtype)]
    (hcoreG : ∀ (g : G) (Q : ValuationSubring F), Q = g • P →
      ∀ (j : ↥(P.comap (FixedPoints.subfield G F).subtype) →+* ↥Q),
      (∀ r, ((j r : ↥Q) : F) = ((r : ↥(FixedPoints.subfield G F)) : F)) →
      Ideal.map j (IsLocalRing.maximalIdeal ↥(P.comap (FixedPoints.subfield G F).subtype))
        = IsLocalRing.maximalIdeal ↥Q ^ n)

    (htrans : ∀ Q : ValuationSubring F, Q ≠ ⊤ →
      (∀ e : ↥(FixedPoints.subfield G F), (e : F) ∈ Q ↔ (e : F) ∈ P) → ∃ g : G, Q = g • P)

    (θE : ↥(FixedPoints.subfield G F) →+* 𝓕) (φ : F →+* F') (ι : 𝓕 →+* F')
    (hsq : ∀ e : ↥(FixedPoints.subfield G F), ι (θE e) = φ (e : F))
    (hθEκ : ∀ c : κ, θE ⟨algebraMap κ F c, fun g => hGκ g c⟩ = algebraMap k 𝓕 (algebraMap κ k c))
    (hφκ : ∀ c : κ, φ (algebraMap κ F c) = algebraMap k F' (algebraMap κ k c))
    (hιk : ∀ c : k, ι (algebraMap k 𝓕 c) = algebraMap k F' c)
    (hgen𝓕 : Algebra.adjoin k (Set.range θE) = ⊤)
    (hgenF' : Algebra.adjoin k (Set.range φ) = ⊤)

    (hfinsep : letI := ι.toAlgebra; FiniteDimensional 𝓕 F' ∧ Algebra.IsSeparable 𝓕 F')

    (w : Place k 𝓕) (hw : ∀ e : ↥(FixedPoints.subfield G F), θE e ∈ w.toValuationSubring ↔ (e : F) ∈ P) :
    ∃ x' : Place k F',
      (∀ f : 𝓕, ι f ∈ x'.toValuationSubring ↔ f ∈ w.toValuationSubring) ∧
      ∀ f : 𝓕, x'.ord (ι f) = n * w.ord f := by
  classical

  let Pb : ValuationSubring ↥(FixedPoints.subfield G F) := P.comap (FixedPoints.subfield G F).subtype
  have hPbmem : ∀ e : ↥(FixedPoints.subfield G F), e ∈ Pb ↔ (e : F) ∈ P := fun _ => Iff.rfl

  letI algι : Algebra 𝓕 F' := ι.toAlgebra
  obtain ⟨hfin, hsep⟩ := hfinsep
  haveI := hfin; haveI := hsep
  haveI : IsScalarTower k 𝓕 F' := IsScalarTower.of_algebraMap_eq (fun c => (hιk c).symm)

  obtain ⟨x', hx'⟩ := AlgebraicCurve.Place.exists_comap_eq_toValuationSubring (K := k) (F := 𝓕) (F' := F') w
  have hmem : ∀ f : 𝓕, ι f ∈ x'.toValuationSubring ↔ f ∈ w.toValuationSubring := fun f => by
    rw [← hx', ValuationSubring.mem_comap]; rfl
  refine ⟨x', hmem, ?_⟩

  have hQκ : ∀ c : κ, φ (algebraMap κ F c) ∈ x'.toValuationSubring := fun c => by
    rw [hφκ]; exact x'.algebraMap_mem' _
  have hQE : ∀ e : ↥(FixedPoints.subfield G F), (e : F) ∈ x'.toValuationSubring.comap φ ↔ (e : F) ∈ P := fun e => by
    rw [ValuationSubring.mem_comap, ← hsq, hmem, hw]
  obtain ⟨ϖb, hϖb⟩ := IsDiscreteValuationRing.exists_irreducible ↥Pb
  have hϖb0 : ((ϖb : ↥(FixedPoints.subfield G F)) : F) ≠ 0 := by
    intro h; apply hϖb.ne_zero; exact Subtype.ext (Subtype.ext h)
  have hϖbP : ((ϖb : ↥(FixedPoints.subfield G F)) : F) ∈ P := (hPbmem _).1 ϖb.2
  have hϖbinv : ((ϖb : ↥(FixedPoints.subfield G F)) : F)⁻¹ ∉ P := by
    intro hinv
    apply hϖb.not_isUnit
    have hinvb : ((ϖb : ↥(FixedPoints.subfield G F))⁻¹ : ↥(FixedPoints.subfield G F)) ∈ Pb := by rw [hPbmem]; simpa using hinv
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hinvb⟩, Subtype.ext ?_⟩
    simp only [Subring.coe_mul, OneMemClass.coe_one]
    exact mul_inv_cancel₀ (fun h => hϖb0 (by rw [h]; rfl))
  have hQne : x'.toValuationSubring.comap φ ≠ ⊤ := by
    intro htop
    have : ((ϖb : ↥(FixedPoints.subfield G F))⁻¹ : ↥(FixedPoints.subfield G F)).1 ∈ x'.toValuationSubring.comap φ := by rw [htop]; trivial
    rw [hQE] at this
    exact hϖbinv (by simpa using this)
  obtain ⟨x, hx⟩ := AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_of_ne_top (K := κ) φ x' hQκ hQne

  obtain ⟨g, hg⟩ := htrans x.toValuationSubring x.ne_top' (fun e => by rw [hx]; exact hQE e)
  let jx : ↥Pb →+* ↥x.toValuationSubring :=
    { toFun := fun r => ⟨((r : ↥(FixedPoints.subfield G F)) : F), by rw [hx, hQE]; exact (hPbmem _).1 r.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun a b => Subtype.ext rfl }
  have hjx : ∀ r, ((jx r : ↥x.toValuationSubring) : F) = ((r : ↥(FixedPoints.subfield G F)) : F) := fun _ => rfl
  have hcore := hcoreG g x.toValuationSubring hg jx hjx

  letI algκE : Algebra κ ↥(FixedPoints.subfield G F) := ((algebraMap κ F).codRestrict (FixedPoints.subfield G F).toSubring (fun c g => hGκ g c)).toAlgebra
  have hκE : ∀ c : κ, ((algebraMap κ ↥(FixedPoints.subfield G F) c : ↥(FixedPoints.subfield G F)) : F) = algebraMap κ F c := fun _ => rfl
  haveI : IsScalarTower κ ↥(FixedPoints.subfield G F) F := IsScalarTower.of_algebraMap_eq (fun c => (hκE c).symm)
  have hPbtop : Pb ≠ ⊤ := by
    intro htop
    have hmemtop : ((ϖb : ↥(FixedPoints.subfield G F))⁻¹ : ↥(FixedPoints.subfield G F)) ∈ (⊤ : ValuationSubring ↥(FixedPoints.subfield G F)) :=
      ValuationSubring.mem_top _
    rw [← htop, hPbmem] at hmemtop
    exact hϖbinv (by simpa using hmemtop)
  let y : AlgebraicCurve.Place κ ↥(FixedPoints.subfield G F) :=
    ⟨Pb, fun c => by rw [hPbmem, hκE]; exact hκP c, hPbtop, inferInstance⟩
  have hu : y.ord ((ϖb : ↥Pb) : ↥(FixedPoints.subfield G F)) = 1 := y.ord_coe_irreducible hϖb
  have hn : x.ord (algebraMap ↥(FixedPoints.subfield G F) F ((ϖb : ↥Pb) : ↥(FixedPoints.subfield G F))) = n := by
    have h1 : Ideal.span {jx ϖb} = IsLocalRing.maximalIdeal ↥x.toValuationSubring ^ n := by
      rw [← hcore, hϖb.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
    exact AlgebraicCurve.Place.ConjugateCore.Place.ord_eq_of_span_eq_pow' x h1

  letI algEF : Algebra ↥(FixedPoints.subfield G F) 𝓕 := θE.toAlgebra
  letI algFF' : Algebra F F' := φ.toAlgebra
  letI algκ𝓕 : Algebra κ 𝓕 := ((algebraMap k 𝓕).comp (algebraMap κ k)).toAlgebra
  letI algκF' : Algebra κ F' := ((algebraMap k F').comp (algebraMap κ k)).toAlgebra
  haveI : IsScalarTower κ k 𝓕 := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower κ k F' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower κ ↥(FixedPoints.subfield G F) 𝓕 := IsScalarTower.of_algebraMap_eq (fun c => by
    show algebraMap k 𝓕 (algebraMap κ k c) = θE (algebraMap κ ↥(FixedPoints.subfield G F) c)
    exact (hθEκ c).symm)
  haveI : IsScalarTower κ F F' := IsScalarTower.of_algebraMap_eq (fun c => by
    show algebraMap k F' (algebraMap κ k c) = φ (algebraMap κ F c)
    rw [hφκ])
  have hsq' : ∀ e : ↥(FixedPoints.subfield G F), algebraMap F F' (algebraMap ↥(FixedPoints.subfield G F) F e) = algebraMap 𝓕 F' (algebraMap ↥(FixedPoints.subfield G F) 𝓕 e) :=
    fun e => (hsq e).symm

  have hgenE : Algebra.adjoin ↥(FixedPoints.subfield G F) (Set.range (algebraMap k 𝓕)) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ (Algebra.adjoin k (Set.range θE)).toSubsemiring := by rw [hgen𝓕]; trivial
    change z ∈ Subsemiring.closure (Set.range (algebraMap k 𝓕) ∪ Set.range θE) at hz
    change z ∈ Subsemiring.closure (Set.range (algebraMap ↥(FixedPoints.subfield G F) 𝓕) ∪ Set.range (algebraMap k 𝓕))
    rwa [Set.union_comm]
  have hgenF : Algebra.adjoin F (Set.range (algebraMap k F')) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ (Algebra.adjoin k (Set.range φ)).toSubsemiring := by rw [hgenF']; trivial
    change z ∈ Subsemiring.closure (Set.range (algebraMap k F') ∪ Set.range φ) at hz
    change z ∈ Subsemiring.closure (Set.range (algebraMap F F') ∪ Set.range (algebraMap k F'))
    rwa [Set.union_comm]

  have hxx' : x'.toValuationSubring.comap (algebraMap F F') = x.toValuationSubring := hx.symm
  have hyw : w.toValuationSubring.comap (algebraMap ↥(FixedPoints.subfield G F) 𝓕) = y.toValuationSubring := by
    ext e
    rw [ValuationSubring.mem_comap]
    exact (hw e).trans (hPbmem e).symm
  have hx'w : x'.toValuationSubring.comap (algebraMap 𝓕 F') = w.toValuationSubring := hx'

  intro f
  exact AlgebraicCurve.Place.ord_algebraMap_eq_mul_ord_of_constant_extension
    (k := κ) (K := k) (E := ↥(FixedPoints.subfield G F)) (F := F) (E' := 𝓕) (F' := F')
    hsq' hgenE hgenF x y x' w hxx' hyw hx'w n ((ϖb : ↥Pb) : ↥(FixedPoints.subfield G F)) hu hn f

end S_AlgebraicCurve_Place_exists_place_comap_eq_and_ord_eq_mul_ord_of_forall_smul_maximalIdeal_map_eq_pow
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_place_comap_eq_and_ord_eq_mul_ord_of_forall_smul_maximalIdeal_map_eq_pow (solution)
