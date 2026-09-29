-- Prove2me | solution 1 for AlgebraicCurve.Annulus.exists_isUnit_residue_mul_evalAt_eq_evalAt_of_isAttached_of_isAttached
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/d701db5e-330f-55a4-bc6a-3e541b9e7943

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_Annulus_ord_residue_eq_neg_and_evalAt_residue_mul_zpow_eq_of_forall_ord_eq_zero_of_rankOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_exists_isUnit_residue_mul_evalAt_eq_evalAt_of_isAttached_of_isAttached
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace R2E

section PlaceLemmas
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_algebraMap (v : Place K F) {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  let u : (v.toValuationSubring)ˣ :=
    ⟨⟨algebraMap K F c, v.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simp [hc]), Subtype.ext (by simp [hc])⟩
  have := v.ord_coe_unit u
  simpa [u] using this

theorem ord_eq_zero_of_evalAt_ne_zero (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (hne : v.evalAt f ≠ 0) : v.ord f = 0 := by
  have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ ≠ 0 := by
    intro h0
    apply hne
    have := v.algebraMap_evalAt hv hf
    rw [h0] at this
    exact (map_eq_zero_iff _ (algebraMap K v.ResidueField).injective).mp this
  have hunit : IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    by_contra h
    apply hres
    have hmem : (⟨f, hf⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring :=
      (IsLocalRing.mem_maximalIdeal _).mpr h
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
  obtain ⟨u, hu⟩ := hunit
  have := v.ord_coe_unit u
  rwa [hu] at this

end PlaceLemmas

section Ends
variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

@[reducible] def rp (C : ComponentChart A F Fbar) : RegularProlongation A F Fbar where
  integers := C.integers
  residue := C.residue
  algebraMap_mem_iff := C.algebraMap_mem_iff
  residue_surjective := C.residue_surjective
  ker_residue := C.ker_residue
  residue_algebraMap := C.residue_algebraMap
  exists_smul_mem := C.exists_smul_mem

private theorem _root_.R2E.isUnit_of_residue_ne_zero (C : ComponentChart A F Fbar) {f : C.integers} (hf : C.residue f ≠ 0) :
    IsUnit f :=
  (rp C).isUnit_of_residue_ne_zero hf

p2m_export "R2E" "isUnit_of_residue_ne_zero"

theorem transfer_end {I : ValuationSubring F} (res : I →+* Fbar) (x : Place (ResidueField A) Fbar)
    {S S' : Set (Place L F)} (hS : S = S') {p p' : F} (hp : p = p')
    (H : ∃ hz : p ∈ I, x.ord (res ⟨p, hz⟩) = 1 ∧
      ∀ (f : F) (hf : f ∈ I), res ⟨f, hf⟩ ≠ 0 → (∀ P ∈ S, P.ord f = 0) → ∀ P ∈ S,
        ∃ h : P.evalAt f * (P.evalAt p) ^ (-(x.ord (res ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A)) :
    ∃ hz : p' ∈ I, x.ord (res ⟨p', hz⟩) = 1 ∧
      ∀ (f : F) (hf : f ∈ I), res ⟨f, hf⟩ ≠ 0 → (∀ P ∈ S', P.ord f = 0) → ∀ P ∈ S',
        ∃ h : P.evalAt f * (P.evalAt p') ^ (-(x.ord (res ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A) := by
  subst hS; subst hp; exact H

theorem param_ne_zero (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) : An.param ≠ 0 := by
  intro h0
  obtain ⟨-, -, -, hne, -⟩ := An.mem_dom P hP
  apply hne
  rw [h0]
  have := P.evalAt_algebraMap_eq (0 : L)
  simpa using this

theorem sub_mem_and_residue_eq (An : Annulus A F) (C : ComponentChart A F Fbar) (hz : An.param ∈ C.integers)
    {P₀ : Place L F} (hP₀ : P₀ ∈ An.dom) :
    ∃ hmem : An.param - algebraMap L F (P₀.evalAt An.param) ∈ C.integers,
      C.residue ⟨_, hmem⟩ = C.residue ⟨An.param, hz⟩ := by
  obtain ⟨-, -, ⟨hA, hmax⟩, -, -⟩ := An.mem_dom P₀ hP₀
  have hc : algebraMap L F (P₀.evalAt An.param) ∈ C.integers := (C.algebraMap_mem_iff _).mpr hA
  refine ⟨sub_mem hz hc, ?_⟩
  have hsub : (⟨An.param - algebraMap L F (P₀.evalAt An.param), sub_mem hz hc⟩ : C.integers) =
      ⟨An.param, hz⟩ - ⟨algebraMap L F (P₀.evalAt An.param), hc⟩ := rfl
  rw [hsub, map_sub]
  have h0 : C.residue ⟨algebraMap L F (P₀.evalAt An.param), hc⟩ = 0 := by
    have := C.residue_algebraMap ⟨P₀.evalAt An.param, hA⟩
    rw [show (⟨algebraMap L F (P₀.evalAt An.param), hc⟩ : C.integers) =
        ⟨algebraMap L F ((⟨P₀.evalAt An.param, hA⟩ : A) : L), (C.algebraMap_mem_iff _).mpr hA⟩ from rfl, this,
      (IsLocalRing.residue_eq_zero_iff _).mpr hmax, map_zero]
  rw [h0, sub_zero]

theorem one_sub_mem_and_residue_eq_one (An An' : Annulus A F)
    (hparam : An'.param * An.param = algebraMap L F (An.modulus : L))
    (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar)
    (hz' : An'.param ∈ C.integers) (hx : x.ord (C.residue ⟨An'.param, hz'⟩) = 1)
    {P₀ : Place L F} (hP₀ : P₀ ∈ An.dom) :
    ∃ hmem : 1 - algebraMap L F (P₀.evalAt An.param)⁻¹ * An.param ∈ C.integers,
      C.residue ⟨_, hmem⟩ = 1 := by
  obtain ⟨-, -, ⟨hA, hmax⟩, hne, m0, hm0, hmod⟩ := An.mem_dom P₀ hP₀
  set c : L := P₀.evalAt An.param with hc
  have hres' : C.residue ⟨An'.param, hz'⟩ ≠ 0 := by
    intro h0; rw [h0] at hx; simp at hx
  have hz'0 : An'.param ≠ 0 := by
    intro h
    apply hres'
    have : (⟨An'.param, hz'⟩ : C.integers) = 0 := Subtype.ext h
    rw [this, map_zero]

  obtain ⟨Z, hZ⟩ := isUnit_of_residue_ne_zero C hres'
  have hinv : An'.param⁻¹ ∈ C.integers := by
    have hval : (((Z⁻¹ : C.integersˣ) : C.integers) : F) = An'.param⁻¹ := by
      have h1 := congrArg (fun u : C.integersˣ => ((u : C.integers) : F)) (mul_inv_cancel Z)
      simp only [Units.val_mul, Units.val_one, OneMemClass.coe_one, hZ] at h1

      exact (eq_inv_of_mul_eq_one_right h1)
    rw [← hval]; exact ((Z⁻¹ : C.integersˣ) : C.integers).2

  have hm0F : algebraMap L F (m0 : L) ∈ C.integers := (C.algebraMap_mem_iff _).mpr m0.2
  have hzq : An.param = algebraMap L F (An.modulus : L) * An'.param⁻¹ := by
    rw [← hparam]; field_simp
  have hkey : algebraMap L F c⁻¹ * An.param = algebraMap L F (m0 : L) * An'.param⁻¹ := by
    rw [hzq, hmod, ← mul_assoc, ← map_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hmem' : 1 - algebraMap L F (m0 : L) * An'.param⁻¹ ∈ C.integers :=
    sub_mem (one_mem _) (mul_mem hm0F hinv)
  have hmem : 1 - algebraMap L F c⁻¹ * An.param ∈ C.integers := by rw [hkey]; exact hmem'
  refine ⟨hmem, ?_⟩
  have h1 : (⟨1 - algebraMap L F c⁻¹ * An.param, hmem⟩ : C.integers) =
      ⟨1 - algebraMap L F (m0 : L) * An'.param⁻¹, hmem'⟩ := Subtype.ext (by show 1 - algebraMap L F c⁻¹ * An.param = _; rw [hkey])
  have h2 : (⟨1 - algebraMap L F (m0 : L) * An'.param⁻¹, hmem'⟩ : C.integers) =
      1 - ⟨algebraMap L F (m0 : L), hm0F⟩ * ⟨An'.param⁻¹, hinv⟩ := Subtype.ext rfl
  rw [h1, h2, map_sub, map_one, map_mul]
  have h3 : C.residue ⟨algebraMap L F (m0 : L), hm0F⟩ = 0 := by
    rw [show (⟨algebraMap L F (m0 : L), hm0F⟩ : C.integers) =
        ⟨algebraMap L F (m0 : L), (C.algebraMap_mem_iff _).mpr m0.2⟩ from rfl,
      C.residue_algebraMap m0, (IsLocalRing.residue_eq_zero_iff _).mpr hm0, map_zero]
  rw [h3, zero_mul, sub_zero]

end Ends
end R2E

namespace R2E
section Main
variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem zpow_mem_and_residue_eq (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers)
    (hres : C.residue ⟨f, hf⟩ ≠ 0) (n : ℤ) :
    ∃ hmem : f ^ n ∈ C.integers, C.residue ⟨f ^ n, hmem⟩ = (C.residue ⟨f, hf⟩) ^ n := by
  obtain ⟨U, hU⟩ := isUnit_of_residue_ne_zero C hres
  let Uf : Fˣ := Units.map (C.integers.subtype : C.integers →* F) U
  have hUf : (Uf : F) = f := by
    show ((U : C.integers) : F) = f
    rw [hU]
  have hval : ((U ^ n : C.integersˣ) : C.integers).1 = f ^ n := by
    have : ((Units.map (C.integers.subtype : C.integers →* F) (U ^ n) : Fˣ) : F) = (Uf ^ n : Fˣ) := by
      rw [map_zpow]
    rw [Units.coe_map, Units.val_zpow_eq_zpow_val, hUf] at this
    exact this
  refine ⟨hval ▸ ((U ^ n : C.integersˣ) : C.integers).2, ?_⟩
  have hsub : (⟨f ^ n, hval ▸ ((U ^ n : C.integersˣ) : C.integers).2⟩ : C.integers) = ((U ^ n : C.integersˣ) : C.integers) :=
    Subtype.ext hval.symm
  rw [hsub]
  have : (Units.map (C.residue : C.integers →* Fbar) (U ^ n) : Fbar) = ((Units.map (C.residue : C.integers →* Fbar) U) ^ n : Fbarˣ) := by
    rw [map_zpow]
  rw [Units.coe_map, Units.val_zpow_eq_zpow_val, Units.coe_map] at this
  rw [MonoidHom.coe_coe] at this
  rw [this]
  congr 1
  show C.residue (U : C.integers) = C.residue ⟨f, hf⟩
  rw [hU]

theorem finite_ord_ne_zero [HasPrincipalDivisors L F] (S : Set (Place L F)) (f : F) (hf : f ≠ 0) :
    {P : Place L F | P ∈ S ∧ P.ord f ≠ 0}.Finite := by
  obtain ⟨E, hE, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (F := F) f hf
  refine (E.support.finite_toSet).subset ?_
  rintro P ⟨-, hP⟩
  simp only [Finset.mem_coe, Finsupp.mem_support_iff, hE P]
  exact hP

theorem dom_nonempty [IsAlgClosed L] (An : Annulus A F) (hmod0 : (An.modulus : L) ≠ 0) : An.dom.Nonempty := by
  set μ : A := An.modulus with hμ
  have hμm : μ ∈ maximalIdeal A := An.modulus_mem
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (μ : L) (n := 2) two_pos
  have hrA : r ∈ A := by
    rw [← A.valuation_le_one_iff]
    by_contra h
    have h' : 1 < A.valuation r := not_le.mp h
    have h2 : 1 < A.valuation r ^ 2 := one_lt_pow₀ h' two_ne_zero
    rw [← map_pow, hr] at h2
    exact absurd (A.valuation_le_one μ) (not_le.mpr h2)
  have hr' : (⟨r, hrA⟩ : A) ^ 2 = μ := Subtype.ext (by simpa using hr)
  have hrm : (⟨r, hrA⟩ : A) ∈ maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hμm ⊢
    intro hu; exact hμm (hr' ▸ hu.pow 2)
  have hr0 : r ≠ 0 := by rintro rfl; apply hmod0; rw [← hr]; simp
  obtain ⟨Q, ⟨hQ, -⟩, -⟩ := An.existsUnique_evalAt_eq ⟨r, hrA⟩ hrm hr0
    ⟨⟨r, hrA⟩, hrm, by rw [← hμ, ← hr]; simp [pow_two]⟩
  exact ⟨Q, hQ⟩

end Main
end R2E

namespace R2E
section Induction
variable {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
variable {Fa : Type*} [Field Fa] [Algebra (ResidueField A) Fa]
variable {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

theorem aux
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (hratA : ∀ x : Place (ResidueField A) Fa, x.IsRational)
    (hratB : ∀ x : Place (ResidueField A) Fb, x.IsRational)
    (An An' : Annulus A F) (hdom : An'.dom = An.dom)
    (hparam : An'.param * An.param = algebraMap L F (An.modulus : L)) (hmod0 : (An.modulus : L) ≠ 0)
    (Ca : ComponentChart A F Fa) (xa : Place (ResidueField A) Fa)
    (hza : An.param ∈ Ca.integers) (hxa : xa.ord (Ca.residue ⟨An.param, hza⟩) = 1)
    (hsla : ∀ (f : F) (hf : f ∈ Ca.integers), Ca.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An.dom, P.ord f = 0) →
      ∀ P ∈ An.dom, ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(xa.ord (Ca.residue ⟨f, hf⟩))) ∈ A,
        IsUnit (⟨_, h⟩ : A))
    (Cb : ComponentChart A F Fb) (xb : Place (ResidueField A) Fb)
    (hzb : An'.param ∈ Cb.integers) (hxb : xb.ord (Cb.residue ⟨An'.param, hzb⟩) = 1)
    (hslb : ∀ (f : F) (hf : f ∈ Cb.integers), Cb.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An'.dom, P.ord f = 0) →
      ∀ P ∈ An'.dom, ∃ h : P.evalAt f * (P.evalAt An'.param) ^ (-(xb.ord (Cb.residue ⟨f, hf⟩))) ∈ A,
        IsUnit (⟨_, h⟩ : A)) :
    ∀ (N : ℕ) (h : F) (hh0 : h ≠ 0) (hha : h ∈ Ca.integers) (hresa : Ca.residue ⟨h, hha⟩ ≠ 0)
      (c' : L) (hc'0 : c' ≠ 0)
      (hhb : (algebraMap L F c')⁻¹ * h ∈ Cb.integers) (hresb : Cb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩ ≠ 0)
      (D : Divisor L F) (hDsupp : ∀ P ∈ D.support, P ∈ An.dom) (hD : ∀ P ∈ An.dom, D P = P.ord h),
      D.support.card = N →
      ∃ hu : c'⁻¹ * (An.modulus : L) ^ (xa.ord (Ca.residue ⟨h, hha⟩) - (D.sum fun _ k => k)) *
          (D.prod fun P k => (-(P.evalAt An.param)) ^ k) ∈ A,
        IsUnit (⟨_, hu⟩ : A) ∧
        IsLocalRing.residue A ⟨_, hu⟩ *
            xa.evalAt (Ca.residue ⟨h, hha⟩ * (Ca.residue ⟨An.param, hza⟩) ^ (-(xa.ord (Ca.residue ⟨h, hha⟩)))) =
          xb.evalAt (Cb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩ *
            (Cb.residue ⟨An'.param, hzb⟩) ^ (-(xb.ord (Cb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩)))) := by
  classical

  have hne : An.dom.Nonempty := dom_nonempty An hmod0
  obtain ⟨Q₀, hQ₀⟩ := hne
  have hz0 : An.param ≠ 0 := param_ne_zero An hQ₀
  have hp' : An'.param = algebraMap L F (An.modulus : L) * An.param⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ hz0).mpr hparam
  have hza_ne : Ca.residue ⟨An.param, hza⟩ ≠ 0 := by intro h0; rw [h0] at hxa; simp at hxa

  obtain ⟨hzb', hxb', hslb'⟩ := transfer_end Cb.residue xb hdom hp' ⟨hzb, hxb, hslb⟩
  have hzbsub : (⟨An'.param, hzb⟩ : Cb.integers) = ⟨algebraMap L F (An.modulus : L) * An.param⁻¹, hzb'⟩ :=
    Subtype.ext hp'
  intro N
  induction N with
  | zero =>
    intro h hh0 hha hresa c' hc'0 hhb hresb D hDsupp hD hcard
    have hD0 : D = 0 := Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp hcard)
    have hzero : ∀ P ∈ An.dom, P.ord h = 0 := fun P hP => by rw [← hD P hP, hD0]; rfl
    obtain ⟨hordb, hu', hunit', hlam⟩ :=
      AlgebraicCurve.Annulus.ord_residue_eq_neg_and_evalAt_residue_mul_zpow_eq_of_forall_ord_eq_zero_of_rankOne
        hrk An hmod0 (finite_ord_ne_zero An.dom) (rp Ca) xa hza hxa hsla (rp Cb) xb hzb' hxb' hslb'
        (hratA xa) (hratB xb) ⟨Q₀, hQ₀⟩ h hh0 hha hresa c' hc'0 hhb hresb hzero

    obtain ⟨T, hT⟩ := hunit'
    have hTval : ((T : A) : L) = c' * (An.modulus : L) ^ (-(xa.ord (Ca.residue ⟨h, hha⟩))) := by
      rw [hT]
    have huval : c'⁻¹ * (An.modulus : L) ^ (xa.ord (Ca.residue ⟨h, hha⟩) - ((0 : Divisor L F).sum fun _ k => k)) *
        ((0 : Divisor L F).prod fun P k => (-(P.evalAt An.param)) ^ k) = (((T⁻¹ : Aˣ) : A) : L) := by
      rw [Finsupp.sum_zero_index, Finsupp.prod_zero_index, sub_zero, mul_one]
      have : (((T⁻¹ : Aˣ) : A) : L) = (((T : A) : L))⁻¹ := by
        have h1 : ((T : A) : L) * (((T⁻¹ : Aˣ) : A) : L) = 1 := by
          have := congrArg Subtype.val T.mul_inv
          push_cast at this
          exact this
        exact eq_inv_of_mul_eq_one_right h1
      rw [this, hTval, mul_inv, ← zpow_neg, neg_neg]
    subst hD0
    refine ⟨huval ▸ ((T⁻¹ : Aˣ) : A).2, ?_, ?_⟩
    · have : (⟨_, huval ▸ ((T⁻¹ : Aˣ) : A).2⟩ : A) = ((T⁻¹ : Aˣ) : A) := Subtype.ext huval
      rw [this]; exact Units.isUnit _
    · have hsubT : (⟨_, huval ▸ ((T⁻¹ : Aˣ) : A).2⟩ : A) = ((T⁻¹ : Aˣ) : A) := Subtype.ext huval
      rw [hsubT]

      have hresT : IsLocalRing.residue A ((T⁻¹ : Aˣ) : A) * IsLocalRing.residue A (T : A) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      have hTsub : (⟨_, hu'⟩ : A) = (T : A) := hT.symm ▸ rfl
      rw [show xa.evalAt ((rp Ca).residue ⟨h, hha⟩ * (rp Ca).residue ⟨An.param, hza⟩ ^ (-(xa.ord ((rp Ca).residue ⟨h, hha⟩)))) =
        xa.evalAt (Ca.residue ⟨h, hha⟩ * Ca.residue ⟨An.param, hza⟩ ^ (-(xa.ord (Ca.residue ⟨h, hha⟩)))) from rfl] at hlam
      rw [hlam, hTsub]
      rw [mul_comm, mul_assoc, mul_comm (IsLocalRing.residue A ↑T), hresT, mul_one]

      show xb.evalAt (Cb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩ *
          Cb.residue ⟨algebraMap L F (An.modulus : L) * An.param⁻¹, hzb'⟩ ^ (xa.ord (Ca.residue ⟨h, hha⟩))) = _
      rw [← hzbsub]
      have hordb' : xb.ord (Cb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩) = -(xa.ord (Ca.residue ⟨h, hha⟩)) := hordb
      rw [hordb', neg_neg]
  | succ N ih =>
    intro h hh0 hha hresa c' hc'0 hhb hresb D hDsupp hD hcard

    obtain ⟨P₀, hP₀D⟩ : D.support.Nonempty := Finset.card_pos.mp (by omega)
    have hP₀ : P₀ ∈ An.dom := hDsupp P₀ hP₀D
    set k : ℤ := D P₀ with hk
    set c₀ : L := P₀.evalAt An.param with hc₀
    obtain ⟨hrat₀, hzP₀, ⟨hA₀, hmax₀⟩, hc₀ne, m₀, hm₀, hmod₀⟩ := An.mem_dom P₀ hP₀

    obtain ⟨hya, hresya⟩ := sub_mem_and_residue_eq An Ca hza hP₀
    obtain ⟨hyb, hresyb⟩ := one_sub_mem_and_residue_eq_one An An' hparam Cb xb hzb hxb hP₀
    have hresya_ne : Ca.residue ⟨An.param - algebraMap L F c₀, hya⟩ ≠ 0 := by rw [hresya]; exact hza_ne
    have hresyb_ne : Cb.residue ⟨1 - algebraMap L F c₀⁻¹ * An.param, hyb⟩ ≠ 0 := by rw [hresyb]; exact one_ne_zero
    obtain ⟨hyka, hresyka⟩ := zpow_mem_and_residue_eq Ca hya hresya_ne (-k)
    obtain ⟨hykb, hresykb⟩ := zpow_mem_and_residue_eq Cb hyb hresyb_ne (-k)
    rw [hresya] at hresyka
    rw [hresyb, one_zpow] at hresykb
    have hy0 : An.param - algebraMap L F c₀ ≠ 0 := by
      intro h0
      have := An.ord_param_sub P₀ hP₀
      rw [← hc₀, h0] at this
      simp at this
    have hac₀ : algebraMap L F c₀ ≠ 0 := (map_ne_zero _).mpr hc₀ne
    have hyrel : (1 - algebraMap L F c₀⁻¹ * An.param) = (An.param - algebraMap L F c₀) * algebraMap L F (-c₀)⁻¹ := by
      simp only [map_inv₀, map_neg]
      rw [← neg_inv, mul_neg, sub_mul, mul_inv_cancel₀ hac₀]
      ring

    have hordy : ∀ R ∈ An.dom, R.ord (An.param - algebraMap L F c₀) = if R = P₀ then 1 else 0 := by
      intro R hR
      by_cases hRP : R = P₀
      · subst hRP; rw [if_pos rfl]; exact An.ord_param_sub _ hP₀
      · rw [if_neg hRP]
        obtain ⟨hratR, hzR, -, -, -⟩ := An.mem_dom R hR
        have hmemR : An.param - algebraMap L F c₀ ∈ R.toValuationSubring := sub_mem hzR (R.algebraMap_mem' c₀)
        apply ord_eq_zero_of_evalAt_ne_zero R hratR hmemR
        intro hev
        apply hRP

        have hval : R.evalAt An.param = c₀ := by
          have h1 : R.evalAt ((An.param - algebraMap L F c₀) + algebraMap L F c₀) = R.evalAt An.param := by
            rw [sub_add_cancel]

          have hadd : algebraMap L R.ResidueField (R.evalAt ((An.param - algebraMap L F c₀) + algebraMap L F c₀)) =
              algebraMap L R.ResidueField (R.evalAt (An.param - algebraMap L F c₀) + c₀) := by
            rw [R.algebraMap_evalAt hratR (add_mem hmemR (R.algebraMap_mem' c₀)), map_add,
              R.algebraMap_evalAt hratR hmemR]
            have : (⟨(An.param - algebraMap L F c₀) + algebraMap L F c₀, add_mem hmemR (R.algebraMap_mem' c₀)⟩ : R.toValuationSubring) =
                ⟨An.param - algebraMap L F c₀, hmemR⟩ + ⟨algebraMap L F c₀, R.algebraMap_mem' c₀⟩ := rfl
            rw [this, map_add]
            congr 1
            all_goals (rw [← R.algebraMap_evalAt hratR (R.algebraMap_mem' c₀), R.evalAt_algebraMap_eq])
          have := (algebraMap L R.ResidueField).injective hadd
          rw [h1, hev, zero_add] at this
          exact this
        obtain ⟨R', -, huniq⟩ := An.existsUnique_evalAt_eq ⟨c₀, hA₀⟩ hmax₀ hc₀ne ⟨m₀, hm₀, hmod₀⟩
        rw [huniq R ⟨hR, hval⟩, huniq P₀ ⟨hP₀, rfl⟩]

    set h₁ : F := h * (An.param - algebraMap L F c₀) ^ (-k) with hh₁
    have hh₁0 : h₁ ≠ 0 := mul_ne_zero hh0 (zpow_ne_zero _ hy0)
    have hha₁ : h₁ ∈ Ca.integers := mul_mem hha hyka
    have hres₁a : Ca.residue ⟨h₁, hha₁⟩ = Ca.residue ⟨h, hha⟩ * (Ca.residue ⟨An.param, hza⟩) ^ (-k) := by
      rw [show (⟨h₁, hha₁⟩ : Ca.integers) = ⟨h, hha⟩ * ⟨_, hyka⟩ from rfl, map_mul, hresyka]
    have hresa₁ : Ca.residue ⟨h₁, hha₁⟩ ≠ 0 := by
      rw [hres₁a]; exact mul_ne_zero hresa (zpow_ne_zero _ hza_ne)
    have hord₁a : xa.ord (Ca.residue ⟨h₁, hha₁⟩) = xa.ord (Ca.residue ⟨h, hha⟩) - k := by
      rw [hres₁a, xa.ord_mul hresa (zpow_ne_zero _ hza_ne), xa.ord_zpow, hxa]; ring
    set d : L := c'⁻¹ * (-c₀) ^ k with hd
    have hnc₀ : (-c₀) ≠ 0 := neg_ne_zero.mpr hc₀ne
    have hd0 : d ≠ 0 := mul_ne_zero (inv_ne_zero hc'0) (zpow_ne_zero _ hnc₀)
    have hc'₁0 : d⁻¹ ≠ 0 := inv_ne_zero hd0
    have hprod₁ : (algebraMap L F d⁻¹)⁻¹ * h₁ = ((algebraMap L F c')⁻¹ * h) * (1 - algebraMap L F c₀⁻¹ * An.param) ^ (-k) := by
      rw [hyrel, mul_zpow, ← map_zpow₀, inv_zpow', neg_neg, map_inv₀, inv_inv, hd, hh₁, map_mul, map_inv₀, map_zpow₀]
      ring
    have hhb₁ : (algebraMap L F d⁻¹)⁻¹ * h₁ ∈ Cb.integers := by rw [hprod₁]; exact mul_mem hhb hykb
    have hres₁b : Cb.residue ⟨(algebraMap L F d⁻¹)⁻¹ * h₁, hhb₁⟩ = Cb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩ := by
      have : (⟨(algebraMap L F d⁻¹)⁻¹ * h₁, hhb₁⟩ : Cb.integers) = ⟨(algebraMap L F c')⁻¹ * h, hhb⟩ * ⟨_, hykb⟩ :=
        Subtype.ext hprod₁
      rw [this, map_mul, hresykb, mul_one]
    have hresb₁ : Cb.residue ⟨(algebraMap L F d⁻¹)⁻¹ * h₁, hhb₁⟩ ≠ 0 := by rw [hres₁b]; exact hresb

    set D₁ : Divisor L F := D.erase P₀ with hD₁
    have hD₁supp : ∀ P ∈ D₁.support, P ∈ An.dom := by
      intro P hP; rw [hD₁, Finsupp.support_erase] at hP; exact hDsupp P (Finset.mem_of_mem_erase hP)
    have hD₁ord : ∀ P ∈ An.dom, D₁ P = P.ord h₁ := by
      intro P hP
      rw [hh₁, P.ord_mul hh0 (zpow_ne_zero _ hy0), P.ord_zpow, hordy P hP, ← hD P hP, hD₁]
      by_cases hPP : P = P₀
      · subst hPP; rw [Finsupp.erase_same, if_pos rfl, hk]; ring
      · rw [Finsupp.erase_ne hPP, if_neg hPP]; ring
    have hcard₁ : D₁.support.card = N := by
      rw [hD₁, Finsupp.support_erase, Finset.card_erase_of_mem hP₀D, hcard]; rfl

    obtain ⟨hu₁, hunit₁, hlam1⟩ := ih h₁ hh₁0 hha₁ hresa₁ d⁻¹ hc'₁0 hhb₁ hresb₁ D₁ hD₁supp hD₁ord hcard₁

    have hmass : (D.sum fun _ k => k) = k + (D₁.sum fun _ k => k) := by
      show (∑ P ∈ D.support, D P) = k + ∑ P ∈ D₁.support, D₁ P
      rw [hD₁, Finsupp.support_erase, ← Finset.add_sum_erase _ _ hP₀D]
      congr 1
      exact Finset.sum_congr rfl (fun P hP => by rw [Finsupp.erase_ne (Finset.ne_of_mem_erase hP)])
    have hprodD : (D.prod fun P k => (-(P.evalAt An.param)) ^ k) =
        (-c₀) ^ k * (D₁.prod fun P k => (-(P.evalAt An.param)) ^ k) := by
      show (∏ P ∈ D.support, (-(P.evalAt An.param)) ^ (D P)) = (-c₀) ^ k * ∏ P ∈ D₁.support, (-(P.evalAt An.param)) ^ (D₁ P)
      rw [hD₁, Finsupp.support_erase, ← Finset.mul_prod_erase _ _ hP₀D]
      congr 1
      exact Finset.prod_congr rfl (fun P hP => by rw [Finsupp.erase_ne (Finset.ne_of_mem_erase hP)])
    have hueq : c'⁻¹ * (An.modulus : L) ^ (xa.ord (Ca.residue ⟨h, hha⟩) - (D.sum fun _ k => k)) *
          (D.prod fun P k => (-(P.evalAt An.param)) ^ k) =
        (d⁻¹)⁻¹ * (An.modulus : L) ^ (xa.ord (Ca.residue ⟨h₁, hha₁⟩) - (D₁.sum fun _ k => k)) *
          (D₁.prod fun P k => (-(P.evalAt An.param)) ^ k) := by
      rw [inv_inv, hd, hord₁a, hmass, hprodD, show xa.ord (Ca.residue ⟨h, hha⟩) - k - (D₁.sum fun _ k => k) =
        xa.ord (Ca.residue ⟨h, hha⟩) - (k + D₁.sum fun _ k => k) by ring]
      ring
    refine ⟨hueq ▸ hu₁, ?_, ?_⟩
    · have : (⟨_, hueq ▸ hu₁⟩ : A) = ⟨_, hu₁⟩ := Subtype.ext hueq
      rw [this]; exact hunit₁
    · have hsub : (⟨_, hueq ▸ hu₁⟩ : A) = ⟨_, hu₁⟩ := Subtype.ext hueq
      rw [hsub]

      have hlama : xa.evalAt (Ca.residue ⟨h₁, hha₁⟩ * (Ca.residue ⟨An.param, hza⟩) ^ (-(xa.ord (Ca.residue ⟨h₁, hha₁⟩)))) =
          xa.evalAt (Ca.residue ⟨h, hha⟩ * (Ca.residue ⟨An.param, hza⟩) ^ (-(xa.ord (Ca.residue ⟨h, hha⟩)))) := by
        rw [hord₁a, hres₁a, mul_assoc, ← zpow_add₀ hza_ne]
        congr 2
        ring

      have hlamb : xb.evalAt (Cb.residue ⟨(algebraMap L F d⁻¹)⁻¹ * h₁, hhb₁⟩ *
            (Cb.residue ⟨An'.param, hzb⟩) ^ (-(xb.ord (Cb.residue ⟨(algebraMap L F d⁻¹)⁻¹ * h₁, hhb₁⟩)))) =
          xb.evalAt (Cb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩ *
            (Cb.residue ⟨An'.param, hzb⟩) ^ (-(xb.ord (Cb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩)))) := by
        rw [hres₁b]
      rw [← hlama, ← hlamb]
      exact hlam1

end Induction
end R2E

open R2E in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    {Fa : Type*} [Field Fa] [Algebra (IsLocalRing.ResidueField A) Fa]
    {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (hratA : ∀ x : Place (IsLocalRing.ResidueField A) Fa, x.IsRational)
    (hratB : ∀ x : Place (IsLocalRing.ResidueField A) Fb, x.IsRational)
    (An An' : Annulus A F) (hdom : An'.dom = An.dom)
    (hparam : An'.param * An.param = algebraMap L F (An.modulus : L)) (hmod0 : (An.modulus : L) ≠ 0)
    (Ca : ComponentChart A F Fa) (xa : Place (IsLocalRing.ResidueField A) Fa) (hatt : An.IsAttached Ca xa)
    (Cb : ComponentChart A F Fb) (xb : Place (IsLocalRing.ResidueField A) Fb) (hatt' : An'.IsAttached Cb xb)
    (h : F) (hh0 : h ≠ 0) (hha : h ∈ Ca.integers) (hresa : Ca.residue ⟨h, hha⟩ ≠ 0)
    (c' : L) (hc'0 : c' ≠ 0)
    (hhb : (algebraMap L F c')⁻¹ * h ∈ Cb.integers) (hresb : Cb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩ ≠ 0)
    (D : Divisor L F) (hDsupp : ∀ P ∈ D.support, P ∈ An.dom) (hD : ∀ P ∈ An.dom, D P = P.ord h)
    :
    ∃ hu : c'⁻¹ * (An.modulus : L) ^ (xa.ord (Ca.residue ⟨h, hha⟩) - (D.sum fun _ k => k)) *
        (D.prod fun P k => (-(P.evalAt An.param)) ^ k) ∈ A,
      IsUnit (⟨_, hu⟩ : A) ∧
      IsLocalRing.residue A ⟨_, hu⟩ *
          xa.evalAt (Ca.residue ⟨h, hha⟩ * (Ca.residue ⟨An.param, hatt.2.choose⟩) ^ (-(xa.ord (Ca.residue ⟨h, hha⟩)))) =
        xb.evalAt (Cb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩ *
          (Cb.residue ⟨An'.param, hatt'.2.choose⟩) ^ (-(xb.ord (Cb.residue ⟨(algebraMap L F c')⁻¹ * h, hhb⟩)))) := by
  classical
  obtain ⟨-, hza, hxa, hsla⟩ := hatt
  obtain ⟨-, hzb, hxb, hslb⟩ := hatt'
  exact R2E.aux hrk hratA hratB An An' hdom hparam hmod0 Ca xa hza hxa hsla Cb xb hzb hxb hslb
    D.support.card h hh0 hha hresa c' hc'0 hhb hresb D hDsupp hD rfl

end S_AlgebraicCurve_Annulus_exists_isUnit_residue_mul_evalAt_eq_evalAt_of_isAttached_of_isAttached
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_exists_isUnit_residue_mul_evalAt_eq_evalAt_of_isAttached_of_isAttached (solution)
