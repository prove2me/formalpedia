-- Prove2me | solution 1 for AlgebraicCurve.SemistableCovering.ord_residue_smul_ge_and_evalAt_mul_eq_of_forall_smul_mem_integers_of_width_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/83c8544f-33b9-5bf2-8cdd-8d4cd80cd780

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_Annulus_ord_residue_nonneg_and_evalAt_residue_eq_of_isAttached_of_isAttached
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableCovering_ord_residue_smul_ge_and_evalAt_mul_eq_of_forall_smul_mem_integers_of_width_one
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"

set_option autoImplicit false

p2m_open "AlgebraicCurve~RegularProlongation P2MW.S_AlgebraicCurve_SemistableCovering_ord_residue_smul_ge_and_evalAt_mul_eq_of_forall_smul_mem_integers_of_width_one.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus ConstantReduction ConstantReduction.ord_algebraMap Place Place.ord_zero Divisor HasPrincipalDivisors HasPrincipalDivisors.exists_divisor genusFF IsCurveOver Annulus.ord_residue_nonneg_and_evalAt_residue_eq_of_isAttached_of_isAttached"
p2m_open "AlgebraicCurve~RegularProlongation"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg ord ord_zero ord_one ord_mul ord_inv ord_coe_unit exists_unit_mul_zpow algebraMap_mem' toValuationSubring IsRational algebraMap_residueField_injective residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem _root_.AlgebraicCurve.Place.ord_zpow' (v : Place K F) {f : F} (hf : f ≠ 0) (n : ℤ) : v.ord (f ^ n) = n * v.ord f := by
  have hpow : ∀ k : ℕ, v.ord (f ^ k) = (k : ℤ) * v.ord f := by
    intro k
    induction k with
    | zero => rw [pow_zero, Nat.cast_zero, zero_mul]; exact v.ord_one
    | succ k ih => rw [pow_succ, v.ord_mul (pow_ne_zero _ hf) hf, ih]; push_cast; ring
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · rw [zpow_natCast, hpow]
  · rw [zpow_neg, zpow_natCast, v.ord_inv, hpow]; ring

p2m_export "AlgebraicCurve.Place" "ord_zpow'"

private theorem _root_.AlgebraicCurve.Place.mem_valuationSubring_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0)
    (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨w, hw⟩ := v.exists_unit_mul_zpow hf hϖ
  rw [hw, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm, zpow_natCast]
  exact mul_mem (w : v.toValuationSubring).2 (pow_mem (ϖ : v.toValuationSubring).2 _)

p2m_export "AlgebraicCurve.Place" "mem_valuationSubring_of_ord_nonneg"

private theorem _root_.AlgebraicCurve.Place.evalAt_zero' (v : Place K F) : v.evalAt (0 : F) = 0 := by
  rw [v.evalAt_of_mem (zero_mem _)]
  have : (⟨(0 : F), zero_mem _⟩ : v.toValuationSubring) = 0 := rfl
  rw [this, map_zero, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

p2m_export "AlgebraicCurve.Place" "evalAt_zero'"

private theorem _root_.AlgebraicCurve.Place.evalAt_mul_of_mem' (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_mul, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg, v.algebraMap_evalAt hv (mul_mem hf hg),
    ← map_mul]
  rfl

p2m_export "AlgebraicCurve.Place" "evalAt_mul_of_mem'"

private theorem _root_.AlgebraicCurve.Place.evalAt_algebraMap' (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have : IsLocalRing.residue v.toValuationSubring ⟨algebraMap K F a, v.algebraMap_mem' a⟩ =
      algebraMap K v.ResidueField a := rfl
  rw [this, v.residueInv_algebraMap]

p2m_export "AlgebraicCurve.Place" "evalAt_algebraMap'"

private theorem _root_.AlgebraicCurve.Place.ord_zpow_eq_zero_of_evalAt_ne_zero (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : v.evalAt f ≠ 0) (n : ℤ) : v.ord (f ^ n) = 0 := by
  have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ ≠ 0 := by
    intro h0
    apply h
    rw [v.evalAt_of_mem hf, h0, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]
  have hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    by_contra hnu
    apply hres
    rwa [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  obtain ⟨w, hw⟩ := hu
  have h0 : v.ord f = 0 := by have := v.ord_coe_unit w; rwa [hw] at this
  have hf0 : f ≠ 0 := by rintro rfl; apply hres; have : (⟨(0:F), hf⟩ : v.toValuationSubring) = 0 := rfl; rw [this, map_zero]
  rw [v.ord_zpow' hf0, h0, mul_zero]

p2m_export "AlgebraicCurve.Place" "ord_zpow_eq_zero_of_evalAt_ne_zero"
end Place

namespace ComponentChart
p2m_export "AlgebraicCurve.ComponentChart" "integers algebraMap_mem_iff placeMap residue nodes residue_algebraMap ker_residue mapDomain_placeMap dom"
p2m_open "AlgebraicCurve.ComponentChart"

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]

private theorem _root_.AlgebraicCurve.ComponentChart.zpow_mem_and_residue_zpow (C : ComponentChart A F Fbar) {x : F} (hx : x ∈ C.integers)
    (hres : C.residue ⟨x, hx⟩ ≠ 0) (n : ℤ) :
    ∃ hn : x ^ n ∈ C.integers, C.residue ⟨x ^ n, hn⟩ = (C.residue ⟨x, hx⟩) ^ n := by
  have hunit : IsUnit (⟨x, hx⟩ : C.integers) := by
    by_contra hnu
    apply hres
    have hmax : (⟨x, hx⟩ : C.integers) ∈ IsLocalRing.maximalIdeal C.integers :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    rw [← C.ker_residue] at hmax
    exact hmax
  obtain ⟨U, hU⟩ := hunit

  have hval : ∀ n : ℤ, (((U ^ n : C.integersˣ) : C.integers) : F) = x ^ n := by
    intro n
    have h1 : (((U ^ n : C.integersˣ) : C.integers) : F) =
        ((Units.map (C.integers.subtype : C.integers →* F) (U ^ n) : Fˣ) : F) := rfl
    rw [h1, map_zpow, Units.val_zpow_eq_zpow_val]
    congr 1
    show ((U : C.integers) : F) = x
    rw [hU]
  have hmem : x ^ n ∈ C.integers := by rw [← hval n]; exact ((U ^ n : C.integersˣ) : C.integers).2
  refine ⟨hmem, ?_⟩
  have hsub : (⟨x ^ n, hmem⟩ : C.integers) = ((U ^ n : C.integersˣ) : C.integers) := Subtype.ext (hval n).symm
  rw [hsub, ← hU]
  have : C.residue ((U ^ n : C.integersˣ) : C.integers) = ((Units.map (C.residue : C.integers →* Fbar) (U ^ n) : Fbarˣ) : Fbar) := rfl
  rw [this, map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

p2m_export "AlgebraicCurve.ComponentChart" "zpow_mem_and_residue_zpow"
end ComponentChart

end AlgebraicCurve

open Classical in

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : Fin m → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hw1 : ∀ e, w e = 1)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + n = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + m + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (φ : Fin n → ℤ)
    (D : Divisor L F) (hD : ∀ P ∈ D.support, ∃ i, P ∈ (C i).dom)
    :
    let Dbar : ∀ i, Divisor (IsLocalRing.ResidueField A) (Fbar i) := fun i =>
      Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom)
    let k : Fin m → ℤ := fun e => φ (tgt e) - φ (src e)
    let zs : ∀ e, Fbar (src e) := fun e => (C (src e)).residue ⟨(An e).param, (hatt e).1.2.choose⟩
    let zt : ∀ e, Fbar (tgt e) := fun e => (C (tgt e)).residue ⟨(An' e).param, (hatt e).2.2.choose⟩
    let ubar : Fin m → IsLocalRing.ResidueField A := fun e => IsLocalRing.residue A ((hw e).choose : A)
    let wt : Fin n → L := fun i => (((π : A) : L) ^ (φ i))⁻¹

    (∀ (g : F) (hg : ∀ i, wt i • g ∈ (C i).integers), g ≠ 0 → (∀ P, 0 ≤ P.ord g + D P) →
      (∀ i, ∀ Q, Q ∉ (C i).nodes → (C i).residue ⟨wt i • g, hg i⟩ ≠ 0 →
        0 ≤ Q.ord ((C i).residue ⟨wt i • g, hg i⟩) + Dbar i Q) ∧
      (∀ e, (C (src e)).residue ⟨wt (src e) • g, hg (src e)⟩ ≠ 0 →
        k e ≤ (xs e).ord ((C (src e)).residue ⟨wt (src e) • g, hg (src e)⟩)) ∧
      (∀ e, (C (tgt e)).residue ⟨wt (tgt e) • g, hg (tgt e)⟩ ≠ 0 →
        -k e ≤ (xt e).ord ((C (tgt e)).residue ⟨wt (tgt e) • g, hg (tgt e)⟩)) ∧
      ∀ e, (xs e).evalAt ((C (src e)).residue ⟨wt (src e) • g, hg (src e)⟩ * zs e ^ (-k e)) * ubar e ^ (k e) =
        (xt e).evalAt ((C (tgt e)).residue ⟨wt (tgt e) • g, hg (tgt e)⟩ * zt e ^ (k e)))
     := by
  intro Dbar k zs zt ubar wt g hg hg0 hgD
  classical
  have _ := hrk; have _ := hgenus; have _ := hdisc; have _ := hratF; have _ := hnodes; have _ := hπ
  have hπL : ((π : A) : L) ≠ 0 := fun h0 => hπ0 (Subtype.ext h0)
  have hwt0 : ∀ i, wt i ≠ 0 := fun i => inv_ne_zero (zpow_ne_zero _ hπL)
  have hordD : ∀ P : Place L F, -D P ≤ P.ord g := fun P => by linarith [hgD P]

  have hDann : ∀ e, ∀ P ∈ (An e).dom, D P = 0 := by
    intro e P hP
    by_contra hne
    obtain ⟨i, hi⟩ := hD P (Finsupp.mem_support_iff.mpr hne)
    rcases hcover P with ⟨j, -, -, hnot⟩ | ⟨e', -, -, hnot⟩
    · exact hnot e hP
    · exact hnot i hi

  have hA : ∀ i, ∀ Q, Q ∉ (C i).nodes → (C i).residue ⟨wt i • g, hg i⟩ ≠ 0 →
      0 ≤ Q.ord ((C i).residue ⟨wt i • g, hg i⟩) + Dbar i Q := by
    intro i y hy hres
    obtain ⟨Dg, hDg, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) g hg0
    have hordw : ∀ P : Place L F, P.ord (wt i • g) = P.ord g := fun P => by
      rw [Algebra.smul_def, P.ord_mul ((map_ne_zero _).mpr (hwt0 i)) hg0, ConstantReduction.ord_algebraMap P (hwt0 i),
        zero_add]
    have hmap := (C i).mapDomain_placeMap ⟨wt i • g, hg i⟩ hres (Dg.filter fun P => P ∈ (C i).dom)
      (fun P hP => by rw [Finsupp.filter_apply, if_pos hP, hDg, hordw]) (fun P hP => by rw [Finsupp.filter_apply, if_neg hP])
      y hy
    have hnn : ∀ v : Place L F,
        0 ≤ ((D.filter fun P => P ∈ (C i).dom) + Dg.filter fun P => P ∈ (C i).dom) v := by
      intro v
      rw [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.filter_apply]
      by_cases hv : v ∈ (C i).dom
      · rw [if_pos hv, if_pos hv, hDg]; linarith [hordD v]
      · rw [if_neg hv, if_neg hv, add_zero]
    have hmapnn : 0 ≤ Finsupp.mapDomain (C i).placeMap
        ((D.filter fun P => P ∈ (C i).dom) + Dg.filter fun P => P ∈ (C i).dom) y := by
      simp only [Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.single_apply]
      refine Finset.sum_nonneg fun v _ => ?_
      split_ifs
      · exact hnn v
      · exact le_rfl
    rw [Finsupp.mapDomain_add, Finsupp.add_apply, hmap] at hmapnn
    show 0 ≤ y.ord ((C i).residue ⟨wt i • g, hg i⟩) + Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom) y
    linarith

  have hAnn : ∀ e,
      ((C (src e)).residue ⟨wt (src e) • g, hg (src e)⟩ ≠ 0 →
        k e ≤ (xs e).ord ((C (src e)).residue ⟨wt (src e) • g, hg (src e)⟩)) ∧
      ((C (tgt e)).residue ⟨wt (tgt e) • g, hg (tgt e)⟩ ≠ 0 →
        -k e ≤ (xt e).ord ((C (tgt e)).residue ⟨wt (tgt e) • g, hg (tgt e)⟩)) ∧
      (xs e).evalAt ((C (src e)).residue ⟨wt (src e) • g, hg (src e)⟩ * zs e ^ (-k e)) * ubar e ^ (k e) =
        (xt e).evalAt ((C (tgt e)).residue ⟨wt (tgt e) • g, hg (tgt e)⟩ * zt e ^ (k e)) := by
    intro e

    have hzs_mem : (An e).param ∈ (C (src e)).integers := (hatt e).1.2.choose
    have hzs_ord : (xs e).ord ((C (src e)).residue ⟨(An e).param, hzs_mem⟩) = 1 := (hatt e).1.2.choose_spec.1
    have hzt_mem : (An' e).param ∈ (C (tgt e)).integers := (hatt e).2.2.choose
    have hzt_ord : (xt e).ord ((C (tgt e)).residue ⟨(An' e).param, hzt_mem⟩) = 1 := (hatt e).2.2.choose_spec.1
    have hzs_def : zs e = (C (src e)).residue ⟨(An e).param, hzs_mem⟩ := rfl
    have hzt_def : zt e = (C (tgt e)).residue ⟨(An' e).param, hzt_mem⟩ := rfl
    have hzs0 : (C (src e)).residue ⟨(An e).param, hzs_mem⟩ ≠ 0 := by
      intro h0; rw [h0, Place.ord_zero] at hzs_ord; exact zero_ne_one hzs_ord
    have hzt0 : (C (tgt e)).residue ⟨(An' e).param, hzt_mem⟩ ≠ 0 := by
      intro h0; rw [h0, Place.ord_zero] at hzt_ord; exact zero_ne_one hzt_ord
    have hπw : (((π : A) : L)) ^ w e = ((π : A) : L) := by rw [hw1 e, pow_one]
    have hmodL : (((An e).modulus : A) : L) = (((hw e).choose : A) : L) * ((π : A) : L) := by
      have h1 := congrArg (fun a : A => (a : L)) (hw e).choose_spec
      push_cast at h1
      rw [hπw] at h1
      exact h1
    have hubar_def : ubar e = IsLocalRing.residue A ((hw e).choose : A) := rfl

    have hcoeL : ∀ N : ℤ, ((((hw e).choose ^ N : Aˣ) : A) : L) = ((((hw e).choose : A) : L)) ^ N := by
      intro N
      have : ((((hw e).choose ^ N : Aˣ) : A) : L) = ((Units.map (A.subtype : A →* L) ((hw e).choose ^ N) : Lˣ) : L) := rfl
      rw [this, map_zpow, Units.val_zpow_eq_zpow_val]; rfl
    have hcoeκ : ∀ N : ℤ, IsLocalRing.residue A (((hw e).choose ^ N : Aˣ) : A) = (IsLocalRing.residue A ((hw e).choose : A)) ^ N := by
      intro N
      have : IsLocalRing.residue A (((hw e).choose ^ N : Aˣ) : A) =
          ((Units.map (IsLocalRing.residue A : A →* IsLocalRing.ResidueField A) ((hw e).choose ^ N) : (IsLocalRing.ResidueField A)ˣ) : _) := rfl
      rw [this, map_zpow, Units.val_zpow_eq_zpow_val]; rfl
    obtain ⟨hdom, -, hmod0, hzz'⟩ := hpair e
    have hz0 : (An e).param ≠ 0 := by
      intro h0; apply hmod0; have : algebraMap L F ((An e).modulus : L) = 0 := by rw [← hzz', h0, mul_zero]
      exact (map_eq_zero _).mp this
    have hz'0 : (An' e).param ≠ 0 := by
      intro h0; apply hmod0; have : algebraMap L F ((An e).modulus : L) = 0 := by rw [← hzz', h0, zero_mul]
      exact (map_eq_zero _).mp this
    have huL0 : (((hw e).choose : A) : L) ≠ 0 := fun h0 => (hw e).choose.ne_zero (Subtype.ext h0)

    obtain ⟨hzpow_s, hres_zpow_s⟩ := (C (src e)).zpow_mem_and_residue_zpow hzs_mem hzs0 (-k e)
    have hGs : (wt (src e) • g * (An e).param ^ (-k e)) ∈ (C (src e)).integers := mul_mem (hg (src e)) hzpow_s
    have hresGs : (C (src e)).residue ⟨(wt (src e) • g * (An e).param ^ (-k e)), hGs⟩ = (C (src e)).residue ⟨wt (src e) • g, hg (src e)⟩ * zs e ^ (-k e) := by
      have : (⟨(wt (src e) • g * (An e).param ^ (-k e)), hGs⟩ : (C (src e)).integers) = ⟨wt (src e) • g, hg (src e)⟩ * ⟨(An e).param ^ (-k e), hzpow_s⟩ := rfl
      rw [this, map_mul, hres_zpow_s, hzs_def]

    have hzrel : (An e).param = algebraMap L F ((((hw e).choose : A) : L) * ((π : A) : L)) * (An' e).param⁻¹ := by
      have h1 : (An' e).param * (An e).param = algebraMap L F ((((hw e).choose : A) : L) * ((π : A) : L)) := by
        rw [hzz', hmodL]
      rw [← h1, mul_comm (An' e).param (An e).param, mul_assoc, mul_inv_cancel₀ hz'0, mul_one]
    have hk_def : k e = φ (tgt e) - φ (src e) := rfl
    have hGt_eq : (wt (src e) • g * (An e).param ^ (-k e)) =
        wt (tgt e) • g * (An' e).param ^ (k e) * algebraMap L F ((((hw e).choose : A) : L) ^ (-k e)) := by
      have ha : algebraMap L F ((π : A) : L) ≠ 0 := (map_ne_zero _).mpr hπL
      have hb : algebraMap L F (((hw e).choose : A) : L) ≠ 0 := (map_ne_zero _).mpr huL0
      have e1 : wt (src e) • g = (algebraMap L F ((π : A) : L)) ^ (-(φ (src e))) * g := by
        show ((((π : A) : L)) ^ (φ (src e)))⁻¹ • g = _
        rw [Algebra.smul_def, map_inv₀, map_zpow₀, ← zpow_neg]
      have e2 : wt (tgt e) • g = (algebraMap L F ((π : A) : L)) ^ (-(φ (tgt e))) * g := by
        show ((((π : A) : L)) ^ (φ (tgt e)))⁻¹ • g = _
        rw [Algebra.smul_def, map_inv₀, map_zpow₀, ← zpow_neg]
      have e3 : (An e).param ^ (-k e) = (algebraMap L F (((hw e).choose : A) : L)) ^ (-k e) *
          (algebraMap L F ((π : A) : L)) ^ (-k e) * (An' e).param ^ (k e) := by
        rw [hzrel, map_mul, mul_zpow, mul_zpow, inv_zpow', neg_neg]
      have e4 : algebraMap L F ((((hw e).choose : A) : L) ^ (-k e)) = (algebraMap L F (((hw e).choose : A) : L)) ^ (-k e) :=
        map_zpow₀ _ _ _
      rw [e1, e2, e3, e4]
      have e5 : (algebraMap L F ((π : A) : L)) ^ (-(φ (src e))) * (algebraMap L F ((π : A) : L)) ^ (-k e) =
          (algebraMap L F ((π : A) : L)) ^ (-(φ (tgt e))) := by
        rw [← zpow_add₀ ha]; congr 1; rw [hk_def]; ring
      calc (algebraMap L F ((π : A) : L)) ^ (-(φ (src e))) * g *
            ((algebraMap L F (((hw e).choose : A) : L)) ^ (-k e) * (algebraMap L F ((π : A) : L)) ^ (-k e) *
              (An' e).param ^ (k e))
          = ((algebraMap L F ((π : A) : L)) ^ (-(φ (src e))) * (algebraMap L F ((π : A) : L)) ^ (-k e)) * g *
              (An' e).param ^ (k e) * (algebraMap L F (((hw e).choose : A) : L)) ^ (-k e) := by ring
        _ = (algebraMap L F ((π : A) : L)) ^ (-(φ (tgt e))) * g * (An' e).param ^ (k e) *
              (algebraMap L F (((hw e).choose : A) : L)) ^ (-k e) := by rw [e5]
    obtain ⟨hzpow_t, hres_zpow_t⟩ := (C (tgt e)).zpow_mem_and_residue_zpow hzt_mem hzt0 (k e)
    have hconst_t : algebraMap L F ((((hw e).choose : A) : L) ^ (-k e)) ∈ (C (tgt e)).integers := by
      rw [← hcoeL]; exact ((C (tgt e)).algebraMap_mem_iff _).mpr (Subtype.mem _)
    have hGt : (wt (src e) • g * (An e).param ^ (-k e)) ∈ (C (tgt e)).integers := by
      rw [hGt_eq]; exact mul_mem (mul_mem (hg (tgt e)) hzpow_t) hconst_t
    have hres_const : (C (tgt e)).residue ⟨algebraMap L F ((((hw e).choose : A) : L) ^ (-k e)), hconst_t⟩ =
        algebraMap (IsLocalRing.ResidueField A) (Fbar (tgt e)) (ubar e ^ (-k e)) := by
      have h1 : (⟨algebraMap L F ((((hw e).choose : A) : L) ^ (-k e)), hconst_t⟩ : (C (tgt e)).integers) =
          ⟨algebraMap L F ((((hw e).choose ^ (-k e) : Aˣ) : A) : L), ((C (tgt e)).algebraMap_mem_iff _).mpr (Subtype.mem _)⟩ :=
        Subtype.ext (congrArg (algebraMap L F) (hcoeL (-k e)).symm)
      rw [h1, (C (tgt e)).residue_algebraMap, hubar_def, hcoeκ]
    have hresGt : (C (tgt e)).residue ⟨(wt (src e) • g * (An e).param ^ (-k e)), hGt⟩ =
        (C (tgt e)).residue ⟨wt (tgt e) • g, hg (tgt e)⟩ * zt e ^ (k e) * algebraMap (IsLocalRing.ResidueField A) (Fbar (tgt e)) (ubar e ^ (-k e)) := by
      have : (⟨(wt (src e) • g * (An e).param ^ (-k e)), hGt⟩ : (C (tgt e)).integers) =
          ⟨wt (tgt e) • g, hg (tgt e)⟩ * ⟨(An' e).param ^ (k e), hzpow_t⟩ * ⟨algebraMap L F ((((hw e).choose : A) : L) ^ (-k e)), hconst_t⟩ :=
        Subtype.ext hGt_eq
      rw [this, map_mul, map_mul, hres_zpow_t, hres_const, hzt_def]

    have hGreg : ∀ P ∈ (An e).dom, 0 ≤ P.ord (wt (src e) • g * (An e).param ^ (-k e)) := by
      intro P hP
      obtain ⟨-, hzP, -, hneP, -⟩ := (An e).mem_dom P hP
      rw [P.ord_mul (smul_ne_zero (hwt0 _) hg0) (zpow_ne_zero _ hz0), Algebra.smul_def,
        P.ord_mul ((map_ne_zero _).mpr (hwt0 _)) hg0, ConstantReduction.ord_algebraMap P (hwt0 _),
        P.ord_zpow_eq_zero_of_evalAt_ne_zero hzP hneP, zero_add, add_zero, ← hDann e P hP]
      linarith [hordD P, hDann e P hP]

    obtain ⟨h1, h2, h3⟩ :=
      AlgebraicCurve.Annulus.ord_residue_nonneg_and_evalAt_residue_eq_of_isAttached_of_isAttached A (An e) (An' e)
        hdom (hpair e).2.1 hmod0 hzz' (C (src e)) (xs e) (hratBar _ _) (hatt e).1 (C (tgt e)) (xt e) (hratBar _ _) (hatt e).2 (wt (src e) • g * (An e).param ^ (-k e)) hGs hGt hGreg
    rw [hresGs] at h1 h3
    rw [hresGt] at h2 h3
    have hubar0 : ubar e ≠ 0 := by
      rw [hubar_def]; exact ((IsLocalRing.residue A).isUnit_map (hw e).choose.isUnit).ne_zero
    have hzs_ne : zs e ≠ 0 := by rw [hzs_def]; exact hzs0
    have hzt_ne : zt e ≠ 0 := by rw [hzt_def]; exact hzt0
    have hconst_ne : algebraMap (IsLocalRing.ResidueField A) (Fbar (tgt e)) (ubar e ^ (-k e)) ≠ 0 :=
      (map_ne_zero _).mpr (zpow_ne_zero _ hubar0)
    refine ⟨fun hne => ?_, fun hne => ?_, ?_⟩
    · have := h1 (mul_ne_zero hne (zpow_ne_zero _ hzs_ne))
      rw [(xs e).ord_mul hne (zpow_ne_zero _ hzs_ne), (xs e).ord_zpow' hzs_ne, hzs_def, hzs_ord] at this
      linarith
    · have := h2 (mul_ne_zero (mul_ne_zero hne (zpow_ne_zero _ hzt_ne)) hconst_ne)
      rw [(xt e).ord_mul (mul_ne_zero hne (zpow_ne_zero _ hzt_ne)) hconst_ne, (xt e).ord_mul hne (zpow_ne_zero _ hzt_ne),
        (xt e).ord_zpow' hzt_ne, hzt_def, hzt_ord, ConstantReduction.ord_algebraMap (xt e) (zpow_ne_zero _ hubar0)] at this
      linarith
    ·
      have hval_t : (xt e).evalAt ((C (tgt e)).residue ⟨wt (tgt e) • g, hg (tgt e)⟩ * zt e ^ (k e) *
          algebraMap (IsLocalRing.ResidueField A) (Fbar (tgt e)) (ubar e ^ (-k e))) =
          (xt e).evalAt ((C (tgt e)).residue ⟨wt (tgt e) • g, hg (tgt e)⟩ * zt e ^ (k e)) * ubar e ^ (-k e) := by
        by_cases hne : (C (tgt e)).residue ⟨wt (tgt e) • g, hg (tgt e)⟩ = 0
        · rw [hne, zero_mul, zero_mul, (xt e).evalAt_zero', zero_mul]
        · have hprod_ne : (C (tgt e)).residue ⟨wt (tgt e) • g, hg (tgt e)⟩ * zt e ^ (k e) ≠ 0 :=
            mul_ne_zero hne (zpow_ne_zero _ hzt_ne)
          have hreg : 0 ≤ (xt e).ord ((C (tgt e)).residue ⟨wt (tgt e) • g, hg (tgt e)⟩ * zt e ^ (k e)) := by
            have := h2 (mul_ne_zero hprod_ne hconst_ne)
            rw [(xt e).ord_mul hprod_ne hconst_ne, ConstantReduction.ord_algebraMap (xt e) (zpow_ne_zero _ hubar0),
              add_zero] at this
            exact this
          rw [(xt e).evalAt_mul_of_mem' (hratBar _ _) ((xt e).mem_valuationSubring_of_ord_nonneg hprod_ne hreg)
            ((xt e).algebraMap_mem' _), (xt e).evalAt_algebraMap']
      rw [hval_t] at h3
      rw [h3, mul_assoc, ← zpow_add₀ hubar0, neg_add_cancel, zpow_zero, mul_one]
  exact ⟨hA, fun e => (hAnn e).1, fun e => (hAnn e).2.1, fun e => (hAnn e).2.2⟩

end S_AlgebraicCurve_SemistableCovering_ord_residue_smul_ge_and_evalAt_mul_eq_of_forall_smul_mem_integers_of_width_one
end P2MW
export P2MW.S_AlgebraicCurve_SemistableCovering_ord_residue_smul_ge_and_evalAt_mul_eq_of_forall_smul_mem_integers_of_width_one (solution)
