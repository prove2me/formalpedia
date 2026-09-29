-- Prove2me | solution 1 for AlgebraicCurve.Divisor.exists_torsion_descent_of_constantFieldExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/51670f80-4adf-5870-bc56-a3f45442b060

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Divisor_isPrincipal_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_exists_derivation_constantFieldExtension_map_mem
import Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_AlgebraicCurve_exists_genus_riemannIndex_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_ell_le_ell_sub_single_add_deg
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_finiteDimensional_lSpace_zero_of_constantsAreBase
import Theorems.Thm_AlgebraicCurve_lSpace_eq_bot_of_degree_neg
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_neg_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_ord_smul_of_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_mk_mem_maximalIdeal_iff
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.ord_zero Place.ord_one Place.ord_mul Place.ord_inv Place.ord_zpow Divisor Divisor.degree Divisor.degree_single Divisor.principal HasPrincipalDivisors Pic HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed LSpace ell mem_lSpace_iff_ord algebraMap_mem_lSpace_zero ConstantsAreBase indexOfSpecialty Place.exists_comap_algebraMap_eq_of_constantFieldExtension Divisor.isPrincipal_of_constantFieldExtension exists_derivation_constantFieldExtension_map_mem Place.exists_of_valuationSubring Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed Place.deg_eq_one_iff_surjective_algebraMap_residueField exists_genus_riemannIndex_of_isCurveOver ell_le_ell_sub_single_add_deg finiteDimensional_lSpace RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase lSpace_eq_bot_of_degree_neg Place.exists_ord_neg_of_transcendental Place.ord_algebraMap Place.ord_smul_of_ne_zero Place.min_ord_le_ord_add Place.mem_iff_ord_nonneg Place.mk_mem_maximalIdeal_iff essFiniteType_of_transcendental_of_finiteDimensional"
p2m_open "AlgebraicCurve"

namespace TorsionDescentDeriv

section General

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

open Classical in

noncomputable def divOf [HasPrincipalDivisors K F] (f : F) : Divisor K F :=
  if hf : f = 0 then 0 else (HasPrincipalDivisors.exists_divisor (K := K) f hf).choose

theorem divOf_apply [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0) (v : Place K F) :
    divOf f v = v.ord f := by
  rw [divOf, dif_neg hf]
  exact (HasPrincipalDivisors.exists_divisor (K := K) f hf).choose_spec.1 v

@[scoped simp] theorem divOf_zero [HasPrincipalDivisors K F] : divOf (K := K) (0 : F) = 0 := by
  rw [divOf, dif_pos rfl]

theorem degree_divOf [HasPrincipalDivisors K F] (f : F) :
    Divisor.degree (divOf (K := K) f) = 0 := by
  by_cases hf : f = 0
  · subst hf; simp
  · rw [divOf, dif_neg hf]
    exact (HasPrincipalDivisors.exists_divisor (K := K) f hf).choose_spec.2

theorem divOf_mem_principal [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0) :
    divOf (K := K) f ∈ Divisor.principal :=
  ⟨f, hf, fun v => divOf_apply hf v⟩

theorem isPrincipal_iff_eq_divOf [HasPrincipalDivisors K F] {D : Divisor K F} :
    D.IsPrincipal ↔ ∃ f : F, f ≠ 0 ∧ D = divOf f := by
  constructor
  · rintro ⟨f, hf, hD⟩
    exact ⟨f, hf, Finsupp.ext fun v => by rw [hD v, divOf_apply hf]⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, fun v => divOf_apply hf v⟩

theorem mem_principal_iff_eq_divOf [HasPrincipalDivisors K F] {D : Divisor K F} :
    D ∈ Divisor.principal ↔ ∃ f : F, f ≠ 0 ∧ D = divOf f :=
  isPrincipal_iff_eq_divOf

theorem divOf_mul [HasPrincipalDivisors K F] {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    divOf (K := K) (f * g) = divOf f + divOf g := by
  ext v
  rw [Finsupp.add_apply, divOf_apply (mul_ne_zero hf hg), divOf_apply hf, divOf_apply hg,
    Place.ord_mul _ hf hg]

theorem divOf_inv [HasPrincipalDivisors K F] (f : F) :
    divOf (K := K) f⁻¹ = -divOf f := by
  by_cases hf : f = 0
  · subst hf; simp
  ext v
  rw [Finsupp.neg_apply, divOf_apply (inv_ne_zero hf), divOf_apply hf, Place.ord_inv]

theorem divOf_pow [HasPrincipalDivisors K F] (f : F) (n : ℕ) :
    divOf (K := K) (f ^ n) = (n : ℤ) • divOf f := by
  by_cases hf : f = 0
  · subst hf
    cases n with
    | zero =>
      ext v
      simp only [pow_zero, Nat.cast_zero, zero_smul, Finsupp.coe_zero, Pi.zero_apply]
      rw [divOf_apply one_ne_zero, Place.ord_one]
    | succ n => simp
  induction n with
  | zero =>
    ext v
    simp only [pow_zero, Nat.cast_zero, zero_smul, Finsupp.coe_zero, Pi.zero_apply]
    rw [divOf_apply one_ne_zero, Place.ord_one]
  | succ n ih =>
    rw [pow_succ, divOf_mul (pow_ne_zero _ hf) hf, ih]
    simp [add_smul]

theorem divOf_smul_const [HasPrincipalDivisors K F] {c : K} (hc : c ≠ 0) (f : F) :
    divOf (K := K) (c • f) = divOf f := by
  by_cases hf : f = 0
  · subst hf; simp
  ext v
  rw [divOf_apply (smul_ne_zero hc hf), divOf_apply hf, Place.ord_smul_of_ne_zero v hc]

theorem divOf_algebraMap [HasPrincipalDivisors K F] (c : K) :
    divOf (K := K) (algebraMap K F c) = 0 := by
  by_cases hc : c = 0
  · subst hc; simp
  ext v
  rw [divOf_apply (by simpa using hc), Place.ord_algebraMap]
  rfl

theorem mem_lSpace_add_divOf_iff [HasPrincipalDivisors K F] {D : Divisor K F} {u : F}
    (hu : u ≠ 0) {y : F} :
    y ∈ LSpace (D + divOf u) ↔ y * u ∈ LSpace D := by
  rw [mem_lSpace_iff_ord, mem_lSpace_iff_ord]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  simp only [hy, mul_ne_zero hy hu, false_or, Finsupp.add_apply]
  constructor
  · intro h v
    have := h v
    rw [divOf_apply hu] at this
    rw [Place.ord_mul _ hy hu]
    linarith
  · intro h v
    have := h v
    rw [Place.ord_mul _ hy hu] at this
    rw [divOf_apply hu]
    linarith

theorem divOf_add_mem_lSpace [HasPrincipalDivisors K F] {D : Divisor K F} {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ LSpace D) : 0 ≤ D + divOf f := by
  intro v
  have := ((mem_lSpace_iff_ord.mp hf).resolve_left hf0) v
  simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply, divOf_apply hf0]
  linarith

theorem constantsAreBase_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F]
    (j : F) (hj : Transcendental K j)
    [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F] :
    ConstantsAreBase K F := by
  classical
  refine le_antisymm ?_ ?_
  · intro f hf
    rcases eq_or_ne f 0 with rfl | hf0
    · exact zero_mem _
    have hord : ∀ v : Place K F, 0 ≤ v.ord f := by
      intro v
      have := ((mem_lSpace_iff_ord.mp hf).resolve_left hf0) v
      simpa using this
    have hzero : ∀ v : Place K F, v.ord f = 0 := by
      have hdeg := degree_divOf (K := K) f
      rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum] at hdeg
      have hnonneg : ∀ v ∈ (divOf (K := K) f).support,
          (0 : ℤ) ≤ (AddMonoidHom.mulRight (v.deg : ℤ)) (divOf (K := K) f v) := by
        intro v _
        simp only [AddMonoidHom.coe_mulRight, IsCurveOver.deg_eq_one_of_isAlgClosed v,
          Nat.cast_one, mul_one, divOf_apply hf0]
        exact hord v
      have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hdeg
      intro v
      by_cases hv : v ∈ (divOf (K := K) f).support
      · have := hall v hv
        simpa [IsCurveOver.deg_eq_one_of_isAlgClosed v, divOf_apply hf0] using this
      · have : divOf (K := K) f v = 0 := Finsupp.notMem_support_iff.mp hv
        rwa [divOf_apply hf0] at this
    obtain ⟨c, hc⟩ := Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed j hj hzero
    exact ⟨c, hc⟩
  · rintro _ ⟨c, rfl⟩
    exact algebraMap_mem_lSpace_zero c

theorem exists_riemann_inequality [IsAlgClosed K] [IsCurveOver K F]
    (j : F) (hj : Transcendental K j)
    [hfd : FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F] :
    ∃ γ : ℤ, ∀ D : Divisor K F, Divisor.degree D + 1 - γ ≤ (ell D : ℤ) := by
  haveI : Algebra.EssFiniteType K F :=
    essFiniteType_of_transcendental_of_finiteDimensional hj hfd
  obtain ⟨γ, hγ⟩ :=
    exists_genus_riemannIndex_of_isCurveOver (K := K) (F := F) (constantsAreBase_of_isAlgClosed j hj)
  refine ⟨γ, fun D => ?_⟩
  have h := (hγ D).2
  have h0 : (0 : ℤ) ≤ (indexOfSpecialty D : ℤ) := Int.natCast_nonneg _
  linarith

theorem exists_reduced [IsAlgClosed K] [IsCurveOver K F]
    (j : F) (hj : Transcendental K j)
    [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F]
    (c : Divisor K F) (hc : Divisor.degree c = 0) (P : Place K F) :
    ∃ (r : ℕ) (f : F), f ≠ 0 ∧ f ∈ LSpace (c + (r : ℤ) • Finsupp.single P 1) ∧
      ∀ h ∈ LSpace (c + (r : ℤ) • Finsupp.single P 1), ∃ a : K, a • f = h := by
  classical
  obtain ⟨γ, hγ⟩ := exists_riemann_inequality (K := K) (F := F) j hj
  have hC := constantsAreBase_of_isAlgClosed (K := K) (F := F) j hj
  haveI := RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase K F hC
  let Dk : ℕ → Divisor K F := fun k => c + (k : ℤ) • Finsupp.single P 1
  have hdeg1 : P.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed P
  have hdegk : ∀ k : ℕ, Divisor.degree (Dk k) = k := by
    intro k
    simp only [Dk, map_add, map_zsmul, hc, Divisor.degree_single, hdeg1, Nat.cast_one, mul_one,
      smul_eq_mul, zero_add]
  have hex : ∃ k : ℕ, LSpace (Dk k) ≠ ⊥ := by
    refine ⟨γ.toNat, fun hbot => ?_⟩
    have h1 := hγ (Dk γ.toNat)
    have h2 : ell (Dk γ.toNat) = 0 := by
      rw [ell, hbot, finrank_bot]
    rw [hdegk, h2] at h1
    have := Int.self_le_toNat γ
    push_cast at h1
    linarith
  set r := Nat.find hex with hr_def
  have hr : LSpace (Dk r) ≠ ⊥ := Nat.find_spec hex
  obtain ⟨f, hfmem, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hr
  refine ⟨r, f, hf0, hfmem, ?_⟩
  have hprev : LSpace (Dk r - Finsupp.single P 1) = ⊥ := by
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · apply lSpace_eq_bot_of_degree_neg
      rw [map_sub, hdegk, h0, Divisor.degree_single, hdeg1]
      norm_num
    · have heq : Dk r - Finsupp.single P 1 = Dk (r - 1) := by
        simp only [Dk]
        rw [Nat.cast_sub hpos, sub_smul, Nat.cast_one, one_smul]
        abel
      rw [heq]
      by_contra hne
      exact Nat.find_min hex (Nat.sub_lt hpos one_pos) hne
  have hle : ell (Dk r) ≤ 1 := by
    have := ell_le_ell_sub_single_add_deg (Dk r) P
    have h0 : ell (Dk r - Finsupp.single P 1) = 0 := by
      rw [ell, hprev, finrank_bot]
    rw [h0, hdeg1, zero_add] at this
    exact this
  haveI : FiniteDimensional K (LSpace (Dk r)) := finiteDimensional_lSpace (Dk r)
  have hfne : (⟨f, hfmem⟩ : LSpace (Dk r)) ≠ 0 := by
    intro h
    apply hf0
    simpa using congrArg Subtype.val h
  have hone : Module.finrank K (LSpace (Dk r)) = 1 := by
    refine le_antisymm hle ?_
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨f, hfmem⟩, hfne⟩
  intro h hh
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨f, hfmem⟩ : LSpace (Dk r)) hfne).mp hone
    ⟨h, hh⟩
  exact ⟨a, by simpa using congrArg Subtype.val ha⟩

end General

section Extension

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
  [Algebra F F']

def LiesOver (w' : Place K' F') (v : Place K F) : Prop :=
  w'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring

def IsGeneric (K F : Type*) [Field K] [Field F] [Algebra K F] [Algebra F F']
    (w' : Place K' F') : Prop :=
  ∀ v : Place K F, ¬ LiesOver w' v

section Tower

variable [Algebra K K'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']

theorem IsGeneric.comap_eq_top [CharZero K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {w' : Place K' F'} (hw : IsGeneric K F w') :
    w'.toValuationSubring.comap (algebraMap F F') = ⊤ := by
  by_contra hne
  obtain ⟨v, hv⟩ := Place.exists_of_valuationSubring (K := K) x
    (w'.toValuationSubring.comap (algebraMap F F')) (fun a => by
      rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply K K' F']
      exact w'.algebraMap_mem' _) hne
  exact hw v hv.symm

theorem IsGeneric.algebraMap_mem [CharZero K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {w' : Place K' F'} (hw : IsGeneric K F w') (y : F) :
    algebraMap F F' y ∈ w'.toValuationSubring := by
  rw [← ValuationSubring.mem_comap, hw.comap_eq_top x]
  exact ValuationSubring.mem_top _

theorem IsGeneric.ord_algebraMap [CharZero K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {w' : Place K' F'} (hw : IsGeneric K F w') (y : F) :
    w'.ord (algebraMap F F' y) = 0 := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hy' : algebraMap F F' y ≠ 0 := by simpa using hy
  have hyi' : algebraMap F F' y⁻¹ ≠ 0 := by simpa using hy
  have h1 := (Place.mem_iff_ord_nonneg w' hy').mp (hw.algebraMap_mem x y)
  have h2 := (Place.mem_iff_ord_nonneg w' hyi').mp (hw.algebraMap_mem x y⁻¹)
  rw [map_inv₀, Place.ord_inv] at h2
  linarith

end Tower

def InMax (w : Place K' F') (y : F') : Prop := y = 0 ∨ 0 < w.ord y

section Tower

variable [Algebra K K'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']

theorem IsGeneric.exists_inMax_sub [CharZero K] [IsAlgClosed K'] [IsCurveOver K' F'] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {w' : Place K' F'} (hw : IsGeneric K F w') :
    ∃ t : K', InMax w' (algebraMap F F' x - algebraMap K' F' t) := by
  have hsurj : Function.Surjective (algebraMap K' w'.ResidueField) :=
    (Place.deg_eq_one_iff_surjective_algebraMap_residueField w').mp
      (IsCurveOver.deg_eq_one_of_isAlgClosed w')
  have hxmem : algebraMap F F' x ∈ w'.toValuationSubring := hw.algebraMap_mem x x
  obtain ⟨t, ht⟩ := hsurj (IsLocalRing.residue _ ⟨algebraMap F F' x, hxmem⟩)
  have htmem : algebraMap K' F' t ∈ w'.toValuationSubring := w'.algebraMap_mem' t
  refine ⟨t, (Place.mk_mem_maximalIdeal_iff w' (sub_mem hxmem htmem)).mp ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff]
  have hsub : (⟨algebraMap F F' x - algebraMap K' F' t, sub_mem hxmem htmem⟩ :
      w'.toValuationSubring) =
      ⟨algebraMap F F' x, hxmem⟩ - algebraMap K' w'.toValuationSubring t := by
    ext; simp [Place.coe_algebraMap]
  rw [hsub, map_sub, ← ht, sub_eq_zero, IsScalarTower.algebraMap_apply K' w'.toValuationSubring
    w'.ResidueField]
  rfl

theorem IsGeneric.not_mem_range [CharZero K] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {w' : Place K' F'} (hw : IsGeneric K F w') {t : K'}
    (ht : InMax w' (algebraMap F F' x - algebraMap K' F' t)) :
    t ∉ Set.range (algebraMap K K') := by
  rintro ⟨c, rfl⟩
  have heq : algebraMap F F' x - algebraMap K' F' (algebraMap K K' c) =
      algebraMap F F' (x - algebraMap K F c) := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [heq] at ht
  have hne : x - algebraMap K F c ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    exact hx (h ▸ isAlgebraic_algebraMap c)
  rcases ht with h | h
  · exact hne ((map_eq_zero_iff _ (algebraMap F F').injective).mp h)
  · rw [hw.ord_algebraMap x] at h
    exact lt_irrefl _ h

end Tower

theorem transcendental_of_not_mem_range [Algebra K K'] [IsAlgClosed K] {t : K'}
    (ht : t ∉ Set.range (algebraMap K K')) : Transcendental K t := by
  intro halg
  have hint : IsIntegral K t := halg.isIntegral
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
  exact ht (minpoly.mem_range_of_degree_eq_one K t hdeg)

end Extension

section DerivationExistence

open scoped IntermediateField
open KaehlerDifferential MvPolynomial

theorem exists_derivation_apply_eq_one (K K' : Type*) [Field K] [Field K'] [Algebra K K']
    [CharZero K] (t : K') (ht : Transcendental K t) :
    ∃ δ : Derivation K K' K', δ t = 1 := by
  classical

  have hind : AlgebraicIndepOn K id ({t} : Set K') :=
    (algebraicIndependent_singleton_iff (R := K) (x := fun i : ({t} : Set K') => (id (i : K')))
      ⟨t, Set.mem_singleton t⟩).mpr ht
  obtain ⟨B, htB, hB⟩ := exists_isTranscendenceBasis_superset hind
  set L : IntermediateField K K' := IntermediateField.adjoin K (Set.range ((↑) : B → K')) with hL
  haveI : Algebra.IsAlgebraic L K' := hB.isAlgebraic_field
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  haveI : Algebra.IsSeparable L K' := inferInstance

  let R := MvPolynomial B K
  let e : FractionRing R ≃ₐ[K] L := hB.1.aevalEquivField
  letI iRL : Algebra R L := (e.toAlgHom.toRingHom.comp (algebraMap R (FractionRing R))).toAlgebra
  letI iRK' : Algebra R K' := ((algebraMap L K').comp (algebraMap R L)).toAlgebra
  haveI : IsScalarTower R L K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have halgL : ∀ p : R, algebraMap R L p = e (algebraMap R (FractionRing R) p) := fun _ => rfl
  have halgK' : ∀ p : R, algebraMap R K' p = ((e (algebraMap R (FractionRing R) p) : L) : K') :=
    fun _ => rfl
  have halgK'' : ∀ p : R, algebraMap R K' p = MvPolynomial.aeval ((↑) : B → K') p := by
    intro p
    rw [halgK', AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
  haveI : IsScalarTower K R K' := IsScalarTower.of_algebraMap_eq fun k => by
    rw [halgK'', MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C]
  haveI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq fun k => by
    apply Subtype.ext
    rw [show ((algebraMap K L k : L) : K') = algebraMap K K' k from rfl,
      show ((algebraMap R L (algebraMap K R k) : L) : K')
      = algebraMap R K' (algebraMap K R k) from rfl, halgK'', MvPolynomial.algebraMap_eq,
      MvPolynomial.aeval_C]

  let e' : FractionRing R ≃ₐ[R] L :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun p => rfl)
  haveI : IsFractionRing R L :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors R) e'
  haveI : Algebra.FormallyEtale R L :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := L) (nonZeroDivisors R)
  haveI : Algebra.FormallyEtale L K' := Algebra.FormallyEtale.of_isSeparable _ _
  haveI : Algebra.FormallyEtale R K' := Algebra.FormallyEtale.comp R L K'

  let t₀ : B := ⟨t, htB (Set.mem_singleton t)⟩
  let D₁ : Derivation K R K' := (Algebra.linearMap R K').compDer (MvPolynomial.pderiv t₀)
  have hD₁ : ∀ p : R, D₁ p = algebraMap R K' (MvPolynomial.pderiv t₀ p) := fun _ => rfl

  have hBC := KaehlerDifferential.isBaseChange_of_formallyEtale K R K'
  let Φ : Ω[K'⁄K] →ₗ[K'] K' := hBC.lift D₁.liftKaehlerDifferential
  have hΦ : ∀ p : R, Φ (KaehlerDifferential.D K K' (algebraMap R K' p)) = D₁ p := by
    intro p
    rw [← KaehlerDifferential.map_D K K R K' p]
    show hBC.lift D₁.liftKaehlerDifferential _ = _
    rw [hBC.lift_eq, Derivation.liftKaehlerDifferential_comp_D]
  let δ : Derivation K K' K' := Φ.compDer (KaehlerDifferential.D K K')
  have hδalg : ∀ p : R, δ (algebraMap R K' p) = D₁ p := fun p => hΦ p
  refine ⟨δ, ?_⟩
  have hX : algebraMap R K' (MvPolynomial.X t₀) = t := by
    rw [halgK'', MvPolynomial.aeval_X]
  calc δ t = δ (algebraMap R K' (MvPolynomial.X t₀)) := by rw [hX]
    _ = D₁ (MvPolynomial.X t₀) := hδalg _
    _ = 1 := by rw [hD₁, MvPolynomial.pderiv_X_self, map_one]

end DerivationExistence

section LocalCalc

variable {R K F : Type*} [CommRing R] [Field K] [Field F] [Algebra K F] [Algebra R F]

theorem leibniz_zpow (D : Derivation R F F) {a : F} (ha : a ≠ 0) (k : ℤ) :
    D (a ^ k) = (k : F) * a ^ (k - 1) * D a := by
  rcases k with n | n
  ·
    rw [Int.ofNat_eq_natCast, zpow_natCast, D.leibniz_pow, nsmul_eq_mul, smul_eq_mul, Int.cast_natCast]
    rcases n with _ | n
    · simp
    · rw [Nat.add_sub_cancel, show ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) by push_cast; ring, zpow_natCast]
      ring
  · rw [zpow_negSucc, D.leibniz_inv, D.leibniz_pow, Int.negSucc_sub_one, zpow_negSucc,
      Int.cast_negSucc, Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul, smul_eq_mul]
    have hp : a ^ (n + 1) ≠ 0 := pow_ne_zero _ ha
    have hp' : a ^ (n + 1 + 1) ≠ 0 := pow_ne_zero _ ha
    field_simp
    push_cast
    ring

variable (w : Place K F)

theorem ne_zero_of_ord_ne_zero {f : F} (hf : w.ord f ≠ 0) : f ≠ 0 := by
  rintro rfl
  exact hf (Place.ord_zero w)

theorem mem_of_ord_eq_zero {u : F} (hu0 : u ≠ 0) (hu : w.ord u = 0) : u ∈ w.toValuationSubring :=
  (Place.mem_iff_ord_nonneg w hu0).mpr hu.ge

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ w.toValuationSubring) : 0 ≤ w.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  · exact (Place.mem_iff_ord_nonneg w hf0).mp hf

theorem ord_intCast (k : ℤ) : w.ord (k : F) = 0 := by
  rw [show (k : F) = algebraMap K F (k : K) by rw [map_intCast]]
  exact Place.ord_algebraMap w _

theorem ord_natCast (k : ℕ) : w.ord (k : F) = 0 := by
  rw [show (k : F) = algebraMap K F (k : K) by rw [map_natCast]]
  exact Place.ord_algebraMap w _

theorem le_ord_add {a b : F} {m : ℤ} (ha : a = 0 ∨ m ≤ w.ord a) (hb : b = 0 ∨ m ≤ w.ord b)
    (hab : a + b ≠ 0) : m ≤ w.ord (a + b) := by
  rcases ha with rfl | ha
  · rw [zero_add] at hab ⊢
    exact hb.resolve_left hab
  rcases hb with rfl | hb
  · rw [add_zero]
    exact ha
  by_cases ha0 : a = 0
  · rw [ha0, zero_add] at hab ⊢; exact hb
  by_cases hb0 : b = 0
  · rw [hb0, add_zero]; exact ha
  exact (le_min ha hb).trans (Place.min_ord_le_ord_add w ha0 hb0 hab)

theorem ord_sub_le_ord_apply (D : Derivation R F F)
    (hD : ∀ z ∈ w.toValuationSubring, D z ∈ w.toValuationSubring)
    {π : F} (hπ : w.ord π = 1) {c : ℤ} (hc : 0 ≤ c) (hπD : D π = 0 ∨ 1 - c ≤ w.ord (D π))
    {f : F} (hf : f ≠ 0) (hDf : D f ≠ 0) : w.ord f - c ≤ w.ord (D f) := by
  have hπ0 : π ≠ 0 := ne_zero_of_ord_ne_zero w (by rw [hπ]; exact one_ne_zero)
  set k : ℤ := w.ord f with hk
  have hπk : π ^ k ≠ 0 := zpow_ne_zero k hπ0
  have hπk1 : π ^ (k - 1) ≠ 0 := zpow_ne_zero _ hπ0
  set u : F := f * (π ^ k)⁻¹ with hu
  have hu0 : u ≠ 0 := mul_ne_zero hf (inv_ne_zero hπk)
  have hordu : w.ord u = 0 := by
    rw [hu, Place.ord_mul _ hf (inv_ne_zero hπk), Place.ord_inv, Place.ord_zpow, hπ, mul_one, ← hk]
    ring
  have humem : u ∈ w.toValuationSubring := mem_of_ord_eq_zero w hu0 hordu
  have hDu : D u ∈ w.toValuationSubring := hD u humem
  have hfu : f = u * π ^ k := by
    rw [hu, inv_mul_cancel_right₀ hπk]

  have hDf_eq : D f = π ^ k * D u + u * ((k : F) * π ^ (k - 1) * D π) := by
    conv_lhs => rw [hfu]
    rw [D.leibniz, leibniz_zpow D hπ0 k, smul_eq_mul, smul_eq_mul, add_comm]

  have hT1 : π ^ k * D u = 0 ∨ k - c ≤ w.ord (π ^ k * D u) := by
    by_cases hDu0 : D u = 0
    · left; rw [hDu0, mul_zero]
    · right
      rw [Place.ord_mul _ hπk hDu0, Place.ord_zpow, hπ, mul_one]
      have := ord_nonneg_of_mem w hDu
      linarith
  have hT2 : u * ((k : F) * π ^ (k - 1) * D π) = 0 ∨
      k - c ≤ w.ord (u * ((k : F) * π ^ (k - 1) * D π)) := by
    by_cases hz : (k : F) * π ^ (k - 1) * D π = 0
    · left; rw [hz, mul_zero]
    · right
      have hDπ0 : D π ≠ 0 := fun h => hz (by rw [h, mul_zero])
      have hk0 : (k : F) ≠ 0 := fun h => hz (by rw [h, zero_mul, zero_mul])
      have hbound : 1 - c ≤ w.ord (D π) := hπD.resolve_left hDπ0
      rw [Place.ord_mul _ hu0 hz, Place.ord_mul _ (mul_ne_zero hk0 hπk1) hDπ0,
        Place.ord_mul _ hk0 hπk1, hordu, ord_intCast, Place.ord_zpow, hπ, mul_one]
      linarith
  rw [hDf_eq] at hDf ⊢
  exact le_ord_add w hT1 hT2 hDf

theorem exists_ord_eq_one : ∃ π : F, w.ord π = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  exact ⟨π, w.ord_coe_irreducible hπ⟩

theorem ord_le_ord_apply_of_eigen [CharZero F] (D : Derivation R F F)
    (hD : ∀ z ∈ w.toValuationSubring, D z ∈ w.toValuationSubring)
    {φ : F} (hφ0 : φ ≠ 0) (hφ : 0 < w.ord φ) {a : F} (ha : a ∈ w.toValuationSubring)
    (hDφ : D φ = a * φ)
    {z : F} (hz0 : z ≠ 0) (hz : 0 < w.ord z) (hDz : D z ≠ 0) : w.ord z ≤ w.ord (D z) := by

  set k : ℕ := (w.ord φ).toNat with hk
  set m : ℕ := (w.ord z).toNat with hm
  have hkz : (k : ℤ) = w.ord φ := Int.toNat_of_nonneg hφ.le
  have hmz : (m : ℤ) = w.ord z := Int.toNat_of_nonneg hz.le
  have hk1 : 1 ≤ k := by
    have : (1 : ℤ) ≤ k := by rw [hkz]; exact hφ
    exact_mod_cast this
  have hm1 : 1 ≤ m := by
    have : (1 : ℤ) ≤ m := by rw [hmz]; exact hz
    exact_mod_cast this
  have hφm : φ ^ m ≠ 0 := pow_ne_zero _ hφ0
  have hzk : z ^ k ≠ 0 := pow_ne_zero _ hz0

  set u : F := z ^ k * (φ ^ m)⁻¹ with hu
  have hu0 : u ≠ 0 := mul_ne_zero hzk (inv_ne_zero hφm)
  have hordu : w.ord u = 0 := by
    rw [hu, Place.ord_mul _ hzk (inv_ne_zero hφm), Place.ord_inv, ← zpow_natCast, ← zpow_natCast,
      Place.ord_zpow, Place.ord_zpow, ← hkz, ← hmz]
    ring
  have humem : u ∈ w.toValuationSubring := mem_of_ord_eq_zero w hu0 hordu
  have hDu : D u ∈ w.toValuationSubring := hD u humem
  have hzu : z ^ k = u * φ ^ m := by rw [hu, inv_mul_cancel_right₀ hφm]

  have hL : D (z ^ k) = (k : F) * z ^ (k - 1) * D z := by
    rw [D.leibniz_pow, nsmul_eq_mul, smul_eq_mul, mul_assoc]
  have hR : D (u * φ ^ m) = ((m : F) * a * u + D u) * φ ^ m := by
    rw [D.leibniz, D.leibniz_pow, hDφ, smul_eq_mul, smul_eq_mul, nsmul_eq_mul, smul_eq_mul]
    have hpow : φ ^ (m - 1) * φ = φ ^ m := by
      rw [← pow_succ, Nat.sub_add_cancel hm1]
    calc u * ((m : F) * (φ ^ (m - 1) * (a * φ))) + φ ^ m * D u
        = (m : F) * a * u * (φ ^ (m - 1) * φ) + D u * φ ^ m := by ring
      _ = ((m : F) * a * u + D u) * φ ^ m := by rw [hpow]; ring
  have hEq : (k : F) * z ^ (k - 1) * D z = ((m : F) * a * u + D u) * φ ^ m := by
    rw [← hL, ← hR, hzu]

  have hk0 : (k : F) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hzk1 : z ^ (k - 1) ≠ 0 := pow_ne_zero _ hz0
  have hLne : (k : F) * z ^ (k - 1) * D z ≠ 0 := mul_ne_zero (mul_ne_zero hk0 hzk1) hDz
  have hcoef : (m : F) * a * u + D u ≠ 0 := by
    intro h
    rw [h, zero_mul] at hEq
    exact hLne hEq
  have hcoef_mem : (m : F) * a * u + D u ∈ w.toValuationSubring :=
    add_mem (mul_mem (mul_mem (by
      rw [show ((m : ℕ) : F) = algebraMap K F (m : K) by rw [map_natCast]]
      exact w.algebraMap_mem' _) ha) humem) hDu
  have hcoef_ord : 0 ≤ w.ord ((m : F) * a * u + D u) := ord_nonneg_of_mem w hcoef_mem

  have hordL : w.ord ((k : F) * z ^ (k - 1) * D z) = ((k : ℤ) - 1) * w.ord z + w.ord (D z) := by
    rw [Place.ord_mul _ (mul_ne_zero hk0 hzk1) hDz, Place.ord_mul _ hk0 hzk1, ord_natCast,
      ← zpow_natCast, Place.ord_zpow, Nat.cast_sub hk1]
    push_cast
    ring
  have hordR : w.ord (((m : F) * a * u + D u) * φ ^ m) =
      w.ord ((m : F) * a * u + D u) + (m : ℤ) * w.ord φ := by
    rw [Place.ord_mul _ hcoef hφm, ← zpow_natCast, Place.ord_zpow]
  have key : ((k : ℤ) - 1) * w.ord z + w.ord (D z) = w.ord ((m : F) * a * u + D u) + (m : ℤ) * w.ord φ := by
    rw [← hordL, ← hordR, hEq]
  rw [← hkz, ← hmz] at key
  rw [← hmz]
  nlinarith [key, hcoef_ord, hk1, hm1]

end LocalCalc

section Main

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
  [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']

theorem main [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (n : ℕ) (hn : n ≠ 0) (D' : Divisor K' F')
    (hD' : ∃ g' : F', g' ≠ 0 ∧ ∀ v' : Place K' F', (n : ℤ) * D' v' = v'.ord g') :
    ∃ (D : Divisor K F) (h' : F'), h' ≠ 0 ∧
      (∃ g : F, g ≠ 0 ∧ ∀ v : Place K F, (n : ℤ) * D v = v.ord g) ∧
      (∀ (v : Place K F) (v' : Place K' F'),
        v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring →
          D' v' = D v + v'.ord h') ∧
      (∀ v' : Place K' F',
        (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
          D' v' = v'.ord h') := by
  classical
  obtain ⟨x, hx, hxfd⟩ := id hfg
  obtain ⟨x', hx', hxfd'⟩ := id hfg'
  haveI := hxfd
  haveI := hxfd'
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  haveI : CharZero F' := charZero_of_injective_algebraMap (algebraMap K' F').injective
  obtain ⟨g', hg'0, hg'⟩ := hD'
  have hnD' : (n : ℤ) • D' = divOf g' := by
    ext w
    rw [Finsupp.smul_apply, smul_eq_mul, hg' w, divOf_apply hg'0]

  have hlift := Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F K' F' hfg hfg' hgen
  choose lift hliftOver hliftOrd hliftUniq using hlift
  have hU : ∀ (v : Place K F) (w₁ w₂ : Place K' F'), LiesOver w₁ v → LiesOver w₂ v → w₁ = w₂ :=
    fun v w₁ w₂ h₁ h₂ => (hliftUniq v w₁ h₁).trans (hliftUniq v w₂ h₂).symm
  have hV : ∀ (w' : Place K' F') (v₁ v₂ : Place K F), LiesOver w' v₁ → LiesOver w' v₂ → v₁ = v₂ :=
    fun w' v₁ v₂ h₁ h₂ => Place.ext (h₁.symm.trans h₂)

  obtain ⟨P, -⟩ := Place.exists_ord_neg_of_transcendental x hx
  set P₀ : Place K' F' := lift P with hP₀
  have hP₀ : LiesOver P₀ P := hliftOver P
  have hdegP₀ : P₀.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed P₀

  set d : ℤ := Divisor.degree D' with hd
  set c₀ : Divisor K' F' := D' - d • Finsupp.single P₀ 1 with hc₀
  have hc₀deg : Divisor.degree c₀ = 0 := by
    simp only [hc₀, map_sub, map_zsmul, Divisor.degree_single, hdegP₀, Nat.cast_one, mul_one,
      smul_eq_mul, hd]
    ring
  obtain ⟨r, fr, hfr0, hfrmem, hfruniq⟩ := exists_reduced (K := K') (F := F') x' hx' c₀ hc₀deg P₀
  set A : Divisor K' F' := c₀ + (r : ℤ) • Finsupp.single P₀ 1 + divOf fr with hA
  have hA0 : 0 ≤ A := divOf_add_mem_lSpace hfr0 hfrmem
  have hA0w : ∀ w : Place K' F', 0 ≤ A w := fun w => by simpa using hA0 w

  set φ : F' := g' * fr ^ n with hφ
  have hφ0 : φ ≠ 0 := mul_ne_zero hg'0 (pow_ne_zero _ hfr0)
  have hφdiv : divOf φ = (n : ℤ) • A - ((n : ℤ) * ((r : ℤ) - d)) • Finsupp.single P₀ 1 := by
    rw [hφ, divOf_mul hg'0 (pow_ne_zero _ hfr0), divOf_pow, ← hnD']
    simp only [hA, hc₀]
    module
  have hordφ : ∀ w : Place K' F',
      w.ord φ = (n : ℤ) * A w - (n : ℤ) * ((r : ℤ) - d) * Finsupp.single P₀ (1 : ℤ) w := by
    intro w
    have := congrArg (fun E : Divisor K' F' => E w) hφdiv
    simp only [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, divOf_apply hφ0] at this
    rw [this, mul_assoc]
  have hordφ_gen : ∀ w : Place K' F', IsGeneric K F w → w.ord φ = (n : ℤ) * A w := by
    intro w hw
    have hsP₀ : Finsupp.single P₀ (1 : ℤ) w = 0 := by
      rw [Finsupp.single_apply, if_neg]
      rintro rfl
      exact hw P hP₀
    rw [hordφ, hsP₀, mul_zero, sub_zero]

  have hAsupp : ∀ w' ∈ A.support, ¬ IsGeneric K F w' := by
    intro w' hw' hgw

    obtain ⟨t, ht⟩ := hgw.exists_inMax_sub x
    have htK : t ∉ Set.range (algebraMap K K') := hgw.not_mem_range x hx ht
    have httr : Transcendental K t := transcendental_of_not_mem_range htK
    obtain ⟨δ, hδt⟩ := exists_derivation_apply_eq_one K K' t httr

    obtain ⟨Dd, hDF, hDE, hDreg⟩ :=
      AlgebraicCurve.exists_derivation_constantFieldExtension_map_mem K F K' F' hfg hfg' hgen δ

    set y : F' := Dd φ * φ⁻¹ with hy
    have hymem : y ∈ LSpace A := by
      rw [mem_lSpace_iff_ord]
      rcases eq_or_ne y 0 with hy0 | hy0
      · exact Or.inl hy0
      right
      intro w
      have hDφ0 : Dd φ ≠ 0 := by
        intro h; apply hy0; rw [hy, h, zero_mul]
      have hordy : w.ord y = w.ord (Dd φ) - w.ord φ := by
        rw [hy, Place.ord_mul _ hDφ0 (inv_ne_zero hφ0), Place.ord_inv]; ring
      by_cases hgen_w : IsGeneric K F w
      ·
        obtain ⟨π, hπ⟩ := exists_ord_eq_one w
        have hπ0 : π ≠ 0 := ne_zero_of_ord_ne_zero w (by rw [hπ]; exact one_ne_zero)
        have hπmem : π ∈ w.toValuationSubring :=
          (Place.mem_iff_ord_nonneg w hπ0).mpr (by rw [hπ]; exact zero_le_one)
        have hDπ : Dd π = 0 ∨ 1 - 1 ≤ w.ord (Dd π) := by
          by_cases h : Dd π = 0
          · exact Or.inl h
          · right
            rw [sub_self]
            exact ord_nonneg_of_mem w (hDreg w π hπmem)
        have h1 : w.ord φ - 1 ≤ w.ord (Dd φ) :=
          ord_sub_le_ord_apply w Dd (fun z hz => hDreg w z hz) hπ zero_le_one hDπ hφ0 hDφ0
        have hordφw : w.ord φ = (n : ℤ) * A w := hordφ_gen w hgen_w
        by_cases hAw : A w = 0
        · have hφmem : φ ∈ w.toValuationSubring :=
            (Place.mem_iff_ord_nonneg w hφ0).mpr (by rw [hordφw, hAw, mul_zero])
          have h2 := ord_nonneg_of_mem w (hDreg w φ hφmem)
          rw [hordy, hordφw, hAw]
          linarith
        · have hAw1 : 1 ≤ A w := by
            have := hA0w w
            omega
          rw [hordy]
          linarith
      ·
        simp only [IsGeneric, not_forall, not_not] at hgen_w
        obtain ⟨v, hv⟩ := hgen_w
        have hw : w = lift v := hU v w (lift v) hv (hliftOver v)
        obtain ⟨π₀, hπ₀⟩ := exists_ord_eq_one v
        have hπ : w.ord (algebraMap F F' π₀) = 1 := by rw [hw, hliftOrd, hπ₀]
        have hDπ : Dd (algebraMap F F' π₀) = 0 ∨ 1 - 0 ≤ w.ord (Dd (algebraMap F F' π₀)) :=
          Or.inl (hDF π₀)
        have h1 : w.ord φ - 0 ≤ w.ord (Dd φ) :=
          ord_sub_le_ord_apply w Dd (fun z hz => hDreg w z hz) hπ le_rfl hDπ hφ0 hDφ0
        have h2 := hA0w w
        rw [hordy]
        linarith

    have hyfr : y * fr ∈ LSpace (c₀ + (r : ℤ) • Finsupp.single P₀ 1) := by
      rw [hA] at hymem
      exact (mem_lSpace_add_divOf_iff hfr0).mp hymem
    obtain ⟨a, ha⟩ := hfruniq _ hyfr
    have hya : y = algebraMap K' F' a := by
      rw [Algebra.smul_def] at ha
      exact (mul_left_injective₀ hfr0 ha).symm
    have hDφ : Dd φ = algebraMap K' F' a * φ := by
      rw [← hya, hy, inv_mul_cancel_right₀ hφ0]

    have hAw' : 1 ≤ A w' := by
      have h1 := hA0w w'
      have h2 : A w' ≠ 0 := Finsupp.mem_support_iff.mp hw'
      omega
    have hn1 : (1 : ℤ) ≤ n := by
      have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      exact_mod_cast this
    have hφpos : 0 < w'.ord φ := by
      rw [hordφ_gen w' hgw]
      nlinarith

    have hDy₀ : Dd (algebraMap F F' x - algebraMap K' F' t) = -1 := by
      rw [map_sub, hDF, hDE, hδt, map_one, zero_sub]
    rcases ht with hy00 | hy0pos
    · rw [hy00, map_zero] at hDy₀
      norm_num at hDy₀
    · have hy0ne : algebraMap F F' x - algebraMap K' F' t ≠ 0 := by
        intro h
        rw [h, Place.ord_zero] at hy0pos
        exact lt_irrefl _ hy0pos
      have hDy₀ne : Dd (algebraMap F F' x - algebraMap K' F' t) ≠ 0 := by
        rw [hDy₀]; norm_num
      have key := ord_le_ord_apply_of_eigen w' Dd (fun z hz => hDreg w' z hz) hφ0 hφpos
        (w'.algebraMap_mem' a) hDφ hy0ne hy0pos hDy₀ne
      rw [hDy₀, show (-1 : F') = algebraMap K' F' (-1) by simp, Place.ord_algebraMap] at key
      exact absurd key (not_le.mpr hy0pos)

  set B : Divisor K' F' := A + (d - r) • Finsupp.single P₀ 1 with hB
  have hBsupp : ∀ w' ∈ B.support, ∃ v : Place K F, LiesOver w' v := by
    intro w' hw'
    rcases Finset.mem_union.mp (Finsupp.support_add hw') with h | h
    · have := hAsupp w' h
      simp only [IsGeneric, not_forall, not_not] at this
      exact this
    · have h2 := Finsupp.support_smul h
      rw [Finsupp.mem_support_single] at h2
      exact ⟨P, h2.1 ▸ hP₀⟩
  have hD'B : D' = B + divOf fr⁻¹ := by
    rw [divOf_inv]
    simp only [hB, hA, hc₀, sub_smul]
    abel
  let π : Place K' F' → Place K F := fun w' =>
    if h : ∃ v : Place K F, LiesOver w' v then h.choose else P
  have hπ : ∀ (w' : Place K' F') (v : Place K F), LiesOver w' v → π w' = v := by
    intro w' v h
    have hex : ∃ v : Place K F, LiesOver w' v := ⟨v, h⟩
    simp only [π, dif_pos hex]
    exact hV w' _ _ hex.choose_spec h
  set R₀ : Divisor K F := Finsupp.mapDomain π B with hR₀
  have hR₀v : ∀ v : Place K F, R₀ v = B (lift v) := by
    intro v
    have hS : ((B.support : Finset (Place K' F')) : Set (Place K' F')) ⊆
        {w' : Place K' F' | ∃ v : Place K F, LiesOver w' v} := fun w' hw' => hBsupp w' hw'
    have hinjOn : Set.InjOn π {w' : Place K' F' | ∃ v : Place K F, LiesOver w' v} := by
      rintro w₁ ⟨v₁, h₁⟩ w₂ ⟨v₂, h₂⟩ heq
      rw [hπ w₁ v₁ h₁, hπ w₂ v₂ h₂] at heq
      subst heq
      exact hU v₁ w₁ w₂ h₁ h₂
    have := Finsupp.mapDomain_apply' _ B hS hinjOn (a := lift v) ⟨v, hliftOver v⟩
    rwa [hπ (lift v) v (hliftOver v)] at this
  have hB0 : ∀ w' : Place K' F', (∀ v : Place K F, ¬ LiesOver w' v) → B w' = 0 := by
    intro w' hw'
    by_contra hne
    obtain ⟨v, hv⟩ := hBsupp w' (Finsupp.mem_support_iff.mpr hne)
    exact hw' v hv

  have hprin : ((n : ℤ) • R₀).IsPrincipal := by
    apply Divisor.isPrincipal_of_constantFieldExtension K F K' F' hfg hfg' hgen
      ((n : ℤ) • R₀) ((n : ℤ) • B)
    · intro w' v hw'v
      have hw : w' = lift v := hU v w' (lift v) hw'v (hliftOver v)
      simp only [Finsupp.smul_apply, smul_eq_mul]
      rw [hR₀v v, hw]
    · intro w' hw'
      simp only [Finsupp.smul_apply, smul_eq_mul, hB0 w' hw', mul_zero]
    · refine isPrincipal_iff_eq_divOf.mpr ⟨g' * fr ^ n, mul_ne_zero hg'0 (pow_ne_zero _ hfr0), ?_⟩
      rw [divOf_mul hg'0 (pow_ne_zero _ hfr0), divOf_pow, ← hnD']
      have : B = D' + divOf fr := by
        rw [hD'B, divOf_inv]
        abel
      rw [this, smul_add]
  obtain ⟨g, hg0, hg⟩ := hprin
  refine ⟨R₀, fr⁻¹, inv_ne_zero hfr0, ⟨g, hg0, fun v => ?_⟩, fun v v' hv' => ?_, fun v' hv' => ?_⟩
  · have := hg v
    simpa only [Finsupp.smul_apply, smul_eq_mul] using this
  · have hw : v' = lift v := hU v v' (lift v) hv' (hliftOver v)
    rw [hD'B, Finsupp.add_apply, divOf_apply (inv_ne_zero hfr0), hw, hR₀v v]
  · rw [hD'B, Finsupp.add_apply, divOf_apply (inv_ne_zero hfr0), hB0 v' hv', zero_add]

end Main

end TorsionDescentDeriv
p2m_reactivate "P2MW.S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension.AlgebraicCurve.TorsionDescentDeriv"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension.AlgebraicCurve.TorsionDescentDeriv P2MW.S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension.AlgebraicCurve"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension.AlgebraicCurve"

theorem solution
    (K F K' F' : Type*) [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (n : ℕ) (hn : n ≠ 0) (D' : Divisor K' F')
    (hD' : ∃ g' : F', g' ≠ 0 ∧ ∀ v' : Place K' F', (n : ℤ) * D' v' = v'.ord g') :
    ∃ (D : Divisor K F) (h' : F'), h' ≠ 0 ∧
      (∃ g : F, g ≠ 0 ∧ ∀ v : Place K F, (n : ℤ) * D v = v.ord g) ∧
      (∀ (v : Place K F) (v' : Place K' F'),
        v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring →
          D' v' = D v + v'.ord h') ∧
      (∀ v' : Place K' F',
        (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
          D' v' = v'.ord h') :=
  AlgebraicCurve.TorsionDescentDeriv.main hfg hfg' hgen n hn D' hD'

end S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension (solution)
