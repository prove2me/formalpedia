-- Prove2me | solution 1 for AlgebraicCurve.Divisor.exists_torsion_descent_of_constantFieldExtension_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/f794c0f6-3b11-5fff-90cd-6c07ca7c98de

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Divisor_isPrincipal_of_constantFieldExtension
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
import Theorems.Thm_IsAlgClosed_exists_algEquiv_apply_eq_add_algebraMap_of_transcendental
import Theorems.Thm_AlgebraicCurve_SemilinearAut_exists_baseAut_eq_of_constantFieldExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension_of_finite
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension_of_finite.AlgebraicCurve"
open scoped Pointwise

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.ord_one Place.ord_mul Place.ord_inv Divisor Divisor.degree Divisor.degree_single Divisor.degZero Divisor.mem_degZero Divisor.principal HasPrincipalDivisors Pic Pic0 Pic0.mk HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed LSpace ell mem_lSpace_iff_ord algebraMap_mem_lSpace_zero ConstantsAreBase indexOfSpecialty SemilinearAut SemilinearAut.baseAut SemilinearAut.smul_algebraMap SemilinearAut.smul_toValuationSubring SemilinearAut.ord_smul SemilinearAut.smul_single SemilinearAut.divisor_smul_apply_smul SemilinearAut.divisor_smul_apply SemilinearAut.degree_smul SemilinearAut.smul_mem_principal Place.exists_comap_algebraMap_eq_of_constantFieldExtension Divisor.isPrincipal_of_constantFieldExtension Place.exists_of_valuationSubring Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed Place.deg_eq_one_iff_surjective_algebraMap_residueField exists_genus_riemannIndex_of_isCurveOver ell_le_ell_sub_single_add_deg finiteDimensional_lSpace RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase lSpace_eq_bot_of_degree_neg Place.exists_ord_neg_of_transcendental Place.ord_algebraMap Place.ord_smul_of_ne_zero Place.min_ord_le_ord_add Place.mem_iff_ord_nonneg Place.mk_mem_maximalIdeal_iff essFiniteType_of_transcendental_of_finiteDimensional SemilinearAut.exists_baseAut_eq_of_constantFieldExtension"
p2m_open "AlgebraicCurve"

namespace TorsionDescentFin

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

theorem ord_smul_eq (g : SemilinearAut K F) (w : Place K F) (f : F) :
    w.ord (g • f) = (g⁻¹ • w).ord f := by
  conv_lhs => rw [← smul_inv_smul g w]
  exact SemilinearAut.ord_smul g (g⁻¹ • w) f

theorem smul_divOf [HasPrincipalDivisors K F] (g : SemilinearAut K F) (f : F) :
    g • divOf (K := K) f = divOf (g • f) := by
  by_cases hf : f = 0
  · subst hf; simp
  have hgf : g • f ≠ 0 := by
    intro h
    exact hf ((smul_eq_zero_iff_eq g).mp h)
  ext w
  rw [SemilinearAut.divisor_smul_apply, divOf_apply hf, divOf_apply hgf, ord_smul_eq]

theorem pow_smul_eq_self {α : Type*} [MulAction (SemilinearAut K F) α] {g : SemilinearAut K F}
    {a : α} (h : g • a = a) (k : ℕ) : g ^ k • a = a := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_smul, h, ih]

theorem smul_zsmul_divisor (g : SemilinearAut K F) (m : ℤ) (D : Divisor K F) :
    g • (m • D) = m • (g • D) :=
  (DistribSMul.toAddMonoidHom (Divisor K F) g).map_zsmul m D

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

theorem smul_mem_lSpace_iff (g : SemilinearAut K F) {D : Divisor K F} {y : F} :
    g • y ∈ LSpace (g • D) ↔ y ∈ LSpace D := by
  rw [mem_lSpace_iff_ord, mem_lSpace_iff_ord, smul_eq_zero_iff_eq]
  refine or_congr Iff.rfl ⟨fun h v => ?_, fun h w => ?_⟩
  · have := h (g • v)
    rwa [SemilinearAut.divisor_smul_apply_smul, SemilinearAut.ord_smul] at this
  · rw [SemilinearAut.divisor_smul_apply, ord_smul_eq]
    exact h _

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

theorem smul_reduced_eq [HasPrincipalDivisors K F] (g : SemilinearAut K F)
    {c : Divisor K F} {r : ℤ} {P : Place K F} {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ LSpace (c + r • Finsupp.single P 1))
    (huniq : ∀ h ∈ LSpace (c + r • Finsupp.single P 1), ∃ a : K, a • f = h)
    (hP : g • P = P) (hc : g • c - c ∈ Divisor.principal) :
    g • (c + r • Finsupp.single P 1 + divOf f) = c + r • Finsupp.single P 1 + divOf f := by
  obtain ⟨u, hu0, hu⟩ := mem_principal_iff_eq_divOf.mp hc
  set D := c + r • Finsupp.single P 1 with hD
  have hgc : g • c = c + divOf u := by rw [← hu]; abel
  have hgD : g • D = D + divOf u := by
    simp only [hD, smul_add, smul_zsmul_divisor, SemilinearAut.smul_single, hP, hgc]
    abel
  have h1 : g • f ∈ LSpace (g • D) := (smul_mem_lSpace_iff g).mpr hf
  rw [hgD, mem_lSpace_add_divOf_iff hu0] at h1
  obtain ⟨a, ha⟩ := huniq _ h1
  have hgf : g • f ≠ 0 := fun h => hf0 ((smul_eq_zero_iff_eq g).mp h)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact mul_ne_zero hgf hu0 ha.symm
  rw [smul_add, hgD, smul_divOf, add_assoc, add_comm (divOf u), ← divOf_mul hgf hu0, ← ha,
    divOf_smul_const ha0]

end General

section Extension

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
  [Algebra F F']

def LiesOver (w' : Place K' F') (v : Place K F) : Prop :=
  w'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring

def IsGeneric (K F : Type*) [Field K] [Field F] [Algebra K F] [Algebra F F']
    (w' : Place K' F') : Prop :=
  ∀ v : Place K F, ¬ LiesOver w' v

def FixesF (F : Type*) [Field F] [Algebra F F'] (g : SemilinearAut K' F') : Prop :=
  ∀ y : F, g • algebraMap F F' y = algebraMap F F' y

namespace FixesF

variable {g h : SemilinearAut K' F'}

theorem one : FixesF F (1 : SemilinearAut K' F') := fun _ => one_smul _ _

theorem mul (hg : FixesF F g) (hh : FixesF F h) : FixesF F (g * h) := fun y => by
  rw [mul_smul, hh y, hg y]

theorem inv (hg : FixesF F g) : FixesF F g⁻¹ := fun y => by
  rw [inv_smul_eq_iff, hg y]

theorem pow (hg : FixesF F g) (k : ℕ) : FixesF F (g ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact one
  | succ k ih => rw [pow_succ]; exact ih.mul hg

theorem comap_smul (hg : FixesF F g) (w' : Place K' F') :
    (g • w').toValuationSubring.comap (algebraMap F F') =
      w'.toValuationSubring.comap (algebraMap F F') := by
  ext y
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
    SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    hg.inv y]

theorem liesOver_smul_iff (hg : FixesF F g) {w' : Place K' F'} {v : Place K F} :
    LiesOver (g • w') v ↔ LiesOver w' v := by
  rw [LiesOver, LiesOver, hg.comap_smul]

theorem isGeneric_smul_iff (hg : FixesF F g) {w' : Place K' F'} :
    IsGeneric K F (g • w') ↔ IsGeneric K F w' := by
  simp only [IsGeneric, hg.liesOver_smul_iff]

theorem smul_eq_of_liesOver (hg : FixesF F g)
    (hU : ∀ (v : Place K F) (w₁ w₂ : Place K' F'), LiesOver w₁ v → LiesOver w₂ v → w₁ = w₂)
    {w' : Place K' F'} {v : Place K F} (hw : LiesOver w' v) : g • w' = w' :=
  hU v _ _ (hg.liesOver_smul_iff.mpr hw) hw

end FixesF

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

theorem InMax.sub {w : Place K' F'} {a b : F'} (ha : InMax w a) (hb : InMax w b) :
    InMax w (a - b) := by
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · left; simp
    · right; rwa [zero_sub, ← neg_one_smul K' b, Place.ord_smul_of_ne_zero w (by norm_num) b]
  rcases hb with rfl | hb
  · right; rwa [sub_zero]
  by_cases hab : a - b = 0
  · exact Or.inl hab
  right
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have hb0 : -b ≠ 0 := by
    intro h; rw [neg_eq_zero] at h; subst h; simp at hb
  have hnb : 0 < w.ord (-b) := by
    rwa [← neg_one_smul K' b, Place.ord_smul_of_ne_zero w (by norm_num) b]
  have := Place.min_ord_le_ord_add w ha0 hb0 (by rwa [← sub_eq_add_neg])
  rw [← sub_eq_add_neg] at this
  exact lt_of_lt_of_le (lt_min ha hnb) this

theorem InMax.eq_zero_of_algebraMap {w : Place K' F'} {c : K'} (h : InMax w (algebraMap K' F' c)) :
    c = 0 := by
  rcases h with h | h
  · simpa using h
  · rw [Place.ord_algebraMap] at h
    exact absurd h (lt_irrefl 0)

theorem InMax.smul_iff (g : SemilinearAut K' F') {w : Place K' F'} {y : F'} :
    InMax (g • w) (g • y) ↔ InMax w y := by
  simp only [InMax, SemilinearAut.ord_smul, smul_eq_zero_iff_eq]

theorem injective_pow_smul [CharZero K'] (g : SemilinearAut K' F') (w : Place K' F') (y : F')
    (hy : InMax w y) (hg : ∀ k : ℕ, g ^ k • y = y - algebraMap K' F' k) :
    Function.Injective fun k : ℕ => g ^ k • w := by
  intro i j hij
  simp only at hij
  have hi : InMax (g ^ i • w) (y - algebraMap K' F' i) := by
    rw [← hg i]; exact (InMax.smul_iff _).mpr hy
  have hj : InMax (g ^ i • w) (y - algebraMap K' F' j) := by
    rw [hij, ← hg j]; exact (InMax.smul_iff _).mpr hy
  have h := hi.sub hj
  rw [show y - algebraMap K' F' (i : K') - (y - algebraMap K' F' (j : K')) =
      algebraMap K' F' ((j : K') - i) by rw [map_sub]; ring] at h
  have := h.eq_zero_of_algebraMap
  exact_mod_cast (sub_eq_zero.mp this).symm

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

theorem pow_smul_sub_algebraMap (ρ : SemilinearAut K' F') {X : F'} (hX : ρ • X = X) {t a : K'}
    (ht : SemilinearAut.baseAut ρ t = t + a) (ha : SemilinearAut.baseAut ρ a = a) (m : ℕ) :
    ρ ^ m • (X - algebraMap K' F' t) = X - algebraMap K' F' t - algebraMap K' F' (m * a) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_smul, ih, smul_sub, smul_sub, hX, SemilinearAut.smul_algebraMap,
      SemilinearAut.smul_algebraMap, ht, map_mul, ha, map_natCast]
    push_cast
    ring

end Extension

section Pigeonhole

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem pow_mul_smul_sub_mem_principal (g : SemilinearAut K F) (D : Divisor K F) (m : ℕ)
    (h : g ^ m • D - D ∈ Divisor.principal) (q : ℕ) :
    g ^ (m * q) • D - D ∈ Divisor.principal := by
  induction q with
  | zero => simp [zero_mem]
  | succ q ih =>
    have heq : g ^ (m * (q + 1)) • D - D = g ^ m • (g ^ (m * q) • D - D) + (g ^ m • D - D) := by
      rw [Nat.mul_succ, pow_add, pow_mul_comm, mul_smul, smul_sub]
      abel
    rw [heq]
    exact add_mem (SemilinearAut.smul_mem_principal _ ih) h

theorem pow_factorial_smul_sub_mem_principal (g : SemilinearAut K F) (D : Divisor K F) (n : ℕ)
    [Finite {c : Pic0 K F // n • c = 0}]
    (hdeg : ∀ k : ℕ, Divisor.degree (g ^ k • D - D) = 0)
    (htor : ∀ k : ℕ, n • (g ^ k • D - D) ∈ Divisor.principal) :
    g ^ (Nat.card {c : Pic0 K F // n • c = 0}).factorial • D - D ∈ Divisor.principal := by
  classical
  set M := Nat.card {c : Pic0 K F // n • c = 0} with hM
  let dz : ℕ → Divisor.degZero (K := K) (F := F) := fun k =>
    ⟨g ^ k • D - D, Divisor.mem_degZero.mpr (hdeg k)⟩
  have hcl0 : ∀ k, n • (Pic0.mk (dz k)) = 0 := fun k => by
    show n • (QuotientAddGroup.mk (dz k) : Pic0 K F) = 0
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact htor k
  let cl : Fin (M + 1) → {c : Pic0 K F // n • c = 0} := fun i => ⟨Pic0.mk (dz i), hcl0 i⟩
  have hnotinj : ¬ Function.Injective cl := by
    intro hinj
    have h := Nat.card_le_card_of_injective cl hinj
    rw [← hM, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    omega
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hnotinj
  have hstep : ∀ a m : ℕ, Pic0.mk (dz a) = Pic0.mk (dz (a + m)) →
      g ^ m • D - D ∈ Divisor.principal := by
    intro a m h
    have h2 : -(dz a) + dz (a + m) ∈ (Divisor.principal).addSubgroupOf Divisor.degZero :=
      QuotientAddGroup.eq.mp h
    have h3 : -(g ^ a • D - D) + (g ^ (a + m) • D - D) ∈ Divisor.principal (K := K) (F := F) :=
      AddSubgroup.mem_addSubgroupOf.mp h2
    rw [pow_add] at h3
    have h4 : (g ^ a)⁻¹ • (-(g ^ a • D - D) + ((g ^ a * g ^ m) • D - D)) = g ^ m • D - D := by
      rw [mul_smul, smul_add, smul_neg, smul_sub, smul_sub, inv_smul_smul, inv_smul_smul]
      abel
    exact h4 ▸ SemilinearAut.smul_mem_principal _ h3
  have hij' : Pic0.mk (dz i) = Pic0.mk (dz j) := congrArg Subtype.val hij
  have hne' : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
  obtain ⟨m, hm0, hmM, hm⟩ : ∃ m : ℕ, 0 < m ∧ m ≤ M ∧ g ^ m • D - D ∈ Divisor.principal := by
    rcases lt_or_gt_of_ne hne' with hlt | hlt
    · refine ⟨j - i, Nat.sub_pos_of_lt hlt, ?_, hstep i (j - i) ?_⟩
      · have := j.isLt; omega
      · rw [Nat.add_sub_cancel' hlt.le]; exact hij'
    · refine ⟨i - j, Nat.sub_pos_of_lt hlt, ?_, hstep j (i - j) ?_⟩
      · have := i.isLt; omega
      · rw [Nat.add_sub_cancel' hlt.le]; exact hij'.symm
  obtain ⟨q, hq⟩ := Nat.dvd_factorial hm0 hmM
  rw [hq]
  exact pow_mul_smul_sub_mem_principal g D m hm q

end Pigeonhole

section Main

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
  [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']

theorem main [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (n : ℕ) (_hn : n ≠ 0) [Finite {c : Pic0 K' F' // n • c = 0}] (D' : Divisor K' F')
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
  obtain ⟨g', hg'0, hg'⟩ := hD'
  have hnD' : (n : ℤ) • D' = divOf g' := by
    ext w
    rw [Finsupp.smul_apply, smul_eq_mul, hg' w, divOf_apply hg'0]

  set N : ℕ := (Nat.card {c : Pic0 K' F' // n • c = 0}).factorial with hN_def
  have hN : N ≠ 0 := Nat.factorial_ne_zero _

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

  have hEfix : ∀ g : SemilinearAut K' F', FixesF F g → g ^ N • D' - D' ∈ Divisor.principal := by
    intro g _
    refine pow_factorial_smul_sub_mem_principal g D' n (fun k => ?_) (fun k => ?_)
    · rw [map_sub, SemilinearAut.degree_smul, sub_self]
    · have hgk : g ^ k • g' ≠ 0 := fun h => hg'0 ((smul_eq_zero_iff_eq _).mp h)
      refine mem_principal_iff_eq_divOf.mpr ⟨g ^ k • g' * g'⁻¹, mul_ne_zero hgk (inv_ne_zero hg'0), ?_⟩
      rw [← natCast_zsmul, smul_sub, ← smul_zsmul_divisor, hnD', smul_divOf,
        divOf_mul hgk (inv_ne_zero hg'0), divOf_inv]
      abel

  set d : ℤ := Divisor.degree D' with hd
  set c₀ : Divisor K' F' := D' - d • Finsupp.single P₀ 1 with hc₀
  have hc₀deg : Divisor.degree c₀ = 0 := by
    simp only [hc₀, map_sub, map_zsmul, Divisor.degree_single, hdegP₀, Nat.cast_one, mul_one,
      smul_eq_mul, hd]
    ring
  obtain ⟨r, fr, hfr0, hfrmem, hfruniq⟩ := exists_reduced (K := K') (F := F') x' hx' c₀ hc₀deg P₀
  set A : Divisor K' F' := c₀ + (r : ℤ) • Finsupp.single P₀ 1 + divOf fr with hA
  have hAfix : ∀ g : SemilinearAut K' F', FixesF F g → g ^ N • A = A := by
    intro g hg
    have hgP : g ^ N • P₀ = P₀ := (hg.pow N).smul_eq_of_liesOver hU hP₀
    apply smul_reduced_eq (g ^ N) hfr0 hfrmem hfruniq hgP
    have : g ^ N • c₀ - c₀ = g ^ N • D' - D' := by
      simp only [hc₀, smul_sub, smul_zsmul_divisor, SemilinearAut.smul_single, hgP]
      abel
    rw [this]
    exact hEfix g hg

  have hAsupp : ∀ w' ∈ A.support, ¬ IsGeneric K F w' := by
    intro w' hw' hgw
    obtain ⟨t, ht⟩ := hgw.exists_inMax_sub x
    have htK : t ∉ Set.range (algebraMap K K') := hgw.not_mem_range x hx ht
    have httr : Transcendental K t := transcendental_of_not_mem_range htK
    obtain ⟨τ, hτ⟩ := IsAlgClosed.exists_algEquiv_apply_eq_add_algebraMap_of_transcendental K K' t
      httr (N : K)⁻¹
    obtain ⟨ρ, hρτ, hρF⟩ :=
      SemilinearAut.exists_baseAut_eq_of_constantFieldExtension K F K' F' hfg hfg' hgen τ
    set σ := ρ ^ N with hσ
    have hσA : σ • A = A := hAfix ρ hρF
    set y : F' := algebraMap F F' x - algebraMap K' F' t with hy
    have hρt : SemilinearAut.baseAut ρ t = t + algebraMap K K' (N : K)⁻¹ := by rw [hρτ, hτ]
    have hρa : SemilinearAut.baseAut ρ (algebraMap K K' (N : K)⁻¹) = algebraMap K K' (N : K)⁻¹ := by
      rw [hρτ, AlgEquiv.commutes]
    have hρm : ∀ m : ℕ, ρ ^ m • y = y - algebraMap K' F' (m * algebraMap K K' (N : K)⁻¹) :=
      fun m => pow_smul_sub_algebraMap ρ (hρF x) hρt hρa m
    have hNK' : (N : K') ≠ 0 := Nat.cast_ne_zero.mpr hN
    have hσy : ∀ k : ℕ, σ ^ k • y = y - algebraMap K' F' k := by
      intro k
      rw [hσ, ← pow_mul, hρm (N * k)]
      congr 2
      rw [map_inv₀, map_natCast]
      push_cast
      field_simp
    have hinj := injective_pow_smul σ w' y ht hσy
    have hmem : ∀ k : ℕ, σ ^ k • w' ∈ (A.support : Set (Place K' F')) := by
      intro k
      have hk : σ ^ k • A = A := pow_smul_eq_self hσA k
      rw [Finset.mem_coe, Finsupp.mem_support_iff, ← hk, SemilinearAut.divisor_smul_apply_smul]
      exact Finsupp.mem_support_iff.mp hw'
    exact Set.infinite_of_injective_forall_mem hinj hmem (A.support.finite_toSet)

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

end TorsionDescentFin
p2m_reactivate "P2MW.S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension_of_finite.AlgebraicCurve.TorsionDescentFin"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension_of_finite.AlgebraicCurve.TorsionDescentFin P2MW.S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension_of_finite.AlgebraicCurve"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension_of_finite.AlgebraicCurve"

theorem solution
    (K F K' F' : Type*) [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (n : ℕ) (hn : n ≠ 0) (hfin : Finite {c : Pic0 K' F' // n • c = 0}) (D' : Divisor K' F')
    (hD' : ∃ g' : F', g' ≠ 0 ∧ ∀ v' : Place K' F', (n : ℤ) * D' v' = v'.ord g') :
    ∃ (D : Divisor K F) (h' : F'), h' ≠ 0 ∧
      (∃ g : F, g ≠ 0 ∧ ∀ v : Place K F, (n : ℤ) * D v = v.ord g) ∧
      (∀ (v : Place K F) (v' : Place K' F'),
        v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring →
          D' v' = D v + v'.ord h') ∧
      (∀ v' : Place K' F',
        (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
          D' v' = v'.ord h') :=
  haveI := hfin
  AlgebraicCurve.TorsionDescentFin.main hfg hfg' hgen n hn D' hD'

end S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension_of_finite
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension_of_finite (solution)
