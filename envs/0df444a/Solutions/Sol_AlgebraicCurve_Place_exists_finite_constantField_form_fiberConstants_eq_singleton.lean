-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_finite_constantField_form_fiberConstants_eq_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/abf26218-2b81-58c2-bc72-bfe4206a8d2a

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension
import Theorems.Thm_AlgebraicCurve_constantFieldDegreeFormula_of_isConstantFieldExtension_of_isCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_finite_constantField_form_fiberConstants_eq_singleton
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_exists_finite_constantField_form_fiberConstants_eq_singleton.AlgebraicCurve IntermediateField"

universe u v

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Divisor Divisor.degree_single IsCurveOver IsCurveOver.finite_residueField Place.forgetConstants Place.restrictConstants Place.fiberConstants Place.mem_fiberConstants Divisor.pullbackConstants_single ConstantFieldDegreeFormula ConstantFieldDegreeFormula.degree_pullbackConstants LSpace algebraMap_mem_lSpace_zero ConstantsAreBase IsCurveOver.exists_separating_transcendental isCurveOver_of_transcendental essFiniteType_of_transcendental_of_finiteDimensional Place.ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension constantFieldDegreeFormula_of_isConstantFieldExtension_of_isCurveOver"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg ord ord_zero ord_mul ord_inv ord_coe_irreducible ord_zpow ne_top' algebraMap_mem' toValuationSubring forgetConstants restrictConstants fiberConstants mem_fiberConstants ramificationIndex adicValuation_le_one_of_mem adicValuation_le_one_iff mem_iff_adicValuation_le_one ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension"
namespace FiniteConstantFieldFormAux
p2m_open "AlgebraicCurve.Place~ord_nonneg_of_mem~mem_of_ord_nonneg AlgebraicCurve"

theorem isAlgebraic_of_forall_pow_pow_eq (K K' : Type*) [Field K] [Field K'] [Algebra K K']
    (ℓ : ℕ) [Fact ℓ.Prime] (halg : ∀ a : K', ∃ n : ℕ, 0 < n ∧ a ^ ℓ ^ n = a) :
    Algebra.IsAlgebraic K K' := by
  refine ⟨fun a => ?_⟩
  obtain ⟨n, hn, ha⟩ := halg a
  refine ⟨Polynomial.X ^ ℓ ^ n - Polynomial.X, ?_, ?_⟩
  · exact FiniteField.X_pow_card_pow_sub_X_ne_zero K hn.ne' (Fact.out : ℓ.Prime).one_lt
  · simp only [map_sub, map_pow, Polynomial.aeval_X, ha, sub_self]

theorem perfectField_of_forall_pow_pow_eq (K' : Type*) [Field K'] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K' ℓ]
    (halg : ∀ a : K', ∃ n : ℕ, 0 < n ∧ a ^ ℓ ^ n = a) : PerfectField K' := by
  haveI : ExpChar K' ℓ := ExpChar.prime Fact.out
  haveI : PerfectRing K' ℓ := PerfectRing.ofSurjective K' ℓ fun a => by
    obtain ⟨n, hn, ha⟩ := halg a
    refine ⟨a ^ ℓ ^ (n - 1), ?_⟩
    rw [frobenius_def, ← pow_mul, ← pow_succ, Nat.sub_add_cancel hn, ha]
  exact PerfectRing.toPerfectField K' ℓ

section PlaceBasics

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_iff_zero_or_ord_nonneg (v : Place K F) (f : F) :
    f ∈ v.toValuationSubring ↔ f = 0 ∨ 0 ≤ v.ord f := by
  rw [v.mem_iff_adicValuation_le_one, v.adicValuation_le_one_iff]

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring :=
  (mem_iff_zero_or_ord_nonneg v f).mpr (Or.inr h)

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ≠ 0) (h : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f :=
  ((mem_iff_zero_or_ord_nonneg v f).mp h).resolve_left hf

theorem exists_mem_and_not_mem_of_ne {w w' : Place K F} (h : w ≠ w') :
    ∃ f : F, f ∈ w.toValuationSubring ∧ f ∉ w'.toValuationSubring := by
  by_contra hcon
  push_neg at hcon
  have hle : ∀ f : F, f ∈ w.toValuationSubring → f ∈ w'.toValuationSubring := hcon

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hπ1 : w.ord (π : F) = 1 := w.ord_coe_irreducible hπ
  have hπ0 : (π : F) ≠ 0 := by
    intro h0; have := hπ1; rw [h0, w.ord_zero] at this; exact zero_ne_one this

  have hne : w'.toValuationSubring ≠ w.toValuationSubring := fun heq => h (Place.ext heq.symm)
  obtain ⟨x, hxw', hxw⟩ : ∃ x : F, x ∈ w'.toValuationSubring ∧ x ∉ w.toValuationSubring := by
    by_contra hc
    push_neg at hc
    exact hne (le_antisymm (fun f hf => hc f hf) (fun f hf => hle f hf))
  have hx0 : x ≠ 0 := by rintro rfl; exact hxw (zero_mem _)
  have hxord : w.ord x < 0 := by
    by_contra hc; push_neg at hc; exact hxw (mem_of_ord_nonneg w hc)

  set n : ℤ := -w.ord x with hn
  have hy : w.ord (x * (π : F) ^ n) = 0 := by
    rw [w.ord_mul hx0 (zpow_ne_zero _ hπ0), w.ord_zpow, hπ1, mul_one, hn]; ring
  have hy0 : x * (π : F) ^ n ≠ 0 := mul_ne_zero hx0 (zpow_ne_zero _ hπ0)
  have hyinv : w.ord (x * (π : F) ^ n)⁻¹ = 0 := by rw [w.ord_inv, hy, neg_zero]
  have hyinv_mem' : (x * (π : F) ^ n)⁻¹ ∈ w'.toValuationSubring :=
    hle _ (mem_of_ord_nonneg w (le_of_eq hyinv.symm))

  have hπw' : 0 ≤ w'.ord (π : F) :=
    ord_nonneg_of_mem w' hπ0 (hle _ (mem_of_ord_nonneg w (by rw [hπ1]; exact zero_le_one)))
  have hzmem : (π : F) ^ (-n) ∈ w'.toValuationSubring := by
    have : (π : F) ^ (-n) = x * (x * (π : F) ^ n)⁻¹ := by
      rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul, ← zpow_neg]
    rw [this]
    exact mul_mem hxw' hyinv_mem'
  have hπw'0 : w'.ord (π : F) = 0 := by
    have h1 := ord_nonneg_of_mem w' (zpow_ne_zero _ hπ0) hzmem
    rw [w'.ord_zpow] at h1
    have hnpos : 0 < n := by omega
    nlinarith

  apply w'.ne_top'
  refine eq_top_iff.mpr fun f _ => ?_
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  have hsplit : f = (f * (π : F) ^ (-w.ord f)) * (π : F) ^ (w.ord f) := by
    rw [mul_assoc, ← zpow_add₀ hπ0, neg_add_cancel, zpow_zero, mul_one]
  rw [hsplit]
  refine mul_mem (hle _ (mem_of_ord_nonneg w ?_)) (mem_of_ord_nonneg w' ?_)
  · rw [w.ord_mul hf0 (zpow_ne_zero _ hπ0), w.ord_zpow, hπ1]; ring_nf; exact le_refl _
  · rw [w'.ord_zpow, hπw'0, mul_zero]

end PlaceBasics

section Square

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
  [Algebra K F] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F']

theorem restrictConstants_eq_iff (w w' : Place K' F') :
    restrictConstants F (K := K) w = restrictConstants F (K := K) w' ↔
      ∀ f : F, algebraMap F F' f ∈ w.toValuationSubring ↔ algebraMap F F' f ∈ w'.toValuationSubring := by
  constructor
  · intro h f
    have := congrArg (fun v : Place K F => f ∈ v.toValuationSubring) h
    simpa using this
  · intro h
    refine Place.ext ?_
    ext f
    exact h f

theorem constantsAreBase_of_forall (hC' : ConstantsAreBase K' F')
    (h : ∀ a : K', algebraMap K' F' a ∈ Set.range (algebraMap F F') → a ∈ Set.range (algebraMap K K')) :
    ConstantsAreBase K F := by
  refine le_antisymm ?_ ?_
  · intro f hf
    have hf' : algebraMap F F' f ∈ LSpace (0 : Divisor K' F') := by
      intro W
      rw [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero]
      refine W.adicValuation_le_one_of_mem ?_
      have hfv := hf (restrictConstants F (K := K) W)
      rw [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero] at hfv
      have : f ∈ (restrictConstants F (K := K) W).toValuationSubring :=
        ((restrictConstants F (K := K) W).mem_iff_adicValuation_le_one).mpr hfv
      exact this
    have hC'' : LSpace (0 : Divisor K' F') = LinearMap.range (Algebra.linearMap K' F') := hC'
    rw [hC''] at hf'
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hf'
    obtain ⟨k, hk⟩ := h a ⟨f, ha.symm⟩
    refine LinearMap.mem_range.mpr ⟨k, ?_⟩
    apply (algebraMap F F').injective
    show algebraMap F F' (algebraMap K F k) = algebraMap F F' f
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K K' F', hk]
    exact ha
  · rintro _ ⟨k, rfl⟩
    exact algebraMap_mem_lSpace_zero k

theorem mem_range_of_isAlgebraic_of_constantsAreBase
    (hC : ConstantsAreBase K F) (y : F) (hy : IsAlgebraic K y) : y ∈ (algebraMap K F).range := by
  have hint : IsIntegral K y := hy.isIntegral
  have hmem : y ∈ LSpace (0 : Divisor K F) := by
    intro v
    rw [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero]
    refine v.adicValuation_le_one_of_mem ?_
    have hint' : IsIntegral v.toValuationSubring y := hint.tower_top
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
    rw [← hz]
    exact z.2
  have hC' : LSpace (0 : Divisor K F) = LinearMap.range (Algebra.linearMap K F) := hC
  rw [hC'] at hmem
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hmem
  exact ⟨c, hc⟩

end Square

section Level

variable (K' : Type u) (F' : Type v) [Field K'] [Field F'] [Algebra K' F']
  (ℓ : ℕ) [Fact ℓ.Prime] [CharP K' ℓ]

attribute [local instance] ZMod.algebra

abbrev Klvl (S : Finset K') : IntermediateField (ZMod ℓ) K' :=
  IntermediateField.adjoin (ZMod ℓ) (S : Set K')

abbrev Flvl (S : Finset K') (T : Finset F') : IntermediateField (Klvl K' ℓ S) F' :=
  IntermediateField.adjoin (Klvl K' ℓ S) (T : Set F')

variable {K' ℓ} in
theorem finite_Klvl (halg : ∀ a : K', ∃ n : ℕ, 0 < n ∧ a ^ ℓ ^ n = a) (S : Finset K') :
    Finite (Klvl K' ℓ S) := by
  haveI : Algebra.IsAlgebraic (ZMod ℓ) K' := isAlgebraic_of_forall_pow_pow_eq (ZMod ℓ) K' ℓ halg
  haveI : FiniteDimensional (ZMod ℓ) (Klvl K' ℓ S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  exact Module.finite_of_finite (ZMod ℓ)

theorem range_algebraMap_Klvl (S : Finset K') :
    Set.range (algebraMap (Klvl K' ℓ S) F') = algebraMap K' F' '' (Klvl K' ℓ S : Set K') := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, a.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

theorem coe_Flvl (S : Finset K') (T : Finset F') :
    ((Flvl K' F' ℓ S T : IntermediateField (Klvl K' ℓ S) F') : Set F')
      = Subfield.closure (algebraMap K' F' '' (Klvl K' ℓ S : Set K') ∪ (T : Set F')) := by
  rw [← range_algebraMap_Klvl]
  show ((Flvl K' F' ℓ S T).toSubfield : Set F') = _
  rw [IntermediateField.adjoin_toSubfield]

theorem coe_Flvl_mono {S S' : Finset K'} {T T' : Finset F'} (hS : S ⊆ S') (hT : T ⊆ T') :
    ((Flvl K' F' ℓ S T : IntermediateField (Klvl K' ℓ S) F') : Set F')
      ⊆ ((Flvl K' F' ℓ S' T' : IntermediateField (Klvl K' ℓ S') F') : Set F') := by
  rw [coe_Flvl, coe_Flvl]
  refine Subfield.closure_mono (Set.union_subset_union (Set.image_mono ?_) (by exact_mod_cast hT))
  exact IntermediateField.adjoin.mono _ _ _ (by exact_mod_cast hS)

theorem algebraMap_mem_Flvl {S : Finset K'} (T : Finset F') {a : K'} (ha : a ∈ Klvl K' ℓ S) :
    algebraMap K' F' a ∈ Flvl K' F' ℓ S T :=
  IntermediateField.algebraMap_mem (Flvl K' F' ℓ S T) (⟨a, ha⟩ : Klvl K' ℓ S)

theorem mem_Flvl_of_mem {S : Finset K'} {T : Finset F'} {f : F'} (hf : f ∈ T) :
    f ∈ Flvl K' F' ℓ S T :=
  IntermediateField.subset_adjoin _ _ (by exact_mod_cast hf)

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem level_core (halg : ∀ a : K', ∃ n : ℕ, 0 < n ∧ a ^ ℓ ^ n = a)
    {t : F'} (ht : Transcendental K' t) (hfd : FiniteDimensional K'⟮t⟯ F')
    (hsep : Algebra.IsSeparable K'⟮t⟯ F') (S : Finset K') (T : Finset F') (htT : t ∈ T) :
    ∃ x : Flvl K' F' ℓ S T, (x : F') = t ∧ Transcendental (Klvl K' ℓ S) x ∧
      FiniteDimensional (IntermediateField.adjoin (Klvl K' ℓ S) ({x} : Set (Flvl K' F' ℓ S T)))
        (Flvl K' F' ℓ S T) ∧
      Algebra.IsSeparable (IntermediateField.adjoin (Klvl K' ℓ S) ({x} : Set (Flvl K' F' ℓ S T)))
        (Flvl K' F' ℓ S T) ∧
      Algebra.IsAlgebraic (Flvl K' F' ℓ S T) F' := by

  set K : IntermediateField (ZMod ℓ) K' := Klvl K' ℓ S with hKdef
  set F : IntermediateField K F' := Flvl K' F' ℓ S T with hFdef
  haveI : Finite K := finite_Klvl halg S
  haveI : PerfectField K := inferInstance
  haveI : Algebra.IsAlgebraic K K' := isAlgebraic_of_forall_pow_pow_eq K K' ℓ halg
  haveI : Algebra.IsSeparable K K' := inferInstance

  set L : IntermediateField K F' := IntermediateField.adjoin K ({t} : Set F') with hLdef

  set N : IntermediateField L F' := IntermediateField.adjoin L (Set.range (algebraMap K' F')) with hNdef

  have hgenN : ∀ y ∈ Set.range (algebraMap K' F'), IsSeparable L y ∧ IsIntegral L y := by
    rintro _ ⟨a, rfl⟩
    have hs : IsSeparable K (algebraMap K' F' a) := by
      unfold IsSeparable
      rw [show algebraMap K' F' a = IsScalarTower.toAlgHom K K' F' a from rfl,
        minpoly.algHom_eq _ (algebraMap K' F').injective]
      exact Algebra.IsSeparable.isSeparable K a
    have hi : IsIntegral K (algebraMap K' F' a) :=
      (Algebra.IsIntegral.isIntegral (R := K) a).map (IsScalarTower.toAlgHom K K' F')
    exact ⟨hs.tower_top L, hi.tower_top⟩
  haveI hNsep : Algebra.IsSeparable L N := by
    rw [hNdef, IntermediateField.isSeparable_adjoin_iff_isSeparable]
    exact fun y hy => (hgenN y hy).1
  haveI hNalg : Algebra.IsAlgebraic L N :=
    IntermediateField.isAlgebraic_adjoin fun y hy => (hgenN y hy).2

  have hKtN : (K'⟮t⟯).toSubfield ≤ (N.restrictScalars K).toSubfield := by
    rw [IntermediateField.adjoin_toSubfield]
    refine Subfield.closure_le.mpr ?_
    rintro y (⟨a, rfl⟩ | hy)
    · exact IntermediateField.subset_adjoin L _ ⟨a, rfl⟩
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have : t ∈ L := IntermediateField.subset_adjoin K _ (Set.mem_singleton t)
      exact IntermediateField.algebraMap_mem N (⟨t, this⟩ : L)
  let φ : K'⟮t⟯ →+* N :=
    { toFun := fun y => ⟨(y : F'), hKtN y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI : Algebra K'⟮t⟯ N := φ.toAlgebra
  letI : SMul K'⟮t⟯ N := Algebra.toSMul
  letI : Module K'⟮t⟯ N := Algebra.toModule
  haveI : IsScalarTower K'⟮t⟯ N F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsSeparable N F' := Algebra.isSeparable_tower_top_of_isSeparable K'⟮t⟯ N F'
  haveI : Module.Finite N F' := Module.Finite.of_restrictScalars_finite K'⟮t⟯ N F'
  haveI hLsep : Algebra.IsSeparable L F' := Algebra.IsSeparable.trans L N F'
  haveI hLalg : Algebra.IsAlgebraic L F' := Algebra.IsAlgebraic.trans L N F'

  have hLF : L ≤ F := by
    rw [hLdef, IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact mem_Flvl_of_mem K' F' ℓ htT
  letI : Algebra L F := (IntermediateField.inclusion hLF).toAlgebra
  letI : SMul L F := Algebra.toSMul
  letI : Module L F := Algebra.toModule
  haveI : IsScalarTower L F F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower K L F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hFalg : Algebra.IsAlgebraic F F' := Algebra.IsAlgebraic.tower_top (K := L) F
  haveI hFsepL : Algebra.IsSeparable L F := Algebra.isSeparable_tower_bot_of_isSeparable L F F'
  haveI hFfinL : Module.Finite L F := by

    have hFL : IntermediateField.extendScalars hLF
        = IntermediateField.adjoin L (T : Set F') := by
      apply IntermediateField.restrictScalars_injective K
      rw [IntermediateField.extendScalars_restrictScalars, IntermediateField.restrictScalars_adjoin]
      refine le_antisymm ?_ ?_
      · exact IntermediateField.adjoin.mono _ _ _ Set.subset_union_right
      · rw [IntermediateField.adjoin_le_iff]
        rintro y (hy | hy)
        · exact hLF hy
        · exact IntermediateField.subset_adjoin _ _ hy
    haveI : FiniteDimensional L (IntermediateField.adjoin L (T : Set F')) :=
      IntermediateField.finiteDimensional_adjoin fun y _ =>
        (Algebra.IsAlgebraic.isAlgebraic (R := L) y).isIntegral
    have e : (IntermediateField.adjoin L (T : Set F')) ≃ₐ[L] IntermediateField.extendScalars hLF :=
      IntermediateField.equivOfEq hFL.symm
    exact Module.Finite.equiv e.toLinearEquiv

  have htF : t ∈ F := hLF (IntermediateField.subset_adjoin K _ (Set.mem_singleton t))
  let x : F := ⟨t, htF⟩
  have hx : (x : F') = t := rfl
  have hxtr : Transcendental K x := by
    intro hxalg
    apply ht
    have h1 : IsAlgebraic K (algebraMap F F' x) := hxalg.algHom (IsScalarTower.toAlgHom K F F')
    exact h1.tower_top K'
  set Kx : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F) with hKxdef
  have hKxL : Kx.map (IsScalarTower.toAlgHom K F F') = L := by
    rw [hKxdef, IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  let e₁ : Kx ≃ₐ[K] L :=
    (IntermediateField.equivMap Kx (IsScalarTower.toAlgHom K F F')).trans (IntermediateField.equivOfEq hKxL)
  have he₁ : ∀ y : Kx, ((e₁ y : L) : F') = ((y : F) : F') := by
    intro y
    rfl
  letI : Algebra Kx F := inferInstance

  have hcomp : (algebraMap Kx F).comp (e₁.symm : L ≃+* Kx).toRingHom
      = (RingEquiv.refl F).toRingHom.comp (algebraMap L F) := by
    ext y
    show (((e₁.symm y : Kx) : F) : F') = ((algebraMap L F y : F) : F')
    rw [← he₁ (e₁.symm y), AlgEquiv.apply_symm_apply]
    rfl
  haveI hfinKx : FiniteDimensional Kx F :=
    Module.Finite.of_equiv_equiv (e₁.symm : L ≃+* Kx) (RingEquiv.refl F) hcomp
  haveI hsepKx : Algebra.IsSeparable Kx F :=
    Algebra.IsSeparable.of_equiv_equiv (e₁.symm : L ≃+* Kx) (RingEquiv.refl F) hcomp
  exact ⟨x, hx, hxtr, hfinKx, hsepKx, hFalg⟩

end Level

end AlgebraicCurve.Place.FiniteConstantFieldFormAux

open AlgebraicCurve.Place.FiniteConstantFieldFormAux in
set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem solution
    (K' : Type u) (F' : Type v) [Field K'] [Field F'] [Algebra K' F']
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP K' ℓ]
    (halg : ∀ a : K', ∃ n : ℕ, 0 < n ∧ a ^ ℓ ^ n = a)
    (hfg : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K' F'] (hC : ConstantsAreBase K' F') (W : Finset (Place K' F')) :
    ∃ (K : Type u) (F : Type v) (_ : Field K) (_ : Finite K) (_ : Field F)
      (_ : Algebra K K') (_ : Algebra K F) (_ : Algebra F F') (_ : Algebra K F')
      (_ : IsScalarTower K K' F') (_ : IsScalarTower K F F') (_ : Algebra.IsIntegral F F')
      (_ : IsCurveOver K F) (_ : Algebra.EssFiniteType K F),
        Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤ ∧
        ConstantsAreBase K F ∧
        ∀ w ∈ W, Place.fiberConstants K' F' (Place.restrictConstants F (K := K) w) = {w} ∧
          (Place.restrictConstants F (K := K) w).deg = w.deg := by
  classical
  letI : Algebra (ZMod ℓ) K' := ZMod.algebra K' ℓ

  haveI : PerfectField K' := perfectField_of_forall_pow_pow_eq K' ℓ halg
  haveI : Algebra.EssFiniteType K' F' := by
    obtain ⟨x, hx, hxfd⟩ := hfg
    exact AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hxfd
  obtain ⟨t, ht, hfd, hsep⟩ :=
    AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := K') (F := F')
  haveI := hfd

  obtain ⟨W₀⟩ : Nonempty (Place K' F') := by
    by_contra hno
    rw [not_nonempty_iff] at hno
    apply ht
    have htL : t ∈ LSpace (0 : Divisor K' F') := fun W => hno.elim W
    have hC' : LSpace (0 : Divisor K' F') = LinearMap.range (Algebra.linearMap K' F') := hC
    rw [hC'] at htL
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp htL
    rw [← ha]
    exact isAlgebraic_algebraMap a

  let bF := Module.finBasis K'⟮t⟯ F'
  let T₀ : Finset F' := insert t (Finset.univ.image fun i => (bF i : F'))
  have htT₀ : t ∈ T₀ := Finset.mem_insert_self _ _

  obtain ⟨x₀, -, hx₀tr, hx₀fd, hx₀sep, hx₀alg⟩ := level_core K' F' ℓ halg ht hfd hsep ∅ T₀ htT₀
  haveI hInt₀ : Algebra.IsIntegral (Flvl K' F' ℓ ∅ T₀) F' := Algebra.isAlgebraic_iff_isIntegral.mp hx₀alg

  let sep : Place K' F' → Place K' F' → F' := fun w w' =>
    if h : w ≠ w' then (exists_mem_and_not_mem_of_ne h).choose else 0
  have hsep' : ∀ w w' : Place K' F', w ≠ w' →
      sep w w' ∈ w.toValuationSubring ∧ sep w w' ∉ w'.toValuationSubring := by
    intro w w' h
    simp only [sep, dif_pos h]
    exact (exists_mem_and_not_mem_of_ne h).choose_spec
  let fib₀ : Place K' F' → Finset (Place K' F') := fun w =>
    Place.fiberConstants K' F' (Place.restrictConstants (Flvl K' F' ℓ ∅ T₀) (K := Klvl K' ℓ ∅) w)
  let T : Finset F' := T₀ ∪ W.biUnion fun w => (fib₀ w).image (sep w)
  have hT₀T : T₀ ⊆ T := Finset.subset_union_left
  have htT : t ∈ T := hT₀T htT₀

  obtain ⟨x₁, -, hx₁tr, hx₁fd, hx₁sep, hx₁alg⟩ := level_core K' F' ℓ halg ht hfd hsep ∅ T htT
  haveI hcurve₁ : IsCurveOver (Klvl K' ℓ ∅) (Flvl K' F' ℓ ∅ T) :=
    AlgebraicCurve.isCurveOver_of_transcendental hx₁tr hx₁fd hx₁sep
  haveI hInt₁ : Algebra.IsIntegral (Flvl K' F' ℓ ∅ T) F' := Algebra.isAlgebraic_iff_isIntegral.mp hx₁alg
  haveI hfinE : Finite (Klvl K' ℓ ∅) := finite_Klvl halg ∅

  let Kc : Subfield K' := Subfield.comap (algebraMap K' F') (Flvl K' F' ℓ ∅ T).toSubfield
  have hKc_mem : ∀ {a : K'}, a ∈ Kc ↔ algebraMap K' F' a ∈ Flvl K' F' ℓ ∅ T := fun {a} => Iff.rfl
  have hkfin : (Kc : Set K').Finite := by
    let v₀ : Place (Klvl K' ℓ ∅) (Flvl K' F' ℓ ∅ T) :=
      Place.restrictConstants (Flvl K' F' ℓ ∅ T) (K := Klvl K' ℓ ∅) W₀
    haveI : Module.Finite (Klvl K' ℓ ∅) v₀.ResidueField := IsCurveOver.finite_residueField v₀
    haveI : Finite v₀.ResidueField := Module.finite_of_finite (Klvl K' ℓ ∅)

    let ψ₀ : Kc →+* v₀.toValuationSubring :=
      { toFun := fun a => ⟨⟨algebraMap K' F' a, a.2⟩, W₀.algebraMap_mem' (a : K')⟩
        map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one _
        map_mul' := fun a b => by apply Subtype.ext; apply Subtype.ext; exact map_mul _ _ _
        map_zero' := by apply Subtype.ext; apply Subtype.ext; exact map_zero _
        map_add' := fun a b => by apply Subtype.ext; apply Subtype.ext; exact map_add _ _ _ }
    let ψ : Kc →+* v₀.ResidueField := (IsLocalRing.residue v₀.toValuationSubring).comp ψ₀
    haveI : Finite Kc := Finite.of_injective ψ ψ.injective
    exact Set.toFinite _

  let S : Finset K' := hkfin.toFinset
  have hSKc : ∀ a : K', a ∈ S ↔ a ∈ Kc := fun a => by
    rw [Set.Finite.mem_toFinset]; rfl
  obtain ⟨x, -, hxtr, hxfd, hxsep, hxalg⟩ := level_core K' F' ℓ halg ht hfd hsep S T htT
  haveI hKfin : Finite (Klvl K' ℓ S) := finite_Klvl halg S
  haveI hcurve : IsCurveOver (Klvl K' ℓ S) (Flvl K' F' ℓ S T) :=
    AlgebraicCurve.isCurveOver_of_transcendental hxtr hxfd hxsep
  haveI hEFT : Algebra.EssFiniteType (Klvl K' ℓ S) (Flvl K' F' ℓ S T) :=
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hxtr hxfd
  haveI hInt : Algebra.IsIntegral (Flvl K' F' ℓ S T) F' := Algebra.isAlgebraic_iff_isIntegral.mp hxalg

  have hKS : ∀ a : K', a ∈ Klvl K' ℓ S → algebraMap K' F' a ∈ Flvl K' F' ℓ ∅ T := by

    let Kci : IntermediateField (ZMod ℓ) K' := Kc.toIntermediateField fun r => by
      show ((algebraMap K' F').comp (algebraMap (ZMod ℓ) K')) r ∈ Flvl K' F' ℓ ∅ T
      rw [← ZMod.natCast_zmod_val r, map_natCast]
      exact _root_.natCast_mem _ _
    have hle : Klvl K' ℓ S ≤ Kci := by
      rw [IntermediateField.adjoin_le_iff]
      intro a ha
      exact (hSKc a).mp (by exact_mod_cast ha)
    intro a ha
    exact (hKc_mem).mp (hle ha)
  have hFeq : ((Flvl K' F' ℓ S T : IntermediateField (Klvl K' ℓ S) F') : Set F')
      = ((Flvl K' F' ℓ ∅ T : IntermediateField (Klvl K' ℓ ∅) F') : Set F') := by
    refine le_antisymm ?_ (coe_Flvl_mono K' F' ℓ (Finset.empty_subset S) subset_rfl)
    rw [coe_Flvl]
    change ((Subfield.closure _ : Subfield F') : Set F') ⊆ ((Flvl K' F' ℓ ∅ T).toSubfield : Set F')
    refine SetLike.coe_subset_coe.mpr (Subfield.closure_le.mpr (Set.union_subset ?_ ?_))
    · rintro _ ⟨a, ha, rfl⟩
      exact hKS a ha
    · intro f hf
      exact mem_Flvl_of_mem K' F' ℓ (by exact_mod_cast hf)

  have hgen : Algebra.adjoin (Flvl K' F' ℓ S T) (Set.range (algebraMap K' F')) = ⊤ := by
    haveI : Algebra.IsAlgebraic (Klvl K' ℓ S) K' := isAlgebraic_of_forall_pow_pow_eq _ K' ℓ halg
    have halgK' : ∀ y ∈ Set.range (algebraMap K' F'), IsAlgebraic (Flvl K' F' ℓ S T) y := by
      rintro _ ⟨a, rfl⟩
      have h1 : IsAlgebraic (Klvl K' ℓ S) (algebraMap K' F' a) :=
        (Algebra.IsAlgebraic.isAlgebraic (R := Klvl K' ℓ S) a).algHom (IsScalarTower.toAlgHom _ K' F')
      exact h1.tower_top (Flvl K' F' ℓ S T)
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halgK', ← IntermediateField.top_toSubalgebra]
    congr 1
    rw [eq_top_iff]
    intro z _
    set E := IntermediateField.adjoin (Flvl K' F' ℓ S T) (Set.range (algebraMap K' F')) with hEdef
    have hsub : (K'⟮t⟯).toSubfield ≤ (E.restrictScalars (Klvl K' ℓ S)).toSubfield := by
      rw [IntermediateField.adjoin_toSubfield]
      refine Subfield.closure_le.mpr ?_
      rintro y (⟨a, rfl⟩ | hy)
      · exact IntermediateField.subset_adjoin _ _ ⟨a, rfl⟩
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact IntermediateField.algebraMap_mem E
          (⟨t, mem_Flvl_of_mem K' F' ℓ htT⟩ : Flvl K' F' ℓ S T)
    rw [← bF.sum_repr z]
    refine sum_mem fun i _ => ?_
    have hbT : (bF i : F') ∈ T :=
      hT₀T (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    have hsmul : (bF.repr z i) • bF i = ((bF.repr z i : K'⟮t⟯) : F') * bF i := rfl
    rw [hsmul]
    exact mul_mem (hsub (bF.repr z i).2)
      (IntermediateField.algebraMap_mem E (⟨bF i, mem_Flvl_of_mem K' F' ℓ hbT⟩ : Flvl K' F' ℓ S T))

  have hconst : ConstantsAreBase (Klvl K' ℓ S) (Flvl K' F' ℓ S T) := by
    refine constantsAreBase_of_forall hC fun a ha => ?_
    obtain ⟨f, hf⟩ := ha
    have hmem : algebraMap K' F' a ∈ ((Flvl K' F' ℓ S T : IntermediateField (Klvl K' ℓ S) F') : Set F') := by
      rw [← hf]; exact f.2
    rw [hFeq] at hmem
    have haS : a ∈ S := (hSKc a).mpr ((hKc_mem).mpr hmem)
    have haK : a ∈ Klvl K' ℓ S := IntermediateField.subset_adjoin _ _ (by exact_mod_cast haS)
    exact ⟨⟨a, haK⟩, rfl⟩

  haveI : Algebra.IsAlgebraic (Klvl K' ℓ S) K' := isAlgebraic_of_forall_pow_pow_eq _ K' ℓ halg
  haveI : PerfectField (Klvl K' ℓ S) := inferInstance
  haveI : Algebra.IsSeparable (Klvl K' ℓ S) K' := inferInstance
  have hconstK : ∀ y : Flvl K' F' ℓ S T, IsAlgebraic (Klvl K' ℓ S) y →
      y ∈ (algebraMap (Klvl K' ℓ S) (Flvl K' F' ℓ S T)).range :=
    fun y hy => mem_range_of_isAlgebraic_of_constantsAreBase hconst y hy
  have he : ∀ w : Place K' F',
      (Place.forgetConstants (K := Klvl K' ℓ S) w).ramificationIndex (Flvl K' F' ℓ S T) = 1 :=
    fun w => AlgebraicCurve.Place.ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension
      hgen hconstK w
  haveI hCFDF : ConstantFieldDegreeFormula (Klvl K' ℓ S) K' (Flvl K' F' ℓ S T) F' :=
    AlgebraicCurve.constantFieldDegreeFormula_of_isConstantFieldExtension_of_isCurveOver hgen hconstK

  have hfib : ∀ w ∈ W, Place.fiberConstants K' F'
      (Place.restrictConstants (Flvl K' F' ℓ S T) (K := Klvl K' ℓ S) w) = {w} := by
    intro w hw
    ext w''
    rw [Place.mem_fiberConstants, Finset.mem_singleton]
    constructor
    · intro hres
      by_contra hne
      have hres' := (restrictConstants_eq_iff (K := Klvl K' ℓ S) (F := Flvl K' F' ℓ S T) w'' w).mp hres

      have hmem₀ : w'' ∈ fib₀ w := by
        show w'' ∈ Place.fiberConstants K' F' _
        rw [Place.mem_fiberConstants]
        refine (restrictConstants_eq_iff (K := Klvl K' ℓ ∅) (F := Flvl K' F' ℓ ∅ T₀) w'' w).mpr fun f => ?_
        have hf : (f : F') ∈ Flvl K' F' ℓ S T := coe_Flvl_mono K' F' ℓ (Finset.empty_subset S) hT₀T f.2
        exact hres' ⟨f, hf⟩

      have hsepT : sep w w'' ∈ T :=
        Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_image_of_mem _ hmem₀⟩)
      obtain ⟨h1, h2⟩ := hsep' w w'' (Ne.symm hne)
      exact h2 ((hres' ⟨sep w w'', mem_Flvl_of_mem K' F' ℓ hsepT⟩).mpr h1)
    · rintro rfl
      rfl

  have hdeg : ∀ w ∈ W,
      (Place.restrictConstants (Flvl K' F' ℓ S T) (K := Klvl K' ℓ S) w).deg = w.deg := by
    intro w hw
    have h := ConstantFieldDegreeFormula.degree_pullbackConstants (K := Klvl K' ℓ S) (K' := K')
      (F := Flvl K' F' ℓ S T) (F' := F')
      (Finsupp.single (Place.restrictConstants (Flvl K' F' ℓ S T) (K := Klvl K' ℓ S) w) 1)
    rw [Divisor.pullbackConstants_single, hfib w hw, Finset.sum_singleton, he w, Nat.cast_one, mul_one,
      Divisor.degree_single, Divisor.degree_single, one_mul, one_mul] at h
    exact_mod_cast h.symm
  exact ⟨Klvl K' ℓ S, Flvl K' F' ℓ S T, inferInstance, hKfin, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hInt, hcurve, hEFT,
    hgen, hconst, fun w hw => ⟨hfib w hw, hdeg w hw⟩⟩

end S_AlgebraicCurve_Place_exists_finite_constantField_form_fiberConstants_eq_singleton
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_finite_constantField_form_fiberConstants_eq_singleton (solution)
