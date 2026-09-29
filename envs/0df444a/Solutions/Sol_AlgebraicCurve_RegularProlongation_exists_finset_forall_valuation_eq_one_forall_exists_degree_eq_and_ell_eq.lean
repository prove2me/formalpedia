-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_finset_forall_valuation_eq_one_forall_exists_degree_eq_and_ell_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ee80e3a3-657a-5da5-882f-e2144c132339

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank
import Theorems.Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_monic_coeff_natDegree_le_of_forall_valuationSubring
import Theorems.Thm_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_exists_forall_ell_nsmul_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_exists_degree_eq_and_ell_eq
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

universe u v

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private noncomputable def g1_placeOf (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (V : ValuationSubring F) (hK : ∀ a : K, algebraMap K F a ∈ V) (hV : V ≠ ⊤) : Place K F where
  toValuationSubring := V
  algebraMap_mem' := hK
  ne_top' := hV
  isPrincipalIdealRing' :=
    ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin x V hK hV

private theorem g1_ord_neg_of_not_mem (v : Place K F) {g : F} (hg : g ∉ v.toValuationSubring) :
    v.ord g < 0 := by
  have hg0 : g ≠ 0 := fun h => hg (h ▸ v.toValuationSubring.zero_mem)
  by_contra h
  exact hg ((v.mem_iff_ord_nonneg hg0).mpr (not_lt.mp h))

private theorem g1_mem_valuationSubring_of_mem_lSpace (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) (m : ℕ) {g : F}
    (hg : g ∈ LSpace (m • D)) (V : ValuationSubring F) (hK : ∀ a : K, algebraMap K F a ∈ V) :
    (x ∈ V → g ∈ V) ∧ (x ∉ V → g * (x ^ m)⁻¹ ∈ V) := by
  rcases eq_or_ne g 0 with rfl | hg0
  · simp [V.zero_mem]
  by_cases hV : V = ⊤
  · subst hV
    exact ⟨fun _ => ValuationSubring.mem_top _, fun _ => ValuationSubring.mem_top _⟩
  set v : Place K F := g1_placeOf x V hK hV with hv
  have hVv : v.toValuationSubring = V := rfl
  have hgord : ∀ w : Place K F, -((m • D) w) ≤ w.ord g :=
    ((mem_lSpace_iff_ord.mp hg).resolve_left hg0)
  have hgv : -((m : ℤ) * D v) ≤ v.ord g := by
    have := hgord v
    simpa [Finsupp.smul_apply, smul_eq_mul, nsmul_eq_mul] using this
  rw [hD v] at hgv
  constructor
  · intro hxV
    rcases eq_or_ne x 0 with rfl | hx0
    · have : (0 : ℤ) ≤ v.ord g := by simpa [Place.ord_zero] using hgv
      rw [← hVv]
      exact (v.mem_iff_ord_nonneg hg0).mpr this
    · have hxord : 0 ≤ v.ord x := (v.mem_iff_ord_nonneg hx0).mp (hVv ▸ hxV)
      have hmax : max 0 (-v.ord x) = 0 := max_eq_left (by linarith)
      rw [hmax, mul_zero, neg_zero] at hgv
      rw [← hVv]
      exact (v.mem_iff_ord_nonneg hg0).mpr hgv
  · intro hxV
    have hx0 : x ≠ 0 := fun h => hxV (h ▸ V.zero_mem)
    have hxord : v.ord x < 0 := g1_ord_neg_of_not_mem v (hVv ▸ hxV)
    have hmax : max 0 (-v.ord x) = -v.ord x := max_eq_right (by linarith)
    rw [hmax] at hgv
    have hne : g * (x ^ m)⁻¹ ≠ 0 := mul_ne_zero hg0 (inv_ne_zero (pow_ne_zero _ hx0))
    rw [← hVv]
    refine (v.mem_iff_ord_nonneg hne).mpr ?_
    rw [v.ord_mul hg0 (inv_ne_zero (pow_ne_zero _ hx0)), v.ord_inv, ← zpow_natCast,
      v.ord_zpow]
    nlinarith

private theorem g1_exists_poleDivisor [HasPrincipalDivisors K F] {x : F} (hx : x ≠ 0) :
    ∃ D : Divisor K F, ∀ v : Place K F, D v = max 0 (-v.ord x) := by
  obtain ⟨P, hP, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) x hx
  exact ⟨Finsupp.mapRange (fun n => max 0 (-n)) (by simp) P, fun v => by simp [hP v]⟩

private theorem g1_finiteDimensional_lSpace_zero (hC : ConstantsAreBase K F) :
    FiniteDimensional K (LSpace (0 : Divisor K F)) := by
  have h : LSpace (0 : Divisor K F) = LinearMap.range (Algebra.linearMap K F) := hC
  rw [h]
  infer_instance

variable [IsAlgClosed K]

private theorem g1_finiteDimensional_lSpace (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (E : Divisor K F) :
    FiniteDimensional K (LSpace E) := by
  haveI : IsCurveOver K F := isCurveOver_of_isAlgClosed_of_transcendental x hx
  haveI : FiniteDimensional K (LSpace (0 : Divisor K F)) :=
    g1_finiteDimensional_lSpace_zero (constantsAreBase_of_isAlgClosed_of_transcendental x hx)
  exact finiteDimensional_lSpace E

private theorem g1_exists_poleDivisor_of_transcendental (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] :
    ∃ D : Divisor K F, ∀ v : Place K F, D v = max 0 (-v.ord x) := by
  haveI : IsCurveOver K F := isCurveOver_of_isAlgClosed_of_transcendental x hx
  exact g1_exists_poleDivisor (fun h0 => hx (h0 ▸ isAlgebraic_zero))

private theorem g1_degree_poleDivisor (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    Divisor.degree D = (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ) := by
  haveI : IsCurveOver K F := isCurveOver_of_isAlgClosed_of_transcendental x hx
  haveI : FiniteDimensional K (LSpace (0 : Divisor K F)) :=
    g1_finiteDimensional_lSpace_zero (constantsAreBase_of_isAlgClosed_of_transcendental x hx)
  exact Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord x hx D hD

end Generic

section Prolongation

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

private def g1_constHom (R : RegularProlongation A F Fb) : A →+* R.integers where
  toFun a := ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

private theorem g1_residue_constHom (R : RegularProlongation A F Fb) (a : A) :
    R.residue (g1_constHom R a) = algebraMap (ResidueField A) Fb (IsLocalRing.residue A a) :=
  R.residue_algebraMap a

private theorem g1_transcendental_coe [IsAlgClosed L] (R : RegularProlongation A F Fb)
    (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x)) :
    Transcendental L (x : F) := by
  intro halg
  have hint : IsIntegral L (x : F) := halg.isIntegral
  have h1 : (minpoly L (x : F)).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible L (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one L (x : F) h1
  have hcA : c ∈ A := (R.algebraMap_mem_iff c).mp (hc ▸ x.2)
  apply hx
  have hxeq : x = g1_constHom R ⟨c, hcA⟩ := Subtype.ext hc.symm
  rw [hxeq, g1_residue_constHom]
  exact isAlgebraic_algebraMap _

private theorem g1_residue_mem_lSpace_nsmul (R : RegularProlongation A F Fb) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fb)) Fb)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fb)) Fb)
    [FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F]
    {D : Divisor L F} (hD : ∀ v : Place L F, D v = max 0 (-v.ord (x : F)))
    {Db : Divisor (ResidueField A) Fb}
    (hDb : ∀ w : Place (ResidueField A) Fb, Db w = max 0 (-w.ord (R.residue x)))
    (m : ℕ) {g : R.integers} (hg : (g : F) ∈ LSpace (m • D)) :
    R.residue g ∈ LSpace (m • Db) := by
  obtain ⟨p, hp, hpdeg, hroot⟩ :=
    AlgebraicCurve.RegularProlongation.exists_monic_coeff_natDegree_le_of_forall_valuationSubring
      A R x hx (g : F) m
      (fun V hV hxV => (g1_mem_valuationSubring_of_mem_lSpace (x : F) D hD m hg V hV).1 hxV)
      (fun V hV hxV => (g1_mem_valuationSubring_of_mem_lSpace (x : F) D hD m hg V hV).2 hxV)
      (fun V hV => by
        rw [AlgebraicCurve.RegularProlongation.eq_integers_of_forall_mem_adjoin_iff
          A R x hx hfin hdeg V hV]
        exact g.2)
  have hM := AlgebraicCurve.RegularProlongation.mul_min_ord_residue_le_of_monic
    A R x g m p hp hpdeg hroot
  refine mem_lSpace_iff_ord.mpr (Or.inr fun w => ?_)
  have h1 := hM w
  have h2 : -((m : ℤ) * Db w) = (m : ℤ) * min 0 (w.ord (R.residue x)) := by
    rw [hDb w, ← mul_neg]
    congr 1
    rcases le_total 0 (w.ord (R.residue x)) with h0 | h0
    · rw [max_eq_left (by linarith), min_eq_left h0, neg_zero]
    · rw [max_eq_right (by linarith), min_eq_right h0, neg_neg]
  have h3 : (m • Db) w = (m : ℤ) * Db w := by simp
  rw [h3, h2]
  exact h1

variable [IsAlgClosed L]

private theorem g1_ell_le (R : RegularProlongation A F Fb) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    (hdeg : Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fb)) Fb
      = Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F)
    [hfd : FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F]
    {D : Divisor L F} (hD : ∀ v : Place L F, D v = max 0 (-v.ord (x : F)))
    {Db : Divisor (ResidueField A) Fb}
    (hDb : ∀ w : Place (ResidueField A) Fb, Db w = max 0 (-w.ord (R.residue x)))
    (m : ℕ) : ell (m • D) ≤ ell (m • Db) := by
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  have hxL : Transcendental L (x : F) := g1_transcendental_coe R x hx
  have hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fb)) Fb := by
    rw [hdeg]
    exact Module.finrank_pos
  haveI hfdb : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fb)) Fb :=
    Module.finite_of_finrank_pos hfin
  haveI : FiniteDimensional L (LSpace (m • D)) := g1_finiteDimensional_lSpace (x : F) hxL _
  haveI : FiniteDimensional (ResidueField A) (LSpace (m • Db)) :=
    g1_finiteDimensional_lSpace (R.residue x) hx _
  set S : Submodule (ResidueField A) Fb := Submodule.span (ResidueField A)
    {h : Fb | ∃ g : R.integers, (g : F) ∈ LSpace (m • D) ∧ R.residue g = h} with hS
  have hSle : S ≤ LSpace (m • Db) := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    exact g1_residue_mem_lSpace_nsmul R x hx hfin hdeg.symm hD hDb m hg
  have hfinS : Module.finrank (ResidueField A) S = Module.finrank L (LSpace (m • D)) :=
    AlgebraicCurve.RegularProlongation.finrank_span_residue_eq_finrank A R x hx hfin hdeg.symm
      (LSpace (m • D))
  have hmono : Module.finrank (ResidueField A) S ≤
      Module.finrank (ResidueField A) (LSpace (m • Db)) := Submodule.finrank_mono hSle
  change Module.finrank L (LSpace (m • D)) ≤ Module.finrank (ResidueField A) (LSpace (m • Db))
  rw [← hfinS]
  exact hmono

private theorem g1_degree_nsmul_eq (R : RegularProlongation A F Fb) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    (hdeg : Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fb)) Fb
      = Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F)
    [FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F]
    {D : Divisor L F} (hD : ∀ v : Place L F, D v = max 0 (-v.ord (x : F)))
    {Db : Divisor (ResidueField A) Fb}
    (hDb : ∀ w : Place (ResidueField A) Fb, Db w = max 0 (-w.ord (R.residue x)))
    (m : ℕ) :
    Divisor.degree (m • D)
        = (m : ℤ) * Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F ∧
      Divisor.degree (m • Db) = Divisor.degree (m • D) := by
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  have hxL : Transcendental L (x : F) := g1_transcendental_coe R x hx
  haveI hfdb : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fb)) Fb :=
    Module.finite_of_finrank_pos (by rw [hdeg]; exact Module.finrank_pos)
  have h1 := g1_degree_poleDivisor (x : F) hxL D hD
  have h2 := g1_degree_poleDivisor (R.residue x) hx Db hDb
  refine ⟨?_, ?_⟩
  · rw [map_nsmul, h1, nsmul_eq_mul]
  · rw [map_nsmul, map_nsmul, h1, h2, hdeg]

private theorem g1_exists_poleDivisors (R : RegularProlongation A F Fb) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    (hdeg : Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fb)) Fb
      = Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F)
    [FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F] :
    (∃ D : Divisor L F, ∀ v : Place L F, D v = max 0 (-v.ord (x : F))) ∧
      ∃ Db : Divisor (ResidueField A) Fb,
        ∀ w : Place (ResidueField A) Fb, Db w = max 0 (-w.ord (R.residue x)) := by
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  have hxL : Transcendental L (x : F) := g1_transcendental_coe R x hx
  haveI hfdb : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fb)) Fb :=
    Module.finite_of_finrank_pos (by rw [hdeg]; exact Module.finrank_pos)
  exact ⟨g1_exists_poleDivisor_of_transcendental (x : F) hxL,
    g1_exists_poleDivisor_of_transcendental (R.residue x) hx⟩

end Prolongation

theorem solution
    {L : Type u} [Field L] [IsAlgClosed L]
    {F : Type v} [Field F] [Algebra L F]
    (f : F)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin L ({f} : Set F)) F] :
    ∃ S : Finset L, (∀ s ∈ S, s ≠ 0) ∧
      ∀ A : ValuationSubring L, (∀ s ∈ S, A.valuation s = 1) →
        ∀ (Fb : Type v) [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
          (R : AlgebraicCurve.RegularProlongation A F Fb) (hfR : f ∈ R.integers),
          Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfR⟩) →
          Module.finrank
              (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)) Fb
            = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F →
          ∀ m : ℤ, ∃ (D : AlgebraicCurve.Divisor L F) (Db : AlgebraicCurve.Divisor (IsLocalRing.ResidueField A) Fb),
            m ≤ AlgebraicCurve.Divisor.degree D ∧
              AlgebraicCurve.Divisor.degree Db = AlgebraicCurve.Divisor.degree D ∧
                AlgebraicCurve.ell Db = AlgebraicCurve.ell D := by
  obtain ⟨S, hS, hres⟩ :=
    RegularProlongation.exists_finset_forall_valuation_eq_one_forall_exists_forall_ell_nsmul_le (L := L) f
  refine ⟨S, hS, ?_⟩
  intro A hA Fb _instF _instA R hfR htr hdeg m
  obtain ⟨⟨D, hD⟩, ⟨Db, hDb⟩⟩ := g1_exists_poleDivisors R ⟨f, hfR⟩ htr hdeg
  obtain ⟨m₀, hm₀⟩ := hres A hA Fb R hfR htr hdeg D Db hD hDb
  refine ⟨(max m.toNat m₀) • D, (max m.toNat m₀) • Db, ?_, ?_, ?_⟩
  · obtain ⟨h1, -⟩ := g1_degree_nsmul_eq R ⟨f, hfR⟩ htr hdeg hD hDb (max m.toNat m₀)
    rw [h1]
    have hd : (1 : ℤ) ≤ Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F := by
      exact_mod_cast Module.finrank_pos
    calc m ≤ (m.toNat : ℤ) := Int.self_le_toNat m
      _ ≤ ((max m.toNat m₀ : ℕ) : ℤ) := by exact_mod_cast le_max_left _ _
      _ ≤ ((max m.toNat m₀ : ℕ) : ℤ)
            * Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F :=
          le_mul_of_one_le_right (by positivity) hd
  · exact (g1_degree_nsmul_eq R ⟨f, hfR⟩ htr hdeg hD hDb _).2
  · exact le_antisymm (hm₀ _ (le_max_right _ _)) (g1_ell_le R ⟨f, hfR⟩ htr hdeg hD hDb _)

end S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_exists_degree_eq_and_ell_eq
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_exists_degree_eq_and_ell_eq (solution)
