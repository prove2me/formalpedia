-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_finset_forall_valuation_eq_one_forall_lSpace_le_span_and_linearIndependent_residue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/8b091417-0751-5f30-9b68-3b36a0c76f0d

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin
import Theorems.Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_monic_coeff_natDegree_le_of_forall_valuationSubring
import Theorems.Thm_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_exists_mem_integers_residue_uniqueRepr_and_span
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_eq_sum_aeval_residue_mul_residue_of_forall_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_lSpace_le_span_and_linearIndependent_residue
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

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

end Prolongation

section Star

variable {K : Type*} [Field K] {E : Type*} [Field E] [Algebra K E]

private theorem st_mem_span_of_natDegree_le {n : ℕ} (t : E) (b : Fin n → E) (e : Fin n → ℕ)
    (M : ℕ) (q : Fin n → Polynomial K) (hq : ∀ σ, q σ = 0 ∨ (q σ).natDegree + e σ ≤ M) :
    ∑ σ, Polynomial.aeval t (q σ) * b σ
      ∈ Submodule.span K {z : E | ∃ σ j, j + e σ ≤ M ∧ z = t ^ j * b σ} := by
  classical
  refine Submodule.sum_mem _ fun σ _ => ?_
  rcases hq σ with h0 | hdeg
  · simp [h0]
  · rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul]
    refine Submodule.sum_mem _ fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, j, by omega, rfl⟩)

private theorem st_uniqueRepr_of_linearIndependent {n : ℕ} (t : E) (b : Fin n → E)
    (hli : LinearIndependent K (fun p : Fin n × ℕ => t ^ p.2 * b p.1))
    (c : Fin n → Polynomial K) (hc : ∑ i, Polynomial.aeval t (c i) * b i = 0) :
    ∀ i, c i = 0 := by
  classical
  set N : ℕ := Finset.univ.sup (fun i => (c i).natDegree) + 1 with hN
  have hlt : ∀ i, (c i).natDegree < N := fun i =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (c i).natDegree) (Finset.mem_univ i))
  have hsum : ∑ p ∈ (Finset.univ : Finset (Fin n)) ×ˢ Finset.range N,
      (fun p : Fin n × ℕ => (c p.1).coeff p.2) p • (t ^ p.2 * b p.1) = 0 := by
    rw [Finset.sum_product, ← hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.aeval_eq_sum_range' (hlt i), Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc]
  have h0 := linearIndependent_iff'.mp hli _ _ hsum
  intro i
  ext j
  rw [Polynomial.coeff_zero]
  by_cases hj : j < N
  · exact h0 (i, j) (Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr hj⟩)
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hlt i) (not_lt.mp hj))

private theorem st_linearIndependent_of_uniqueRepr {n : ℕ} (t : E) (b : Fin n → E)
    (huniq : ∀ q q' : Fin n → Polynomial K,
      ∑ i, Polynomial.aeval t (q i) * b i = ∑ i, Polynomial.aeval t (q' i) * b i → q = q') :
    LinearIndependent K (fun p : Fin n × ℕ => t ^ p.2 * b p.1) := by
  classical
  rw [linearIndependent_iff']
  intro T g hg p hp
  let q : Fin n → Polynomial K := fun i =>
    ∑ p ∈ T.filter (fun p => p.1 = i), Polynomial.C (g p) * Polynomial.X ^ p.2
  have hexp : ∀ i, Polynomial.aeval t (q i) * b i
      = ∑ p ∈ T.filter (fun p => p.1 = i), g p • (t ^ p.2 * b p.1) := by
    intro i
    simp only [q, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, hp.2, Algebra.smul_def,
      mul_assoc]
  have hq : ∑ i, Polynomial.aeval t (q i) * b i = ∑ p ∈ T, g p • (t ^ p.2 * b p.1) := by
    simp_rw [hexp]
    exact Finset.sum_fiberwise_of_maps_to (g := fun p : Fin n × ℕ => p.1)
      (fun p _ => Finset.mem_univ _) _
  have hzero : ∑ i, Polynomial.aeval t (q i) * b i
      = ∑ i, Polynomial.aeval t ((0 : Fin n → Polynomial K) i) * b i := by
    rw [hq, hg]; simp
  have hq0 : q = 0 := huniq q 0 hzero
  have hcoeff : (q p.1).coeff p.2 = g p := by
    simp only [q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single p]
    · simp
    · intro p' hp' hne
      rw [Finset.mem_filter] at hp'
      rw [if_neg]
      intro h2
      exact hne (Prod.ext hp'.2 h2.symm)
    · intro hnot
      exact (hnot (Finset.mem_filter.mpr ⟨hp, rfl⟩)).elim
  rw [← hcoeff, hq0]
  simp

private theorem st_natDegree_add_le {n : ℕ} (t : E) (ht : Transcendental K t) (b : Fin n → E)
    (huniq : ∀ q q' : Fin n → Polynomial K,
      ∑ i, Polynomial.aeval t (q i) * b i = ∑ i, Polynomial.aeval t (q' i) * b i → q = q')
    (e : Fin n → ℕ) (M : ℕ) (q q' : Fin n → Polynomial K) (s : Polynomial K) (hs : s.eval 0 ≠ 0)
    (heq : Polynomial.aeval t⁻¹ s * (t⁻¹ ^ M * ∑ σ, Polynomial.aeval t (q σ) * b σ)
      = ∑ σ, Polynomial.aeval t⁻¹ (q' σ) * (t⁻¹ ^ e σ * b σ)) :
    ∀ σ, q σ = 0 ∨ (q σ).natDegree + e σ ≤ M := by
  classical
  have ht0 : t ≠ 0 := fun h => ht (h ▸ isAlgebraic_zero)
  haveI : Invertible t := invertibleOfNonzero ht0
  have hdegrefl : ∀ (p : Polynomial K) (d : ℕ), p.natDegree ≤ d →
      (Polynomial.reflect d p).natDegree ≤ d := by
    intro p d hd
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [Polynomial.coeff_reflect, Polynomial.revAt, Function.Embedding.coeFn_mk,
      if_neg (not_le_of_gt hi)]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd hi)
  have hevrefl : ∀ (p : Polynomial K) (d : ℕ), p.natDegree ≤ d →
      Polynomial.aeval t⁻¹ p * t ^ d = Polynomial.aeval t (Polynomial.reflect d p) := by
    intro p d hd
    have h := Polynomial.eval₂_reflect_mul_pow (algebraMap K E) t d (Polynomial.reflect d p)
      (hdegrefl p d hd)
    rw [Polynomial.reflect_reflect, invOf_eq_inv] at h
    rw [Polynomial.aeval_def, Polynomial.aeval_def]
    exact h
  set ds : ℕ := s.natDegree with hds
  set dq : Fin n → ℕ := fun σ => (q' σ).natDegree with hdq
  set B : ℕ := Finset.univ.sup (fun σ => e σ + dq σ) with hB
  have hBle : ∀ σ, e σ + dq σ ≤ B := fun σ =>
    Finset.le_sup (f := fun σ => e σ + dq σ) (Finset.mem_univ σ)
  set N : ℕ := M + ds + B with hN
  set P : Fin n → Polynomial K := fun σ => Polynomial.X ^ B * Polynomial.reflect ds s * q σ with hP
  set Q : Fin n → Polynomial K :=
    fun σ => Polynomial.X ^ (N - dq σ - e σ) * Polynomial.reflect (dq σ) (q' σ) with hQ
  have hscal : t ^ N * (Polynomial.aeval t⁻¹ s * t⁻¹ ^ M)
      = t ^ B * Polynomial.aeval t (Polynomial.reflect ds s) := by
    rw [← hevrefl s ds le_rfl]
    have : t ^ N = t ^ M * t ^ ds * t ^ B := by rw [← pow_add, ← pow_add]
    have hMM : t ^ M * t⁻¹ ^ M = 1 := by rw [← mul_pow, mul_inv_cancel₀ ht0, one_pow]
    rw [this]
    calc t ^ M * t ^ ds * t ^ B * (Polynomial.aeval t⁻¹ s * t⁻¹ ^ M)
        = (t ^ M * t⁻¹ ^ M) * (t ^ B * (Polynomial.aeval t⁻¹ s * t ^ ds)) := by ring
      _ = _ := by rw [hMM, one_mul]
  have hscal' : ∀ σ, t ^ N * (Polynomial.aeval t⁻¹ (q' σ) * t⁻¹ ^ e σ)
      = t ^ (N - dq σ - e σ) * Polynomial.aeval t (Polynomial.reflect (dq σ) (q' σ)) := by
    intro σ
    rw [← hevrefl (q' σ) (dq σ) le_rfl]
    have : t ^ N = t ^ (N - dq σ - e σ) * t ^ (dq σ) * t ^ (e σ) := by
      rw [← pow_add, ← pow_add]; congr 1; have := hBle σ; omega
    have hEE : t ^ e σ * t⁻¹ ^ e σ = 1 := by rw [← mul_pow, mul_inv_cancel₀ ht0, one_pow]
    rw [this]
    calc t ^ (N - dq σ - e σ) * t ^ dq σ * t ^ e σ * (Polynomial.aeval t⁻¹ (q' σ) * t⁻¹ ^ e σ)
        = (t ^ e σ * t⁻¹ ^ e σ)
            * (t ^ (N - dq σ - e σ) * (Polynomial.aeval t⁻¹ (q' σ) * t ^ dq σ)) := by ring
      _ = _ := by rw [hEE, one_mul]
  have hL : ∑ σ, Polynomial.aeval t (P σ) * b σ
      = t ^ N * (Polynomial.aeval t⁻¹ s * (t⁻¹ ^ M * ∑ σ, Polynomial.aeval t (q σ) * b σ)) := by
    calc ∑ σ, Polynomial.aeval t (P σ) * b σ
        = ∑ σ, t ^ B * Polynomial.aeval t (Polynomial.reflect ds s)
            * (Polynomial.aeval t (q σ) * b σ) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          simp only [hP, map_mul, map_pow, Polynomial.aeval_X]
          ring
      _ = t ^ B * Polynomial.aeval t (Polynomial.reflect ds s)
            * ∑ σ, Polynomial.aeval t (q σ) * b σ := by rw [Finset.mul_sum]
      _ = t ^ N * (Polynomial.aeval t⁻¹ s * t⁻¹ ^ M)
            * ∑ σ, Polynomial.aeval t (q σ) * b σ := by rw [hscal]
      _ = _ := by ring
  have hR : ∑ σ, Polynomial.aeval t (Q σ) * b σ
      = t ^ N * ∑ σ, Polynomial.aeval t⁻¹ (q' σ) * (t⁻¹ ^ e σ * b σ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    calc Polynomial.aeval t (Q σ) * b σ
        = t ^ (N - dq σ - e σ) * Polynomial.aeval t (Polynomial.reflect (dq σ) (q' σ)) * b σ := by
          simp only [hQ, map_mul, map_pow, Polynomial.aeval_X]
      _ = t ^ N * (Polynomial.aeval t⁻¹ (q' σ) * t⁻¹ ^ e σ) * b σ := by rw [hscal']
      _ = _ := by ring
  have hPQ : P = Q := huniq P Q (by rw [hL, hR, heq])

  have hr0 : (Polynomial.reflect ds s).coeff ds ≠ 0 := by
    rw [Polynomial.coeff_reflect, Polynomial.revAt_le le_rfl, Nat.sub_self,
      Polynomial.coeff_zero_eq_eval_zero]
    exact hs
  have hrne : Polynomial.reflect ds s ≠ 0 := fun h => hr0 (by rw [h, Polynomial.coeff_zero])
  have hrdeg : (Polynomial.reflect ds s).natDegree = ds :=
    le_antisymm (hdegrefl s ds le_rfl) (Polynomial.le_natDegree_of_ne_zero hr0)
  intro σ
  by_cases hq0 : q σ = 0
  · exact Or.inl hq0
  right
  have hPσ : P σ = Q σ := congrFun hPQ σ
  have hXB : (Polynomial.X ^ B : Polynomial K) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  have hPne : P σ ≠ 0 := mul_ne_zero (mul_ne_zero hXB hrne) hq0
  have hPdeg : (P σ).natDegree = B + ds + (q σ).natDegree := by
    simp only [hP]
    rw [Polynomial.natDegree_mul (mul_ne_zero hXB hrne) hq0, Polynomial.natDegree_mul hXB hrne,
      Polynomial.natDegree_X_pow, hrdeg]
  have hQne : Polynomial.reflect (dq σ) (q' σ) ≠ 0 := by
    intro h
    apply hPne
    rw [hPσ]
    simp only [hQ, h, mul_zero]
  have hQdeg : (Q σ).natDegree ≤ (N - dq σ - e σ) + dq σ := by
    simp only [hQ]
    rw [Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) hQne,
      Polynomial.natDegree_X_pow]
    exact Nat.add_le_add_left (hdegrefl (q' σ) (dq σ) le_rfl) _
  have h1 : B + ds + (q σ).natDegree ≤ (N - dq σ - e σ) + dq σ := by
    rw [← hPdeg, hPσ]; exact hQdeg
  have h2 := hBle σ
  omega

end Star

section PoleSpace

variable {K : Type*} [Field K] {E : Type*} [Field E] [Algebra K E]

private theorem st_ord_of_mem_lSpace (t : E) (D : Divisor K E)
    (hD : ∀ w : Place K E, D w = max 0 (-w.ord t)) (M : ℕ) {h : E} (hh : h ∈ LSpace (M • D)) :
    (∀ w : Place K E, 0 ≤ w.ord t → 0 ≤ w.ord h) ∧
      (∀ w : Place K E, w.ord t < 0 → 0 ≤ w.ord (t⁻¹ ^ M * h)) := by
  rcases eq_or_ne h 0 with rfl | h0
  · refine ⟨fun w _ => by simp [Place.ord_zero], fun w _ => by simp [Place.ord_zero]⟩
  have hord : ∀ w : Place K E, -((M • D) w) ≤ w.ord h := (mem_lSpace_iff_ord.mp hh).resolve_left h0
  constructor
  · intro w hw
    have h1 := hord w
    have hmax : max 0 (-w.ord t) = 0 := max_eq_left (by linarith)
    have h2 : -((M : ℤ) * 0) ≤ w.ord h := by
      simpa [Finsupp.smul_apply, nsmul_eq_mul, hD w, hmax] using h1
    simpa using h2
  · intro w hw
    have ht0 : t ≠ 0 := by
      rintro rfl
      simp [Place.ord_zero] at hw
    have h1 := hord w
    have hmax : max 0 (-w.ord t) = -w.ord t := max_eq_right (by linarith)
    have h2 : -((M : ℤ) * -w.ord t) ≤ w.ord h := by
      simpa [Finsupp.smul_apply, nsmul_eq_mul, hD w, hmax] using h1
    rw [inv_pow, w.ord_mul (inv_ne_zero (pow_ne_zero _ ht0)) h0, w.ord_inv, ← zpow_natCast,
      w.ord_zpow]
    nlinarith

end PoleSpace

section TransportUp

variable {K : Type*} [Field K] {E : Type*} [Field E] [Algebra K E]

private theorem tr_adjoin_inv (x : E) :
    IntermediateField.adjoin K ({x⁻¹} : Set E) = IntermediateField.adjoin K ({x} : Set E) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact inv_mem (IntermediateField.subset_adjoin K ({x} : Set E) (Set.mem_singleton x))
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    have h := inv_mem (IntermediateField.subset_adjoin K ({x⁻¹} : Set E) (Set.mem_singleton x⁻¹))
    rwa [inv_inv] at h

private theorem tr_mem_of_inv_mem (x : E)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set E)) E]
    (D : Divisor K E) (hD : ∀ v : Place K E, D v = max 0 (-v.ord x))
    {d' : ℕ} (y : Fin d' → E) (e : Fin d' → ℕ) (hyL : ∀ σ, y σ ∈ LSpace ((e σ) • D)) :
    ∀ σ, ∀ V : ValuationSubring E, (∀ c : K, algebraMap K E c ∈ V) → x⁻¹ ∈ V →
      x⁻¹ ^ e σ * y σ ∈ V := by
  intro σ V hK hxV
  have hmem := g1_mem_valuationSubring_of_mem_lSpace x D hD (e σ) (hyL σ) V hK
  by_cases hxmem : x ∈ V
  · exact mul_mem (pow_mem hxV (e σ)) (hmem.1 hxmem)
  · have h2 := hmem.2 hxmem
    have heq : x⁻¹ ^ e σ * y σ = y σ * (x ^ e σ)⁻¹ := by rw [inv_pow, mul_comm]
    rw [heq]
    exact h2

private theorem tr_forall_eq_zero_inv (x : E) (hx : x ≠ 0) {d' : ℕ} (y : Fin d' → E) (e : Fin d' → ℕ)
    (hyli : ∀ c : Fin d' → Polynomial K, ∑ i, Polynomial.aeval x (c i) * y i = 0 → ∀ i, c i = 0) :
    ∀ c : Fin d' → Polynomial K,
      ∑ i, Polynomial.aeval x⁻¹ (c i) * (x⁻¹ ^ e i * y i) = 0 → ∀ i, c i = 0 := by
  classical
  intro c hc
  haveI : Invertible x := invertibleOfNonzero hx
  have hdegrefl : ∀ (p : Polynomial K) (d : ℕ), p.natDegree ≤ d →
      (Polynomial.reflect d p).natDegree ≤ d := by
    intro p d hd
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [Polynomial.coeff_reflect, Polynomial.revAt, Function.Embedding.coeFn_mk,
      if_neg (not_le_of_gt hi)]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd hi)
  have hevrefl : ∀ (p : Polynomial K) (d : ℕ), p.natDegree ≤ d →
      Polynomial.aeval x⁻¹ p * x ^ d = Polynomial.aeval x (Polynomial.reflect d p) := by
    intro p d hd
    have h := Polynomial.eval₂_reflect_mul_pow (algebraMap K E) x d (Polynomial.reflect d p)
      (hdegrefl p d hd)
    rw [Polynomial.reflect_reflect, invOf_eq_inv] at h
    rw [Polynomial.aeval_def, Polynomial.aeval_def]
    exact h
  set dc : Fin d' → ℕ := fun i => (c i).natDegree with hdc
  set N : ℕ := Finset.univ.sup (fun i => dc i + e i) with hN
  have hNle : ∀ i, dc i + e i ≤ N := fun i =>
    Finset.le_sup (f := fun i => dc i + e i) (Finset.mem_univ i)
  set c' : Fin d' → Polynomial K :=
    fun i => Polynomial.X ^ (N - dc i - e i) * Polynomial.reflect (dc i) (c i) with hc'
  have hterm : ∀ i, Polynomial.aeval x (c' i) * y i
      = x ^ N * (Polynomial.aeval x⁻¹ (c i) * (x⁻¹ ^ e i * y i)) := by
    intro i
    have hsplit : x ^ N = x ^ (N - dc i - e i) * x ^ dc i * x ^ e i := by
      rw [← pow_add, ← pow_add]
      congr 1
      have := hNle i
      omega
    have hE : x ^ e i * x⁻¹ ^ e i = 1 := by rw [← mul_pow, mul_inv_cancel₀ hx, one_pow]
    simp only [hc', map_mul, map_pow, Polynomial.aeval_X]
    rw [← hevrefl (c i) (dc i) le_rfl, hsplit]
    linear_combination (-(x ^ (N - dc i - e i) * x ^ dc i * (Polynomial.aeval x⁻¹ (c i) * y i))) * hE
  have hsum : ∑ i, Polynomial.aeval x (c' i) * y i = 0 := by
    simp_rw [hterm]
    rw [← Finset.mul_sum, hc, mul_zero]
  have hc'0 := hyli c' hsum
  intro i
  have hi := hc'0 i
  simp only [hc'] at hi
  rcases mul_eq_zero.mp hi with hX | hr
  · exact absurd hX (pow_ne_zero _ Polynomial.X_ne_zero)
  · exact Polynomial.reflect_eq_zero_iff.mp hr

private theorem tr_exists_eq_sum_of_mem_span (x : E) {d' : ℕ} (y : Fin d' → E) (e : Fin d' → ℕ)
    (M : ℕ) {h : E}
    (hh : h ∈ Submodule.span K {z | ∃ σ j, j + e σ ≤ M ∧ z = x ^ j * y σ}) :
    ∃ p : Fin d' → Polynomial K, h = ∑ σ, Polynomial.aeval x (p σ) * y σ ∧
      ∀ σ j, M < j + e σ → (p σ).coeff j = 0 := by
  let W : Submodule K E :=
    { carrier := {z | ∃ p : Fin d' → Polynomial K, z = ∑ σ, Polynomial.aeval x (p σ) * y σ ∧
          ∀ σ j, M < j + e σ → (p σ).coeff j = 0}
      zero_mem' := ⟨0, by simp, fun σ j _ => by simp⟩
      add_mem' := by
        rintro a b ⟨pa, rfl, hpa⟩ ⟨pb, rfl, hpb⟩
        refine ⟨pa + pb, ?_, fun σ j hj => ?_⟩
        · simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
        · simp only [Pi.add_apply, Polynomial.coeff_add, hpa σ j hj, hpb σ j hj, add_zero]
      smul_mem' := by
        rintro a b ⟨pb, rfl, hpb⟩
        refine ⟨fun σ => Polynomial.C a * pb σ, ?_, fun σ j hj => ?_⟩
        · simp only [map_mul, Polynomial.aeval_C, Algebra.smul_def, Finset.mul_sum, mul_assoc]
        · simp only [Polynomial.coeff_C_mul, hpb σ j hj, mul_zero] }
  have hle : Submodule.span K {z : E | ∃ σ j, j + e σ ≤ M ∧ z = x ^ j * y σ} ≤ W := by
    rw [Submodule.span_le]
    rintro z ⟨σ, j, hj, rfl⟩
    show ∃ p : Fin d' → Polynomial K, x ^ j * y σ = ∑ τ, Polynomial.aeval x (p τ) * y τ ∧
      ∀ τ i, M < i + e τ → (p τ).coeff i = 0
    refine ⟨Pi.single σ (Polynomial.X ^ j), ?_, fun τ i hi => ?_⟩
    · rw [Finset.sum_eq_single σ]
      · simp
      · intro τ _ hτ
        simp [Pi.single_eq_of_ne hτ]
      · intro hσ
        exact absurd (Finset.mem_univ σ) hσ
    · by_cases hτ : τ = σ
      · subst hτ
        rw [Pi.single_eq_same, Polynomial.coeff_X_pow]
        exact if_neg (by omega)
      · simp [Pi.single_eq_of_ne hτ]
  exact hle hh

private theorem tr_exists_forall_neg_le_ord [HasPrincipalDivisors K E] (h : E) :
    ∃ k : ℕ, ∀ v : Place K E, -(k : ℤ) ≤ v.ord h := by
  classical
  rcases eq_or_ne h 0 with rfl | h0
  · exact ⟨0, fun v => by simp⟩
  obtain ⟨P, hP, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) h h0
  refine ⟨P.support.sup (fun v => (-P v).toNat), fun v => ?_⟩
  rw [← hP v]
  by_cases hneg : P v < 0
  · have hv : v ∈ P.support := Finsupp.mem_support_iff.mpr hneg.ne
    have h1 : (((-P v).toNat : ℕ) : ℤ) ≤ ((P.support.sup (fun v => (-P v).toNat) : ℕ) : ℤ) :=
      Nat.cast_le.mpr (Finset.le_sup (f := fun v => (-P v).toNat) hv)
    linarith [Int.self_le_toNat (-P v)]
  · omega

variable [IsAlgClosed K]

private theorem tr_exists_eq_sum (x : E) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set E)) E]
    (D : Divisor K E) (hD : ∀ v : Place K E, D v = max 0 (-v.ord x))
    {d' : ℕ} (y : Fin d' → E) (e : Fin d' → ℕ)
    (hspan : ∀ M : ℕ, (LSpace (M • D) : Submodule K E)
      ≤ Submodule.span K {z | ∃ σ j, j + e σ ≤ M ∧ z = x ^ j * y σ}) :
    ∀ h : E, (∀ V : ValuationSubring E, (∀ c : K, algebraMap K E c ∈ V) → x ∈ V → h ∈ V) →
      ∃ c : Fin d' → Polynomial K, h = ∑ i, Polynomial.aeval x (c i) * y i := by
  intro h hh
  haveI : IsCurveOver K E := isCurveOver_of_isAlgClosed_of_transcendental x hx
  have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ isAlgebraic_zero)
  obtain ⟨k, hk⟩ := tr_exists_forall_neg_le_ord (K := K) h
  have hmem : h ∈ LSpace (k • D) := by
    rcases eq_or_ne h 0 with rfl | h0
    · exact Submodule.zero_mem _
    refine mem_lSpace_iff_ord.mpr (Or.inr fun v => ?_)
    have hkD : (k • D) v = (k : ℤ) * D v := by simp
    rw [hkD, hD v]
    by_cases hvx : 0 ≤ v.ord x
    · have hxV : x ∈ v.toValuationSubring := (v.mem_iff_ord_nonneg hx0).mpr hvx
      have hh0 : 0 ≤ v.ord h :=
        (v.mem_iff_ord_nonneg h0).mp (hh v.toValuationSubring v.algebraMap_mem' hxV)
      have hmax : max 0 (-v.ord x) = 0 := max_eq_left (by omega)
      rw [hmax]
      simpa using hh0
    · have hlt : v.ord x < 0 := not_le.mp hvx
      have hmax : max 0 (-v.ord x) = -v.ord x := max_eq_right (by omega)
      rw [hmax]
      have hk0 : (0 : ℤ) ≤ k := Nat.cast_nonneg k
      have hvh := hk v
      nlinarith [mul_nonneg hk0 (show (0 : ℤ) ≤ -(v.ord x + 1) by omega)]
  obtain ⟨p, hp, -⟩ := tr_exists_eq_sum_of_mem_span x y e k (hspan k hmem)
  exact ⟨p, hp⟩

private theorem tr_exists_eq_sum_inv (x : E) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set E)) E]
    (D : Divisor K E) (hD : ∀ v : Place K E, D v = max 0 (-v.ord x))
    {d' : ℕ} (y : Fin d' → E) (e : Fin d' → ℕ)
    (hspan : ∀ M : ℕ, (LSpace (M • D) : Submodule K E)
      ≤ Submodule.span K {z | ∃ σ j, j + e σ ≤ M ∧ z = x ^ j * y σ}) :
    ∀ h : E, (∀ V : ValuationSubring E, (∀ c : K, algebraMap K E c ∈ V) → x⁻¹ ∈ V → h ∈ V) →
      ∃ c : Fin d' → Polynomial K, h = ∑ i, Polynomial.aeval x⁻¹ (c i) * (x⁻¹ ^ e i * y i) := by
  intro h hh
  haveI : IsCurveOver K E := isCurveOver_of_isAlgClosed_of_transcendental x hx
  have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ isAlgebraic_zero)
  obtain ⟨k₀, hk₀⟩ := tr_exists_forall_neg_le_ord (K := K) h
  obtain ⟨k, hk₀k, hek⟩ : ∃ k : ℕ, k₀ ≤ k ∧ ∀ σ, e σ ≤ k :=
    ⟨max k₀ (Finset.univ.sup e), le_max_left _ _, fun σ =>
      le_trans (Finset.le_sup (f := e) (Finset.mem_univ σ)) (le_max_right _ _)⟩
  have hkh : ∀ v : Place K E, -(k : ℤ) ≤ v.ord h := fun v => le_trans (by omega) (hk₀ v)
  have hk0 : (0 : ℤ) ≤ k := Nat.cast_nonneg k
  have hmem : x ^ k * h ∈ LSpace (k • D) := by
    rcases eq_or_ne h 0 with rfl | h0
    · rw [mul_zero]
      exact Submodule.zero_mem _
    refine mem_lSpace_iff_ord.mpr (Or.inr fun v => ?_)
    have hkD : (k • D) v = (k : ℤ) * D v := by simp
    rw [hkD, hD v, v.ord_mul (pow_ne_zero _ hx0) h0, ← zpow_natCast, v.ord_zpow]
    have hvh := hkh v
    rcases lt_trichotomy (v.ord x) 0 with hlt | hzero | hgt
    · have hxV : x⁻¹ ∈ v.toValuationSubring := by
        rw [v.mem_iff_ord_nonneg (inv_ne_zero hx0), v.ord_inv]
        omega
      have hh0 : 0 ≤ v.ord h :=
        (v.mem_iff_ord_nonneg h0).mp (hh v.toValuationSubring v.algebraMap_mem' hxV)
      have hmax : max 0 (-v.ord x) = -v.ord x := max_eq_right (by omega)
      rw [hmax]
      linarith
    · have hxV : x⁻¹ ∈ v.toValuationSubring := by
        rw [v.mem_iff_ord_nonneg (inv_ne_zero hx0), v.ord_inv]
        omega
      have hh0 : 0 ≤ v.ord h :=
        (v.mem_iff_ord_nonneg h0).mp (hh v.toValuationSubring v.algebraMap_mem' hxV)
      have hmax : max 0 (-v.ord x) = 0 := max_eq_left (by omega)
      rw [hmax, hzero]
      simpa using hh0
    · have hmax : max 0 (-v.ord x) = 0 := max_eq_left (by omega)
      rw [hmax]
      linarith [mul_nonneg hk0 (show (0 : ℤ) ≤ v.ord x - 1 by omega)]
  obtain ⟨p, hp, hpb⟩ := tr_exists_eq_sum_of_mem_span x y e k (hspan k hmem)
  have hpdeg : ∀ σ, (p σ).natDegree ≤ k - e σ := by
    intro σ
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    exact hpb σ j (by omega)
  haveI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx0)
  have hdegrefl : ∀ (q : Polynomial K) (d : ℕ), q.natDegree ≤ d →
      (Polynomial.reflect d q).natDegree ≤ d := by
    intro q d hd
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [Polynomial.coeff_reflect, Polynomial.revAt, Function.Embedding.coeFn_mk,
      if_neg (not_le_of_gt hi)]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd hi)
  have hevrefl : ∀ (q : Polynomial K) (d : ℕ), q.natDegree ≤ d →
      Polynomial.aeval x q * x⁻¹ ^ d = Polynomial.aeval x⁻¹ (Polynomial.reflect d q) := by
    intro q d hd
    have h := Polynomial.eval₂_reflect_mul_pow (algebraMap K E) x⁻¹ d (Polynomial.reflect d q)
      (hdegrefl q d hd)
    rw [Polynomial.reflect_reflect, invOf_eq_inv, inv_inv] at h
    rw [Polynomial.aeval_def, Polynomial.aeval_def]
    exact h
  have hterm : ∀ σ, Polynomial.aeval x⁻¹ (Polynomial.reflect (k - e σ) (p σ)) * (x⁻¹ ^ e σ * y σ)
      = x⁻¹ ^ k * (Polynomial.aeval x (p σ) * y σ) := by
    intro σ
    rw [← hevrefl (p σ) (k - e σ) (hpdeg σ)]
    have hsplit : x⁻¹ ^ k = x⁻¹ ^ (k - e σ) * x⁻¹ ^ e σ := by
      rw [← pow_add, Nat.sub_add_cancel (hek σ)]
    rw [hsplit]
    ring
  refine ⟨fun σ => Polynomial.reflect (k - e σ) (p σ), ?_⟩
  calc h = x⁻¹ ^ k * (x ^ k * h) := by
        rw [← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hx0), one_mul]
    _ = x⁻¹ ^ k * ∑ σ, Polynomial.aeval x (p σ) * y σ := by rw [hp]
    _ = ∑ σ, x⁻¹ ^ k * (Polynomial.aeval x (p σ) * y σ) := by rw [Finset.mul_sum]
    _ = ∑ σ, Polynomial.aeval x⁻¹ (Polynomial.reflect (k - e σ) (p σ)) * (x⁻¹ ^ e σ * y σ) := by
        simp_rw [hterm]

end TransportUp

section PoleSpaceInv

variable {K : Type*} [Field K] {E : Type*} [Field E] [Algebra K E]

private theorem st_ord_inv_pow_mul_nonneg (t : E) (D : Divisor K E)
    (hD : ∀ w : Place K E, D w = max 0 (-w.ord t)) (M : ℕ) {h : E} (hh : h ∈ LSpace (M • D)) :
    ∀ w : Place K E, 0 ≤ w.ord t⁻¹ → 0 ≤ w.ord (t⁻¹ ^ M * h) := by
  intro w hw
  obtain ⟨h1, h2⟩ := st_ord_of_mem_lSpace t D hD M hh
  by_cases hneg : w.ord t < 0
  · exact h2 w hneg
  have hnn : 0 ≤ w.ord t := not_lt.mp hneg
  have hh0 : 0 ≤ w.ord h := h1 w hnn
  rcases eq_or_ne h 0 with rfl | hne
  · simp
  rcases eq_or_ne t 0 with rfl | ht0
  · rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM
      simpa using hh0
    · simp [zero_pow hM.ne']
  have ht' : w.ord t = 0 := by
    rw [w.ord_inv] at hw
    omega
  rw [inv_pow, w.ord_mul (inv_ne_zero (pow_ne_zero _ ht0)) hne, w.ord_inv, ← zpow_natCast,
    w.ord_zpow, ht']
  simpa using hh0

end PoleSpaceInv

section TransportDown

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

private theorem td_inv_mem (R : RegularProlongation A F Fb) {f : F} (hfR : f ∈ R.integers)
    (h0 : R.residue ⟨f, hfR⟩ ≠ 0) : f⁻¹ ∈ R.integers := by
  obtain ⟨u, hu⟩ := R.isUnit_of_residue_ne_zero h0
  have hmul : f * ((u⁻¹ : R.integersˣ) : R.integers) = 1 := by
    have h := congrArg (fun z : R.integers => (z : F)) u.mul_inv
    simpa [hu] using h
  rw [inv_eq_of_mul_eq_one_right hmul]
  exact SetLike.coe_mem _

private theorem td_residue_inv (R : RegularProlongation A F Fb) {f : F} (hfR : f ∈ R.integers)
    (hfR' : f⁻¹ ∈ R.integers) (h0 : R.residue ⟨f, hfR⟩ ≠ 0) :
    R.residue ⟨f⁻¹, hfR'⟩ = (R.residue ⟨f, hfR⟩)⁻¹ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    have hz : (⟨0, hfR⟩ : R.integers) = 0 := Subtype.ext rfl
    exact h0 (by rw [hz, map_zero])
  have h1 : (⟨f, hfR⟩ : R.integers) * ⟨f⁻¹, hfR'⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hf0)
  have h2 : R.residue ⟨f, hfR⟩ * R.residue ⟨f⁻¹, hfR'⟩ = 1 := by rw [← map_mul, h1, map_one]
  exact eq_inv_of_mul_eq_one_right h2

private theorem td_residue_inv_pow_mul (R : RegularProlongation A F Fb) {f : F} (hfR : f ∈ R.integers)
    (hfR' : f⁻¹ ∈ R.integers) (h0 : R.residue ⟨f, hfR⟩ ≠ 0) (n : ℕ) {g : F} (hg : g ∈ R.integers)
    (hm : f⁻¹ ^ n * g ∈ R.integers) :
    R.residue ⟨f⁻¹ ^ n * g, hm⟩ = (R.residue ⟨f, hfR⟩)⁻¹ ^ n * R.residue ⟨g, hg⟩ := by
  have h1 : (⟨f⁻¹ ^ n * g, hm⟩ : R.integers) = ⟨f⁻¹, hfR'⟩ ^ n * ⟨g, hg⟩ := Subtype.ext (by simp)
  rw [h1, map_mul, map_pow, td_residue_inv R hfR hfR' h0]

end TransportDown

theorem solution
    {L : Type u} [Field L] [IsAlgClosed L]
    {F : Type v} [Field F] [Algebra L F]
    (f : F)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin L ({f} : Set F)) F]
    (D : AlgebraicCurve.Divisor L F) (hD : ∀ v : AlgebraicCurve.Place L F, D v = max 0 (-v.ord f))
    {d' : ℕ} (y : Fin d' → F) (e : Fin d' → ℕ)
    (hcard : d' = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (hspan : ∀ M : ℕ, (AlgebraicCurve.LSpace (M • D) : Submodule L F)
      ≤ Submodule.span L {z | ∃ σ j, j + e σ ≤ M ∧ z = f ^ j * y σ})
    (hli : LinearIndependent L (fun p : Fin d' × ℕ => f ^ p.2 * y p.1))
    (hyL : ∀ σ, y σ ∈ AlgebraicCurve.LSpace ((e σ) • D)) :
    ∃ S : Finset L, (∀ s ∈ S, s ≠ 0) ∧
      ∀ A : ValuationSubring L, (∀ s ∈ S, A.valuation s = 1) →
        ∀ (Fb : Type v) [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
          (R : AlgebraicCurve.RegularProlongation A F Fb) (hfR : f ∈ R.integers),
          Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfR⟩) →
          Module.finrank
              (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)) Fb
            = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F →
          ∃ hyO : ∀ σ, y σ ∈ R.integers,
            ∀ Db : AlgebraicCurve.Divisor (IsLocalRing.ResidueField A) Fb,
              (∀ w : AlgebraicCurve.Place (IsLocalRing.ResidueField A) Fb,
                Db w = max 0 (-w.ord (R.residue ⟨f, hfR⟩))) →
              (∀ M : ℕ, (AlgebraicCurve.LSpace (M • Db) : Submodule (IsLocalRing.ResidueField A) Fb)
                ≤ Submodule.span (IsLocalRing.ResidueField A)
                    {z | ∃ σ j, j + e σ ≤ M ∧
                      z = R.residue ⟨f, hfR⟩ ^ j * R.residue ⟨y σ, hyO σ⟩}) ∧
              LinearIndependent (IsLocalRing.ResidueField A)
                (fun p : Fin d' × ℕ => R.residue ⟨f, hfR⟩ ^ p.2 * R.residue ⟨y p.1, hyO p.1⟩) ∧
              (∀ σ, R.residue ⟨y σ, hyO σ⟩ ∈ AlgebraicCurve.LSpace ((e σ) • Db)) := by
  classical
  by_cases hx : Transcendental L f
  swap
  · refine ⟨∅, by simp, ?_⟩
    intro A hA Fb _instF _instA R hfR htr
    exact absurd (g1_transcendental_coe R ⟨f, hfR⟩ htr) hx
  have hf0 : f ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
  have hadj : IntermediateField.adjoin L ({f⁻¹} : Set F) = IntermediateField.adjoin L ({f} : Set F) :=
    tr_adjoin_inv f

  have hyint : ∀ σ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → y σ ∈ V :=
    fun σ V hV hfV => (g1_mem_valuationSubring_of_mem_lSpace f D hD (e σ) (hyL σ) V hV).1 hfV
  have hyli : ∀ c : Fin d' → Polynomial L,
      ∑ i, Polynomial.aeval f (c i) * y i = 0 → ∀ i, c i = 0 :=
    fun c hc => st_uniqueRepr_of_linearIndependent f y hli c hc
  have hysp := tr_exists_eq_sum f hx D hD y e hspan
  have hyint' := tr_mem_of_inv_mem f D hD y e hyL
  have hyli' := tr_forall_eq_zero_inv f hf0 y e hyli
  have hysp' := tr_exists_eq_sum_inv f hx D hD y e hspan
  have hcard' : Fintype.card (Fin d') = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F := by
    rw [Fintype.card_fin, hcard]
  haveI : FiniteDimensional (IntermediateField.adjoin L ({f⁻¹} : Set F)) F := by
    rw [hadj]; infer_instance
  haveI : Algebra.IsSeparable (IntermediateField.adjoin L ({f⁻¹} : Set F)) F := by
    rw [hadj]; infer_instance
  have hcard'' : Fintype.card (Fin d')
      = Module.finrank (IntermediateField.adjoin L ({f⁻¹} : Set F)) F := by
    rw [hcard', hadj]
  obtain ⟨S₃, hS₃, H₃⟩ :=
    RegularProlongation.exists_finset_forall_valuation_eq_one_forall_exists_mem_integers_residue_uniqueRepr_and_span
      f y hcard' hyint hyli
  obtain ⟨Sf, hSf, Hf⟩ :=
    RegularProlongation.exists_finset_forall_valuation_eq_one_forall_eq_sum_aeval_residue_mul_residue_of_forall_ord_nonneg
      f y hcard' hyint hyli hysp
  obtain ⟨Su, hSu, Hu⟩ :=
    RegularProlongation.exists_finset_forall_valuation_eq_one_forall_eq_sum_aeval_residue_mul_residue_of_forall_ord_nonneg
      f⁻¹ (fun σ => f⁻¹ ^ e σ * y σ) hcard'' hyint' hyli' hysp'
  refine ⟨S₃ ∪ Sf ∪ Su, ?_, ?_⟩
  · intro s hs
    simp only [Finset.mem_union] at hs
    rcases hs with (hs | hs) | hs
    exacts [hS₃ s hs, hSf s hs, hSu s hs]
  intro A hA Fb _instF _instA R hfR htr hdeg
  have hA₃ : ∀ s ∈ S₃, A.valuation s = 1 := fun s hs => hA s (by simp [hs])
  have hAf : ∀ s ∈ Sf, A.valuation s = 1 := fun s hs => hA s (by simp [hs])
  have hAu : ∀ s ∈ Su, A.valuation s = 1 := fun s hs => hA s (by simp [hs])

  have hfb0 : R.residue ⟨f, hfR⟩ ≠ 0 := fun h => htr (h ▸ isAlgebraic_zero)
  have hfR' : f⁻¹ ∈ R.integers := td_inv_mem R hfR hfb0
  have hres' : R.residue ⟨f⁻¹, hfR'⟩ = (R.residue ⟨f, hfR⟩)⁻¹ := td_residue_inv R hfR hfR' hfb0
  have hadj' : IntermediateField.adjoin (ResidueField A) ({(R.residue ⟨f, hfR⟩)⁻¹} : Set Fb)
      = IntermediateField.adjoin (ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb) :=
    tr_adjoin_inv _
  have htr' : Transcendental (ResidueField A) (R.residue ⟨f⁻¹, hfR'⟩) := by
    rw [hres']
    exact fun h => htr (IsAlgebraic.inv_iff.mp h)
  have hdeg' : Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({R.residue ⟨f⁻¹, hfR'⟩} : Set Fb)) Fb
      = Module.finrank (IntermediateField.adjoin L ({f⁻¹} : Set F)) F := by
    rw [hres', hadj', hadj, hdeg]
  obtain ⟨hyO, huniq, -⟩ := H₃ A hA₃ Fb R hfR htr hdeg
  obtain ⟨hyOf, Hf'⟩ := Hf A hAf Fb R hfR htr hdeg
  obtain ⟨hyOu, Hu'⟩ := Hu A hAu Fb R hfR' htr' hdeg'
  refine ⟨hyO, fun Db hDb => ⟨?_, ?_, ?_⟩⟩
  · intro M h hh
    obtain ⟨hfin, -⟩ := st_ord_of_mem_lSpace (R.residue ⟨f, hfR⟩) Db hDb M hh
    have hreg := st_ord_inv_pow_mul_nonneg (R.residue ⟨f, hfR⟩) Db hDb M hh
    obtain ⟨q, hq⟩ := Hf' h hfin
    obtain ⟨q', hq'⟩ := Hu' ((R.residue ⟨f, hfR⟩)⁻¹ ^ M * h) (by rwa [hres'])
    have hq'' : Polynomial.aeval (R.residue ⟨f, hfR⟩)⁻¹ (1 : Polynomial (ResidueField A))
        * ((R.residue ⟨f, hfR⟩)⁻¹ ^ M * ∑ σ, Polynomial.aeval (R.residue ⟨f, hfR⟩) (q σ)
            * R.residue ⟨y σ, hyO σ⟩)
        = ∑ σ, Polynomial.aeval (R.residue ⟨f, hfR⟩)⁻¹ (q' σ)
            * ((R.residue ⟨f, hfR⟩)⁻¹ ^ e σ * R.residue ⟨y σ, hyO σ⟩) := by
      rw [map_one, one_mul, ← hq, hq']
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [hres', td_residue_inv_pow_mul R hfR hfR' hfb0 (e σ) (hyO σ) (hyOu σ)]
    have hdegq := st_natDegree_add_le (R.residue ⟨f, hfR⟩) htr (fun σ => R.residue ⟨y σ, hyO σ⟩)
      huniq e M q q' 1 (by simp) hq''
    rw [hq]
    exact st_mem_span_of_natDegree_le (R.residue ⟨f, hfR⟩) (fun σ => R.residue ⟨y σ, hyO σ⟩)
      e M q hdegq
  · exact st_linearIndependent_of_uniqueRepr (R.residue ⟨f, hfR⟩) (fun σ => R.residue ⟨y σ, hyO σ⟩)
      huniq
  · intro σ
    have hfin : 0 < Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)) Fb := by
      rw [hdeg]; exact Module.finrank_pos
    exact g1_residue_mem_lSpace_nsmul R ⟨f, hfR⟩ htr hfin hdeg.symm hD hDb (e σ)
      (g := ⟨y σ, hyO σ⟩) (hyL σ)

end S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_lSpace_le_span_and_linearIndependent_residue
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_lSpace_le_span_and_linearIndependent_residue (solution)
