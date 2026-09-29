-- Prove2me | solution 1 for AlgebraicCurve.exists_derivation_constantFieldExtension_map_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/a3317d23-c063-5b0b-8e91-35a9097d88d5

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_existsUnique_valuation_sub_lt_one_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_derivation_constantFieldExtension_map_mem
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve~finiteDimensional_adjoin_of_transcendental P2MW.S_AlgebraicCurve_exists_derivation_constantFieldExtension_map_mem.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.coe_algebraMap HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.finiteResidue linearIndependent_of_constantFieldExtension Place.exists_of_valuationSubring Place.exists_comap_algebraMap_eq_of_constantFieldExtension Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension mem_span_range_algebraMap_of_constantFieldExtension"
namespace HorizDeriv
p2m_open "AlgebraicCurve~finiteDimensional_adjoin_of_transcendental"

section Toolkit

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem one_le_ord_of_mem_of_inv_not_mem {f : F} (h1 : f ∈ v.toValuationSubring)
    (h2 : f⁻¹ ∉ v.toValuationSubring) : 1 ≤ v.ord f := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact h2 (by simp)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hπ
  have h0 := ord_nonneg_of_mem v h1
  by_contra hlt
  have hz : v.ord f = 0 := by omega
  apply h2
  have hmul : ((u : v.toValuationSubring) : F) *
      (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
  rw [hu, hz, zpow_zero, mul_one, ← eq_inv_of_mul_eq_one_right hmul]
  exact SetLike.coe_mem _

theorem mem_iff_ord_nonneg (f : F) : f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f := by
  refine ⟨ord_nonneg_of_mem v, fun h => ?_⟩
  by_contra hmem
  have hinv : f⁻¹ ∈ v.toValuationSubring :=
    (v.toValuationSubring.mem_or_inv_mem f).resolve_left hmem
  have := one_le_ord_of_mem_of_inv_not_mem v hinv (by simpa using hmem)
  rw [v.ord_inv] at this
  omega

theorem ord_algebraMap (a : K) : v.ord (algebraMap K F a) = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have h1 := ord_nonneg_of_mem v (v.algebraMap_mem' a)
  have h2 := ord_nonneg_of_mem v (v.algebraMap_mem' a⁻¹)
  rw [map_inv₀, v.ord_inv] at h2
  omega

theorem inv_mem_of_ord_eq_zero {f : F} (hf : v.ord f = 0) : f⁻¹ ∈ v.toValuationSubring := by
  rw [mem_iff_ord_nonneg, v.ord_inv, hf, neg_zero]

end Toolkit

section BasisD

open scoped Polynomial
open KaehlerDifferential TensorProduct IntermediateField

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem finiteDimensional_adjoin_of_transcendental {L F : Type*} [Field L] [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    {f : F} (hf : Transcendental L f) :
    FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F := by
  classical
  obtain ⟨x, -, hxfin⟩ := hF
  set Ex := IntermediateField.adjoin L ({x} : Set F) with hEx
  set Ef := IntermediateField.adjoin L ({f} : Set F) with hEf
  haveI := hxfin
  haveI halgx : Algebra.IsAlgebraic (Algebra.adjoin L ({x} : Set F)) F := by
    haveI : Algebra.IsAlgebraic Ex F := Algebra.IsAlgebraic.of_finite Ex F
    exact Algebra.IsAlgebraic.trans (Algebra.adjoin L ({x} : Set F)) Ex F
  have htr : Algebra.trdeg L F ≤ 1 := by
    have h := Algebra.IsAlgebraic.trdeg_le_cardinalMk L ({x} : Set F)
    simpa using h
  have hind : AlgebraicIndependent L ((↑) : ({f} : Set F) → F) := by
    haveI : Subsingleton ({f} : Set F) := Set.subsingleton_coe _ |>.mpr (Set.subsingleton_singleton)
    exact (algebraicIndependent_singleton_iff (⟨f, Set.mem_singleton f⟩ : ({f} : Set F))).mpr hf
  have hB : IsTranscendenceBasis L ((↑) : ({f} : Set F) → F) :=
    hind.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using htr)
  haveI halg : Algebra.IsAlgebraic Ef F := by
    have h := hB.isAlgebraic_field
    rwa [Subtype.range_coe] at h
  let bx := Module.finBasis Ex F
  let T : Set F := insert x (Set.range bx)
  haveI : Finite T := ((Set.finite_range bx).insert x).to_subtype
  have hT : ∀ t ∈ T, IsIntegral Ef t := fun t _ => (Algebra.IsAlgebraic.isAlgebraic t).isIntegral
  haveI hfin : FiniteDimensional Ef (IntermediateField.adjoin Ef T) :=
    IntermediateField.finiteDimensional_adjoin hT
  have htop : IntermediateField.adjoin Ef T = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hyL : y ∈ IntermediateField.adjoin L T := by
      rw [← bx.sum_repr y]
      refine sum_mem fun i _ => ?_
      rw [Algebra.smul_def]
      refine mul_mem ?_ (IntermediateField.subset_adjoin L T (Set.mem_insert_of_mem _ ⟨i, rfl⟩))
      exact IntermediateField.adjoin.mono L _ _
        (Set.singleton_subset_iff.mpr (Set.mem_insert x _)) (bx.repr y i).2
    have hle : IntermediateField.adjoin L T ≤ (IntermediateField.adjoin Ef T).restrictScalars L :=
      IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin Ef T)
    exact hle hyL
  rw [htop] at hfin
  exact LinearEquiv.finiteDimensional
    (IntermediateField.topEquiv (F := Ef) (E := F)).toLinearEquiv

variable (K : Type*) [Field K]

noncomputable def polyBasis : Module.Basis (Fin 1) K[X] Ω[K[X]⁄K] :=
  (Module.Basis.singleton (Fin 1) K[X]).map (KaehlerDifferential.polynomialEquiv K).symm

theorem polyBasis_zero : polyBasis K 0 = D K K[X] Polynomial.X := by
  simp [polyBasis]

noncomputable def ratFuncBasis : Module.Basis (Fin 1) (RatFunc K) Ω[(RatFunc K)⁄K] :=
  haveI : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := RatFunc K) (nonZeroDivisors K[X])
  ((polyBasis K).baseChange (RatFunc K)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K K[X] (RatFunc K))

theorem ratFuncBasis_zero : ratFuncBasis K 0 = D K (RatFunc K) RatFunc.X := by
  haveI : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := RatFunc K) (nonZeroDivisors K[X])
  simp only [ratFuncBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply, polyBasis_zero,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D,
    RatFunc.algebraMap_X]

variable {F : Type*} [Field F] [Algebra K F]

noncomputable def towerBasis [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsSeparable (RatFunc K) F] : Module.Basis (Fin 1) F Ω[F⁄K] :=
  haveI : Algebra.FormallyEtale (RatFunc K) F := Algebra.FormallyEtale.of_isSeparable _ _
  ((ratFuncBasis K).baseChange F).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (RatFunc K) F)

theorem towerBasis_zero [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsSeparable (RatFunc K) F] :
    towerBasis K (F := F) 0 = D K F (algebraMap (RatFunc K) F RatFunc.X) := by
  haveI : Algebra.FormallyEtale (RatFunc K) F := Algebra.FormallyEtale.of_isSeparable _ _
  simp only [towerBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply, ratFuncBasis_zero,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]

theorem exists_basis_D (F : Type*) [Field F] [Algebra K F] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {t : F} (ht : Transcendental K t) :
    ∃ b : Module.Basis (Fin 1) F (Ω[F⁄K]), b 0 = D K F t := by
  haveI hfin : FiniteDimensional K⟮t⟯ F := finiteDimensional_adjoin_of_transcendental hfg ht
  haveI : CharZero K⟮t⟯ := charZero_of_injective_algebraMap (algebraMap K K⟮t⟯).injective
  haveI : Algebra.IsSeparable K⟮t⟯ F := Algebra.IsSeparable.of_integral K⟮t⟯ F
  let e : RatFunc K ≃ₐ[K] K⟮t⟯ := RatFunc.algEquivOfTranscendental t ht
  letI : Algebra (RatFunc K) F :=
    ((algebraMap K⟮t⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F)
        (e.symm.toRingEquiv : K⟮t⟯ →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮t⟯ F) := by
    refine RingHom.ext fun a => ?_
    show algebraMap K⟮t⟯ F (e (e.symm a)) = algebraMap K⟮t⟯ F a
    rw [e.apply_symm_apply]
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap K F a = algebraMap K⟮t⟯ F (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  refine ⟨towerBasis K, ?_⟩
  rw [towerBasis_zero]
  show D K F (algebraMap K⟮t⟯ F (e RatFunc.X)) = D K F t
  congr 1
  exact RatFunc.algEquivOfTranscendental_X t ht

theorem derivation_eq_zero_of_apply_transcendental (F : Type*) [Field F] [Algebra K F]
    [CharZero K] {M : Type*} [AddCommGroup M] [Module K M] [Module F M] [IsScalarTower K F M]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {t : F} (ht : Transcendental K t) (D' : Derivation K F M) (hD : D' t = 0) : D' = 0 := by
  obtain ⟨b, hb⟩ := exists_basis_D K F hfg ht
  ext f
  obtain ⟨c, hc⟩ : ∃ c : F, c • b 0 = D K F f :=
    ⟨b.repr (D K F f) 0, by
      conv_rhs => rw [← b.sum_repr (D K F f)]
      rw [Fin.sum_univ_one]⟩
  have h1 : D' f = D'.liftKaehlerDifferential (D K F f) :=
    (D'.liftKaehlerDifferential_comp_D f).symm
  have h2 : D'.liftKaehlerDifferential (b 0) = 0 := by
    rw [hb, Derivation.liftKaehlerDifferential_comp_D, hD]
  rw [Derivation.zero_apply, h1, ← hc, map_smul, h2, smul_zero]

end BasisD

section Transc

open scoped Polynomial

theorem transcendental_iff_linearIndependent_pow {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] (x : A) :
    Transcendental R x ↔ LinearIndependent R (fun n : ℕ => x ^ n) := by
  constructor
  · intro hx
    rw [linearIndependent_iff]
    intro l hl
    set p : R[X] := l.sum fun n a => Polynomial.monomial n a with hp
    have hcoeff : ∀ n, p.coeff n = l n := fun n => by
      rw [hp, Finsupp.sum, Polynomial.finset_sum_coeff]
      simp only [Polynomial.coeff_monomial]
      rw [Finset.sum_ite_eq']
      split_ifs with h
      · rfl
      · exact (Finsupp.notMem_support_iff.mp h).symm
    have h1 : Polynomial.aeval x p = Finsupp.linearCombination R (fun k : ℕ => x ^ k) l := by
      rw [hp, Finsupp.sum, map_sum, Finsupp.linearCombination_apply, Finsupp.sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Polynomial.aeval_monomial, Algebra.smul_def]
    have h2 := (transcendental_iff.mp hx) p (h1.trans hl)
    ext n
    rw [← hcoeff, h2, Polynomial.coeff_zero, Finsupp.zero_apply]

  · intro h
    rw [transcendental_iff]
    intro p hpx
    let l : ℕ →₀ R := Finsupp.onFinset p.support p.coeff fun n hn => Polynomial.mem_support_iff.mpr hn
    have hl : ∀ n, l n = p.coeff n := fun n => Finsupp.onFinset_apply
    have key : Finsupp.linearCombination R (fun j : ℕ => x ^ j) l = Polynomial.aeval x p := by
      rw [Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset l Finsupp.support_onFinset_subset (fun i a => a • x ^ i)
          (fun n _ => zero_smul R _),
        Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hl, Algebra.smul_def]
    have := linearIndependent_iff.mp h l (by rw [key, hpx])
    ext n
    rw [← hl n, this, Finsupp.zero_apply, Polynomial.coeff_zero]


theorem transcendental_algebraMap (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE]
    [Algebra K F] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    {x : F} (hx : Transcendental K x) : Transcendental E (algebraMap F FE x) := by
  rw [transcendental_iff_linearIndependent_pow] at hx ⊢
  have h := AlgebraicCurve.linearIndependent_of_constantFieldExtension K F E FE hfg hfgE hgen hx
  simpa only [map_pow] using h

end Transc

section Construction

open scoped Polynomial IntermediateField
open KaehlerDifferential

theorem exists_derivation_of_transcendental
    {K E FE : Type*} [Field K] [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra K FE]
    [IsScalarTower K E FE] [CharZero K]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    {t : FE} (ht : Transcendental E t) (δ : Derivation K E E) :
    ∃ D : Derivation K FE FE, D t = 0 ∧ ∀ e : E, D (algebraMap E FE e) = algebraMap E FE (δ e) := by
  classical
  haveI hfin : FiniteDimensional E⟮t⟯ FE := finiteDimensional_adjoin_of_transcendental hfgE ht
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  haveI : CharZero E⟮t⟯ := charZero_of_injective_algebraMap (algebraMap E E⟮t⟯).injective
  haveI : Algebra.IsSeparable E⟮t⟯ FE := Algebra.IsSeparable.of_integral E⟮t⟯ FE
  let e : RatFunc E ≃ₐ[E] E⟮t⟯ := RatFunc.algEquivOfTranscendental t ht
  letI iRF : Algebra (RatFunc E) FE :=
    ((algebraMap E⟮t⟯ FE).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc E) FE)
        (e.symm.toRingEquiv : E⟮t⟯ →+* RatFunc E)
      = RingHom.comp (RingEquiv.refl FE : FE →+* FE) (algebraMap E⟮t⟯ FE) := by
    refine RingHom.ext fun a => ?_
    show algebraMap E⟮t⟯ FE (e (e.symm a)) = algebraMap E⟮t⟯ FE a
    rw [e.apply_symm_apply]
  haveI : Algebra.IsSeparable (RatFunc E) FE :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl FE) hsq
  letI iPX : Algebra E[X] FE :=
    ((algebraMap (RatFunc E) FE).comp (algebraMap E[X] (RatFunc E))).toAlgebra
  haveI : IsScalarTower E[X] (RatFunc E) FE := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have halgX : ∀ g : E[X], algebraMap E[X] FE g = Polynomial.aeval t g := by
    intro g
    show algebraMap E⟮t⟯ FE (e (algebraMap E[X] (RatFunc E) g)) = _
    rw [RatFunc.algEquivOfTranscendental_algebraMap, ← Polynomial.aeval_algebraMap_apply,
      IntermediateField.AdjoinSimple.algebraMap_gen]
  haveI : IsScalarTower E E[X] FE := IsScalarTower.of_algebraMap_eq fun a => by
    rw [halgX, Polynomial.algebraMap_eq, Polynomial.aeval_C]
  haveI : IsScalarTower K E[X] FE := IsScalarTower.of_algebraMap_eq fun k => by
    rw [IsScalarTower.algebraMap_apply K E FE, IsScalarTower.algebraMap_apply K E E[X],
      ← IsScalarTower.algebraMap_apply E E[X] FE]
  haveI : Algebra.FormallyEtale E[X] (RatFunc E) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := RatFunc E) (nonZeroDivisors E[X])
  haveI : Algebra.FormallyEtale (RatFunc E) FE := Algebra.FormallyEtale.of_isSeparable _ _
  haveI : Algebra.FormallyEtale E[X] FE := Algebra.FormallyEtale.comp E[X] (RatFunc E) FE

  let D₁ : Derivation K E[X] FE :=
    ((Algebra.linearMap E[X] FE).comp
        (PolynomialModule.equivPolynomialSelf :
          PolynomialModule E E ≃ₗ[E[X]] E[X]).toLinearMap).compDer
      (Derivation.mapCoeffs δ)
  have hD₁ : ∀ g : E[X], D₁ g = algebraMap E[X] FE
      (PolynomialModule.equivPolynomialSelf (Derivation.mapCoeffs δ g)) := fun _ => rfl
  have hD₁C : ∀ a : E, D₁ (Polynomial.C a) = algebraMap E FE (δ a) := by
    intro a
    rw [hD₁, Derivation.mapCoeffs_C, PolynomialModule.equivPolynomialSelf_apply_eq,
      PolynomialModule.equivPolynomial_single, halgX, Polynomial.monomial_zero_left,
      Polynomial.aeval_C]
  have hD₁X : D₁ Polynomial.X = 0 := by
    rw [hD₁, Derivation.mapCoeffs_X, map_zero, map_zero]

  have hBC := KaehlerDifferential.isBaseChange_of_formallyEtale K E[X] FE
  let Φ : Ω[FE⁄K] →ₗ[FE] FE := hBC.lift D₁.liftKaehlerDifferential
  have hΦ : ∀ g : E[X], Φ (KaehlerDifferential.D K FE (algebraMap E[X] FE g)) = D₁ g := by
    intro g
    rw [← KaehlerDifferential.map_D K K E[X] FE g]
    show hBC.lift D₁.liftKaehlerDifferential _ = _
    rw [hBC.lift_eq, Derivation.liftKaehlerDifferential_comp_D]
  let D : Derivation K FE FE := Φ.compDer (KaehlerDifferential.D K FE)
  have hDalg : ∀ g : E[X], D (algebraMap E[X] FE g) = D₁ g := fun g => hΦ g
  refine ⟨D, ?_, fun a => ?_⟩
  · have hX : algebraMap E[X] FE Polynomial.X = t := by rw [halgX, Polynomial.aeval_X]
    calc D t = D (algebraMap E[X] FE Polynomial.X) := by rw [hX]
      _ = 0 := by rw [hDalg, hD₁X]
  · have hC : algebraMap E[X] FE (Polynomial.C a) = algebraMap E FE a := by
      rw [halgX, Polynomial.aeval_C]
    calc D (algebraMap E FE a) = D (algebraMap E[X] FE (Polynomial.C a)) := by rw [hC]
      _ = algebraMap E FE (δ a) := by rw [hDalg, hD₁C]

theorem exists_derivation (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE]
    [Algebra K F] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (δ : Derivation K E E) :
    ∃ D : Derivation K FE FE,
      (∀ f : F, D (algebraMap F FE f) = 0) ∧
      (∀ e : E, D (algebraMap E FE e) = algebraMap E FE (δ e)) := by
  obtain ⟨x, hx, hxfin⟩ := hfg
  have hx' : Transcendental E (algebraMap F FE x) :=
    transcendental_algebraMap K F E FE ⟨x, hx, hxfin⟩ hfgE hgen hx
  obtain ⟨D, hDx, hDE⟩ := exists_derivation_of_transcendental hfgE hx' δ
  refine ⟨D, fun f => ?_, hDE⟩
  have h := derivation_eq_zero_of_apply_transcendental K F ⟨x, hx, hxfin⟩ hx
    (D.compAlgebraMap F) (by rw [Derivation.compAlgebraMap_apply]; exact hDx)
  have := Derivation.congr_fun h f
  rwa [Derivation.compAlgebraMap_apply, Derivation.zero_apply] at this

end Construction

section Basic

variable {k L : Type*} [Field k] [Field L] [Algebra k L] (w : Place k L)

theorem mem_of_ord_nonneg {f : L} (hf : 0 ≤ w.ord f) : f ∈ w.toValuationSubring :=
  (mem_iff_ord_nonneg w f).2 hf

theorem irreducible_coe_ne_zero {π : w.toValuationSubring} (hπ : Irreducible π) : (π : L) ≠ 0 := by
  intro h
  exact hπ.ne_zero (by exact_mod_cast h)

theorem ord_coe_isUnit {X : w.toValuationSubring} (h : IsUnit X) : w.ord (X : L) = 0 := by
  obtain ⟨u, rfl⟩ := h
  exact w.ord_coe_unit u

theorem isUnit_of_ord_eq_zero {X : w.toValuationSubring} (h0 : X ≠ 0) (h : w.ord (X : L) = 0) :
    IsUnit X := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hX0 : (X : L) ≠ 0 := fun h' => h0 (by exact_mod_cast h')
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hX0 hπ
  rw [h, zpow_zero, mul_one] at hu
  have : X = (u : w.toValuationSubring) := Subtype.ext hu
  rw [this]
  exact Units.isUnit u

theorem ord_pos_of_mem_maximalIdeal {Y : w.toValuationSubring}
    (hY : Y ∈ IsLocalRing.maximalIdeal w.toValuationSubring) (h0 : Y ≠ 0) :
    0 < w.ord (Y : L) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hY
  obtain ⟨b, rfl⟩ := hY
  have hb : b ≠ 0 := by rintro rfl; exact h0 (by simp)
  have hb' : (b : L) ≠ 0 := fun h' => hb (by exact_mod_cast h')
  push_cast
  rw [w.ord_mul hb' (irreducible_coe_ne_zero w hπ), w.ord_coe_irreducible hπ]
  have := ord_nonneg_of_mem w b.2
  omega

theorem mem_maximalIdeal_of_ord_pos {Y : w.toValuationSubring} (h : 0 < w.ord (Y : L)) :
    Y ∈ IsLocalRing.maximalIdeal w.toValuationSubring := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have := ord_coe_isUnit w hu
  omega

theorem isUnit_add_of_mem_maximalIdeal {X Y : w.toValuationSubring} (hX : IsUnit X)
    (hY : Y ∈ IsLocalRing.maximalIdeal w.toValuationSubring) : IsUnit (X + Y) := by
  by_contra h
  have h1 : X + Y ∈ IsLocalRing.maximalIdeal w.toValuationSubring :=
    (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 h)
  have h2 : X ∈ IsLocalRing.maximalIdeal w.toValuationSubring := by
    simpa using sub_mem h1 hY
  exact (IsLocalRing.mem_maximalIdeal _).1 h2 hX

theorem exists_sub_algebraMap_mem_maximalIdeal [IsAlgClosed k] [IsCurveOver k L]
    (X : w.toValuationSubring) :
    ∃ a : k, X - algebraMap k w.toValuationSubring a ∈
      IsLocalRing.maximalIdeal w.toValuationSubring := by
  haveI : Module.Finite k w.ResidueField := IsCurveOver.finiteResidue w
  haveI : Algebra.IsIntegral k w.ResidueField := Algebra.IsIntegral.of_finite k _
  have hbij : Function.Bijective (algebraMap k w.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨a, ha⟩ := hbij.2 (IsLocalRing.residue w.toValuationSubring X)
  refine ⟨a, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← ha,
    IsScalarTower.algebraMap_apply k w.toValuationSubring w.ResidueField,
    IsLocalRing.ResidueField.algebraMap_eq]

end Basic

section Gauss

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F]
  [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F']
  [IsScalarTower K F F']

theorem ord_sum_le [IsAlgClosed K] [IsCurveOver K F]
    (P : Place K F) (P' : Place K' F')
    (hcomap : P'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring)
    (hord : ∀ f : F, P'.ord (algebraMap F F' f) = P.ord f)
    {ι : Type*} (s : Finset ι) (β : ι → K') (hβ : LinearIndependent K β) (u : ι → F)
    {i : ι} (hi : i ∈ s) (hui : u i ≠ 0) :
    P'.ord (∑ j ∈ s, algebraMap K' F' (β j) * algebraMap F F' (u j)) ≤ P.ord (u i) := by
  classical
  have hφmem : ∀ x : F, x ∈ P.toValuationSubring → algebraMap F F' x ∈ P'.toValuationSubring := by
    intro x hx
    rw [← hcomap] at hx
    exact hx

  set T := s.filter (fun j => u j ≠ 0) with hT
  have hiT : i ∈ T := Finset.mem_filter.2 ⟨hi, hui⟩
  have hTne : T.Nonempty := ⟨i, hiT⟩
  obtain ⟨i₀, hi₀T, hi₀⟩ := Finset.exists_mem_eq_inf' hTne (fun j => P.ord (u j))
  set m := T.inf' hTne (fun j => P.ord (u j)) with hm
  have hm_le : ∀ j ∈ T, m ≤ P.ord (u j) := fun j hj => Finset.inf'_le _ hj
  have hui₀ : u i₀ ≠ 0 := (Finset.mem_filter.1 hi₀T).2
  have hi₀s : i₀ ∈ s := (Finset.mem_filter.1 hi₀T).1
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := irreducible_coe_ne_zero P hπ

  have ho_mem : ∀ j ∈ s, u j * (π : F) ^ (-m) ∈ P.toValuationSubring := by
    intro j hj
    by_cases huj : u j = 0
    · rw [huj, zero_mul]; exact zero_mem _
    apply mem_of_ord_nonneg
    rw [P.ord_mul huj (zpow_ne_zero _ hπ0), P.ord_zpow, P.ord_coe_irreducible hπ]
    have := hm_le j (Finset.mem_filter.2 ⟨hj, huj⟩)
    linarith

  have hdig : ∀ j ∈ s, ∃ a : K, ∃ r : P.toValuationSubring,
      r ∈ IsLocalRing.maximalIdeal P.toValuationSubring ∧
      u j * (π : F) ^ (-m) = algebraMap K F a + (r : F) := by
    intro j hj
    obtain ⟨a, ha⟩ := exists_sub_algebraMap_mem_maximalIdeal P ⟨_, ho_mem j hj⟩
    refine ⟨a, _, ha, ?_⟩
    simp only [AddSubgroupClass.coe_sub, Place.coe_algebraMap]
    ring
  choose! a r har hur using hdig

  have hai₀ : a i₀ ≠ 0 := by
    intro h0
    have hunit : IsUnit (⟨_, ho_mem i₀ hi₀s⟩ : P.toValuationSubring) := by
      apply isUnit_of_ord_eq_zero P
      · intro h
        apply hui₀
        have h' : u i₀ * (π : F) ^ (-m) = 0 := by
          simpa using congrArg Subtype.val h
        rcases mul_eq_zero.1 h' with h'' | h''
        · exact h''
        · exact absurd h'' (zpow_ne_zero _ hπ0)
      · show P.ord (u i₀ * (π : F) ^ (-m)) = 0
        rw [P.ord_mul hui₀ (zpow_ne_zero _ hπ0), P.ord_zpow, P.ord_coe_irreducible hπ, ← hi₀]
        ring
    have heq : (⟨_, ho_mem i₀ hi₀s⟩ : P.toValuationSubring) = r i₀ := by
      apply Subtype.ext
      show u i₀ * (π : F) ^ (-m) = r i₀
      rw [hur i₀ hi₀s, h0, map_zero, zero_add]
    rw [heq] at hunit
    exact (IsLocalRing.mem_maximalIdeal _).1 (har i₀ hi₀s) hunit

  set d : K' := ∑ j ∈ s, a j • β j with hd
  have hd0 : d ≠ 0 := by
    intro h0
    exact hai₀ (linearIndependent_iff'.1 hβ s a h0 i₀ hi₀s)

  have hrmem : ∀ j ∈ s, (⟨algebraMap F F' (r j), hφmem _ (r j).2⟩ : P'.toValuationSubring) ∈
      IsLocalRing.maximalIdeal P'.toValuationSubring := by
    intro j hj
    by_cases hr0 : r j = 0
    · have : (⟨algebraMap F F' (r j), hφmem _ (r j).2⟩ : P'.toValuationSubring) = 0 := by
        apply Subtype.ext
        simp [hr0]
      rw [this]
      exact Ideal.zero_mem _
    apply mem_maximalIdeal_of_ord_pos P'
    show 0 < P'.ord (algebraMap F F' (r j))
    rw [hord]
    exact ord_pos_of_mem_maximalIdeal P (har j hj) hr0
  set Dd : P'.toValuationSubring := ⟨algebraMap K' F' d, P'.algebraMap_mem' d⟩ with hDd
  set Tt : P'.toValuationSubring := ∑ j ∈ s,
    (⟨algebraMap K' F' (β j), P'.algebraMap_mem' (β j)⟩ : P'.toValuationSubring) *
      ⟨algebraMap F F' (r j), hφmem _ (r j).2⟩ with hTt
  have hDunit : IsUnit Dd := by
    apply isUnit_of_ord_eq_zero P'
    · intro h
      have : algebraMap K' F' d = 0 := by simpa [hDd] using congrArg Subtype.val h
      exact hd0 ((algebraMap K' F').injective (by rw [this, map_zero]))
    · exact ord_algebraMap P' d
  have hTmem : Tt ∈ IsLocalRing.maximalIdeal P'.toValuationSubring :=
    Ideal.sum_mem _ fun j hj => Ideal.mul_mem_left _ _ (hrmem j hj)
  have hunit := isUnit_add_of_mem_maximalIdeal P' hDunit hTmem
  have hcoe : ((Dd + Tt : P'.toValuationSubring) : F') =
      algebraMap K' F' d + ∑ j ∈ s, algebraMap K' F' (β j) * algebraMap F F' (r j) := by
    simp [hDd, hTt]
  have hne' : algebraMap K' F' d + ∑ j ∈ s, algebraMap K' F' (β j) * algebraMap F F' (r j) ≠ 0 := by
    rw [← hcoe]
    exact_mod_cast hunit.ne_zero
  have hord0 : P'.ord (algebraMap K' F' d +
      ∑ j ∈ s, algebraMap K' F' (β j) * algebraMap F F' (r j)) = 0 := by
    rw [← hcoe]
    exact ord_coe_isUnit P' hunit

  have hS : ∑ j ∈ s, algebraMap K' F' (β j) * algebraMap F F' (u j) =
      algebraMap F F' (π : F) ^ m * (algebraMap K' F' d +
        ∑ j ∈ s, algebraMap K' F' (β j) * algebraMap F F' (r j)) := by
    rw [hd, map_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have huj : u j = (algebraMap K F (a j) + r j) * (π : F) ^ m := by
      rw [← hur j hj, mul_assoc, ← zpow_add₀ hπ0, neg_add_cancel, zpow_zero, mul_one]
    rw [huj, map_mul, map_add, map_zpow₀, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply K K' F', ← IsScalarTower.algebraMap_apply K F F']
    ring
  rw [hS, P'.ord_mul (zpow_ne_zero _ ((map_ne_zero _).2 hπ0)) hne', P'.ord_zpow, hord,
    P.ord_coe_irreducible hπ, hord0]
  simpa using hm_le i hiT

theorem exists_linearIndependent_repr {z : F'}
    (hz : z ∈ Submodule.span K' (Set.range (algebraMap F F'))) :
    ∃ (n : ℕ) (β : Fin n → K') (u : Fin n → F), LinearIndependent K β ∧
      z = ∑ k, algebraMap K' F' (β k) * algebraMap F F' (u k) := by
  classical
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hz
  set W : Submodule K K' := Submodule.span K (↑(c.support.image c) : Set K') with hW
  haveI : Module.Finite K W := FiniteDimensional.span_of_finite K (Finset.finite_toSet _)
  set b := Module.finBasis K W
  have hcW : ∀ f : F, c f ∈ W := by
    intro f
    by_cases hf : f ∈ c.support
    · exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem c hf))
    · rw [Finsupp.notMem_support_iff.1 hf]; exact zero_mem _
  refine ⟨_, fun k => (b k : K'), fun k => ∑ f ∈ c.support, b.repr ⟨c f, hcW f⟩ k • f,
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W), ?_⟩
  have hcf : ∀ f : F, c f = ∑ k, b.repr ⟨c f, hcW f⟩ k • (b k : K') := by
    intro f
    have h2 := congrArg Subtype.val (b.sum_repr ⟨c f, hcW f⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    exact h2.symm
  simp only [Finsupp.sum, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  conv_lhs => rw [hcf f]
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul,
    ← IsScalarTower.algebraMap_apply K K' F', ← IsScalarTower.algebraMap_apply K F F']
  ring

end Gauss

section Span

variable {K F E FE : Type*} [Field K] [Field F] [Field E] [Field FE]
    [Algebra K F] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE]

variable (F E FE) in

abbrev spanF : Submodule E FE := Submodule.span E (Set.range (algebraMap F FE))

theorem algebraMap_mem_spanF (f : F) : algebraMap F FE f ∈ spanF F E FE :=
  Submodule.subset_span ⟨f, rfl⟩

theorem algebraMap_left_mem_spanF (a : E) : algebraMap E FE a ∈ spanF F E FE := by
  have : algebraMap E FE a = a • algebraMap F FE 1 := by rw [map_one, Algebra.smul_def, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (algebraMap_mem_spanF 1)

theorem mul_mem_spanF {a b : FE} (ha : a ∈ spanF F E FE) (hb : b ∈ spanF F E FE) :
    a * b ∈ spanF F E FE := by
  have h := Submodule.mul_mem_mul ha hb
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨x, ⟨f, rfl⟩, y, ⟨g, rfl⟩, rfl⟩
  exact ⟨f * g, map_mul _ _ _⟩

variable (F E FE) in

def spanSubalgebra : Subalgebra E FE :=
  (spanF F E FE).toSubalgebra (Submodule.subset_span ⟨1, map_one _⟩)
    (fun _ _ ha hb => mul_mem_spanF ha hb)

theorem mem_spanSubalgebra {a : FE} : a ∈ spanSubalgebra F E FE ↔ a ∈ spanF F E FE :=
  Submodule.mem_toSubalgebra

theorem mem_spanF_of_mem_adjoin {a : FE} (ha : a ∈ Algebra.adjoin E (Set.range (algebraMap F FE))) :
    a ∈ spanF F E FE := by
  have h : Algebra.adjoin E (Set.range (algebraMap F FE)) ≤ spanSubalgebra F E FE :=
    Algebra.adjoin_le fun x hx => (mem_spanSubalgebra).2 (Submodule.subset_span hx)
  exact (mem_spanSubalgebra).1 (h ha)

theorem exists_eq_div_of_adjoin_eq_top
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤) (z : FE) :
    ∃ r ∈ spanF F E FE, ∃ s ∈ spanF F E FE, z = r / s := by
  have hz : z ∈ IntermediateField.adjoin E (Set.range (algebraMap F FE)) := by
    rw [hgen]; exact IntermediateField.mem_top
  rw [IntermediateField.mem_adjoin_iff_div] at hz
  obtain ⟨r, hr, s, hs, hzrs⟩ := hz
  exact ⟨r, mem_spanF_of_mem_adjoin hr, s, mem_spanF_of_mem_adjoin hs, hzrs⟩

omit [Algebra K F] [Algebra K E] [IsScalarTower K E FE] [IsScalarTower K F FE] in

theorem map_mem_spanF (D : Derivation K FE FE) (hDF : ∀ f : F, D (algebraMap F FE f) = 0)
    (hDE : ∀ e : E, D (algebraMap E FE e) ∈ Set.range (algebraMap E FE))
    {a : FE} (ha : a ∈ spanF F E FE) : D a ∈ spanF F E FE := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, rfl⟩ := hx
    rw [hDF]
    exact zero_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x hxmem hx =>
    rw [Algebra.smul_def, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    obtain ⟨c, hc⟩ := hDE a
    refine add_mem ?_ ?_
    · rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hx
    · rw [← hc, mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hxmem

def placeSubmodule (P : Place E FE) : Submodule E FE where
  carrier := P.toValuationSubring
  add_mem' := fun ha hb => add_mem ha hb
  zero_mem' := zero_mem _
  smul_mem' := fun a y hy => by
    show a • y ∈ P.toValuationSubring
    rw [Algebra.smul_def]
    exact mul_mem (P.algebraMap_mem' a) hy

theorem mem_of_mem_spanF (P : Place E FE)
    (hP : ∀ f : F, algebraMap F FE f ∈ P.toValuationSubring)
    {a : FE} (ha : a ∈ spanF F E FE) : a ∈ P.toValuationSubring := by
  have h : spanF F E FE ≤ placeSubmodule P :=
    Submodule.span_le.2 (by rintro _ ⟨f, rfl⟩; exact hP f)
  exact h ha

end Span

section OldPlaces

variable {K F E FE : Type*} [Field K] [Field F] [Field E] [Field FE]
    [Algebra K F] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE]

theorem apply_mul_inv_mem [IsAlgClosed K] [IsCurveOver K F]
    (p : Place K F) (P : Place E FE)
    (hcomap : P.toValuationSubring.comap (algebraMap F FE) = p.toValuationSubring)
    (hord : ∀ f : F, P.ord (algebraMap F FE f) = p.ord f)
    (D : Derivation K FE FE) (hDF : ∀ f : F, D (algebraMap F FE f) = 0)
    (hDE : ∀ e : E, D (algebraMap E FE e) ∈ Set.range (algebraMap E FE))
    {r : FE} (hr : r ∈ spanF F E FE) (hr0 : r ≠ 0) :
    D r * r⁻¹ ∈ P.toValuationSubring := by
  classical
  obtain ⟨n, β, u, hβ, hru⟩ := exists_linearIndependent_repr (K := K) hr
  have hDr : D r = ∑ k, D (algebraMap E FE (β k)) * algebraMap F FE (u k) := by
    rw [hru, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Derivation.leibniz, hDF, smul_zero, zero_add, smul_eq_mul, mul_comm]
  rw [hDr, Finset.sum_mul]
  refine sum_mem fun k _ => ?_
  rw [mul_assoc]
  refine mul_mem ?_ ?_
  · obtain ⟨c, hc⟩ := hDE (β k)
    rw [← hc]
    exact P.algebraMap_mem' c
  · by_cases huk : u k = 0
    · rw [huk, map_zero, zero_mul]; exact zero_mem _
    apply mem_of_ord_nonneg
    have hle := ord_sum_le p P hcomap hord Finset.univ β hβ u (Finset.mem_univ k) huk
    rw [← hru] at hle
    rw [P.ord_mul ((map_ne_zero _).2 huk) (inv_ne_zero hr0), P.ord_inv, hord]
    linarith

theorem map_mem_of_comap_eq [IsAlgClosed K] [IsCurveOver K F]
    (p : Place K F) (P : Place E FE)
    (hcomap : P.toValuationSubring.comap (algebraMap F FE) = p.toValuationSubring)
    (hord : ∀ f : F, P.ord (algebraMap F FE f) = p.ord f)
    (D : Derivation K FE FE) (hDF : ∀ f : F, D (algebraMap F FE f) = 0)
    (hDE : ∀ e : E, D (algebraMap E FE e) ∈ Set.range (algebraMap E FE))
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    {z : FE} (hz : z ∈ P.toValuationSubring) : D z ∈ P.toValuationSubring := by
  obtain ⟨r, hr, s, hs, hzrs⟩ := exists_eq_div_of_adjoin_eq_top hgen z
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [hzrs, zero_div, map_zero]; exact zero_mem _
  rcases eq_or_ne s 0 with rfl | hs0
  · rw [hzrs, div_zero, map_zero]; exact zero_mem _
  have hDz : D z = z * (D r * r⁻¹ - D s * s⁻¹) := by
    rw [hzrs, div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, smul_eq_mul, smul_eq_mul,
      smul_eq_mul]
    field_simp
    ring
  rw [hDz]
  exact mul_mem hz (sub_mem (apply_mul_inv_mem p P hcomap hord D hDF hDE hr hr0)
    (apply_mul_inv_mem p P hcomap hord D hDF hDE hs hs0))

end OldPlaces

section NewPlaces

variable {K F E FE : Type*} [Field K] [Field F] [Field E] [Field FE]
    [Algebra K F] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE]

theorem exists_comap_eq_of_not_forall_mem [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (P : Place E FE) (hP : ¬ ∀ f : F, algebraMap F FE f ∈ P.toValuationSubring) :
    ∃ p : Place K F, P.toValuationSubring.comap (algebraMap F FE) = p.toValuationSubring := by
  obtain ⟨x, -, hxfin⟩ := hfg
  haveI := hxfin
  push Not at hP
  obtain ⟨f, hf⟩ := hP
  set A := P.toValuationSubring.comap (algebraMap F FE) with hA
  have hAK : ∀ a : K, algebraMap K F a ∈ A := by
    intro a
    show algebraMap F FE (algebraMap K F a) ∈ P.toValuationSubring
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K E FE]
    exact P.algebraMap_mem' _
  have hAtop : A ≠ ⊤ := by
    intro h
    apply hf
    have : f ∈ A := by rw [h]; exact ValuationSubring.mem_top f
    exact this
  obtain ⟨p, hp⟩ := Place.exists_of_valuationSubring x A hAK hAtop
  exact ⟨p, hp.symm⟩

theorem forall_mem_of_forall_comap_ne [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (P : Place E FE)
    (hP : ∀ v : Place K F, P.toValuationSubring.comap (algebraMap F FE) ≠ v.toValuationSubring) :
    ∀ f : F, algebraMap F FE f ∈ P.toValuationSubring := by
  by_contra h
  obtain ⟨p, hp⟩ := exists_comap_eq_of_not_forall_mem hfg P h
  exact hP p hp

theorem map_mem_of_forall_mem [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    [IsAlgClosed E] [IsCurveOver E FE]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (D : Derivation K FE FE) (hDF : ∀ f : F, D (algebraMap F FE f) = 0)
    (hDE : ∀ e : E, D (algebraMap E FE e) ∈ Set.range (algebraMap E FE))
    (P : Place E FE) (hP : ∀ f : F, algebraMap F FE f ∈ P.toValuationSubring)
    {z : FE} (hz : z ∈ P.toValuationSubring) : D z ∈ P.toValuationSubring := by
  classical
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [map_zero]; exact zero_mem _
  obtain ⟨huniq, hexist⟩ :=
    Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension K F hfg E FE hfgE hgen

  have hcentre : ∀ Q : Place E FE, (∀ f : F, algebraMap F FE f ∈ Q.toValuationSubring) →
      ∃ e : F →ₐ[K] E, ∀ f : F, ∃ hm : algebraMap F FE f - algebraMap E FE (e f) ∈
        Q.toValuationSubring, (⟨_, hm⟩ : Q.toValuationSubring) ∈
          IsLocalRing.maximalIdeal Q.toValuationSubring := by
    intro Q hQ
    obtain ⟨e, he⟩ := hexist Q hQ
    refine ⟨e, fun f => ?_⟩
    have hm : algebraMap F FE f - algebraMap E FE (e f) ∈ Q.toValuationSubring :=
      (Q.toValuationSubring.valuation_le_one_iff _).1 (he f).le
    exact ⟨hm, (Q.toValuationSubring.valuation_lt_one_iff ⟨_, hm⟩).2 (he f)⟩
  obtain ⟨eP, heP⟩ := hcentre P hP

  have hsep : ∀ Q : Place E FE, Q ≠ P → (∀ f : F, algebraMap F FE f ∈ Q.toValuationSubring) →
      ∃ g : FE, g ∈ spanF F E FE ∧ 1 ≤ Q.ord g ∧ g ≠ 0 ∧ g⁻¹ ∈ P.toValuationSubring := by
    intro Q hQP hQ
    obtain ⟨eQ, heQ⟩ := hcentre Q hQ

    have hne : eP ≠ eQ := by
      intro h
      apply hQP
      have hPval : ∀ f : F, P.toValuationSubring.valuation
          (algebraMap F FE f - algebraMap E FE (eP f)) < 1 := fun f => by
        obtain ⟨hm, hmax⟩ := heP f
        exact (P.toValuationSubring.valuation_lt_one_iff ⟨_, hm⟩).1 hmax
      have hQval : ∀ f : F, Q.toValuationSubring.valuation
          (algebraMap F FE f - algebraMap E FE (eP f)) < 1 := fun f => by
        obtain ⟨hm, hmax⟩ := heQ f
        rw [h]
        exact (Q.toValuationSubring.valuation_lt_one_iff ⟨_, hm⟩).1 hmax
      exact (huniq eP).unique hQval hPval
    obtain ⟨f₀, hf₀⟩ : ∃ f₀ : F, eP f₀ ≠ eQ f₀ := by
      by_contra h
      push Not at h
      exact hne (AlgHom.ext h)
    set g := algebraMap F FE f₀ - algebraMap E FE (eQ f₀) with hg
    obtain ⟨hmQ, hmaxQ⟩ := heQ f₀
    obtain ⟨hmP, hmaxP⟩ := heP f₀

    set c : E := eP f₀ - eQ f₀ with hc
    have hc0 : c ≠ 0 := sub_ne_zero.2 hf₀
    have hcunit : IsUnit (⟨algebraMap E FE c, P.algebraMap_mem' c⟩ : P.toValuationSubring) := by
      apply isUnit_of_ord_eq_zero P
      · intro h
        have : algebraMap E FE c = 0 := by simpa using congrArg Subtype.val h
        exact hc0 ((map_eq_zero _).1 this)
      · exact ord_algebraMap P c
    have hunit := isUnit_add_of_mem_maximalIdeal P hcunit hmaxP
    have hcoe : (((⟨algebraMap E FE c, P.algebraMap_mem' c⟩ : P.toValuationSubring) +
        ⟨_, hmP⟩ : P.toValuationSubring) : FE) = g := by
      push_cast
      rw [hg, hc, map_sub]
      ring
    have hg0 : g ≠ 0 := by
      rw [← hcoe]
      exact_mod_cast hunit.ne_zero
    refine ⟨g, ?_, ?_, hg0, ?_⟩
    · exact sub_mem (algebraMap_mem_spanF f₀) (algebraMap_left_mem_spanF _)
    · have hgQ0 : (⟨g, hmQ⟩ : Q.toValuationSubring) ≠ 0 := by
        intro h
        exact hg0 (by simpa using congrArg Subtype.val h)
      have := ord_pos_of_mem_maximalIdeal Q hmaxQ hgQ0
      exact this
    · apply inv_mem_of_ord_eq_zero
      rw [← hcoe]
      exact ord_coe_isUnit P hunit

  obtain ⟨Dv, hDv, -⟩ := HasPrincipalDivisors.exists_divisor (K := E) z hz0
  set T := Dv.support.filter
    (fun Q => Q ≠ P ∧ ∀ f : F, algebraMap F FE f ∈ Q.toValuationSubring) with hT
  have hg : ∀ Q ∈ T, ∃ g : FE, g ∈ spanF F E FE ∧ 1 ≤ Q.ord g ∧ g ≠ 0 ∧
      g⁻¹ ∈ P.toValuationSubring := by
    intro Q hQ
    obtain ⟨hQP, hQnew⟩ := (Finset.mem_filter.1 hQ).2
    exact hsep Q hQP hQnew
  choose! g hgspan hgord hg0 hginv using hg
  set n : Place E FE → ℕ := fun Q => (-(Dv Q)).toNat with hn
  set h : FE := ∏ Q ∈ T, g Q ^ n Q with hh
  have hhspan : h ∈ spanF F E FE := by
    rw [← mem_spanSubalgebra]
    exact Subalgebra.prod_mem _ fun Q hQ =>
      Subalgebra.pow_mem _ ((mem_spanSubalgebra).2 (hgspan Q hQ)) _
  have hh0 : h ≠ 0 := Finset.prod_ne_zero_iff.2 fun Q hQ => pow_ne_zero _ (hg0 Q hQ)
  have hhinv : h⁻¹ ∈ P.toValuationSubring := by
    rw [hh, ← Finset.prod_inv_distrib]
    exact prod_mem fun Q hQ => by rw [← inv_pow]; exact pow_mem (hginv Q hQ) _

  have hw : ∀ Q : Place E FE, (∀ f : F, algebraMap F FE f ∈ Q.toValuationSubring) →
      h * z ∈ Q.toValuationSubring := by
    intro Q hQnew
    by_cases hQP : Q = P
    · subst hQP
      exact mul_mem (mem_of_mem_spanF Q hQnew hhspan) hz
    by_cases hQT : Q ∈ T
    · rw [hh, ← Finset.mul_prod_erase T (fun Q => g Q ^ n Q) hQT, mul_comm, ← mul_assoc]
      refine mul_mem ?_ (prod_mem fun Q' hQ' =>
        pow_mem (mem_of_mem_spanF Q hQnew (hgspan Q' (Finset.mem_of_mem_erase hQ'))) _)
      apply mem_of_ord_nonneg
      rw [Q.ord_mul hz0 (pow_ne_zero _ (hg0 Q hQT)), ← zpow_natCast, Q.ord_zpow, ← hDv Q]
      have h1 := hgord Q hQT
      have h2 : (-(Dv Q)) ≤ ((n Q : ℕ) : ℤ) := Int.self_le_toNat _
      nlinarith
    · have hDvQ : Dv Q = 0 := by
        by_contra hne
        exact hQT (Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 hne, hQP, hQnew⟩)
      refine mul_mem (mem_of_mem_spanF Q hQnew hhspan) (mem_of_ord_nonneg Q ?_)
      rw [← hDv Q, hDvQ]

  have hwspan : h * z ∈ spanF F E FE :=
    AlgebraicCurve.mem_span_range_algebraMap_of_constantFieldExtension K F E FE hfg hfgE hgen
      (h * z) fun Q hQ => hw Q (forall_mem_of_forall_comap_ne hfg Q hQ)

  have hDz : D z = h⁻¹ * (D (h * z) - D h * z) := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    field_simp
    ring
  rw [hDz]
  exact mul_mem hhinv (sub_mem (mem_of_mem_spanF P hP (map_mem_spanF D hDF hDE hwspan))
    (mul_mem (mem_of_mem_spanF P hP (map_mem_spanF D hDF hDE hhspan)) hz))

end NewPlaces

section Assembly

theorem exists_derivation_map_mem (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE]
    [Algebra K F] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (δ : Derivation K E E) :
    ∃ D : Derivation K FE FE,
      (∀ f : F, D (algebraMap F FE f) = 0) ∧
      (∀ e : E, D (algebraMap E FE e) = algebraMap E FE (δ e)) ∧
      ∀ (P : Place E FE) (z : FE), z ∈ P.toValuationSubring → D z ∈ P.toValuationSubring := by
  obtain ⟨D, hDF, hDE⟩ := exists_derivation K F E FE hfg hfgE hgen δ
  have hDE' : ∀ e : E, D (algebraMap E FE e) ∈ Set.range (algebraMap E FE) :=
    fun e => ⟨δ e, (hDE e).symm⟩
  refine ⟨D, hDF, hDE, fun P z hz => ?_⟩
  by_cases hP : ∀ f : F, algebraMap F FE f ∈ P.toValuationSubring
  · exact map_mem_of_forall_mem hfg hfgE hgen D hDF hDE' P hP hz
  · obtain ⟨p, hp⟩ := exists_comap_eq_of_not_forall_mem hfg P hP
    obtain ⟨P', hP'comap, hP'ord, hP'uniq⟩ :=
      Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F E FE hfg hfgE hgen p
    have hPP' : P = P' := hP'uniq P hp
    subst hPP'
    exact map_mem_of_comap_eq p P hp hP'ord D hDF hDE' hgen hz

end Assembly

end AlgebraicCurve.HorizDeriv

end

p2m_open "AlgebraicCurve~finiteDimensional_adjoin_of_transcendental" in open _root_.P2MW.S_AlgebraicCurve_exists_derivation_constantFieldExtension_map_mem.AlgebraicCurve in
theorem solution
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE]
    [Algebra K F] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (δ : Derivation K E E) :
    ∃ D : Derivation K FE FE,
      (∀ f : F, D (algebraMap F FE f) = 0) ∧
      (∀ e : E, D (algebraMap E FE e) = algebraMap E FE (δ e)) ∧
      ∀ (P : Place E FE) (z : FE), z ∈ P.toValuationSubring → D z ∈ P.toValuationSubring :=
  AlgebraicCurve.HorizDeriv.exists_derivation_map_mem K F E FE hfg hfgE hgen δ

end S_AlgebraicCurve_exists_derivation_constantFieldExtension_map_mem
end P2MW
export P2MW.S_AlgebraicCurve_exists_derivation_constantFieldExtension_map_mem (solution)
