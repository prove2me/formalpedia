-- Prove2me | solution 1 for AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/5f4d3769-accf-57b3-8560-f31fd24cd3ec

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_AlgebraicCurve_ell_sub_ell_le_degree_sub_degree
import Theorems.Thm_AlgebraicCurve_constantFieldDegreeFormula_of_isConstantFieldExtension_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_Place_exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Place.ext Divisor HasPrincipalDivisors genusFF LSpace ell mem_lSpace_iff_ord ConstantsAreBase ell_zero_eq_one_of_constantsAreBase RiemannGenusReachedAt Place.forgetConstants Place.ord_forgetConstants Place.restrictConstants Place.restrictConstants_toValuationSubring Place.ord_restrictConstants Divisor.pullbackConstants Divisor.pullbackConstants_apply ConstantFieldDegreeFormula ConstantFieldDegreeFormula.degree_pullbackConstants Place.ramificationIndex SemilinearAut SemilinearAut.baseAut SemilinearAut.smul_algebraMap SemilinearAut.smul_toValuationSubring SemilinearAut.ord_smul IsCurveOver.exists_separating_transcendental constantsAreBase_of_isAlgClosed_of_transcendental isCurveOver_of_transcendental_of_perfectField Place.ord_eq_zero_of_isAlgebraic genusFF_eq_of_constantFieldExtension_of_isAlgClosed stichtenothGenusExists_of_isCurveOver indexOfSpecialty_eq_of_genusReached indexOfSpecialty_eq_finrank_H1 finiteDimensional_lSpace ell_sub_ell_le_degree_sub_degree constantFieldDegreeFormula_of_isConstantFieldExtension_of_isCurveOver Place.exists_forgetConstants_restrict_eq_of_isConstantFieldExtension"
namespace GenusFinToAlgClosedG
p2m_open "AlgebraicCurve"

section Engine

p2m_open "Polynomial IntermediateField AlgebraicCurve P2MW.S_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed.AlgebraicCurve"

section Genus

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem finiteDimensional_lSpace_zero_of_constantsAreBase (hC : ConstantsAreBase K F) :
    FiniteDimensional K (LSpace (0 : Divisor K F)) := by
  rw [hC]; infer_instance

theorem genusFF_eq_of_riemannGenusReachedAt [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))] (hC : ConstantsAreBase K F)
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) : (genusFF K F : ℤ) = γ := by
  have h1 := (indexOfSpecialty_eq_of_genusReached h 0).2
  rw [indexOfSpecialty_eq_finrank_H1, ell_zero_eq_one_of_constantsAreBase hC, map_zero] at h1
  rw [genusFF]
  push_cast at h1 ⊢
  linarith

theorem exists_riemannGenusReachedAt_genusFF [PerfectField K] [Algebra.EssFiniteType K F]
    [IsCurveOver K F] (hC : ConstantsAreBase K F) :
    Nonempty (Place K F) ∧ ∃ D₀ : Divisor K F, RiemannGenusReachedAt (genusFF K F : ℤ) D₀ := by
  obtain ⟨hne, hfin, γ, D₀, hR⟩ := stichtenothGenusExists_of_isCurveOver hC
  haveI := hne
  haveI := hfin
  have hg := genusFF_eq_of_riemannGenusReachedAt hC hR
  exact ⟨hne, D₀, hg ▸ hR⟩

end Genus

section LinAlg

variable {R V : Type*} [Field R] [AddCommGroup V] [Module R V]

theorem mem_of_combinations_mem {n : Type*} [Fintype n] [DecidableEq n] (N : Matrix n n R)
    (hN : N.det ≠ 0) (S : Submodule R V) (u : n → V) (h : ∀ j, ∑ i, N j i • u i ∈ S) (i : n) :
    u i ∈ S := by
  have hadj : ∀ k, (∑ j, N.adjugate i j * N j k) = if i = k then N.det else 0 := fun k => by
    have h1 := congrFun (congrFun (Matrix.adjugate_mul N) i) k
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero] at h1
    exact h1
  have key : ∑ j, N.adjugate i j • ∑ k, N j k • u k = N.det • u i := by
    calc ∑ j, N.adjugate i j • ∑ k, N j k • u k
        = ∑ j, ∑ k, (N.adjugate i j * N j k) • u k := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun k _ => smul_smul _ _ _
      _ = ∑ k, (∑ j, N.adjugate i j * N j k) • u k := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => (Finset.sum_smul).symm
      _ = N.det • u i := by
          simp_rw [hadj, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hmem : N.det • u i ∈ S := key ▸ S.sum_mem fun j _ => S.smul_mem _ (h j)
  simpa [smul_smul, inv_mul_cancel₀ hN] using S.smul_mem N.det⁻¹ hmem

end LinAlg

section Compare

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
  [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] [HasPrincipalDivisors K' F']

theorem algebraMap_mem_lSpace_pullbackConstants {D : Divisor K F} {y : F} (hy : y ∈ LSpace D) :
    algebraMap F F' y ∈ LSpace (Divisor.pullbackConstants K' F' D) := by
  rw [mem_lSpace_iff_ord] at hy ⊢
  rcases hy with rfl | hy
  · exact Or.inl (map_zero _)
  refine Or.inr fun w => ?_
  rw [Divisor.pullbackConstants_apply, Place.ord_restrictConstants (K := K)]
  have h1 := hy (Place.restrictConstants F (K := K) w)
  have h2 : (0 : ℤ) ≤ (Place.forgetConstants (K := K) w).ramificationIndex F := by positivity
  nlinarith

theorem mem_lSpace_of_algebraMap_mem
    (hsurj : ∀ v : Place K F, ∃ w : Place K' F', Place.restrictConstants F (K := K) w = v)
    {D : Divisor K F} {y : F}
    (hy : algebraMap F F' y ∈ LSpace (Divisor.pullbackConstants K' F' D)) : y ∈ LSpace D := by
  rw [mem_lSpace_iff_ord] at hy ⊢
  rcases hy with h0 | hy
  · exact Or.inl ((map_eq_zero_iff _ (algebraMap F F').injective).mp h0)
  refine Or.inr fun v => ?_
  obtain ⟨w, rfl⟩ := hsurj v
  have h1 := hy w
  rw [Divisor.pullbackConstants_apply, Place.ord_restrictConstants (K := K)] at h1
  have h2 : (0 : ℤ) < (Place.forgetConstants (K := K) w).ramificationIndex F := by
    exact_mod_cast (Place.forgetConstants (K := K) w).ramificationIndex_pos (F := F)
  by_contra hlt
  push Not at hlt
  have : ((Place.forgetConstants (K := K) w).ramificationIndex F : ℤ)
      * (Place.restrictConstants F (K := K) w).ord y
        ≤ ((Place.forgetConstants (K := K) w).ramificationIndex F : ℤ)
          * (-D (Place.restrictConstants F (K := K) w) - 1) :=
    mul_le_mul_of_nonneg_left (by omega) h2.le
  nlinarith

theorem ell_le_ell_pullbackConstants
    (hLD : ∀ (n : ℕ) (b : Fin n → F), LinearIndependent K b →
      LinearIndependent K' (fun i => algebraMap F F' (b i)))
    (D : Divisor K F) [FiniteDimensional K (LSpace D)]
    [FiniteDimensional K' (LSpace (Divisor.pullbackConstants K' F' D))] :
    ell D ≤ ell (Divisor.pullbackConstants K' F' D) := by
  set b := Module.finBasis K (LSpace D)
  have hb : LinearIndependent K (fun i => (b i : F)) :=
    b.linearIndependent.map' (LSpace D).subtype (Submodule.ker_subtype _)
  have hb' := hLD _ _ hb
  let c : Fin (Module.finrank K (LSpace D)) → LSpace (Divisor.pullbackConstants K' F' D) :=
    fun i => ⟨algebraMap F F' (b i), algebraMap_mem_lSpace_pullbackConstants (b i).2⟩
  have hc : LinearIndependent K' c :=
    LinearIndependent.of_comp (LSpace (Divisor.pullbackConstants K' F' D)).subtype hb'
  simpa [ell] using hc.fintype_card_le_finrank

theorem pullbackConstants_apply_smul {g : SemilinearAut K' F'}
    (hg : ∀ y : F, g • algebraMap F F' y = algebraMap F F' y) (D : Divisor K F)
    (w : Place K' F') :
    Divisor.pullbackConstants K' F' D (g • w) = Divisor.pullbackConstants K' F' D w := by
  have hg' : ∀ y : F, g⁻¹ • algebraMap F F' y = algebraMap F F' y := fun y => by
    conv_lhs => rw [← hg y]
    rw [inv_smul_smul]
  have hord : ∀ y : F, (g • w).ord (algebraMap F F' y) = w.ord (algebraMap F F' y) := fun y => by
    conv_lhs => rw [← hg y]
    exact SemilinearAut.ord_smul g w _
  have hres : Place.restrictConstants F (K := K) (g • w) = Place.restrictConstants F (K := K) w := by
    apply Place.ext
    rw [Place.restrictConstants_toValuationSubring, Place.restrictConstants_toValuationSubring]
    ext y
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
      SemilinearAut.smul_toValuationSubring,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hg']
  have hram : (Place.forgetConstants (K := K) (g • w)).ramificationIndex F
      = (Place.forgetConstants (K := K) w).ramificationIndex F := by
    simp only [Place.ramificationIndex, Place.ord_forgetConstants, hord]
  rw [Divisor.pullbackConstants_apply, Divisor.pullbackConstants_apply, hres, hram]

theorem smul_mem_lSpace_pullbackConstants {g : SemilinearAut K' F'}
    (hg : ∀ y : F, g • algebraMap F F' y = algebraMap F F' y) {D : Divisor K F} {z : F'}
    (hz : z ∈ LSpace (Divisor.pullbackConstants K' F' D)) :
    g • z ∈ LSpace (Divisor.pullbackConstants K' F' D) := by
  rw [mem_lSpace_iff_ord] at hz ⊢
  rcases hz with rfl | hz
  · exact Or.inl (smul_zero g)
  refine Or.inr fun w' => ?_
  have hw : w' = g • (g⁻¹ • w') := (smul_inv_smul g w').symm
  rw [hw, SemilinearAut.ord_smul, pullbackConstants_apply_smul hg]
  exact hz _

omit [Algebra.IsIntegral F F'] [HasPrincipalDivisors K' F'] in

theorem exists_eq_sum_basis [Algebra.IsAlgebraic K K']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤) (z : F') :
    ∃ (E : IntermediateField K K') (_ : FiniteDimensional K E)
      (y : Fin (Module.finrank K E) → F),
      z = ∑ i, algebraMap F F' (y i) * algebraMap K' F' (Module.finBasis K E i) := by
  classical

  have hspan : z ∈ Submodule.span F (Set.range (algebraMap K' F')) := by
    have hz : z ∈ Subalgebra.toSubmodule (Algebra.adjoin F (Set.range (algebraMap K' F'))) := by
      rw [hgen]; trivial
    rw [Algebra.adjoin_eq_span] at hz
    have hcl : (Submonoid.closure (Set.range (algebraMap K' F')) : Set F')
        = Set.range (algebraMap K' F') := by
      have : Set.range (algebraMap K' F')
          = ((MonoidHom.mrange ((algebraMap K' F' : K' →+* F') : K' →* F')) : Set F') := by
        ext x; simp
      rw [this, Submonoid.closure_eq]
    rwa [hcl] at hz
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hspan

  set S : Set K' := (c.support : Set K')
  let E : IntermediateField K K' := IntermediateField.adjoin K S
  haveI : Finite S := (c.support.finite_toSet).to_subtype
  haveI hE : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsIntegral.isIntegral x)
  set b := Module.finBasis K E
  have hmemE : ∀ a ∈ c.support, (a : K') ∈ E := fun a ha =>
    IntermediateField.subset_adjoin K S (by exact_mod_cast ha)

  let r : K' → Fin (Module.finrank K E) → K := fun a i =>
    if ha : a ∈ c.support then b.repr ⟨a, hmemE a ha⟩ i else 0
  have hexp : ∀ a ∈ c.support,
      algebraMap K' F' a = ∑ i, algebraMap K F' (r a i) * algebraMap K' F' (b i : K') := by
    intro a ha
    have h1 : (⟨a, hmemE a ha⟩ : E) = ∑ i, b.repr ⟨a, hmemE a ha⟩ i • b i :=
      (b.sum_repr _).symm
    have h2 : (a : K') = ∑ i, b.repr ⟨a, hmemE a ha⟩ i • (b i : K') := by
      have := congrArg (fun x : E => (x : K')) h1
      simpa only [IntermediateField.coe_sum, IntermediateField.coe_smul] using this
    conv_lhs => rw [h2, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
    simp only [r, dif_pos ha]
  refine ⟨E, hE, fun i => ∑ a ∈ c.support, algebraMap K F (r a i) * c a, ?_⟩
  rw [← hc]
  simp_rw [map_sum, Finset.sum_mul, map_mul, ← IsScalarTower.algebraMap_apply K F F']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finsupp.sum] at hc
  show c a • algebraMap K' F' a = _
  rw [Algebra.smul_def, hexp a ha, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem lSpace_pullbackConstants_le_span [PerfectField K] [IsAlgClosed K']
    [Algebra.IsAlgebraic K K']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hsurj : ∀ v : Place K F, ∃ w : Place K' F', Place.restrictConstants F (K := K) w = v)
    (hAut : ∀ σ : K' ≃ₐ[K] K', ∃ g : SemilinearAut K' F',
      (∀ a : K', SemilinearAut.baseAut g a = σ a) ∧
        ∀ y : F, g • algebraMap F F' y = algebraMap F F' y)
    (D : Divisor K F) :
    LSpace (Divisor.pullbackConstants K' F' D)
      ≤ Submodule.span K' (algebraMap F F' '' (LSpace D : Set F)) := by
  classical
  intro z hz
  obtain ⟨E, hE, y, rfl⟩ := exists_eq_sum_basis (K := K) hgen z
  set b := Module.finBasis K E
  haveI : Algebra.IsSeparable K E := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsAlgClosure K K' := ⟨‹IsAlgClosed K'›, ‹Algebra.IsAlgebraic K K'›⟩

  have hcard : Fintype.card (E →ₐ[K] K') = Module.finrank K E := AlgHom.card K E K'
  let e : Fin (Module.finrank K E) ≃ (E →ₐ[K] K') := (Fintype.equivFinOfCardEq hcard).symm
  let M : Matrix (Fin (Module.finrank K E)) (Fin (Module.finrank K E)) K' := Algebra.embeddingsMatrixReindex K K' (fun i => b i) e
  have hM : M.det ≠ 0 := by
    intro h0
    have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two K K' (fun i => b i) e
    rw [show Algebra.embeddingsMatrixReindex K K' (fun i => b i) e = M from rfl, h0,
      zero_pow two_ne_zero, map_eq_zero] at h1
    exact Algebra.discr_not_zero_of_basis K b h1
  have hMapply : ∀ i j, M i j = e j (b i) := fun i j => rfl

  have hext : ∀ j : Fin (Module.finrank K E), ∃ g : SemilinearAut K' F',
      (∀ x : E, SemilinearAut.baseAut g (x : K') = e j x) ∧
        ∀ y : F, g • algebraMap F F' y = algebraMap F F' y := by
    intro j
    let τ : K' →ₐ[K] K' := (e j).liftNormal K'
    let τ' : K' ≃ₐ[K] K' := AlgEquiv.ofBijective τ (Algebra.IsAlgebraic.algHom_bijective τ)
    obtain ⟨g, hg1, hg2⟩ := hAut τ'
    refine ⟨g, fun x => ?_, hg2⟩
    rw [hg1]
    show τ (algebraMap E K' x) = _
    rw [AlgHom.liftNormal_commutes]
    rfl
  choose g hgb hgF using hext

  let u : Fin (Module.finrank K E) → F' := fun i => algebraMap F F' (y i)
  have hcomb : ∀ j, ∑ i, M.transpose j i • u i ∈ LSpace (Divisor.pullbackConstants K' F' D) := by
    intro j
    have h1 := smul_mem_lSpace_pullbackConstants (hgF j) hz
    have h2 : g j • ∑ i, algebraMap F F' (y i) * algebraMap K' F' (b i : K')
        = ∑ i, M.transpose j i • u i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul', hgF j, SemilinearAut.smul_algebraMap, hgb, Matrix.transpose_apply,
        hMapply, Algebra.smul_def, mul_comm]
    rwa [h2] at h1
  have hu : ∀ i, u i ∈ LSpace (Divisor.pullbackConstants K' F' D) :=
    mem_of_combinations_mem M.transpose (by rwa [Matrix.det_transpose]) _ u hcomb

  have hy : ∀ i, y i ∈ LSpace D := fun i => mem_lSpace_of_algebraMap_mem hsurj (hu i)
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y i, hy i, rfl⟩)

theorem ell_pullbackConstants_le_ell [PerfectField K] [IsAlgClosed K']
    [Algebra.IsAlgebraic K K']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hsurj : ∀ v : Place K F, ∃ w : Place K' F', Place.restrictConstants F (K := K) w = v)
    (hAut : ∀ σ : K' ≃ₐ[K] K', ∃ g : SemilinearAut K' F',
      (∀ a : K', SemilinearAut.baseAut g a = σ a) ∧
        ∀ y : F, g • algebraMap F F' y = algebraMap F F' y)
    (D : Divisor K F) [FiniteDimensional K (LSpace D)] :
    ell (Divisor.pullbackConstants K' F' D) ≤ ell D := by
  classical
  set b := Module.finBasis K (LSpace D)
  let s : Set F' := Set.range fun i => algebraMap F F' (b i : F)
  have hle : Submodule.span K' (algebraMap F F' '' (LSpace D : Set F)) ≤ Submodule.span K' s := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (⟨x, hx⟩ : LSpace D) = ∑ i, b.repr ⟨x, hx⟩ i • b i := (b.sum_repr _).symm
    have hx'' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : F) := by
      have := congrArg (fun t : LSpace D => (t : F)) hx'
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using this
    rw [hx'', map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply K K' F', ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : Module.Finite K' (Submodule.span K' s) := Module.Finite.span_of_finite K' (Set.finite_range _)
  calc ell (Divisor.pullbackConstants K' F' D)
      ≤ Module.finrank K' (Submodule.span K' s) :=
        Submodule.finrank_mono ((lSpace_pullbackConstants_le_span hgen hsurj hAut D).trans hle)
    _ ≤ Fintype.card (Fin (Module.finrank K (LSpace D))) := finrank_range_le_card _
    _ = ell D := by simp [ell]

theorem exists_le_pullbackConstants (D' : Divisor K' F') :
    ∃ D : Divisor K F, D' ≤ Divisor.pullbackConstants K' F' D := by
  classical
  let D : Divisor K F :=
    ∑ w ∈ D'.support, Finsupp.single (Place.restrictConstants F (K := K) w) |D' w|
  have hnn : ∀ (x : Place K' F') (v : Place K F),
      0 ≤ (Finsupp.single (Place.restrictConstants F (K := K) x) |D' x| : Divisor K F) v :=
    fun x v => by
      rw [Finsupp.single_apply]; split_ifs <;> simp [abs_nonneg]
  have hD0 : ∀ v, 0 ≤ D v := fun v => by
    simp only [D, Finsupp.finsetSum_apply]
    exact Finset.sum_nonneg fun x _ => hnn x v
  refine ⟨D, fun w => ?_⟩
  rw [Divisor.pullbackConstants_apply]
  have he : (1 : ℤ) ≤ (Place.forgetConstants (K := K) w).ramificationIndex F := by
    exact_mod_cast (Place.forgetConstants (K := K) w).ramificationIndex_pos (F := F)
  by_cases hw : w ∈ D'.support
  · have h1 : |D' w| ≤ D (Place.restrictConstants F (K := K) w) := by
      have := Finset.single_le_sum (s := D'.support)
        (f := fun x => (Finsupp.single (Place.restrictConstants F (K := K) x) |D' x| :
          Divisor K F) (Place.restrictConstants F (K := K) w))
        (fun x _ => hnn x _) hw
      simpa only [D, Finsupp.finsetSum_apply, Finsupp.single_eq_same] using this
    calc D' w ≤ |D' w| := le_abs_self _
      _ ≤ 1 * D (Place.restrictConstants F (K := K) w) := by rw [one_mul]; exact h1
      _ ≤ _ := mul_le_mul_of_nonneg_right he ((abs_nonneg _).trans h1)
  · rw [Finsupp.notMem_support_iff.mp hw]
    exact mul_nonneg (by positivity) (hD0 _)

theorem genusFF_eq_of_perfectField [PerfectField K] [IsAlgClosed K'] [Algebra.IsAlgebraic K K']
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [Algebra.EssFiniteType K' F'] [IsCurveOver K' F']
    (hC : ConstantsAreBase K F) (hC' : ConstantsAreBase K' F')
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (hconst : ∀ y : F, IsAlgebraic K y → y ∈ (algebraMap K F).range)
    (hLD : ∀ (n : ℕ) (b : Fin n → F), LinearIndependent K b →
      LinearIndependent K' (fun i => algebraMap F F' (b i)))
    (hAut : ∀ σ : K' ≃ₐ[K] K', ∃ g : SemilinearAut K' F',
      (∀ a : K', SemilinearAut.baseAut g a = σ a) ∧
        ∀ y : F, g • algebraMap F F' y = algebraMap F F' y) :
    genusFF K F = genusFF K' F' := by
  haveI : Algebra.IsSeparable K K' := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI := finiteDimensional_lSpace_zero_of_constantsAreBase hC
  haveI := finiteDimensional_lSpace_zero_of_constantsAreBase hC'
  obtain ⟨hne, D₀, hR⟩ := exists_riemannGenusReachedAt_genusFF hC
  obtain ⟨hne', D₀', hR'⟩ := exists_riemannGenusReachedAt_genusFF hC'
  haveI := hne
  haveI := hne'
  haveI : ConstantFieldDegreeFormula K K' F F' :=
    constantFieldDegreeFormula_of_isConstantFieldExtension_of_isCurveOver hgen hconst
  have hsurj : ∀ v : Place K F, ∃ w : Place K' F', Place.restrictConstants F (K := K) w = v :=
    fun v => Place.exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
      hgen hconst (M := F) v
  have hdeg := ConstantFieldDegreeFormula.degree_pullbackConstants (K := K) (K' := K')
    (F := F) (F' := F')
  apply le_antisymm
  ·
    have h1 := hR.eq
    have h2 := hR'.isMax (Divisor.pullbackConstants K' F' D₀)
    haveI := finiteDimensional_lSpace (K := K) (F := F) D₀
    have h3 : (ell (Divisor.pullbackConstants K' F' D₀) : ℤ) ≤ ell D₀ := by
      exact_mod_cast ell_pullbackConstants_le_ell hgen hsurj hAut D₀
    rw [hdeg] at h2
    have : (genusFF K F : ℤ) ≤ genusFF K' F' := by linarith
    exact_mod_cast this
  ·
    obtain ⟨D, hD⟩ := exists_le_pullbackConstants (K := K) (F := F) D₀'
    haveI := finiteDimensional_lSpace (K := K') (F := F') (Divisor.pullbackConstants K' F' D)
    haveI := finiteDimensional_lSpace (K := K) (F := F) D
    have h1 := hR'.eq
    have h2 := ell_sub_ell_le_degree_sub_degree hD
    have h3 := hR.isMax D
    have h4 : (ell D : ℤ) ≤ ell (Divisor.pullbackConstants K' F' D) := by
      exact_mod_cast ell_le_ell_pullbackConstants hLD D
    rw [hdeg] at h2
    have : (genusFF K' F' : ℤ) ≤ genusFF K F := by linarith
    exact_mod_cast this

end Compare

end Engine

section Constants

variable {k K F₀ F : Type*} [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F]

theorem exists_constantEmbedding :
    ∃ j : k →+* K, ∀ a : k, algebraMap K F (j a) = algebraMap F₀ F (algebraMap k F₀ a) := by
  letI : Fintype k := Fintype.ofFinite k
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have hmem : ∀ a : k, algebraMap F₀ F (algebraMap k F₀ a) ∈ (algebraMap K F).range := by
    intro a
    set y := algebraMap F₀ F (algebraMap k F₀ a) with hydef
    have hy : y ^ Fintype.card k = y := by
      rw [hydef, ← map_pow, ← map_pow, FiniteField.pow_card]
    have hint : IsIntegral K y := by
      refine ⟨Polynomial.X ^ Fintype.card k - Polynomial.X, ?_, ?_⟩
      · exact (Polynomial.monic_X_pow _).sub_of_left
          (by rw [Polynomial.degree_X_pow, Polynomial.degree_X]; exact_mod_cast hq)
      · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, hy, sub_self]
    have hdeg : (minpoly K y).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
    exact minpoly.mem_range_of_degree_eq_one K y hdeg
  choose j hj using fun a => RingHom.mem_range.mp (hmem a)
  have hinj := (algebraMap K F).injective
  refine ⟨{ toFun := j, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hj⟩
  · apply hinj
    rw [hj, map_one, map_one, map_one]
  · intro a b
    apply hinj
    rw [map_mul, hj, hj, hj, map_mul, map_mul]
  · apply hinj
    rw [hj, map_zero, map_zero, map_zero]
  · intro a b
    apply hinj
    rw [map_add, hj, hj, hj, map_add, map_add]

omit [IsAlgClosed K] [Algebra K F] [Algebra F₀ F] in

theorem mem_range_algebraMap_of_pow_card_eq {L : Type*} [Field L] [Algebra k L] {y : L}
    (hy : y ^ Nat.card k = y) : y ∈ Set.range (algebraMap k L) := by
  classical
  letI : Fintype k := Fintype.ofFinite k
  have hq : 1 < Nat.card k := by rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  by_contra hy'
  set Z : Finset L := insert y (Finset.univ.image (algebraMap k L)) with hZ
  have hyZ : y ∉ Finset.univ.image (algebraMap k L) := by
    intro h
    apply hy'
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp h
    exact ⟨a, ha⟩
  have hcardZ : Z.card = Nat.card k + 1 := by
    rw [hZ, Finset.card_insert_of_notMem hyZ,
      Finset.card_image_of_injective _ (algebraMap k L).injective, Finset.card_univ,
      Nat.card_eq_fintype_card]
  have hsub : Z.val ⊆ (Polynomial.X ^ Nat.card k - Polynomial.X : Polynomial L).roots := by
    intro z hz
    rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero _ hq)]
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      sub_eq_zero]
    rcases Finset.mem_insert.mp (Finset.mem_val.mp hz) with rfl | hz''
    · exact hy
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz''
      rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ hq, hcardZ] at hle
  omega

variable [Algebra k K]

variable [Algebra k F] [IsScalarTower k K F] [IsScalarTower k F₀ F]

theorem linearDisjoint (φ : F →ₐ[K] F)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k)) :
    ∀ (n : ℕ) (f : Fin n → F₀) (c : Fin n → K), LinearIndependent k f →
      ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) = 0 → ∀ i, c i = 0 := by
  classical
  intro n f c hf hrel
  letI : Fintype k := Fintype.ofFinite k

  obtain ⟨p, hchar⟩ := CharP.exists k
  haveI hp : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  obtain ⟨m, -, hqm⟩ := FiniteField.card k p
  have hq : Nat.card k = p ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hqm]
  have hq0 : Nat.card k ≠ 0 := by rw [hq]; exact pow_ne_zero _ hp.out.ne_zero
  haveI : CharP F₀ p := charP_of_injective_algebraMap (algebraMap k F₀).injective p
  haveI : CharP F p := charP_of_injective_ringHom (algebraMap F₀ F).injective p
  haveI : CharP K p := ((algebraMap K F).charP_iff_charP p).mpr inferInstance

  let ρ : K ≃+* K := (iterateFrobeniusEquiv K p m).symm
  have hρ : ∀ x : K, (ρ x) ^ Nat.card k = x := by
    intro x
    rw [hq, ← iterateFrobeniusEquiv_def K p m]
    exact (iterateFrobeniusEquiv K p m).apply_symm_apply x

  have hT : ∀ c : Fin n → K,
      (∑ i, algebraMap K F (ρ (c i)) * algebraMap F₀ F (f i)) ^ Nat.card k
        = φ (∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i)) := by
    intro c
    rw [map_sum, hq, sum_pow_char_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, ← map_pow (algebraMap K F), ← map_pow (algebraMap F₀ F), ← hq, hρ, map_mul,
      AlgHom.commutes, hφ]

  suffices key : ∀ (N : ℕ) (c : Fin n → K),
      (Finset.univ.filter fun i => c i ≠ 0).card ≤ N →
      ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) = 0 → ∀ i, c i = 0 from
    key _ c le_rfl hrel
  intro N
  induction N with
  | zero =>
    intro c hc _ i
    by_contra hi
    have hmem : i ∈ Finset.univ.filter fun i => c i ≠ 0 := by simp [hi]
    have := Finset.card_pos.mpr ⟨i, hmem⟩
    omega
  | succ N ih =>
    intro c hc hrel
    by_contra hne
    push Not at hne
    obtain ⟨i₀, hi₀⟩ := hne

    set c' : Fin n → K := fun i => c i / c i₀ with hc'def
    have hc'i₀ : c' i₀ = 1 := by simp [c', hi₀]
    have hc'zero : ∀ i, c i = 0 → c' i = 0 := by
      intro i hi
      simp [c', hi]
    have hrel' : ∑ i, algebraMap K F (c' i) * algebraMap F₀ F (f i) = 0 := by
      have : ∑ i, algebraMap K F (c' i) * algebraMap F₀ F (f i)
          = (algebraMap K F (c i₀))⁻¹ * ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [c']
        rw [div_eq_inv_mul, map_mul, map_inv₀, mul_assoc]
      rw [this, hrel, mul_zero]

    set b : Fin n → K := fun i => ρ (c' i) with hbdef
    have hrelb : ∑ i, algebraMap K F (b i) * algebraMap F₀ F (f i) = 0 := by
      have h := hT c'
      rw [hrel', map_zero] at h
      exact (pow_eq_zero_iff hq0).mp h

    set d : Fin n → K := fun i => b i - c' i with hddef
    have hreld : ∑ i, algebraMap K F (d i) * algebraMap F₀ F (f i) = 0 := by
      simp only [d, map_sub, sub_mul, Finset.sum_sub_distrib, hrelb, hrel', sub_zero]
    have hdsupp : (Finset.univ.filter fun i => d i ≠ 0)
        ⊆ (Finset.univ.filter fun i => c i ≠ 0).erase i₀ := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [Finset.mem_erase, Finset.mem_filter]
      refine ⟨?_, Finset.mem_univ _, ?_⟩
      · rintro rfl
        apply hi
        simp only [d, b, hc'i₀, map_one, sub_self]
      · intro hci
        apply hi
        simp only [d, b, hc'zero i hci, map_zero, sub_self]
    have hdcard : (Finset.univ.filter fun i => d i ≠ 0).card ≤ N := by
      have h1 := Finset.card_le_card hdsupp
      have h2 : i₀ ∈ Finset.univ.filter fun i => c i ≠ 0 := by simp [hi₀]
      rw [Finset.card_erase_of_mem h2] at h1
      omega
    have hd0 := ih d hdcard hreld

    have hfix : ∀ i, c' i ^ Nat.card k = c' i := by
      intro i
      have hbc : b i = c' i := sub_eq_zero.mp (hd0 i)
      conv_lhs => rw [← hbc]
      exact hρ (c' i)
    choose a ha using fun i => mem_range_algebraMap_of_pow_card_eq (k := k) (hfix i)

    have hrelk : ∑ i, a i • f i = 0 := by
      apply (algebraMap F₀ F).injective
      rw [map_sum, map_zero, ← hrel']
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply k F₀ F,
        IsScalarTower.algebraMap_apply k K F, ha]
    have hai₀ : a i₀ = 0 := Fintype.linearIndependent_iff.mp hf a hrelk i₀
    have : c' i₀ = 0 := by rw [← ha i₀, hai₀, map_zero]
    rw [hc'i₀] at this
    exact one_ne_zero this

end Constants

section Upstairs

variable {k K F₀ F : Type*} [Field k] [Field K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
  [Algebra k K] [Algebra k F] [IsScalarTower k K F] [IsScalarTower k F₀ F]

theorem essFiniteType_of_gen
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤) :
    Algebra.EssFiniteType K F := by
  classical
  obtain ⟨s, hs⟩ := hfg
  rw [← IntermediateField.fg_top_iff]
  refine ⟨s.image (algebraMap F₀ F), ?_⟩
  apply le_antisymm le_top
  rw [← hgen]
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨y, rfl⟩

  let ι' : F₀ →ₐ[k] F := IsScalarTower.toAlgHom k F₀ F
  have hy : y ∈ IntermediateField.adjoin k (s : Set F₀) := by rw [hs]; trivial
  have h1 : ι' y ∈ (IntermediateField.adjoin k (s : Set F₀)).map ι' := ⟨y, hy, rfl⟩
  rw [IntermediateField.adjoin_map] at h1
  have h2 : IntermediateField.adjoin k (ι' '' (s : Set F₀))
      ≤ (IntermediateField.adjoin K ((s.image (algebraMap F₀ F) : Finset F) : Set F)).restrictScalars k := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨z, hz, rfl⟩
    exact IntermediateField.subset_adjoin K _ (by
      rw [Finset.coe_image]
      exact ⟨z, hz, rfl⟩)
  exact h2 h1

end Upstairs

section Compositum

variable {k K F₀ F : Type*} [Field k] [Field K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
  [Algebra k K] [Algebra k F] [IsScalarTower k K F] [IsScalarTower k F₀ F]
  (Ω : IntermediateField k K)

def AA : Subalgebra k F := (IsScalarTower.toAlgHom k F₀ F).range

def BB : Subalgebra k F := (IsScalarTower.toAlgHom k Ω F).range

omit [IsScalarTower k K F] in
theorem algebraMap_mem_AA (y : F₀) : algebraMap F₀ F y ∈ AA (k := k) (F₀ := F₀) (F := F) :=
  ⟨y, rfl⟩

theorem algebraMap_mem_BB (ω : Ω) : algebraMap Ω F ω ∈ BB (F := F) Ω := ⟨ω, rfl⟩

def compSubalg : Subalgebra F₀ F where
  carrier := (AA (k := k) (F₀ := F₀) (F := F) ⊔ BB (F := F) Ω : Subalgebra k F)
  mul_mem' ha hb := Subalgebra.mul_mem _ ha hb
  add_mem' ha hb := Subalgebra.add_mem _ ha hb
  algebraMap_mem' y := Algebra.mem_sup_left (algebraMap_mem_AA (k := k) y)

theorem mem_compSubalg_iff {x : F} :
    x ∈ compSubalg (k := k) (F₀ := F₀) (F := F) Ω ↔
      x ∈ (AA (k := k) (F₀ := F₀) (F := F) ⊔ BB (F := F) Ω : Subalgebra k F) := Iff.rfl

variable [Algebra.IsAlgebraic k Ω]

theorem isIntegral_algebraMap_of_mem_Ω (ω : Ω) : IsIntegral F₀ (algebraMap Ω F ω) := by
  have h1 : IsAlgebraic k (ω : K) := by
    have := Algebra.IsAlgebraic.isAlgebraic (R := k) ω
    exact (isAlgebraic_algHom_iff (IntermediateField.val Ω) (IntermediateField.val Ω).injective).mpr
      this
  have h2 : IsAlgebraic k (algebraMap K F (ω : K)) :=
    h1.algHom (IsScalarTower.toAlgHom k K F)
  have h3 : IsAlgebraic F₀ (algebraMap K F (ω : K)) := h2.tower_top F₀
  rw [IsScalarTower.algebraMap_apply Ω K F]
  exact h3.isIntegral

theorem isIntegral_of_mem_compSubalg {x : F}
    (hx : x ∈ compSubalg (k := k) (F₀ := F₀) (F := F) Ω) : IsIntegral F₀ x := by
  rw [mem_compSubalg_iff, ← Algebra.adjoin_eq (AA (k := k) (F₀ := F₀) (F := F)),
    ← Algebra.adjoin_eq (BB (F := F) Ω), ← Algebra.adjoin_union] at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨y, rfl⟩ | ⟨ω, rfl⟩
    · exact isIntegral_algebraMap
    · exact isIntegral_algebraMap_of_mem_Ω Ω ω
  | algebraMap a =>
    rw [IsScalarTower.algebraMap_apply k F₀ F]
    exact isIntegral_algebraMap
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul hy

def FΩ : IntermediateField F₀ F :=
  (compSubalg (k := k) (F₀ := F₀) (F := F) Ω).toIntermediateField fun x hx =>
    Subalgebra.inv_mem_of_algebraic (K := F₀) (A := compSubalg (k := k) (F₀ := F₀) (F := F) Ω)
      (x := ⟨x, hx⟩) (isIntegral_of_mem_compSubalg Ω hx).isAlgebraic

theorem mem_FΩ_iff {x : F} :
    x ∈ FΩ (k := k) (F₀ := F₀) (F := F) Ω ↔
      x ∈ (AA (k := k) (F₀ := F₀) (F := F) ⊔ BB (F := F) Ω : Subalgebra k F) := Iff.rfl

scoped instance isIntegral_FΩ : Algebra.IsIntegral F₀ (FΩ (k := k) (F₀ := F₀) (F := F) Ω) :=
  ⟨fun x => (isIntegral_algHom_iff (IntermediateField.val _) Subtype.val_injective).mp
    (isIntegral_of_mem_compSubalg Ω x.2)⟩

scoped instance algΩ : Algebra Ω (FΩ (k := k) (F₀ := F₀) (F := F) Ω) :=
  RingHom.toAlgebra
    { toFun := fun ω => ⟨algebraMap Ω F ω, Algebra.mem_sup_right (algebraMap_mem_BB Ω ω)⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ a b) }

@[scoped simp] theorem coe_algebraMap_Ω (ω : Ω) :
    ((algebraMap Ω (FΩ (k := k) (F₀ := F₀) (F := F) Ω) ω : FΩ (k := k) (F₀ := F₀) (F := F) Ω) : F)
      = algebraMap Ω F ω := rfl

scoped instance towerΩ : IsScalarTower Ω (FΩ (k := k) (F₀ := F₀) (F := F) Ω) F :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance towerkΩ : IsScalarTower k Ω (FΩ (k := k) (F₀ := F₀) (F := F) Ω) :=
  IsScalarTower.of_algebraMap_eq fun a => Subtype.ext (by
    show algebraMap k F a = algebraMap Ω F (algebraMap k Ω a)
    exact IsScalarTower.algebraMap_apply k Ω F a)

example : IsScalarTower k F₀ (FΩ (k := k) (F₀ := F₀) (F := F) Ω) := inferInstance
example : IsScalarTower F₀ (FΩ (k := k) (F₀ := F₀) (F := F) Ω) F := inferInstance
example : IsScalarTower Ω K F := inferInstance

@[scoped simp] theorem coe_algebraMap_F₀ (y : F₀) :
    ((algebraMap F₀ (FΩ (k := k) (F₀ := F₀) (F := F) Ω) y : FΩ (k := k) (F₀ := F₀) (F := F) Ω) : F)
      = algebraMap F₀ F y := rfl

theorem mem_FΩ_iff_adjoin {x : F} :
    x ∈ FΩ (k := k) (F₀ := F₀) (F := F) Ω ↔
      x ∈ Algebra.adjoin k ((AA (k := k) (F₀ := F₀) (F := F) : Set F) ∪ (BB (F := F) Ω : Set F)) := by
  rw [mem_FΩ_iff, Algebra.adjoin_union, Algebra.adjoin_eq, Algebra.adjoin_eq]

theorem mem_adjoin_range_algebraMap_Ω (x : F) (hx : x ∈ FΩ (k := k) (F₀ := F₀) (F := F) Ω) :
    (⟨x, hx⟩ : FΩ (k := k) (F₀ := F₀) (F := F) Ω)
      ∈ Algebra.adjoin F₀ (Set.range (algebraMap Ω (FΩ (k := k) (F₀ := F₀) (F := F) Ω))) := by

  set T := Algebra.adjoin F₀ (Set.range (algebraMap Ω (FΩ (k := k) (F₀ := F₀) (F := F) Ω)))
    with hT
  suffices h : ∀ z : F, z ∈ Algebra.adjoin k ((AA (k := k) (F₀ := F₀) (F := F) : Set F) ∪
      (BB (F := F) Ω : Set F)) → ∃ hz : z ∈ FΩ (k := k) (F₀ := F₀) (F := F) Ω, (⟨z, hz⟩ : FΩ _ ) ∈ T by
    obtain ⟨_, h'⟩ := h x ((mem_FΩ_iff_adjoin Ω).mp hx)
    exact h'
  intro z hz
  induction hz using Algebra.adjoin_induction with
  | mem x h =>
    rcases h with ⟨y, rfl⟩ | ⟨ω, rfl⟩
    · exact ⟨(algebraMap F₀ (FΩ (k := k) (F₀ := F₀) (F := F) Ω) y).2, Subalgebra.algebraMap_mem T y⟩
    · exact ⟨(algebraMap Ω (FΩ (k := k) (F₀ := F₀) (F := F) Ω) ω).2, Algebra.subset_adjoin ⟨ω, rfl⟩⟩
  | algebraMap a =>
    have hmem : algebraMap k F a ∈ FΩ (k := k) (F₀ := F₀) (F := F) Ω := by
      rw [IsScalarTower.algebraMap_apply k F₀ F a]
      exact (algebraMap F₀ (FΩ (k := k) (F₀ := F₀) (F := F) Ω) (algebraMap k F₀ a)).2
    refine ⟨hmem, ?_⟩
    have : (⟨algebraMap k F a, hmem⟩ : FΩ (k := k) (F₀ := F₀) (F := F) Ω)
        = algebraMap F₀ _ (algebraMap k F₀ a) :=
      Subtype.ext (IsScalarTower.algebraMap_apply k F₀ F a)
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ ihx ihy =>
    obtain ⟨hxm, hxT⟩ := ihx
    obtain ⟨hym, hyT⟩ := ihy
    exact ⟨add_mem hxm hym, Subalgebra.add_mem T hxT hyT⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨hxm, hxT⟩ := ihx
    obtain ⟨hym, hyT⟩ := ihy
    exact ⟨mul_mem hxm hym, Subalgebra.mul_mem T hxT hyT⟩

theorem adjoin_range_algebraMap_Ω_eq_top :
    Algebra.adjoin F₀ (Set.range (algebraMap Ω (FΩ (k := k) (F₀ := F₀) (F := F) Ω))) = ⊤ := by
  apply le_antisymm le_top
  rintro ⟨x, hx⟩ -
  exact mem_adjoin_range_algebraMap_Ω Ω x hx

end Compositum

section Semilinear

open TensorProduct

variable {k K F₀ F : Type*} [Field k] [Field K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
  [Algebra k K] [Algebra k F] [IsScalarTower k K F] [IsScalarTower k F₀ F]
  (Ω : IntermediateField k K)

theorem linearDisjoint_AA_BB
    (hLD : ∀ (n : ℕ) (f : Fin n → F₀) (c : Fin n → K), LinearIndependent k f →
      ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) = 0 → ∀ i, c i = 0) :
    (AA (k := k) (F₀ := F₀) (F := F)).LinearDisjoint (BB (F := F) Ω) := by
  classical

  let ιA : F₀ →ₐ[k] F := IsScalarTower.toAlgHom k F₀ F
  let eA : F₀ ≃ₐ[k] (AA (k := k) (F₀ := F₀) (F := F)) := AlgEquiv.ofInjectiveField ιA
  let b₀ := Module.Basis.ofVectorSpace k F₀
  let a : Module.Basis _ k (AA (k := k) (F₀ := F₀) (F := F)) := b₀.map eA.toLinearEquiv
  refine Subalgebra.LinearDisjoint.of_basis_left _ _ a ?_
  rw [linearIndependent_iff']
  intro s g hsum i hi

  have hcoe : ∀ j, ((AA (k := k) (F₀ := F₀) (F := F)).val ∘ a) j = algebraMap F₀ F (b₀ j) := by
    intro j
    show ((a j : AA (k := k) (F₀ := F₀) (F := F)) : F) = _
    simp only [a, Module.Basis.map_apply]
    rfl
  choose ω hω using fun j => (g j).2

  set n := s.card
  let e : s ≃ Fin n := s.equivFin
  let f : Fin n → F₀ := fun t => b₀ ((e.symm t : s) : _)
  let c : Fin n → K := fun t => (ω ((e.symm t : s) : _) : K)
  have hf : LinearIndependent k f := by
    have h1 : LinearIndependent k (fun j : s => b₀ (j : _)) :=
      b₀.linearIndependent.comp _ Subtype.val_injective
    exact h1.comp _ e.symm.injective
  have hrel : ∑ t, algebraMap K F (c t) * algebraMap F₀ F (f t) = 0 := by
    have : ∑ t, algebraMap K F (c t) * algebraMap F₀ F (f t)
        = ∑ j ∈ s, g j • ((AA (k := k) (F₀ := F₀) (F := F)).val ∘ a) j := by
      rw [← Finset.sum_coe_sort s, ← Fintype.sum_equiv e.symm _ _ (fun _ => rfl)]
      refine Fintype.sum_congr _ _ fun t => ?_
      rw [hcoe]
      show algebraMap K F (ω _ : K) * _ = ((g _ : BB (F := F) Ω) : F) • _
      rw [smul_eq_mul, ← hω]
      rfl
    rw [this, hsum]
  have hc := hLD n f c hf hrel (e ⟨i, hi⟩)
  apply Subtype.ext
  show ((g i : BB (F := F) Ω) : F) = 0
  rw [← hω i]
  have : (ω i : K) = 0 := by
    have := hc
    simp only [c, Equiv.symm_apply_apply] at this
    exact this
  show (IsScalarTower.toAlgHom k Ω F) (ω i) = 0
  have h2 : algebraMap Ω K (ω i) = (ω i : K) := rfl
  rw [IsScalarTower.coe_toAlgHom', IsScalarTower.algebraMap_apply Ω K F, h2, this, map_zero]

variable (hLD : ∀ (n : ℕ) (f : Fin n → F₀) (c : Fin n → K), LinearIndependent k f →
      ∑ i, algebraMap K F (c i) * algebraMap F₀ F (f i) = 0 → ∀ i, c i = 0)

def mulEquiv : (AA (k := k) (F₀ := F₀) (F := F)) ⊗[k] (BB (F := F) Ω) ≃ₐ[k]
    ↥((AA (k := k) (F₀ := F₀) (F := F)) ⊔ (BB (F := F) Ω)) :=
  (AlgEquiv.ofInjective _ ((Subalgebra.linearDisjoint_iff_injective).mp
    (linearDisjoint_AA_BB Ω hLD))).trans (Subalgebra.equivOfEq _ _ (Subalgebra.mulMap_range _ _))

theorem coe_mulEquiv_tmul (a : AA (k := k) (F₀ := F₀) (F := F)) (b : BB (F := F) Ω) :
    ((mulEquiv Ω hLD (a ⊗ₜ[k] b) : ↥((AA (k := k) (F₀ := F₀) (F := F)) ⊔ (BB (F := F) Ω))) : F)
      = (a : F) * (b : F) := by
  simp [mulEquiv, Subalgebra.mulMap_tmul]

def eB : Ω ≃ₐ[k] BB (F := F) Ω := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k Ω F)

@[scoped simp] theorem coe_eB (ω : Ω) : ((eB (F := F) Ω ω : BB (F := F) Ω) : F) = algebraMap Ω F ω := rfl

def supAut (σ : Ω ≃ₐ[k] Ω) :
    ↥((AA (k := k) (F₀ := F₀) (F := F)) ⊔ (BB (F := F) Ω)) ≃ₐ[k]
      ↥((AA (k := k) (F₀ := F₀) (F := F)) ⊔ (BB (F := F) Ω)) :=
  (mulEquiv Ω hLD).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : _ ≃ₐ[k] AA (k := k) (F₀ := F₀) (F := F))
      ((eB (F := F) Ω).symm.trans (σ.trans (eB (F := F) Ω)))).trans (mulEquiv Ω hLD))

theorem supAut_algebraMap_F₀ (σ : Ω ≃ₐ[k] Ω) (y : F₀)
    (hy : algebraMap F₀ F y ∈ (AA (k := k) (F₀ := F₀) (F := F)) ⊔ (BB (F := F) Ω)) :
    ((supAut Ω hLD σ ⟨algebraMap F₀ F y, hy⟩ : ↥((AA (k := k) (F₀ := F₀) (F := F)) ⊔ (BB (F := F) Ω))) : F)
      = algebraMap F₀ F y := by
  have h1 : (mulEquiv Ω hLD).symm ⟨algebraMap F₀ F y, hy⟩
      = (⟨algebraMap F₀ F y, algebraMap_mem_AA (k := k) y⟩ : AA (k := k) (F₀ := F₀) (F := F)) ⊗ₜ[k] 1 := by
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [coe_mulEquiv_tmul]
    simp
  simp only [supAut, AlgEquiv.trans_apply, h1]
  rw [show (Algebra.TensorProduct.congr (AlgEquiv.refl : _ ≃ₐ[k] AA (k := k) (F₀ := F₀) (F := F))
      ((eB (F := F) Ω).symm.trans (σ.trans (eB (F := F) Ω))))
      ((⟨algebraMap F₀ F y, algebraMap_mem_AA (k := k) y⟩ : AA (k := k) (F₀ := F₀) (F := F)) ⊗ₜ[k] 1)
      = (⟨algebraMap F₀ F y, algebraMap_mem_AA (k := k) y⟩ : AA (k := k) (F₀ := F₀) (F := F)) ⊗ₜ[k] 1 by
    simp]
  rw [coe_mulEquiv_tmul]
  simp

theorem supAut_algebraMap_Ω (σ : Ω ≃ₐ[k] Ω) (ω : Ω)
    (hω : algebraMap Ω F ω ∈ (AA (k := k) (F₀ := F₀) (F := F)) ⊔ (BB (F := F) Ω)) :
    ((supAut Ω hLD σ ⟨algebraMap Ω F ω, hω⟩ : ↥((AA (k := k) (F₀ := F₀) (F := F)) ⊔ (BB (F := F) Ω))) : F)
      = algebraMap Ω F (σ ω) := by
  have h1 : (mulEquiv Ω hLD).symm ⟨algebraMap Ω F ω, hω⟩ = (1 : AA (k := k) (F₀ := F₀) (F := F)) ⊗ₜ[k] eB (F := F) Ω ω := by
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [coe_mulEquiv_tmul]
    simp
  simp only [supAut, AlgEquiv.trans_apply, h1]
  rw [show (Algebra.TensorProduct.congr (AlgEquiv.refl : _ ≃ₐ[k] AA (k := k) (F₀ := F₀) (F := F))
      ((eB (F := F) Ω).symm.trans (σ.trans (eB (F := F) Ω))))
      ((1 : AA (k := k) (F₀ := F₀) (F := F)) ⊗ₜ[k] eB (F := F) Ω ω)
      = (1 : AA (k := k) (F₀ := F₀) (F := F)) ⊗ₜ[k] eB (F := F) Ω (σ ω) by
    simp]
  rw [coe_mulEquiv_tmul]
  simp

variable [Algebra.IsAlgebraic k Ω]

def ringAutFΩ (σ : Ω ≃ₐ[k] Ω) : (FΩ (k := k) (F₀ := F₀) (F := F) Ω) ≃+* (FΩ (k := k) (F₀ := F₀) (F := F) Ω) where
  toFun x := ⟨supAut Ω hLD σ ⟨x.1, x.2⟩, (supAut Ω hLD σ ⟨x.1, x.2⟩).2⟩
  invFun x := ⟨(supAut Ω hLD σ).symm ⟨x.1, x.2⟩, ((supAut Ω hLD σ).symm ⟨x.1, x.2⟩).2⟩
  left_inv x := by
    apply Subtype.ext
    show (((supAut Ω hLD σ).symm ⟨(supAut Ω hLD σ ⟨x.1, x.2⟩ : F), _⟩ : ↥((AA (k := k) (F₀ := F₀) (F := F)) ⊔ (BB (F := F) Ω))) : F) = x.1
    rw [Subtype.coe_eta, AlgEquiv.symm_apply_apply]
  right_inv x := by
    apply Subtype.ext
    show (((supAut Ω hLD σ) ⟨((supAut Ω hLD σ).symm ⟨x.1, x.2⟩ : F), _⟩ : ↥((AA (k := k) (F₀ := F₀) (F := F)) ⊔ (BB (F := F) Ω))) : F) = x.1
    rw [Subtype.coe_eta, AlgEquiv.apply_symm_apply]
  map_mul' x y := by
    apply Subtype.ext
    show ((supAut Ω hLD σ ⟨x.1 * y.1, _⟩ : ↥((AA (k := k) (F₀ := F₀) (F := F)) ⊔ (BB (F := F) Ω))) : F) = _
    rw [show (⟨x.1 * y.1, (x * y).2⟩ : ↥((AA (k := k) (F₀ := F₀) (F := F)) ⊔ (BB (F := F) Ω)))
        = ⟨x.1, x.2⟩ * ⟨y.1, y.2⟩ from rfl, map_mul]
    rfl
  map_add' x y := by
    apply Subtype.ext
    show ((supAut Ω hLD σ ⟨x.1 + y.1, _⟩ : ↥((AA (k := k) (F₀ := F₀) (F := F)) ⊔ (BB (F := F) Ω))) : F) = _
    rw [show (⟨x.1 + y.1, (x + y).2⟩ : ↥((AA (k := k) (F₀ := F₀) (F := F)) ⊔ (BB (F := F) Ω)))
        = ⟨x.1, x.2⟩ + ⟨y.1, y.2⟩ from rfl, map_add]
    rfl

theorem coe_ringAutFΩ_apply (σ : Ω ≃ₐ[k] Ω) (x : FΩ (k := k) (F₀ := F₀) (F := F) Ω) :
    ((ringAutFΩ Ω hLD σ x : FΩ (k := k) (F₀ := F₀) (F := F) Ω) : F) = (supAut Ω hLD σ ⟨x.1, x.2⟩ : F) := rfl

include hLD in

theorem exists_semilinearAut (σ : Ω ≃ₐ[k] Ω) :
    ∃ g : SemilinearAut Ω (FΩ (k := k) (F₀ := F₀) (F := F) Ω),
      (∀ a : Ω, SemilinearAut.baseAut g a = σ a) ∧
        ∀ y : F₀, g • algebraMap F₀ (FΩ (k := k) (F₀ := F₀) (F := F) Ω) y
          = algebraMap F₀ (FΩ (k := k) (F₀ := F₀) (F := F) Ω) y := by
  refine ⟨⟨(ringAutFΩ Ω hLD σ, (σ : Ω ≃+* Ω)), fun a => ?_⟩, fun a => rfl, fun y => ?_⟩
  · apply Subtype.ext
    show ((ringAutFΩ Ω hLD σ (algebraMap Ω _ a) : FΩ (k := k) (F₀ := F₀) (F := F) Ω) : F) = algebraMap Ω F (σ a)
    rw [coe_ringAutFΩ_apply]
    exact supAut_algebraMap_Ω Ω hLD σ a _
  · apply Subtype.ext
    show ((ringAutFΩ Ω hLD σ (algebraMap F₀ _ y) : FΩ (k := k) (F₀ := F₀) (F := F) Ω) : F) = algebraMap F₀ F y
    rw [coe_ringAutFΩ_apply]
    exact supAut_algebraMap_F₀ Ω hLD σ y _

end Semilinear

section Curve

variable {k K F₀ F : Type*} [Field k] [Field K] [Field F₀] [Field F]
  [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
  [Algebra k K] [Algebra k F] [IsScalarTower k K F] [IsScalarTower k F₀ F]
  (Ω : IntermediateField k K) [Algebra.IsAlgebraic k Ω]

variable (F) in

def ψ : F₀ →ₐ[k] FΩ (k := k) (F₀ := F₀) (F := F) Ω := IsScalarTower.toAlgHom k F₀ _

@[scoped simp] theorem ψ_apply (y : F₀) : ψ F Ω y = algebraMap F₀ (FΩ (k := k) (F₀ := F₀) (F := F) Ω) y := rfl

theorem isIntegral_adjoin_ψ {t y : F₀}
    (hy : IsIntegral (IntermediateField.adjoin k ({t} : Set F₀)) y) :
    IsIntegral (IntermediateField.adjoin Ω ({ψ F Ω t} : Set (FΩ (k := k) (F₀ := F₀) (F := F) Ω)))
      (ψ F Ω y) := by
  classical

  have h1 : IsIntegral ((IntermediateField.adjoin k ({t} : Set F₀)).map (ψ F Ω)) (ψ F Ω y) := by
    obtain ⟨p, hp, hpy⟩ := hy
    let e : (IntermediateField.adjoin k ({t} : Set F₀)) ≃ₐ[k]
        ((IntermediateField.adjoin k ({t} : Set F₀)).map (ψ F Ω)) :=
      IntermediateField.equivMap _ (ψ F Ω)
    refine ⟨p.map (e : _ →+* _), hp.map _, ?_⟩
    have hcomp : (algebraMap ((IntermediateField.adjoin k ({t} : Set F₀)).map (ψ F Ω))
        (FΩ (k := k) (F₀ := F₀) (F := F) Ω)).comp (e : _ →+* _)
        = (ψ F Ω).toRingHom.comp (algebraMap (IntermediateField.adjoin k ({t} : Set F₀)) F₀) := by
      refine RingHom.ext fun r => ?_
      show ((e r : (IntermediateField.adjoin k ({t} : Set F₀)).map (ψ F Ω)) :
        FΩ (k := k) (F₀ := F₀) (F := F) Ω) = ψ F Ω (r : F₀)
      simp [e]
    rw [Polynomial.eval₂_map, hcomp]
    have h := Polynomial.hom_eval₂ p (algebraMap (IntermediateField.adjoin k ({t} : Set F₀)) F₀)
      (ψ F Ω).toRingHom y
    rw [hpy, map_zero] at h
    simpa using h.symm

  have hle : (IntermediateField.adjoin k ({t} : Set F₀)).map (ψ F Ω)
      ≤ (IntermediateField.adjoin Ω ({ψ F Ω t} : Set (FΩ (k := k) (F₀ := F₀) (F := F) Ω))).restrictScalars k := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    apply IntermediateField.adjoin_le_iff.mpr
    rw [Set.singleton_subset_iff]
    exact IntermediateField.subset_adjoin Ω _ (Set.mem_singleton _)
  let θ : ((IntermediateField.adjoin k ({t} : Set F₀)).map (ψ F Ω)) →+*
      (IntermediateField.adjoin Ω ({ψ F Ω t} : Set (FΩ (k := k) (F₀ := F₀) (F := F) Ω))) :=
    { toFun := fun r => ⟨(r : FΩ (k := k) (F₀ := F₀) (F := F) Ω),
        (IntermediateField.mem_restrictScalars k).mp (hle r.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI : Algebra ((IntermediateField.adjoin k ({t} : Set F₀)).map (ψ F Ω))
      (IntermediateField.adjoin Ω ({ψ F Ω t} : Set (FΩ (k := k) (F₀ := F₀) (F := F) Ω))) :=
    θ.toAlgebra
  haveI : IsScalarTower ((IntermediateField.adjoin k ({t} : Set F₀)).map (ψ F Ω))
      (IntermediateField.adjoin Ω ({ψ F Ω t} : Set (FΩ (k := k) (F₀ := F₀) (F := F) Ω)))
      (FΩ (k := k) (F₀ := F₀) (F := F) Ω) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact h1.tower_top

variable (φ : F →ₐ[K] F) [Finite k]
  (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))

include hφ in
omit [Algebra k K] [Algebra k F] [IsScalarTower k K F] [IsScalarTower k F₀ F] [Algebra.IsAlgebraic k Ω] in

theorem mem_range_of_isAlgebraic [IsAlgClosed K] {t : F₀}
    (ht : IsAlgebraic K (algebraMap F₀ F t)) : t ∈ Set.range (algebraMap k F₀) := by
  have hint : IsIntegral K (algebraMap F₀ F t) := ht.isIntegral
  have hdeg : (minpoly K (algebraMap F₀ F t)).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := RingHom.mem_range.mp (minpoly.mem_range_of_degree_eq_one K _ hdeg)
  have hfix : t ^ Nat.card k = t := by
    apply (algebraMap F₀ F).injective
    rw [← hφ t, ← hc]
    exact φ.commutes c
  exact mem_range_algebraMap_of_pow_card_eq hfix

include hφ in

theorem transcendental_ψ [IsAlgClosed K] {t : F₀} (ht : Transcendental k t) :
    Transcendental Ω (ψ F Ω t : FΩ (k := k) (F₀ := F₀) (F := F) Ω) := by
  intro halg
  apply ht

  have h1 : IsAlgebraic Ω (algebraMap F₀ F t) := by
    have := halg.algHom (IsScalarTower.toAlgHom Ω (FΩ (k := k) (F₀ := F₀) (F := F) Ω) F)
    simpa using this
  have h2 : IsAlgebraic K (algebraMap F₀ F t) := h1.tower_top K
  obtain ⟨a, ha⟩ := mem_range_of_isAlgebraic (k := k) φ hφ h2
  rw [← ha]
  exact isAlgebraic_algebraMap a

omit [Finite k] in

theorem adjoin_image_ψ_eq_top {s : Set F₀}
    (hs : IntermediateField.adjoin k s = ⊤) :
    IntermediateField.adjoin Ω (ψ F Ω '' s : Set (FΩ (k := k) (F₀ := F₀) (F := F) Ω)) = ⊤ := by
  set T := IntermediateField.adjoin Ω (ψ F Ω '' s : Set (FΩ (k := k) (F₀ := F₀) (F := F) Ω)) with hT

  have hA : ∀ y : F₀, ψ F Ω y ∈ T := by
    intro y
    have hy : y ∈ IntermediateField.adjoin k s := by rw [hs]; trivial
    have h1 : ψ F Ω y ∈ (IntermediateField.adjoin k s).map (ψ F Ω) := ⟨y, hy, rfl⟩
    rw [IntermediateField.adjoin_map] at h1
    have h2 : IntermediateField.adjoin k (ψ F Ω '' s) ≤ T.restrictScalars k :=
      IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin Ω _)
    exact h2 h1
  apply le_antisymm le_top
  rintro ⟨z, hz⟩ -

  suffices h : ∀ w : F, w ∈ Algebra.adjoin k ((AA (k := k) (F₀ := F₀) (F := F) : Set F) ∪
      (BB (F := F) Ω : Set F)) → ∃ hw : w ∈ FΩ (k := k) (F₀ := F₀) (F := F) Ω, (⟨w, hw⟩ : FΩ _ ) ∈ T by
    obtain ⟨_, h'⟩ := h z ((mem_FΩ_iff_adjoin Ω).mp hz)
    exact h'
  intro w hw
  induction hw using Algebra.adjoin_induction with
  | mem x h =>
    rcases h with ⟨y, rfl⟩ | ⟨ω, rfl⟩
    · exact ⟨(algebraMap F₀ (FΩ (k := k) (F₀ := F₀) (F := F) Ω) y).2, hA y⟩
    · exact ⟨(algebraMap Ω (FΩ (k := k) (F₀ := F₀) (F := F) Ω) ω).2, T.algebraMap_mem ω⟩
  | algebraMap a =>
    have hmem : algebraMap k F a ∈ FΩ (k := k) (F₀ := F₀) (F := F) Ω := by
      rw [IsScalarTower.algebraMap_apply k F₀ F a]
      exact (algebraMap F₀ (FΩ (k := k) (F₀ := F₀) (F := F) Ω) (algebraMap k F₀ a)).2
    refine ⟨hmem, ?_⟩
    have : (⟨algebraMap k F a, hmem⟩ : FΩ (k := k) (F₀ := F₀) (F := F) Ω)
        = algebraMap F₀ _ (algebraMap k F₀ a) :=
      Subtype.ext (IsScalarTower.algebraMap_apply k F₀ F a)
    rw [this]
    exact hA _
  | add x y _ _ ihx ihy =>
    obtain ⟨hxm, hxT⟩ := ihx
    obtain ⟨hym, hyT⟩ := ihy
    exact ⟨add_mem hxm hym, add_mem hxT hyT⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨hxm, hxT⟩ := ihx
    obtain ⟨hym, hyT⟩ := ihy
    exact ⟨mul_mem hxm hym, mul_mem hxT hyT⟩

omit [Finite k] in

theorem finiteDimensional_adjoin_ψ {t : F₀}
    (hfd : FiniteDimensional (IntermediateField.adjoin k ({t} : Set F₀)) F₀)
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤) :
    FiniteDimensional (IntermediateField.adjoin Ω ({ψ F Ω t} : Set (FΩ (k := k) (F₀ := F₀) (F := F) Ω)))
      (FΩ (k := k) (F₀ := F₀) (F := F) Ω) := by
  classical
  obtain ⟨s, hs⟩ := hfg

  have hint : ∀ x ∈ (↑(s.image (ψ F Ω)) : Set (FΩ (k := k) (F₀ := F₀) (F := F) Ω)),
      IsIntegral (IntermediateField.adjoin Ω ({ψ F Ω t} :
        Set (FΩ (k := k) (F₀ := F₀) (F := F) Ω))) x := by
    intro x hx
    rw [Finset.coe_image] at hx
    obtain ⟨y, -, rfl⟩ := hx
    haveI := hfd
    exact isIntegral_adjoin_ψ Ω (IsIntegral.of_finite _ y)
  haveI hfin := IntermediateField.finiteDimensional_adjoin
    (K := IntermediateField.adjoin Ω ({ψ F Ω t} : Set (FΩ (k := k) (F₀ := F₀) (F := F) Ω))) hint
  have htop : IntermediateField.adjoin
      (IntermediateField.adjoin Ω ({ψ F Ω t} : Set (FΩ (k := k) (F₀ := F₀) (F := F) Ω)))
      (↑(s.image (ψ F Ω)) : Set (FΩ (k := k) (F₀ := F₀) (F := F) Ω)) = ⊤ := by
    apply IntermediateField.restrictScalars_injective Ω
    rw [IntermediateField.restrictScalars_top, IntermediateField.adjoin_adjoin_left,
      eq_top_iff, ← adjoin_image_ψ_eq_top Ω hs, Finset.coe_image]
    exact IntermediateField.adjoin.mono _ _ _ Set.subset_union_right
  rw [htop] at hfin
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end Curve

end AlgebraicCurve.GenusFinToAlgClosedG
p2m_reactivate "P2MW.S_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed.AlgebraicCurve.GenusFinToAlgClosedG"
p2m_reactivate "P2MW.S_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed.AlgebraicCurve P2MW.S_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed.AlgebraicCurve.GenusFinToAlgClosedG"

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed.AlgebraicCurve AlgebraicCurve.GenusFinToAlgClosedG in

theorem solution
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    (hC : AlgebraicCurve.ConstantsAreBase k F₀) :
    AlgebraicCurve.genusFF K F = AlgebraicCurve.genusFF k F₀ := by
  classical

  obtain ⟨j, hj⟩ := exists_constantEmbedding (k := k) (K := K) (F₀ := F₀) (F := F)
  letI : Algebra k K := j.toAlgebra
  letI : Algebra k F := ((algebraMap K F).comp j).toAlgebra
  haveI : IsScalarTower k K F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k F₀ F := IsScalarTower.of_algebraMap_eq fun a => hj a
  have hLD := linearDisjoint (k := k) (K := K) (F₀ := F₀) (F := F) φ hφ

  let Ω : IntermediateField k K := algebraicClosure k K
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k

  obtain ⟨s, hs⟩ := hfg
  haveI : Algebra.EssFiniteType k F₀ := IntermediateField.fg_top_iff.mp ⟨s, hs⟩
  obtain ⟨t, ht, hfd, -⟩ := IsCurveOver.exists_separating_transcendental (K := k) (F := F₀)

  have htr : Transcendental Ω (ψ F Ω t) := transcendental_ψ Ω φ hφ ht
  haveI hfdΩ : FiniteDimensional (IntermediateField.adjoin Ω ({ψ F Ω t} : Set (FΩ (k := k)
      (F₀ := F₀) (F := F) Ω))) (FΩ (k := k) (F₀ := F₀) (F := F) Ω) :=
    finiteDimensional_adjoin_ψ Ω hfd ⟨s, hs⟩
  haveI : IsCurveOver Ω (FΩ (k := k) (F₀ := F₀) (F := F) Ω) :=
    isCurveOver_of_transcendental_of_perfectField htr hfdΩ
  haveI : Algebra.EssFiniteType Ω (FΩ (k := k) (F₀ := F₀) (F := F) Ω) :=
    IntermediateField.fg_top_iff.mp ⟨s.image (ψ F Ω), by
      rw [Finset.coe_image]; exact adjoin_image_ψ_eq_top Ω hs⟩
  have hCΩ : ConstantsAreBase Ω (FΩ (k := k) (F₀ := F₀) (F := F) Ω) :=
    constantsAreBase_of_isAlgClosed_of_transcendental (ψ F Ω t) htr

  have hconst : ∀ y : F₀, IsAlgebraic k y → y ∈ (algebraMap k F₀).range := by
    intro y hy
    have hmem : y ∈ LSpace (0 : Divisor k F₀) := by
      rw [mem_lSpace_iff_ord]
      refine Or.inr fun v => ?_
      rw [Place.ord_eq_zero_of_isAlgebraic v hy]
      simp
    rw [hC] at hmem
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hmem
    exact ⟨a, ha⟩
  have hLD' : ∀ (n : ℕ) (b : Fin n → F₀), LinearIndependent k b →
      LinearIndependent Ω (fun i => algebraMap F₀ (FΩ (k := k) (F₀ := F₀) (F := F) Ω) (b i)) := by
    intro n b hb
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hsum : ∑ i, algebraMap K F (g i : K) * algebraMap F₀ F (b i) = 0 := by
      have h := congrArg (fun z : FΩ (k := k) (F₀ := F₀) (F := F) Ω => (z : F)) hg
      simp only [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, MulMemClass.coe_mul, coe_algebraMap_Ω, coe_algebraMap_F₀,
        IsScalarTower.algebraMap_apply Ω K F]
      rfl
    have h0 : (g i : K) = 0 := hLD n b (fun i => (g i : K)) hb hsum i
    exact_mod_cast h0
  have h1 : genusFF k F₀ = genusFF Ω (FΩ (k := k) (F₀ := F₀) (F := F) Ω) :=
    genusFF_eq_of_perfectField hC hCΩ (adjoin_range_algebraMap_Ω_eq_top Ω) hconst hLD'
      (exists_semilinearAut Ω hLD)

  haveI : Algebra.EssFiniteType K F := essFiniteType_of_gen (k := k) ⟨s, hs⟩ hgen
  obtain ⟨x', hx', hfd', -⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have hgen' : IntermediateField.adjoin K
      (Set.range (algebraMap (FΩ (k := k) (F₀ := F₀) (F := F) Ω) F)) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨y, rfl⟩
    exact ⟨algebraMap F₀ (FΩ (k := k) (F₀ := F₀) (F := F) Ω) y, rfl⟩
  have h2 := AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_isAlgClosed
    Ω (FΩ (k := k) (F₀ := F₀) (F := F) Ω) K F ⟨ψ F Ω t, htr, hfdΩ⟩ ⟨x', hx', hfd'⟩ hgen'
  rw [h2, ← h1]

end S_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed (solution)
