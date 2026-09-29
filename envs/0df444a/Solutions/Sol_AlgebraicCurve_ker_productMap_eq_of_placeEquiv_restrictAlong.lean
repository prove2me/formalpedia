-- Prove2me | solution 1 for AlgebraicCurve.ker_productMap_eq_of_placeEquiv_restrictAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/553c11d0-0b20-5e72-97fd-888846664283

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Place_evalAt_map_eq_of_comap_eq
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_finite_setOf_not_mem_toValuationSubring_or_evalAt_mem
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_CurveModel_nonempty_of_perfectField
import Theorems.Thm_AlgebraicCurve_CurveModel_infinite_place
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_ker_productMap_eq_of_placeEquiv_restrictAlong
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one"
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open AlgebraicCurve
open scoped TensorProduct

namespace ZeroLocusKerGC3

variable {K : Type*} [Field K]

theorem isRational {F : Type*} [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) :
    v.IsRational :=
  (AlgebraicCurve.Place.isRational_iff_deg_eq_one v).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed v)

private theorem _root_.ZeroLocusKerGC3.infinite_place {F : Type*} [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F]
    [Algebra.EssFiniteType K F] : Infinite (Place K F) := by
  obtain ⟨t, ht, hfd, -⟩ := AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  obtain ⟨M⟩ := AlgebraicCurve.CurveModel.nonempty_of_perfectField K F ⟨t, ht, hfd⟩
  exact AlgebraicCurve.CurveModel.infinite_place M

p2m_export "ZeroLocusKerGC3" "infinite_place"

theorem evalAt_add {F : Type*} [Field F] [Algebra K F] (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    ← map_add]
  rfl

theorem evalAt_zero {F : Type*} [Field F] [Algebra K F] (v : Place K F) : v.evalAt (0 : F) = 0 := by
  simpa using AlgebraicCurve.Place.evalAt_algebraMap v (0 : K)

theorem evalAt_restrictAlong {E F : Type*} [Field E] [Field F] [Algebra K E] [Algebra K F]
    (φ : E →ₐ[K] F) (hφ : φ.toRingHom.IsIntegral) (R : Place K F) (hR : (R.restrictAlong φ hφ).IsRational)
    {x : E} (hx : x ∈ (R.restrictAlong φ hφ).toValuationSubring) :
    R.evalAt (φ x) = (R.restrictAlong φ hφ).evalAt x := by
  have h := AlgebraicCurve.Place.evalAt_map_eq_of_comap_eq (RingHom.id K) φ.toRingHom
    (fun c => by simp) (R.restrictAlong φ hφ) R rfl hR hx
  simpa using h

theorem mem_restrictAlong_iff {E F : Type*} [Field E] [Field F] [Algebra K E] [Algebra K F]
    (φ : E →ₐ[K] F) (hφ : φ.toRingHom.IsIntegral) (R : Place K F) (x : E) :
    x ∈ (R.restrictAlong φ hφ).toValuationSubring ↔ φ x ∈ R.toValuationSubring :=
  Iff.rfl

theorem finite_setOf_not_mem {F : Type*} [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F] (f : F) :
    {v : Place K F | f ∉ v.toValuationSubring}.Finite := by
  by_cases hf : f ∈ Set.range (algebraMap K F)
  · obtain ⟨c, rfl⟩ := hf
    convert Set.finite_empty
    ext v
    simpa using v.algebraMap_mem' c
  · haveI := IsCurveOver.hasPrincipalDivisors (K := K) (F := F)
    refine (AlgebraicCurve.Place.finite_setOf_not_mem_toValuationSubring_or_evalAt_mem isRational f hf ∅).subset ?_
    intro v hv
    exact Or.inl hv

theorem productMap_eq_zero_of_productMap_eq_zero
    {E F F' : Type*} [IsAlgClosed K] [Field E] [Field F] [Field F']
    [Algebra K E] [Algebra K F] [Algebra K F']
    [IsCurveOver K E] [IsCurveOver K F] [Algebra.EssFiniteType K F] [IsCurveOver K F']
    (φ₀ φ₁ : E →ₐ[K] F) (hφ₀ : φ₀.toRingHom.IsIntegral) (hφ₁ : φ₁.toRingHom.IsIntegral)
    (ψ₀ ψ₁ : E →ₐ[K] F') (hψ₀ : ψ₀.toRingHom.IsIntegral) (hψ₁ : ψ₁.toRingHom.IsIntegral)
    (θ : Place K F → Place K F')
    (hθ₀ : ∀ R : Place K F, (θ R).restrictAlong ψ₀ hψ₀ = R.restrictAlong φ₀ hφ₀)
    (hθ₁ : ∀ R : Place K F, (θ R).restrictAlong ψ₁ hψ₁ = R.restrictAlong φ₁ hφ₁)
    (t : E ⊗[K] E) (ht : Algebra.TensorProduct.productMap ψ₀ ψ₁ t = 0) :
    Algebra.TensorProduct.productMap φ₀ φ₁ t = 0 := by
  classical
  set α := Algebra.TensorProduct.productMap φ₀ φ₁ with hα
  set β := Algebra.TensorProduct.productMap ψ₀ ψ₁ with hβ

  have key : ∀ s : E ⊗[K] E, ∃ S : Set (Place K F), S.Finite ∧ ∀ R : Place K F, R ∉ S →
      α s ∈ R.toValuationSubring ∧ β s ∈ (θ R).toValuationSubring ∧ R.evalAt (α s) = (θ R).evalAt (β s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero =>
      refine ⟨∅, Set.finite_empty, fun R _ => ?_⟩
      simp only [map_zero]
      exact ⟨zero_mem _, zero_mem _, by rw [evalAt_zero, evalAt_zero]⟩
    | tmul x y =>
      refine ⟨{R | φ₀ x ∉ R.toValuationSubring} ∪ {R | φ₁ y ∉ R.toValuationSubring},
        (finite_setOf_not_mem (φ₀ x)).union (finite_setOf_not_mem (φ₁ y)), fun R hR => ?_⟩
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hR
      obtain ⟨hx, hy⟩ := hR

      have hx' : x ∈ (R.restrictAlong φ₀ hφ₀).toValuationSubring := (mem_restrictAlong_iff φ₀ hφ₀ R x).mpr hx
      have hy' : y ∈ (R.restrictAlong φ₁ hφ₁).toValuationSubring := (mem_restrictAlong_iff φ₁ hφ₁ R y).mpr hy
      have hxθ : ψ₀ x ∈ (θ R).toValuationSubring := by
        rw [← mem_restrictAlong_iff ψ₀ hψ₀ (θ R) x, hθ₀]; exact hx'
      have hyθ : ψ₁ y ∈ (θ R).toValuationSubring := by
        rw [← mem_restrictAlong_iff ψ₁ hψ₁ (θ R) y, hθ₁]; exact hy'
      simp only [hα, hβ, Algebra.TensorProduct.productMap_apply_tmul]
      refine ⟨mul_mem hx hy, mul_mem hxθ hyθ, ?_⟩
      rw [AlgebraicCurve.Place.evalAt_mul R (isRational R) hx hy,
        AlgebraicCurve.Place.evalAt_mul (θ R) (isRational (θ R)) hxθ hyθ,
        evalAt_restrictAlong φ₀ hφ₀ R (isRational _) hx', evalAt_restrictAlong φ₁ hφ₁ R (isRational _) hy',
        evalAt_restrictAlong ψ₀ hψ₀ (θ R) (isRational _) (by rw [hθ₀]; exact hx'),
        evalAt_restrictAlong ψ₁ hψ₁ (θ R) (isRational _) (by rw [hθ₁]; exact hy')]
      congr 1 <;> congr 1 <;> simp only [hθ₀, hθ₁]
    | add s₁ s₂ h₁ h₂ =>
      obtain ⟨S₁, hS₁, H₁⟩ := h₁
      obtain ⟨S₂, hS₂, H₂⟩ := h₂
      refine ⟨S₁ ∪ S₂, hS₁.union hS₂, fun R hR => ?_⟩
      simp only [Set.mem_union, not_or] at hR
      obtain ⟨a₁, b₁, e₁⟩ := H₁ R hR.1
      obtain ⟨a₂, b₂, e₂⟩ := H₂ R hR.2
      simp only [map_add]
      refine ⟨add_mem a₁ a₂, add_mem b₁ b₂, ?_⟩
      rw [evalAt_add R (isRational R) a₁ a₂, evalAt_add (θ R) (isRational (θ R)) b₁ b₂, e₁, e₂]
  obtain ⟨S, hS, H⟩ := key t

  have hvan : ∀ R : Place K F, R ∉ S → α t ∈ R.toValuationSubring ∧ R.evalAt (α t) = 0 := by
    intro R hR
    obtain ⟨a, -, e⟩ := H R hR
    refine ⟨a, ?_⟩
    rw [e, show β t = 0 from ht, evalAt_zero]

  haveI : Infinite (Place K F) := infinite_place
  have hinf : (Sᶜ).Infinite := Set.Finite.infinite_compl hS
  by_contra hne
  by_cases hc : α t ∈ Set.range (algebraMap K F)
  · obtain ⟨c, hc⟩ := hc
    obtain ⟨R, hR⟩ := hinf.nonempty
    have := (hvan R hR).2
    rw [← hc, AlgebraicCurve.Place.evalAt_algebraMap] at this
    apply hne
    rw [← hc, this, map_zero]
  · haveI := IsCurveOver.hasPrincipalDivisors (K := K) (F := F)
    have hfin := AlgebraicCurve.Place.finite_setOf_not_mem_toValuationSubring_or_evalAt_mem
      (isRational (K := K) (F := F)) (α t) hc {0}
    apply hinf
    refine hfin.subset ?_
    intro R hR
    exact Or.inr (by simpa using (hvan R hR).2)

end ZeroLocusKerGC3

theorem solution
    {K E F F' : Type*} [Field K] [IsAlgClosed K] [Field E] [Field F] [Field F']
    [Algebra K E] [Algebra K F] [Algebra K F']
    [IsCurveOver K E] [Algebra.EssFiniteType K E] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    [IsCurveOver K F'] [Algebra.EssFiniteType K F']
    (φ₀ φ₁ : E →ₐ[K] F) (hφ₀ : φ₀.toRingHom.IsIntegral) (hφ₁ : φ₁.toRingHom.IsIntegral)
    (ψ₀ ψ₁ : E →ₐ[K] F') (hψ₀ : ψ₀.toRingHom.IsIntegral) (hψ₁ : ψ₁.toRingHom.IsIntegral)
    (θ : Place K F ≃ Place K F')
    (hθ₀ : ∀ R : Place K F, (θ R).restrictAlong ψ₀ hψ₀ = R.restrictAlong φ₀ hφ₀)
    (hθ₁ : ∀ R : Place K F, (θ R).restrictAlong ψ₁ hψ₁ = R.restrictAlong φ₁ hφ₁) :
    RingHom.ker (Algebra.TensorProduct.productMap φ₀ φ₁).toRingHom =
      RingHom.ker (Algebra.TensorProduct.productMap ψ₀ ψ₁).toRingHom := by
  have hθ₀' : ∀ R' : Place K F', (θ.symm R').restrictAlong φ₀ hφ₀ = R'.restrictAlong ψ₀ hψ₀ := fun R' => by
    rw [← hθ₀ (θ.symm R'), Equiv.apply_symm_apply]
  have hθ₁' : ∀ R' : Place K F', (θ.symm R').restrictAlong φ₁ hφ₁ = R'.restrictAlong ψ₁ hψ₁ := fun R' => by
    rw [← hθ₁ (θ.symm R'), Equiv.apply_symm_apply]
  ext t
  simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  exact ⟨fun h => ZeroLocusKerGC3.productMap_eq_zero_of_productMap_eq_zero ψ₀ ψ₁ hψ₀ hψ₁ φ₀ φ₁ hφ₀ hφ₁ θ.symm hθ₀' hθ₁' t h,
    fun h => ZeroLocusKerGC3.productMap_eq_zero_of_productMap_eq_zero φ₀ φ₁ hφ₀ hφ₁ ψ₀ ψ₁ hψ₀ hψ₁ θ hθ₀ hθ₁ t h⟩

end S_AlgebraicCurve_ker_productMap_eq_of_placeEquiv_restrictAlong
end P2MW
export P2MW.S_AlgebraicCurve_ker_productMap_eq_of_placeEquiv_restrictAlong (solution)
