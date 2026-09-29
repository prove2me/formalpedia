-- Prove2me | solution 1 for AlgebraicCurve.exists_baseChange_correspondence_of_constantFieldExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/97664929-d52c-5f23-9f97-12caa3cfad25

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Theorems.Thm_AlgebraicCurve_exists_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_existsUnique_valuation_sub_lt_one_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_AlgebraicCurve_normFormulaAlong
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_baseChange_correspondence_of_constantFieldExtension
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C"
p2m_attr_erase "simp" "ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_baseChange_correspondence_of_constantFieldExtension.AlgebraicCurve"
open scoped TensorProduct

universe u v w x

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong isScalarTower_along isIntegral_along FundamentalIdentityAlong FiniteAlong NormFormulaAlong finrankAlong Divisor.pushforwardAlong Divisor.correspondence Divisor.correspondence_apply Divisor.pushforwardAlong_single Place.fiberAlong Place.mem_fiberAlong Divisor.pullbackAlong_single SeparableAlong Place.restrict_toValuationSubring FundamentalIdentity FundamentalIdentity.sum_ramificationIndex_mul_deg Place Place.coe_algebraMap Divisor HasPrincipalDivisors IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed HasCanonicalDivisor exists_constantFieldExtension linearIndependent_of_constantFieldExtension Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension fundamentalIdentityAlong normFormulaAlong separableAlong_of_charZero isCurveOver_of_transcendental_of_isSeparable hasCanonicalDivisor_of_isCurveOver"
namespace BaseChangeCorrespondence
p2m_open "AlgebraicCurve"

section General

variable {E L : Type*} [Field E] [Field L] [Algebra E L]

theorem mem_of_valuation_lt_one (P : Place E L) {y : L}
    (hy : P.toValuationSubring.valuation y < 1) : y ∈ P.toValuationSubring :=
  (ValuationSubring.valuation_le_one_iff _ _).mp hy.le

theorem eq_zero_of_valuation_algebraMap_lt_one (P : Place E L) {c : E}
    (hc : P.toValuationSubring.valuation (algebraMap E L c) < 1) : c = 0 := by
  by_contra h
  have hu : IsUnit (algebraMap E P.toValuationSubring c) := (IsUnit.mk0 c h).map _
  have h1 := (ValuationSubring.valuation_eq_one_iff _ _).mp hu
  rw [Place.coe_algebraMap] at h1
  exact hc.ne h1

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [Algebra K E] [Algebra F L]

theorem centre_unique (P : Place E L) {σ τ : F →ₐ[K] E}
    (hσ : ∀ f : F, P.toValuationSubring.valuation (algebraMap F L f - algebraMap E L (σ f)) < 1)
    (hτ : ∀ f : F, P.toValuationSubring.valuation (algebraMap F L f - algebraMap E L (τ f)) < 1) :
    σ = τ := by
  ext f
  have h : P.toValuationSubring.valuation (algebraMap E L (τ f - σ f)) < 1 := by
    have := Valuation.map_sub P.toValuationSubring.valuation
      (algebraMap F L f - algebraMap E L (σ f)) (algebraMap F L f - algebraMap E L (τ f))
    rw [sub_sub_sub_cancel_left, ← map_sub] at this
    exact this.trans_lt (max_lt (hσ f) (hτ f))
  exact (sub_eq_zero.mp (eq_zero_of_valuation_algebraMap_lt_one P h)).symm

theorem algebraMap_mem_of_centred (P : Place E L) {σ : F →ₐ[K] E}
    (hσ : ∀ f : F, P.toValuationSubring.valuation (algebraMap F L f - algebraMap E L (σ f)) < 1)
    (f : F) : algebraMap F L f ∈ P.toValuationSubring := by
  have h := add_mem (mem_of_valuation_lt_one P (hσ f)) (P.algebraMap_mem' (σ f))
  rwa [sub_add_cancel] at h

end General

section Transport

theorem valuation_lt_one_iff_inv_not_mem {L : Type*} [Field L] (A : ValuationSubring L) {z : L}
    (hz : z ≠ 0) : A.valuation z < 1 ↔ z⁻¹ ∉ A := by
  rw [← A.valuation_le_one_iff, map_inv₀, inv_le_one₀ ((Valuation.pos_iff _).mpr hz), not_le]

theorem valuation_comap_lt_one_iff {L L' : Type*} [Field L] [Field L'] (A : ValuationSubring L')
    (g : L →+* L') (z : L) :
    (A.comap g).valuation z < 1 ↔ A.valuation (g z) < 1 := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [valuation_lt_one_iff_inv_not_mem _ hz,
      valuation_lt_one_iff_inv_not_mem _ (map_ne_zero_iff g g.injective |>.mpr hz),
      ValuationSubring.mem_comap, map_inv₀]

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem valuation_restrictAlong_lt_one_iff (χ : F →ₐ[K] F') (h : χ.toRingHom.IsIntegral)
    [HasPrincipalDivisors K F'] (W : Place K F') (z : F) :
    (W.restrictAlong χ h).toValuationSubring.valuation z < 1 ↔
      W.toValuationSubring.valuation (χ z) < 1 := by
  letI := algebraAlong χ
  haveI := isScalarTower_along χ
  haveI := isIntegral_along χ h
  show (W.restrict F).toValuationSubring.valuation z < 1 ↔ _
  rw [Place.restrict_toValuationSubring]
  exact valuation_comap_lt_one_iff _ _ z

end Transport

theorem span_eq_top_of_adjoin_eq_top {E L M : Type*} [Field E] [Field L] [Field M] [Algebra E L]
    [Algebra L M] [Algebra E M] [IsScalarTower E L M] {ι : Type*} [Finite ι] (b : ι → M)
    (hmul : ∀ i j, b i * b j ∈ Submodule.span L (Set.range b))
    (h1 : (1 : M) ∈ Submodule.span L (Set.range b))
    {T : Set M} (hT : T ⊆ Submodule.span L (Set.range b))
    (hgen : IntermediateField.adjoin E T = ⊤) : Submodule.span L (Set.range b) = ⊤ := by
  set S := Submodule.span L (Set.range b) with hS
  haveI : FiniteDimensional L S := FiniteDimensional.span_of_finite L (Set.finite_range b)
  have hmul' : ∀ s ∈ S, ∀ s' ∈ S, s * s' ∈ S := by
    refine Submodule.mul_le.mp ?_
    rw [hS, Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact hmul i j
  have hinv : ∀ s ∈ S, s⁻¹ ∈ S := by
    intro s hs
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [inv_zero]; exact S.zero_mem
    let m : S →ₗ[L] S :=
      { toFun := fun y => ⟨s * y, hmul' s hs y y.2⟩
        map_add' := fun y y' => Subtype.ext (mul_add _ _ _)
        map_smul' := fun r y => Subtype.ext (by simp) }
    have hinj : Function.Injective m := fun y y' h =>
      Subtype.ext (mul_left_cancel₀ hs0 (congrArg Subtype.val h))
    obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨1, h1⟩
    have hy' : s * y = 1 := congrArg Subtype.val hy
    rw [inv_eq_of_mul_eq_one_right hy']
    exact y.2
  let S' : IntermediateField E M :=
    { carrier := S
      mul_mem' := fun ha hb => hmul' _ ha _ hb
      one_mem' := h1
      add_mem' := S.add_mem
      zero_mem' := S.zero_mem
      algebraMap_mem' := fun c => by
        rw [IsScalarTower.algebraMap_apply E L M, Algebra.algebraMap_eq_smul_one]
        exact S.smul_mem _ h1
      inv_mem' := hinv }
  have hle : (⊤ : IntermediateField E M) ≤ S' := by
    rw [← hgen]
    exact IntermediateField.adjoin_le_iff.mpr hT
  exact eq_top_iff.mpr fun y _ => hle (IntermediateField.mem_top (x := y))

section Lift

variable {K F E M : Type*} [Field K] [Field F] [Algebra K F] [Field E] [Algebra K E]
  [Field M] [Algebra K M] [Algebra E M] [IsScalarTower K E M]

variable (E) in

noncomputable def liftMap (g : F →ₐ[K] M) : E ⊗[K] F →ₐ[E] M :=
  Algebra.TensorProduct.lift (Algebra.ofId E M) g (fun _ _ => Commute.all _ _)

@[scoped simp]
theorem liftMap_tmul (g : F →ₐ[K] M) (c : E) (f : F) :
    liftMap E g (c ⊗ₜ f) = algebraMap E M c * g f := rfl

theorem liftMap_injective (g : F →ₐ[K] M) {ι : Type*} (b : Module.Basis ι K F)
    (hli : LinearIndependent E (fun i => g (b i))) : Function.Injective (liftMap E g) := by
  classical
  let bE := Algebra.TensorProduct.basis E b
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hrepr : Finsupp.linearCombination E bE (bE.repr z) = z := bE.linearCombination_repr z
  have hcomp : ((liftMap E g).toLinearMap : E ⊗[K] F → M) ∘ bE = fun i => g (b i) := by
    funext i
    simp [bE, Algebra.TensorProduct.basis_apply]
  have h0 : Finsupp.linearCombination E (fun i => g (b i)) (bE.repr z) = 0 := by
    rw [← hcomp, ← Finsupp.apply_linearCombination, hrepr]
    exact hz
  have hc : bE.repr z = 0 := linearIndependent_iff.mp hli _ h0
  rw [← hrepr, hc, map_zero]

end Lift

section Extend

variable {K F E FE F' F'E : Type*} [Field K] [Field F] [Algebra K F]
  [Field E] [Field FE] [Algebra E FE] [Algebra F FE]
  [Field F'] [Algebra K F'] [Field F'E] [Algebra E F'E] [Algebra F' F'E]

section WithTower

variable [Algebra K E] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
  [Algebra K F'E] [IsScalarTower K E F'E] [IsScalarTower K F' F'E]

theorem exists_extension [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (hfg' : ∃ x : F', Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F')
    (hfgE' : ∃ x : F'E, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (χ : F →ₐ[K] F') :
    ∃ χE : FE →ₐ[E] F'E, ∀ f : F, χE (algebraMap F FE f) = algebraMap F' F'E (χ f) := by
  classical
  let bF := Module.Basis.ofVectorSpace K F

  let μ : E ⊗[K] F →ₐ[E] FE := liftMap E (IsScalarTower.toAlgHom K F FE)
  have hμ : Function.Injective μ :=
    liftMap_injective _ bF
      (linearIndependent_of_constantFieldExtension K F E FE hfg hfgE hgen bF.linearIndependent)

  let ν : E ⊗[K] F →ₐ[E] F'E := liftMap E ((IsScalarTower.toAlgHom K F' F'E).comp χ)
  have hν : Function.Injective ν := by
    refine liftMap_injective _ bF ?_
    have hli : LinearIndependent K (fun i => χ (bF i)) :=
      bF.linearIndependent.map' χ.toLinearMap (LinearMap.ker_eq_bot.mpr χ.toRingHom.injective)
    exact linearIndependent_of_constantFieldExtension K F' E F'E hfg' hfgE' hgen' hli

  let S : Subalgebra E FE := μ.range
  let ε : (E ⊗[K] F) ≃ₐ[E] S := AlgEquiv.ofInjective μ hμ
  have hε : ∀ z, ((ε z : S) : FE) = μ z := fun z => AlgEquiv.ofInjective_apply μ hμ z
  haveI : FaithfulSMul S FE :=
    (faithfulSMul_iff_algebraMap_injective S FE).mpr Subtype.val_injective
  have hFS : ∀ y : F, algebraMap F FE y ∈ S := fun y =>
    ⟨1 ⊗ₜ y, show μ (1 ⊗ₜ y) = _ by rw [liftMap_tmul, map_one, one_mul]; rfl⟩
  have hadj : Algebra.adjoin E (Set.range (algebraMap F FE)) ≤ S :=
    Algebra.adjoin_le (by rintro _ ⟨y, rfl⟩; exact hFS y)
  haveI : IsFractionRing S FE := by
    refine IsFractionRing.of_field S FE fun z => ?_
    have hz : z ∈ IntermediateField.adjoin E (Set.range (algebraMap F FE)) := by
      rw [hgen]; exact IntermediateField.mem_top
    obtain ⟨r, hr, s, hs, hrs⟩ := (IntermediateField.mem_adjoin_iff_div (F := E)).mp hz
    exact ⟨⟨r, hadj hr⟩, ⟨s, hadj hs⟩, hrs⟩

  let θ : S →ₐ[E] F'E := ν.comp (ε.symm : S →ₐ[E] E ⊗[K] F)
  have hθ : Function.Injective θ := hν.comp ε.symm.injective
  refine ⟨IsFractionRing.liftAlgHom hθ, fun f => ?_⟩
  have h1 : algebraMap F FE f = algebraMap S FE (ε (1 ⊗ₜ f)) := by
    change _ = ((ε (1 ⊗ₜ f) : S) : FE)
    rw [hε, liftMap_tmul, map_one, one_mul]; rfl
  rw [h1, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  change ν (ε.symm (ε (1 ⊗ₜ f))) = _
  rw [AlgEquiv.symm_apply_apply, liftMap_tmul, map_one, one_mul]; rfl

end WithTower

theorem isIntegral_extension (χ : F →ₐ[K] F') (hχ : χ.toRingHom.IsIntegral) (χE : FE →ₐ[E] F'E)
    (hχE : ∀ f : F, χE (algebraMap F FE f) = algebraMap F' F'E (χ f))
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤) :
    χE.toRingHom.IsIntegral := by
  letI : Algebra FE F'E := algebraAlong χE
  haveI : IsScalarTower E FE F'E := isScalarTower_along χE
  have hS : ∀ y ∈ Set.range (algebraMap F' F'E), IsIntegral FE y := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨p, hp, hpy⟩ := hχ y
    refine ⟨p.map (algebraMap F FE), hp.map _, ?_⟩
    have hcomp : (algebraMap FE F'E).comp (algebraMap F FE) =
        (algebraMap F' F'E).comp χ.toRingHom := by
      ext f; exact hχE f
    rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hpy, map_zero]
  have htop : IntermediateField.adjoin FE (Set.range (algebraMap F' F'E)) = ⊤ := by
    rw [← top_le_iff]
    intro z _
    have hz : z ∈ IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) := by
      rw [hgen']; exact IntermediateField.mem_top
    have hle : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) ≤
        (IntermediateField.adjoin FE (Set.range (algebraMap F' F'E))).restrictScalars E :=
      IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin FE _)
    exact hle hz
  intro z
  have hz : z ∈ (IntermediateField.adjoin FE (Set.range (algebraMap F' F'E))).toSubalgebra := by
    rw [htop]; exact Algebra.mem_top
  rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    (fun y hy => (hS y hy).isAlgebraic)] at hz
  have hz' : z ∈ integralClosure FE F'E :=
    (Algebra.adjoin_le (S := integralClosure FE F'E) fun y hy => hS y hy) hz
  exact (mem_integralClosure_iff FE F'E).mp hz'

theorem finite_extension (χ : F →ₐ[K] F') (hfin : FiniteAlong K χ) (χE : FE →ₐ[E] F'E)
    (hχE : ∀ f : F, χE (algebraMap F FE f) = algebraMap F' F'E (χ f))
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤) :
    ∃ _ : FiniteAlong E χE, finrankAlong E χE ≤ finrankAlong K χ := by
  classical
  letI iF : Algebra F F' := algebraAlong χ
  haveI : Module.Finite F F' := hfin
  letI iE : Algebra FE F'E := algebraAlong χE
  haveI : IsScalarTower E FE F'E := isScalarTower_along χE
  set n := Module.finrank F F' with hn
  let b := Module.finBasis F F'
  let b' : Fin n → F'E := fun i => algebraMap F' F'E (b i)
  have hT : ∀ y : F', algebraMap F' F'E y ∈ Submodule.span FE (Set.range b') := by
    intro y
    rw [← b.sum_repr y, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def, map_mul]
    have : algebraMap F' F'E (algebraMap F F' (b.repr y i)) =
        algebraMap FE F'E (algebraMap F FE (b.repr y i)) := (hχE _).symm
    rw [this, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span FE (Set.range b') = ⊤ :=
    span_eq_top_of_adjoin_eq_top (E := E) b'
      (fun i j => by simpa only [b', ← map_mul] using hT (b i * b j))
      (by simpa only [map_one] using hT 1)
      (T := Set.range (algebraMap F' F'E)) (by rintro _ ⟨y, rfl⟩; exact hT y) hgen'
  have hfinE : Module.Finite FE F'E :=
    Module.finite_def.mpr (by rw [← hspan]; exact Submodule.fg_span (Set.finite_range b'))
  refine ⟨hfinE, ?_⟩
  have h := finrank_range_le_card (R := FE) b'
  rw [Fintype.card_fin] at h
  change Module.finrank FE (Submodule.span FE (Set.range b')) ≤ n at h
  rwa [hspan, finrank_top] at h

end Extend

section Bookkeeping

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem essFiniteType_of_fg
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    Algebra.EssFiniteType K F := by
  obtain ⟨x, -, hfin⟩ := hfg
  have h1 : Algebra.EssFiniteType K (IntermediateField.adjoin K ({x} : Set F)) :=
    IntermediateField.essFiniteType_iff.2
      (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x))
  have h2 : Algebra.EssFiniteType (IntermediateField.adjoin K ({x} : Set F)) F := inferInstance
  exact Algebra.EssFiniteType.comp K (IntermediateField.adjoin K ({x} : Set F)) F

theorem finiteAlong_of_isIntegral [Algebra.EssFiniteType K F'] (χ : F →ₐ[K] F')
    (hχ : χ.toRingHom.IsIntegral) : FiniteAlong K χ := by
  letI : Algebra F F' := algebraAlong χ
  haveI : IsScalarTower K F F' := isScalarTower_along χ
  obtain ⟨s, hs⟩ := IntermediateField.fg_top K F'
  haveI : Finite (s : Set F') := s.finite_toSet.to_subtype
  have hfin : FiniteDimensional F (IntermediateField.adjoin F (s : Set F')) :=
    IntermediateField.finiteDimensional_adjoin fun z _ => (hχ z : IsIntegral F z)
  have htop : IntermediateField.adjoin F (s : Set F') = ⊤ := by
    rw [← IntermediateField.restrictScalars_eq_top_iff (K := K), ← top_le_iff, ← hs]
    exact IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin F _)
  rw [htop] at hfin
  exact LinearEquiv.finiteDimensional
    (IntermediateField.topEquiv (F := F) (E := F')).toLinearEquiv

theorem fg_of_finiteAlong (χ : F →ₐ[K] F') (hfin : FiniteAlong K χ) {x : F}
    (hx : Transcendental K x)
    (hfinx : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    Transcendental K (χ x) ∧
      FiniteDimensional (IntermediateField.adjoin K ({χ x} : Set F')) F' := by
  have hinj : Function.Injective χ := χ.toRingHom.injective
  refine ⟨fun h => hx ((isAlgebraic_algHom_iff χ hinj).mp h), ?_⟩
  letI : Algebra F F' := algebraAlong χ
  haveI : IsScalarTower K F F' := isScalarTower_along χ
  haveI : Module.Finite F F' := hfin
  let Kx : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F)
  haveI : FiniteDimensional Kx F := hfinx
  letI : Algebra Kx F' := ((algebraMap F F').comp (algebraMap Kx F)).toAlgebra
  haveI : IsScalarTower Kx F F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite Kx F' := Module.Finite.trans F F'
  let L : IntermediateField K F' := IntermediateField.adjoin K ({χ x} : Set F')
  have hmap : ∀ y ∈ IntermediateField.adjoin K ({x} : Set F), χ y ∈ L := by
    intro y hy
    have h1 : χ y ∈ (IntermediateField.adjoin K ({x} : Set F)).map χ := ⟨y, hy, rfl⟩
    rwa [IntermediateField.adjoin_map, Set.image_singleton] at h1
  have hmem : ∀ c : Kx, χ (c : F) ∈ L := fun c => hmap c c.2
  letI : Algebra Kx L :=
    (((χ : F →+* F').comp (algebraMap Kx F)).codRestrict L fun c => hmem c).toAlgebra
  haveI : IsScalarTower Kx L F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite Kx L F'

end Bookkeeping

section Restrict

variable {E FE F'E : Type*} [Field E] [Field FE] [Algebra E FE] [Field F'E] [Algebra E F'E]

theorem centred_restrictAlong {K F F' : Type*} [Field K] [Field F] [Algebra K F] [Field F']
    [Algebra K F'] [Algebra K E] [Algebra F FE] [Algebra F' F'E]
    [HasPrincipalDivisors E F'E] (χ : F →ₐ[K] F') (χE : FE →ₐ[E] F'E)
    (h : χE.toRingHom.IsIntegral)
    (hχE : ∀ f : F, χE (algebraMap F FE f) = algebraMap F' F'E (χ f))
    {W : Place E F'E} {σ : F' →ₐ[K] E}
    (hW : ∀ y : F', W.toValuationSubring.valuation
      (algebraMap F' F'E y - algebraMap E F'E (σ y)) < 1) (f : F) :
    (W.restrictAlong χE h).toValuationSubring.valuation
      (algebraMap F FE f - algebraMap E FE (σ (χ f))) < 1 := by
  rw [valuation_restrictAlong_lt_one_iff, map_sub, hχE, AlgHom.commutes]
  exact hW (χ f)

theorem inertiaDegAlong_eq_one [IsAlgClosed E] [IsCurveOver E FE] [IsCurveOver E F'E]
    (χE : FE →ₐ[E] F'E) (h : χE.toRingHom.IsIntegral) (W : Place E F'E) :
    W.inertiaDegAlong χE h = 1 := by
  letI := algebraAlong χE
  haveI := isScalarTower_along χE
  haveI := isIntegral_along χE h
  have h1 := W.deg_restrict_mul_inertiaDeg (F := FE)
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed,
    one_mul] at h1
  exact h1

theorem exists_of_correspondence_single_ne_zero [HasPrincipalDivisors E F'E]
    (φE ψE : FE →ₐ[E] F'E) (hφ : φE.toRingHom.IsIntegral) (hψ : ψE.toRingHom.IsIntegral)
    {P Q : Place E FE}
    (hQ : Divisor.correspondence φE ψE hφ hψ (Finsupp.single P 1) Q ≠ 0) :
    ∃ W ∈ Place.fiberAlong φE hφ P, W.restrictAlong ψE hψ = Q := by
  classical
  rw [Divisor.correspondence_apply, Divisor.pullbackAlong_single, map_sum,
    Finsupp.finsetSum_apply] at hQ
  obtain ⟨W, hW, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hQ
  refine ⟨W, hW, ?_⟩
  rw [Divisor.pushforwardAlong_single, Finsupp.single_apply] at hne
  by_contra hWQ
  rw [if_neg hWQ] at hne
  exact hne rfl

end Restrict

section Fibre

variable {K F E FE F' F'E : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
  [IsCurveOver K F]
  [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
  [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
  [Field F'] [Algebra K F'] [IsCurveOver K F']
  [Field F'E] [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E]
  [IsScalarTower K E F'E] [IsScalarTower K F' F'E] [IsCurveOver E F'E]

theorem fibre_centred
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (hfg' : ∃ x : F', Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F')
    (hfgE' : ∃ x : F'E, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (χ : F →ₐ[K] F') (hfin : FiniteAlong K χ)
    (χE : FE →ₐ[E] F'E) (hχEi : χE.toRingHom.IsIntegral)
    (hχE : ∀ f : F, χE (algebraMap F FE f) = algebraMap F' F'E (χ f))
    (hFI : FundamentalIdentityAlong E χE hχEi)
    {P : Place E FE} {e : F →ₐ[K] E}
    (hP : ∀ f : F, P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1) :
    (∀ W ∈ Place.fiberAlong χE hχEi P, W.ramificationIndexAlong χE = 1) ∧
    (∀ W ∈ Place.fiberAlong χE hχEi P, ∃ σ : F' →ₐ[K] E, σ.comp χ = e ∧
      ∀ y : F', W.toValuationSubring.valuation
        (algebraMap F' F'E y - algebraMap E F'E (σ y)) < 1) ∧
    (∀ (σ : F' →ₐ[K] E) (W : Place E F'E), σ.comp χ = e →
      (∀ y : F', W.toValuationSubring.valuation
        (algebraMap F' F'E y - algebraMap E F'E (σ y)) < 1) →
      W ∈ Place.fiberAlong χE hχEi P) ∧
    {σ : F' →ₐ[K] E | σ.comp χ = e}.Finite := by
  classical
  have C1F := Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension
    K F hfg E FE hfgE hgen
  have C1F' := Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension
    K F' hfg' E F'E hfgE' hgen'

  have huF : ∀ (Q : Place E FE), (∀ f : F, Q.toValuationSubring.valuation
      (algebraMap F FE f - algebraMap E FE (e f)) < 1) → Q = P := fun Q hQ => by
    obtain ⟨R, -, hR⟩ := C1F.1 e
    exact (hR Q hQ).trans (hR P hP).symm

  choose Qc hQc hQu using C1F'.1

  have hc : ∀ (σ : F' →ₐ[K] E) (W : Place E F'E), σ.comp χ = e →
      (∀ y : F', W.toValuationSubring.valuation
        (algebraMap F' F'E y - algebraMap E F'E (σ y)) < 1) →
      W ∈ Place.fiberAlong χE hχEi P := by
    intro σ W hσ hW
    rw [Place.mem_fiberAlong]
    refine huF _ fun f => ?_
    have h := centred_restrictAlong χ χE hχEi hχE hW f
    rwa [← AlgHom.comp_apply, hσ] at h

  have hinj : Function.Injective Qc := fun σ τ h =>
    centre_unique (Qc σ) (hQc σ) (fun y => by rw [h]; exact hQc τ y)

  letI iF : Algebra F F' := algebraAlong χ
  haveI : IsScalarTower K F F' := isScalarTower_along χ
  haveI : Module.Finite F F' := hfin

  letI iE : Algebra F E := e.toRingHom.toAlgebra
  haveI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun k => (e.commutes k).symm
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  haveI : Algebra.IsSeparable F F' := Algebra.IsSeparable.of_integral F F'
  have hcard : Fintype.card (F' →ₐ[F] E) = finrankAlong K χ := AlgHom.card F F' E
  let T : Finset (F' →ₐ[K] E) := Finset.univ.image fun σ' : F' →ₐ[F] E => σ'.restrictScalars K
  have hTmem : ∀ σ, σ ∈ T ↔ σ.comp χ = e := by
    intro σ
    constructor
    · intro hσ
      obtain ⟨σ', -, rfl⟩ := Finset.mem_image.mp hσ
      ext f
      exact σ'.commutes f
    · intro hσ
      refine Finset.mem_image.mpr ⟨⟨σ.toRingHom, fun f => ?_⟩, Finset.mem_univ _, ?_⟩
      · exact AlgHom.congr_fun hσ f
      · ext y; rfl
  have hTcard : T.card = finrankAlong K χ := by
    rw [Finset.card_image_of_injective _ (AlgHom.restrictScalars_injective K), Finset.card_univ,
      hcard]
  have hSfin : {σ : F' →ₐ[K] E | σ.comp χ = e}.Finite :=
    T.finite_toSet.subset fun σ hσ => Finset.mem_coe.mpr ((hTmem σ).mpr hσ)

  set Z := Place.fiberAlong χE hχEi P with hZ
  have hsum : ∑ W ∈ Z, (W.ramificationIndexAlong χE : ℤ) = (finrankAlong E χE : ℤ) := by
    letI := algebraAlong χE
    haveI := isScalarTower_along χE
    haveI := isIntegral_along χE hχEi
    haveI : FundamentalIdentity E FE F'E := hFI
    have h := FundamentalIdentity.sum_ramificationIndex_mul_deg (K := E) (F := FE) (F' := F'E) P
    simp only [IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one] at h
    exact h
  have hpos : ∀ W ∈ Z, 1 ≤ W.ramificationIndexAlong χE := fun W _ => by
    letI := algebraAlong χE
    haveI := isScalarTower_along χE
    haveI := isIntegral_along χE hχEi
    exact W.ramificationIndex_pos (F := FE)
  obtain ⟨-, hle⟩ := finite_extension χ hfin χE hχE hgen'

  have hsub : T.image Qc ⊆ Z := by
    intro W hW
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hW
    exact hc σ _ ((hTmem σ).mp hσ) (hQc σ)
  have hTZ : T.card ≤ Z.card := by
    rw [← Finset.card_image_of_injective T hinj]
    exact Finset.card_le_card hsub

  have hZsum : (Z.card : ℤ) ≤ ∑ W ∈ Z, (W.ramificationIndexAlong χE : ℤ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    exact Finset.sum_le_sum fun W hW => by exact_mod_cast hpos W hW
  have hsumZ : ∑ W ∈ Z, (W.ramificationIndexAlong χE : ℤ) ≤ (Z.card : ℤ) := by
    rw [hsum]
    calc (finrankAlong E χE : ℤ) ≤ finrankAlong K χ := by exact_mod_cast hle
      _ = T.card := by rw [hTcard]
      _ ≤ Z.card := by exact_mod_cast hTZ

  have ha : ∀ W ∈ Z, W.ramificationIndexAlong χE = 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨W₀, hW₀, hne⟩ := hcon
    have hlt : (Z.card : ℤ) < ∑ W ∈ Z, (W.ramificationIndexAlong χE : ℤ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_lt_sum (fun W hW => by exact_mod_cast hpos W hW) ⟨W₀, hW₀, ?_⟩
      have h1 := hpos W₀ hW₀
      have h2 : 1 < W₀.ramificationIndexAlong χE := lt_of_le_of_ne h1 (Ne.symm hne)
      exact_mod_cast h2
    omega

  have himg : T.image Qc = Z := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [Finset.card_image_of_injective T hinj]
    have : (Z.card : ℤ) ≤ T.card := by rw [hTcard]; exact hZsum.trans (hsum ▸ by exact_mod_cast hle)
    exact_mod_cast this

  have hb : ∀ W ∈ Z, ∃ σ : F' →ₐ[K] E, σ.comp χ = e ∧
      ∀ y : F', W.toValuationSubring.valuation
        (algebraMap F' F'E y - algebraMap E F'E (σ y)) < 1 := by
    intro W hW
    rw [← himg] at hW
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hW
    exact ⟨σ, (hTmem σ).mp hσ, hQc σ⟩
  exact ⟨ha, hb, hc, hSfin⟩

theorem correspondence_single_apply_centred
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (hfg' : ∃ x : F', Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F')
    (hfgE' : ∃ x : F'E, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φ ψ : F →ₐ[K] F') (hfinφ : FiniteAlong K φ)
    (φE ψE : FE →ₐ[E] F'E) (hφEi : φE.toRingHom.IsIntegral) (hψEi : ψE.toRingHom.IsIntegral)
    (hφE : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (hψE : ∀ f : F, ψE (algebraMap F FE f) = algebraMap F' F'E (ψ f))
    (hFI : FundamentalIdentityAlong E φE hφEi)
    {P : Place E FE} {e : F →ₐ[K] E}
    (hP : ∀ f : F, P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1)
    {Q : Place E FE} {e' : F →ₐ[K] E}
    (hQ : ∀ f : F, Q.toValuationSubring.valuation
      (algebraMap F FE f - algebraMap E FE (e' f)) < 1) :
    Divisor.correspondence φE ψE hφEi hψEi (Finsupp.single P 1) Q =
      (∑ᶠ σ ∈ {σ : F' →ₐ[K] E | σ.comp φ = e},
        Finsupp.single (σ.comp ψ) (1 : ℤ) : (F →ₐ[K] E) →₀ ℤ) e' := by
  classical
  obtain ⟨ha, hb, hc, hSfin⟩ :=
    fibre_centred hfg hfgE hgen hfg' hfgE' hgen' φ hfinφ φE hφEi hφE hFI hP
  have C1F := Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension
    K F hfg E FE hfgE hgen
  have C1F' := Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension
    K F' hfg' E F'E hfgE' hgen'
  choose Qc hQc hQu using C1F'.1

  rw [Divisor.correspondence_apply, Divisor.pullbackAlong_single, map_sum,
    Finsupp.finsetSum_apply]
  have hL : ∀ W ∈ Place.fiberAlong φE hφEi P,
      (Divisor.pushforwardAlong ψE hψEi
        (Finsupp.single W (1 * (W.ramificationIndexAlong φE : ℤ)))) Q =
      if W.restrictAlong ψE hψEi = Q then 1 else 0 := by
    intro W hW
    rw [Divisor.pushforwardAlong_single, ha W hW, inertiaDegAlong_eq_one, Finsupp.single_apply]
    simp
  rw [Finset.sum_congr rfl hL]

  rw [finsum_mem_eq_finite_toFinset_sum _ hSfin, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]

  have hinj : Function.Injective Qc := fun σ τ h =>
    centre_unique (Qc σ) (hQc σ) (fun y => by rw [h]; exact hQc τ y)
  symm
  refine Finset.sum_bij (fun σ _ => Qc σ) (fun σ hσ => ?_) (fun σ₁ _ σ₂ _ h => hinj h)
    (fun W hW => ?_) (fun σ _ => ?_)
  · exact hc σ _ (hSfin.mem_toFinset.mp hσ) (hQc σ)
  · obtain ⟨σ, hσ, hW'⟩ := hb W hW
    exact ⟨σ, hSfin.mem_toFinset.mpr hσ, (hQu σ W hW').symm⟩
  · beta_reduce
    refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
    ·
      obtain ⟨R, -, hR⟩ := C1F.1 e'
      refine (hR _ fun f => ?_).trans (hR Q hQ).symm
      have h2 := centred_restrictAlong ψ ψE hψEi hψE (hQc σ) f
      rwa [← AlgHom.comp_apply, h] at h2
    · refine centre_unique Q (fun f => ?_) hQ
      have h2 := centred_restrictAlong ψ ψE hψEi hψE (hQc σ) f
      rw [h] at h2
      simpa only [AlgHom.comp_apply] using h2

end Fibre

end AlgebraicCurve.BaseChangeCorrespondence
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_baseChange_correspondence_of_constantFieldExtension.AlgebraicCurve P2MW.S_AlgebraicCurve_exists_baseChange_correspondence_of_constantFieldExtension.AlgebraicCurve.BaseChangeCorrespondence"
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_baseChange_correspondence_of_constantFieldExtension.AlgebraicCurve"

open AlgebraicCurve.BaseChangeCorrespondence in
theorem solution
    (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (F' : Type w) [Field F'] [Algebra K F'] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ)
    (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin)
    (E : Type x) (FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE]
    [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤) :
    ∃ (F'E : Type (max w x)) (_ : Field F'E) (_ : Algebra E F'E) (_ : Algebra F' F'E)
      (_ : Algebra K F'E) (_ : IsScalarTower K E F'E) (_ : IsScalarTower K F' F'E)
      (_ : IsCurveOver E F'E)
      (φE ψE : FE →ₐ[E] F'E) (hφE : φE.toRingHom.IsIntegral) (hψE : ψE.toRingHom.IsIntegral)
      (_ : FundamentalIdentityAlong E φE hφE) (hfinE : FiniteAlong E ψE)
      (_ : NormFormulaAlong E ψE hfinE),
      (∃ x' : F'E, Transcendental E x' ∧
        FiniteDimensional (IntermediateField.adjoin E ({x'} : Set F'E)) F'E) ∧
      IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤ ∧
      (∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f)) ∧
      (∀ f : F, ψE (algebraMap F FE f) = algebraMap F' F'E (ψ f)) ∧
      (∀ (P : Place E FE) (e : F →ₐ[K] E),
        (∀ f : F, P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1) →
        ∀ (Q : Place E FE) (e' : F →ₐ[K] E),
        (∀ f : F, Q.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e' f)) < 1) →
          Divisor.correspondence φE ψE hφE hψE (Finsupp.single P 1) Q =
            (∑ᶠ σ ∈ {σ : F' →ₐ[K] E | σ.comp φ = e},
              Finsupp.single (σ.comp ψ) (1 : ℤ) : (F →ₐ[K] E) →₀ ℤ) e') ∧
      (∀ (P : Place E FE) (e : F →ₐ[K] E),
        (∀ f : F, P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1) →
        ∀ Q : Place E FE, Divisor.correspondence φE ψE hφE hψE (Finsupp.single P 1) Q ≠ 0 →
          ∃ e' : F →ₐ[K] E, ∀ f : F,
            Q.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e' f)) < 1) ∧
      (∀ P : Place E FE, (∃ f : F, algebraMap F FE f ∉ P.toValuationSubring) →
        ∀ Q : Place E FE, Divisor.correspondence φE ψE hφE hψE (Finsupp.single P 1) Q ≠ 0 →
          ∃ f : F, algebraMap F FE f ∉ Q.toValuationSubring) := by
  classical

  have _hFI := hFI
  have _hN := hN
  clear hFI hN _hFI _hN
  obtain ⟨x, hx, hfinx⟩ := id hfg

  have hroof := fg_of_finiteAlong ψ hfin hx hfinx
  have hfg' : ∃ x' : F', Transcendental K x' ∧
      FiniteDimensional (IntermediateField.adjoin K ({x'} : Set F')) F' :=
    ⟨ψ x, hroof.1, hroof.2⟩
  haveI : CharZero F' := charZero_of_injective_algebraMap (algebraMap K F').injective
  haveI hCF' : IsCurveOver K F' := by
    haveI := hroof.2
    haveI : Algebra.IsSeparable (IntermediateField.adjoin K ({ψ x} : Set F')) F' :=
      Algebra.IsSeparable.of_integral _ _
    exact isCurveOver_of_transcendental_of_isSeparable K F' (ψ x) hroof.1 hroof.2 inferInstance
  haveI : Algebra.EssFiniteType K F' := essFiniteType_of_fg hfg'
  haveI : HasCanonicalDivisor (K := K) (F := F') := by
    haveI : PerfectField K := PerfectField.ofCharZero
    exact hasCanonicalDivisor_of_isCurveOver

  obtain ⟨F'E, _, _, _, _, _, _, hCE, _, hfgE', hgen'⟩ :=
    exists_constantFieldExtension K F' E hfg'

  obtain ⟨φE, hφE⟩ := exists_extension hfg hfgE hgen hfg' hfgE' hgen' φ
  obtain ⟨ψE, hψE⟩ := exists_extension hfg hfgE hgen hfg' hfgE' hgen' ψ
  have hφEi : φE.toRingHom.IsIntegral := isIntegral_extension φ hφ φE hφE hgen'
  have hψEi : ψE.toRingHom.IsIntegral := isIntegral_extension ψ hψ ψE hψE hgen'
  have hfinφ : FiniteAlong K φ := finiteAlong_of_isIntegral φ hφ
  obtain ⟨hfinφE, -⟩ := finite_extension φ hfinφ φE hφE hgen'
  obtain ⟨hfinψE, -⟩ := finite_extension ψ hfin ψE hψE hgen'
  haveI : CharZero FE := charZero_of_injective_algebraMap (algebraMap K FE).injective
  have hsepφE : SeparableAlong E φE := separableAlong_of_charZero φE hφEi
  have hsepψE : SeparableAlong E ψE := separableAlong_of_charZero ψE hψEi
  have hFIφE : FundamentalIdentityAlong E φE hφEi := fundamentalIdentityAlong φE hφEi hfinφE hsepφE
  have hFIψE : FundamentalIdentityAlong E ψE hψEi := fundamentalIdentityAlong ψE hψEi hfinψE hsepψE
  have hNψE : NormFormulaAlong E ψE hfinψE := normFormulaAlong ψE hfinψE hsepψE
  refine ⟨F'E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hCE, φE, ψE, hφEi, hψEi, hFIφE, hfinψE, hNψE, hfgE', hgen', hφE, hψE,
    ?_, ?_, ?_⟩
  ·
    intro P e hP Q e' hQ
    exact correspondence_single_apply_centred hfg hfgE hgen hfg' hfgE' hgen' φ ψ hfinφ φE ψE
      hφEi hψEi hφE hψE hFIφE hP hQ
  ·
    intro P e hP Q hQ
    obtain ⟨W, hWZ, hWQ⟩ := exists_of_correspondence_single_ne_zero φE ψE hφEi hψEi hQ
    obtain ⟨σ, -, hσ⟩ :=
      (fibre_centred hfg hfgE hgen hfg' hfgE' hgen' φ hfinφ φE hφEi hφE hFIφE hP).2.1 W hWZ
    refine ⟨σ.comp ψ, fun f => ?_⟩
    rw [← hWQ, AlgHom.comp_apply]
    exact centred_restrictAlong ψ ψE hψEi hψE hσ f
  ·
    intro P hPrat Q hQ
    obtain ⟨W, hWZ, hWQ⟩ := exists_of_correspondence_single_ne_zero φE ψE hφEi hψEi hQ
    by_contra hcon
    push Not at hcon
    obtain ⟨e', he'⟩ := (Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension
      K F hfg E FE hfgE hgen).2 Q hcon
    have hWZ' : W ∈ Place.fiberAlong ψE hψEi Q := Place.mem_fiberAlong.mpr hWQ
    obtain ⟨τ, -, hτ⟩ :=
      (fibre_centred hfg hfgE hgen hfg' hfgE' hgen' ψ hfin ψE hψEi hψE hFIψE he').2.1 W hWZ'
    have hPW : W.restrictAlong φE hφEi = P := Place.mem_fiberAlong.mp hWZ
    obtain ⟨f, hf⟩ := hPrat
    apply hf
    rw [← hPW]
    refine algebraMap_mem_of_centred _ (σ := τ.comp φ) (fun f => ?_) f
    rw [AlgHom.comp_apply]
    exact centred_restrictAlong φ φE hφEi hφE hτ f

end S_AlgebraicCurve_exists_baseChange_correspondence_of_constantFieldExtension
end P2MW
export P2MW.S_AlgebraicCurve_exists_baseChange_correspondence_of_constantFieldExtension (solution)
