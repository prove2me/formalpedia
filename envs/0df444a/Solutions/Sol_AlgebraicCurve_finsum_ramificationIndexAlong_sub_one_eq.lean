-- Prove2me | solution 1 for AlgebraicCurve.finsum_ramificationIndexAlong_sub_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/3b3084e6-7b22-5d53-b491-dd502e24bac2

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstance
import Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental
import Theorems.Thm_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_Place_deg_ne_zero_of_finiteDimensional_adjoin
import Theorems.Thm_AlgebraicCurve_exists_D_ne_zero
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_two_mul_genus_sub_two_eq_of_degree_canonical
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_instIsCurveOverRatFunc
import Theorems.Thm_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField
import Theorems.Thm_AlgebraicCurve_genus_ratFunc_eq_zero
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_degree_canonicalDivisor_eq_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_genus_eq_genusFF
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_algEquiv
import Theorems.Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_finsum_ramificationIndexAlong_sub_one_eq
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 6400000

open AlgebraicCurve IntermediateField

namespace RHEtower

section Tower

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
variable {F : Type*} [Field F] [Algebra K F]
variable {f : F}

omit [IsAlgClosed K] [CharZero K] in

theorem transcendental_gen (htr : Transcendental K f) :
    Transcendental K (⟨f, IntermediateField.mem_adjoin_simple_self K f⟩ :
      ↥(IntermediateField.adjoin K ({f} : Set F))) := by
  intro halg
  apply htr
  obtain ⟨p, hp0, hp⟩ := halg
  refine ⟨p, hp0, ?_⟩
  have h2 := Polynomial.aeval_algHom_apply
    (IntermediateField.val (IntermediateField.adjoin K ({f} : Set F)))
    ⟨f, IntermediateField.mem_adjoin_simple_self K f⟩ p
  rw [hp, map_zero] at h2
  simpa using h2

omit [IsAlgClosed K] [CharZero K] in

theorem generator_adjoin' (f : F) :
    ∀ y : ↥(IntermediateField.adjoin K ({f} : Set F)), ∃ pn pd : Polynomial K,
      y = Polynomial.aeval
          (⟨f, IntermediateField.mem_adjoin_simple_self K f⟩ :
            ↥(IntermediateField.adjoin K ({f} : Set F))) pn
        / Polynomial.aeval
          (⟨f, IntermediateField.mem_adjoin_simple_self K f⟩ :
            ↥(IntermediateField.adjoin K ({f} : Set F))) pd := by
  intro y
  obtain ⟨pn, pd, h⟩ := (IntermediateField.mem_adjoin_simple_iff K (y : F)).mp y.2
  refine ⟨pn, pd, ?_⟩
  have hc : ∀ p : Polynomial K,
      ((Polynomial.aeval
        (⟨f, IntermediateField.mem_adjoin_simple_self K f⟩ :
          ↥(IntermediateField.adjoin K ({f} : Set F))) p : _) : F)
      = Polynomial.aeval f p := by
    intro p
    exact (Polynomial.aeval_algHom_apply
      (IntermediateField.val (IntermediateField.adjoin K ({f} : Set F)))
      ⟨f, IntermediateField.mem_adjoin_simple_self K f⟩ p).symm
  apply Subtype.coe_injective
  push_cast [hc]
  exact h

theorem finiteDimensional_top (K' L : Type*) [Field K'] [Field L] [Algebra K' L] :
    FiniteDimensional (↥(⊤ : IntermediateField K' L)) L := by
  have hspan : Submodule.span (↥(⊤ : IntermediateField K' L)) ({(1 : L)} : Set L) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    have : y = (⟨y, trivial⟩ : ↥(⊤ : IntermediateField K' L)) • (1 : L) := by
      simp [IntermediateField.smul_def]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  exact ⟨⟨{1}, by rw [Finset.coe_singleton]; exact hspan⟩⟩

omit [IsAlgClosed K] [CharZero K] in

theorem finiteDimensional_adjoin_gen' (f : F) :
    FiniteDimensional
      (↥(IntermediateField.adjoin K
        ({(⟨f, IntermediateField.mem_adjoin_simple_self K f⟩ :
            ↥(IntermediateField.adjoin K ({f} : Set F)))} :
          Set (↥(IntermediateField.adjoin K ({f} : Set F))))))
      (↥(IntermediateField.adjoin K ({f} : Set F))) := by
  classical
  set E₀ := ↥(IntermediateField.adjoin K ({f} : Set F))
  set x₀ : E₀ := ⟨f, IntermediateField.mem_adjoin_simple_self K f⟩
  have htop : IntermediateField.adjoin K ({x₀} : Set E₀) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨pn, pd, hy⟩ := generator_adjoin' f y
    have haev : ∀ p : Polynomial K,
        Polynomial.aeval x₀ p ∈ IntermediateField.adjoin K ({x₀} : Set E₀) := by
      intro p
      have h1 : Polynomial.aeval x₀ p ∈ Algebra.adjoin K ({x₀} : Set E₀) :=
        Polynomial.aeval_mem_adjoin_singleton K x₀
      exact (IntermediateField.algebra_adjoin_le_adjoin K _) h1
    rw [hy]
    exact div_mem (haev pn) (haev pd)
  rw [htop]
  exact finiteDimensional_top K E₀

theorem transcendental_ratFunc_X (K' : Type*) [Field K'] :
    Transcendental K' (RatFunc.X : RatFunc K') := by
  rw [transcendental_iff_injective]
  have hcomp : (Polynomial.aeval (RatFunc.X : RatFunc K'))
      = IsScalarTower.toAlgHom K' (Polynomial K') (RatFunc K') := by
    apply Polynomial.algHom_ext
    simp
  rw [hcomp]
  exact IsFractionRing.injective (Polynomial K') (RatFunc K')

theorem adjoin_ratFunc_X_eq_top (K' : Type*) [Field K'] :
    IntermediateField.adjoin K' ({(RatFunc.X : RatFunc K')} : Set (RatFunc K')) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have haev : ∀ r : Polynomial K',
      algebraMap (Polynomial K') (RatFunc K') r ∈
        IntermediateField.adjoin K' ({(RatFunc.X : RatFunc K')} : Set (RatFunc K')) := by
    intro r
    have h1 : algebraMap (Polynomial K') (RatFunc K') r
        = Polynomial.aeval (RatFunc.X : RatFunc K') r := by
      have hcomp : (Polynomial.aeval (RatFunc.X : RatFunc K'))
          = IsScalarTower.toAlgHom K' (Polynomial K') (RatFunc K') := by
        apply Polynomial.algHom_ext
        simp
      rw [hcomp]
      rfl
    rw [h1]
    exact (IntermediateField.algebra_adjoin_le_adjoin K' _)
      (Polynomial.aeval_mem_adjoin_singleton K' _)
  induction y using RatFunc.induction_on with
  | _ p q hq =>
    exact div_mem (haev p) (haev q)

theorem essFiniteType_ratFunc (K' : Type*) [Field K'] :
    Algebra.EssFiniteType K' (RatFunc K') := by
  refine essFiniteType_of_transcendental_of_finiteDimensional
    (transcendental_ratFunc_X K') ?_
  rw [adjoin_ratFunc_X_eq_top]
  exact finiteDimensional_top K' (RatFunc K')

noncomputable def adjoinEquivRatFunc (htr : Transcendental K f) :
    (↥(IntermediateField.adjoin K ({f} : Set F))) ≃ₐ[K] RatFunc K := by
  have hAI : AlgebraicIndependent K (fun _ : Unit => f) := by
    rw [algebraicIndependent_iff_injective_aeval]
    have hcomp : (MvPolynomial.aeval (R := K) (fun _ : Unit => f))
        = (Polynomial.aeval f).comp
            (MvPolynomial.uniqueAlgEquiv (R := K) Unit :
              MvPolynomial Unit K ≃ₐ[K] Polynomial K).toAlgHom := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [MvPolynomial.uniqueAlgEquiv]
    rw [hcomp]
    exact (transcendental_iff_injective.mp htr).comp
      (MvPolynomial.uniqueAlgEquiv (R := K) Unit :
        MvPolynomial Unit K ≃ₐ[K] Polynomial K).injective
  have hr : IntermediateField.adjoin K (Set.range (fun _ : Unit => f))
      = IntermediateField.adjoin K ({f} : Set F) := by
    rw [Set.range_const]
  haveI : IsFractionRing K K :=
    IsLocalization.self (fun x hx =>
      IsUnit.mk0 x (mem_nonZeroDivisors_iff_ne_zero.mp hx))
  let e₃ : FractionRing (MvPolynomial Unit K) ≃ₐ[K] FractionRing (Polynomial K) :=
    IsFractionRing.fieldEquivOfAlgEquiv (FA := K) _ _
      (MvPolynomial.uniqueAlgEquiv (R := K) Unit : MvPolynomial Unit K ≃ₐ[K] Polynomial K)
  exact ((IntermediateField.equivOfEq hr).symm.trans hAI.aevalEquivField.symm).symm.symm.trans
    (e₃.trans (RatFunc.toFractionRingAlgEquiv K K).symm)

end Tower

section Heads

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
variable {F : Type*} [Field F] [Algebra K F]
variable {f : F} (htr : Transcendental K f)

set_option quotPrecheck false in
local notation "E" => (↥(IntermediateField.adjoin K ({f} : Set F)))

omit [IsAlgClosed K] in
include htr in

theorem isCurveOver_E : IsCurveOver K E := by
  haveI : PerfectField K := PerfectField.ofCharZero
  exact AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField
    (transcendental_gen htr) (finiteDimensional_adjoin_gen' f)

omit [IsAlgClosed K] [CharZero K] in
include htr in

theorem essFiniteType_E : Algebra.EssFiniteType K E :=
  essFiniteType_of_transcendental_of_finiteDimensional
    (transcendental_gen htr) (finiteDimensional_adjoin_gen' f)

omit [IsAlgClosed K] in
include htr in

theorem hasCanonicalDivisor_E :
    haveI : IsCurveOver K E := isCurveOver_E htr
    HasCanonicalDivisor (K := K) (F := E) := by
  haveI : PerfectField K := PerfectField.ofCharZero
  haveI : IsCurveOver K E := isCurveOver_E htr
  haveI : Algebra.EssFiniteType K E := essFiniteType_E htr
  exact hasCanonicalDivisor_of_isCurveOver

include htr in

theorem genus_E_eq_zero :
    haveI : IsCurveOver K E := isCurveOver_E htr
    haveI : HasCanonicalDivisor (K := K) (F := E) := hasCanonicalDivisor_E htr
    genus K E = 0 := by
  classical
  haveI : PerfectField K := PerfectField.ofCharZero
  haveI hIC : IsCurveOver K E := isCurveOver_E htr
  haveI hEF : Algebra.EssFiniteType K E := essFiniteType_E htr
  haveI hCD : HasCanonicalDivisor (K := K) (F := E) := hasCanonicalDivisor_E htr
  haveI hDC : ∀ v : Place K E, v.DCoordGenerates := dCoordGenerates_of_isCurveOver

  haveI hICr : IsCurveOver K (RatFunc K) := instIsCurveOverRatFunc K
  haveI hEFr : Algebra.EssFiniteType K (RatFunc K) := essFiniteType_ratFunc K
  haveI hCDr : HasCanonicalDivisor (K := K) (F := RatFunc K) :=
    instHasCanonicalDivisorRatFuncPerfectField K
  haveI hDCr : ∀ v : Place K (RatFunc K), v.DCoordGenerates := dCoordGenerates_of_isCurveOver

  let e := adjoinEquivRatFunc htr
  letI : Algebra (RatFunc K) E := (e.symm.toAlgHom.toRingHom).toAlgebra
  haveI : IsScalarTower K (RatFunc K) E := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact congrArg Subtype.val ((e.symm.commutes r).symm))
  let eR : E ≃ₐ[RatFunc K] RatFunc K :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun r => e.apply_symm_apply r)
  haveI : FiniteDimensional (RatFunc K) E := Module.Finite.equiv eR.symm.toLinearEquiv
  haveI : Algebra.IsSeparable (RatFunc K) E :=
    Algebra.IsSeparable.of_algHom _ _ eR.toAlgHom

  have hC_R : ConstantsAreBase K (RatFunc K) :=
    constantsAreBase_of_isAlgClosed K (RatFunc K)
  have hRR_R : FunctionFieldRiemannRoch K (RatFunc K) :=
    functionFieldRiemannRoch_of_isAlgClosed
  have hSG_R : StichtenothGenusExists K (RatFunc K) :=
    stichtenothGenusExists_of_isCurveOver hC_R
  have hWDA_R : WeilDualityAdelic K (RatFunc K) := AlgebraicCurve.weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists hRR_R hSG_R
  have hC_E : ConstantsAreBase K E := constantsAreBase_of_isAlgClosed K E
  have hRR_E : FunctionFieldRiemannRoch K E := functionFieldRiemannRoch_of_isAlgClosed
  have hSG_E : StichtenothGenusExists K E := stichtenothGenusExists_of_isCurveOver hC_E
  have hWDA_E : WeilDualityAdelic K E := AlgebraicCurve.weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists hRR_E hSG_E

  have h1 : genus K E = genusFF K E := AlgebraicCurve.genus_eq_genusFF hRR_E hWDA_E hC_E
  have h2 : genusFF K E = genusFF K (RatFunc K) := AlgebraicCurve.genusFF_eq_of_algEquiv e
  have h3 : genus K (RatFunc K) = genusFF K (RatFunc K) :=
    AlgebraicCurve.genus_eq_genusFF hRR_R hWDA_R hC_R
  have h4 : genus K (RatFunc K) = 0 := genus_ratFunc_eq_zero K
  omega

end Heads

end RHEtower

open AlgebraicCurve IntermediateField KaehlerDifferential

namespace SolRH

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
variable {F : Type*} [Field F] [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
variable [HasCanonicalDivisor (K := K) (F := F)]
variable {f : F} (htr : Transcendental K f)
  [FiniteDimensional (↥(adjoin K ({f} : Set F))) F]

include htr

set_option quotPrecheck false in
local notation "E" => (↥(adjoin K ({f} : Set F)))

private lemma degree_canonicalDivisorOf_F {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    Divisor.degree (canonicalDivisorOf hω) = 2 * (genus K F : ℤ) - 2 := by
  classical
  haveI : PerfectField K := PerfectField.ofCharZero
  haveI : ∀ w : Place K F, w.DCoordGenerates := dCoordGenerates_of_isCurveOver

  let e := RHEtower.adjoinEquivRatFunc htr
  letI algRE : Algebra (RatFunc K) E := e.symm.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower K (RatFunc K) E := IsScalarTower.of_algebraMap_eq' (by
    ext r; exact congrArg Subtype.val ((e.symm.commutes r).symm))
  let eR : E ≃ₐ[RatFunc K] RatFunc K :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun r => e.apply_symm_apply r)
  haveI : Module.Finite (RatFunc K) E := Module.Finite.equiv eR.symm.toLinearEquiv
  letI algRF : Algebra (RatFunc K) F :=
    (((adjoin K ({f} : Set F)).val).comp e.symm.toAlgHom).toRingHom.toAlgebra
  haveI : IsScalarTower K (RatFunc K) F := IsScalarTower.of_algebraMap_eq' (by
    ext r
    show algebraMap K F r = (adjoin K ({f} : Set F)).val (e.symm (algebraMap K (RatFunc K) r))
    rw [e.symm.commutes]; rfl)
  haveI : IsScalarTower (RatFunc K) E F := IsScalarTower.of_algebraMap_eq' rfl

  haveI : FiniteDimensional (RatFunc K) F := Module.Finite.trans E F
  haveI : CharZero (RatFunc K) :=
    charZero_of_injective_algebraMap (algebraMap K (RatFunc K)).injective
  haveI : Algebra.IsIntegral (RatFunc K) F := Algebra.IsIntegral.of_finite _ _

  haveI : IsCurveOver K (RatFunc K) := instIsCurveOverRatFunc K
  haveI : Algebra.EssFiniteType K (RatFunc K) := RHEtower.essFiniteType_ratFunc K
  haveI : HasCanonicalDivisor (K := K) (F := RatFunc K) :=
    instHasCanonicalDivisorRatFuncPerfectField K
  haveI : ∀ v : Place K (RatFunc K), v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  haveI : Nontrivial Ω[F⁄K] := ⟨ω, 0, hω⟩
  haveI : Nontrivial Ω[RatFunc K⁄K] := by
    obtain ⟨t, ht⟩ := AlgebraicCurve.exists_D_ne_zero (K := K) (F := RatFunc K)
    exact ⟨D K (RatFunc K) t, 0, ht⟩
  exact degree_canonicalDivisor_eq_of_isAlgClosed hω

omit [IsCurveOver K F] [Algebra.EssFiniteType K F] [HasCanonicalDivisor (K := K) (F := F)]
  [FiniteDimensional (↥(adjoin K ({f} : Set F))) F] in

private lemma degree_canonicalDivisorOf_E :
    haveI : IsCurveOver K E := RHEtower.isCurveOver_E htr
    haveI : HasCanonicalDivisor (K := K) (F := E) := RHEtower.hasCanonicalDivisor_E htr
    ∀ {ω : Ω[E⁄K]} (hω : ω ≠ 0),
      Divisor.degree (canonicalDivisorOf hω) = 2 * (genus K E : ℤ) - 2 := by
  haveI : IsCurveOver K E := RHEtower.isCurveOver_E htr
  haveI : Algebra.EssFiniteType K E := RHEtower.essFiniteType_E htr
  haveI : HasCanonicalDivisor (K := K) (F := E) := RHEtower.hasCanonicalDivisor_E htr
  intro ω hω

  have hgen := RHEtower.transcendental_gen htr
  haveI hfd : FiniteDimensional (↥(adjoin K ({AdjoinSimple.gen K f} : Set E))) E :=
    RHEtower.finiteDimensional_adjoin_gen' f
  exact @degree_canonicalDivisorOf_F K _ _ _ E _ _ _ _ _ _ hgen hfd _ hω

omit [IsAlgClosed K] [CharZero K] [IsCurveOver K F] [Algebra.EssFiniteType K F] htr
  [HasCanonicalDivisor (K := K) (F := F)]
  [FiniteDimensional (↥(adjoin K ({f} : Set F))) F] in

private lemma ramIdxAlong_eq_ramIdx (w : Place K F) :
    Place.ramificationIndexAlong (adjoin K ({f} : Set F)).val w = w.ramificationIndex E := by
  unfold Place.ramificationIndexAlong
  congr 1

end SolRH

open SolRH in
theorem solution
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {F : Type*} [Field F] [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    [HasCanonicalDivisor (K := K) (F := F)]
    {f : F} (htr : Transcendental K f)
    [FiniteDimensional (↥(adjoin K ({f} : Set F))) F] :
    (∑ᶠ w : Place K F, ((Place.ramificationIndexAlong (adjoin K ({f} : Set F)).val w : ℤ) - 1)) =
      2 * (Module.finrank K ↥(regularDifferentials K F) : ℤ) - 2 +
      2 * (Module.finrank (↥(adjoin K ({f} : Set F))) F : ℤ) := by

  rw [(AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus
    (K := K) (F := F)).2]

  set E := adjoin K ({f} : Set F)
  haveI : IsCurveOver K (↥E) := RHEtower.isCurveOver_E htr
  haveI : Algebra.EssFiniteType K (↥E) := RHEtower.essFiniteType_E htr
  haveI : HasCanonicalDivisor (K := K) (F := ↥E) := RHEtower.hasCanonicalDivisor_E htr
  haveI : ∀ v : Place K (↥E), v.DCoordGenerates :=
    fun v => AlgebraicCurve.dCoordGenerates_of_isCurveOver v
  haveI : ∀ w : Place K F, w.DCoordGenerates :=
    fun w => AlgebraicCurve.dCoordGenerates_of_isCurveOver w
  haveI : Algebra.IsIntegral (↥E) F := Algebra.IsIntegral.of_finite (↥E) F
  haveI : Algebra.IsSeparable (↥E) F := Algebra.IsSeparable.of_integral (↥E) F

  set t := AdjoinSimple.gen K f
  haveI : CharZero (↥E) :=
    charZero_of_injective_algebraMap (algebraMap K (↥E)).injective
  have hdf_ne : D K F f ≠ 0 := KaehlerDifferential.D_ne_zero_of_transcendental K f htr
  have ht_ne : D K (↥E) t ≠ 0 := by
    haveI hfd : FiniteDimensional (↥(adjoin K ({t} : Set (↥E)))) (↥E) :=
      RHEtower.finiteDimensional_adjoin_gen' f
    haveI : Algebra.IsIntegral (↥(adjoin K ({t} : Set (↥E)))) (↥E) :=
      Algebra.IsIntegral.of_finite _ _
    haveI : CharZero (↥(adjoin K ({t} : Set (↥E)))) :=
      charZero_of_injective_algebraMap (algebraMap K _).injective
    exact KaehlerDifferential.D_ne_zero_of_transcendental K t (RHEtower.transcendental_gen htr)
  have hmap : map K K (↥E) F (D K (↥E) t) = D K F f := by
    have := KaehlerDifferential.map_D K K (↥E) F t
    rwa [AdjoinSimple.algebraMap_gen K f] at this

  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective

  have htame : ∀ w : Place K F, ((w.ramificationIndex (↥E) : ℕ) : F) ≠ 0 := by
    intro w
    exact_mod_cast Nat.cast_ne_zero.mpr (w.ramificationIndex_pos (F := ↥E)).ne'

  have hRH := AlgebraicCurve.two_mul_genus_sub_two_eq_of_degree_canonical
    (K := K) (F := ↥E) (F' := F)
    (htame := htame)
    (hω₀ := ht_ne) (hω₀' := hmap ▸ hdf_ne)
    (hK := degree_canonicalDivisorOf_E htr ht_ne)
    (hK' := by
      have heq : canonicalDivisorOf (hmap ▸ hdf_ne) = canonicalDivisorOf hdf_ne := by
        congr 1
      rw [heq]; exact degree_canonicalDivisorOf_F htr hdf_ne)
    (hreg := AlgebraicCurve.localUnitDerivativeRegular_of_isCurveOver)

  rw [RHEtower.genus_E_eq_zero htr] at hRH
  simp only [Nat.cast_zero, mul_zero, zero_sub, mul_neg, mul_comm _ (2 : ℤ)] at hRH
  have hdeg : ∀ w : Place K F, (w.deg : ℤ) = 1 := fun w => by
    exact_mod_cast AlgebraicCurve.Place.deg_eq_one_of_isAlgClosed w
      (AlgebraicCurve.Place.deg_ne_zero_of_finiteDimensional_adjoin f htr w)
  simp only [hdeg, mul_one] at hRH

  have hrw : ∀ w : Place K F,
      ((Place.ramificationIndexAlong E.val w : ℕ) : ℤ) = ((w.ramificationIndex (↥E) : ℕ) : ℤ) := by
    intro w; exact_mod_cast ramIdxAlong_eq_ramIdx w
  simp only [hrw]
  linarith [hRH]

end S_AlgebraicCurve_finsum_ramificationIndexAlong_sub_one_eq
end P2MW
export P2MW.S_AlgebraicCurve_finsum_ramificationIndexAlong_sub_one_eq (solution)
