-- Prove2me | solution 1 for AutomorphicForm.exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/64ae91b8-8a8a-5029-9e60-783ba1842595

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Algebra.Module.ZLattice.Basic
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_AutomorphicForm_exists_flat_isInducedSection_sum_eq_of_differentiable_family
import Theorems.Thm_AutomorphicForm_exists_localComponents_of_isGlobalAddChar
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_EisensteinGeneral_FactorizationDatum
import Mathlib.MeasureTheory.Integral.Pi
import Theorems.Thm_EisensteinGeneral_Glue_whittakerCoefficient_bruhatSeries_eq_finset_sum
import Theorems.Thm_EisensteinGeneral_Piece_continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero
import Theorems.Thm_EisensteinGeneral_Piece_exists_forall_nonempty_factorizationDatum
import Theorems.Thm_EisensteinGeneral_Piece_integrable_weyl_unipotent_mul_of_factorization
import Theorems.Thm_EisensteinGeneral_Piece_exists_entire_partialEulerProduct_mul_eq_whittakerCoefficient_and_summable_majorant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein
p2m_attr_erase "instance" "instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions"
p2m_attr_erase "instance" "NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply"
p2m_attr_erase "simp" "IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent"

set_option autoImplicit false

section GlueHeads

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox NumberField.AdelicFourier NumberField.AdelicHaar IsDedekindDomain AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace EgenGlue

private theorem _root_.EgenGlue.whittakerCoefficient_bruhatSeries_eq_finset_sum (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψc : Continuous ψ) (hψ : ∀ x, ‖ψ x‖ = 1) (n : ℕ) (c : Fin n → ℂ)
    (Ψ : Fin n → AdelicGL2 (𝓞 F) F → ℂ) (Φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hΨ : ∀ i, ∃ χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, IsInducedSection (𝓞 F) F χ₁ χ₂ (Ψ i))
    (hΦ : ∀ g', Φ g' = ∑ i : Fin n, c i * Ψ i g') (ξ : F) (g : AdelicGL2 (𝓞 F) F)
    (hint : ∀ i, Integrable (fun y => Ψ i (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)) (adelicAddHaar (𝓞 F) F)) :
    whittakerCoefficient F (productionPins F) ψ
        (fun g' => Φ g' + ∑' ξ' : F, Φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g'))
        ξ g
      = ∑ i : Fin n, c i * whittakerCoefficient F (productionPins F) ψ
          (fun g' => Ψ i g' + ∑' ξ' : F,
            Ψ i (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) ξ g :=
  EisensteinGeneral.Glue.whittakerCoefficient_bruhatSeries_eq_finset_sum F ψ hψc hψ n c Ψ Φ hΨ hΦ ξ g hint

p2m_export "EgenGlue" "whittakerCoefficient_bruhatSeries_eq_finset_sum"

private theorem differentiable_tsum_and_summable_of_forall_radius {ι : Type} (f : ι → ℂ → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i))
    (hM : ∀ R : ℝ, ∃ M : ι → ℝ, Summable M ∧ ∀ (i : ι) (s : ℂ), ‖s‖ ≤ R → ‖f i s‖ ≤ M i) :
    Differentiable ℂ (fun s : ℂ => ∑' i : ι, f i s) ∧ ∀ s : ℂ, Summable (fun i : ι => f i s) := by
  refine ⟨?_, fun s => ?_⟩
  · have hloc : TendstoLocallyUniformlyOn (fun t : Finset ι => fun s : ℂ => ∑ i ∈ t, f i s)
        (fun s : ℂ => ∑' i : ι, f i s) Filter.atTop Set.univ := by
      refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun s₀ _ => ?_
      obtain ⟨M, hMs, hMb⟩ := hM (‖s₀‖ + 1)
      refine ⟨Metric.closedBall 0 (‖s₀‖ + 1),
        mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds_of_mem (by simp)),
        tendstoUniformlyOn_tsum hMs fun i s hs => hMb i s ?_⟩
      simpa using hs
    exact differentiableOn_univ.mp (hloc.differentiableOn
      (Filter.Eventually.of_forall fun t => DifferentiableOn.fun_sum fun i _ => (hf i).differentiableOn)
      isOpen_univ)
  · obtain ⟨M, hMs, hMb⟩ := hM ‖s‖
    exact Summable.of_norm_bounded hMs fun i => hMb i s le_rfl

private theorem exists_differentiable_mul_eq_tsum_of_pieces {κ : Type} (n : ℕ) (c : Fin n → ℂ → ℂ)
    (hc : ∀ i, Differentiable ℂ (c i)) (Ep : ℂ → ℂ) (W : κ → ℂ → ℂ) (Q : Fin n → κ → ℂ → ℂ)
    (hQ : ∀ i ξ, Differentiable ℂ (Q i ξ))
    (hM : ∀ (i : Fin n) (R : ℝ), ∃ M : κ → ℝ, Summable M ∧ ∀ (ξ : κ) (s : ℂ), ‖s‖ ≤ R → ‖Q i ξ s‖ ≤ M ξ)
    (hW : ∀ s : ℂ, 1 < s.re → ∀ ξ : κ, W ξ s = ∑ i : Fin n, c i s * (Ep s * Q i ξ s)) :
    ∃ Nc : ℂ → ℂ, Differentiable ℂ Nc ∧ ∀ s : ℂ, 1 < s.re → Ep s * Nc s = ∑' ξ : κ, W ξ s := by
  have hD : ∀ i : Fin n, Differentiable ℂ (fun s : ℂ => ∑' ξ : κ, Q i ξ s) ∧
      ∀ s : ℂ, Summable (fun ξ : κ => Q i ξ s) := fun i =>
    differentiable_tsum_and_summable_of_forall_radius (Q i) (hQ i) (hM i)
  refine ⟨fun s => ∑ i : Fin n, c i s * ∑' ξ : κ, Q i ξ s,
    Differentiable.fun_sum fun i _ => (hc i).fun_mul (hD i).1, fun s hs => ?_⟩
  have hsum : ∀ i : Fin n, Summable (fun ξ : κ => c i s * (Ep s * Q i ξ s)) := fun i =>
    (((hD i).2 s).mul_left (Ep s)).mul_left (c i s)
  rw [tsum_congr (hW s hs), Summable.tsum_finsetSum fun i _ => hsum i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tsum_mul_left, tsum_mul_left]
  ring

private theorem exists_uniformizer_valued_eq (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : (v.adicCompletion F)ˣ, Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hval : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [v.valuedAdicCompletion_eq_valuation' π, hπ]
  have hne : (π : v.adicCompletion F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hval
    exact WithZero.exp_ne_zero hval.symm
  exact ⟨Units.mk0 _ hne, hval⟩

private theorem isUnitaryChar_and_isIdeleClassChar_mul_inv (F : Type) [Field F] [NumberField F]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hμic : IsIdeleClassChar (𝓞 F) F μ) (hνic : IsIdeleClassChar (𝓞 F) F ν) :
    IsUnitaryChar (𝓞 F) F (μ * ν⁻¹) ∧ IsIdeleClassChar (𝓞 F) F (μ * ν⁻¹) ∧
      (Continuous μ → Continuous ν → Continuous (μ * ν⁻¹)) := by
  refine ⟨fun x => ?_, fun u => ?_, fun hμc hνc => ?_⟩
  · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul,
      norm_inv, hμ x, hν x, inv_one, mul_one]
  · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hμic u, hνic u, inv_one, mul_one]
  · show Continuous (fun x => μ x * (ν x)⁻¹)
    exact hμc.mul hνc.inv

end EgenGlue

end GlueHeads

section PieceLayer

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox NumberField.AdelicFourier NumberField.AdelicHaar IsDedekindDomain AutomorphicForm

open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace EgenPiece

open scoped Classical in

private theorem _root_.EgenPiece.integrable_weyl_unipotent_mul_of_factorization
    (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ) (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
    (hnψfin : (Function.support nψ).Finite)
    (hψv : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
      Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1)
    (hψv' : ∀ v : HeightOneSpectrum (𝓞 F),
      ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (nψ v + 1) ∧ ψv v x ≠ 1)
    (hψfin : ∀ x : FiniteAdeleRing (𝓞 F) F,
      ψ (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) x)
        = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ψv v (x v))
    (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (hθr : ∀ i, θr i ≠ 0)
    (θc : {w : InfinitePlace F // w.IsComplex} → ℂ) (hθc : ∀ w, θc w ≠ 0)
    (hψarch : ∀ p : mixedEmbedding.mixedSpace F,
      ψ (AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p))
        = (∏ i : {w : InfinitePlace F // w.IsReal},
              Complex.exp (-(((2 * Real.pi * θr i * p.1 i : ℝ) : ℂ) * Complex.I)))
          * ∏ w : {w : InfinitePlace F // w.IsComplex},
              Complex.exp (-(((4 * Real.pi * (θc w * p.2 w).re : ℝ) : ℂ) * Complex.I)))
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (hχϖ : ∀ v, ‖((NumberField.TateGlobal.localChar χ v (ϖ v) : ℂˣ) : ℂ)‖ = 1)
    (hχS : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 →
      NumberField.TateGlobal.localChar χ v u = 1)
    (hnψ : ∀ v ∉ S, nψ v = 0)
    (cS : HeightOneSpectrum (𝓞 F) → ℕ) (hcS : ∀ v ∈ S, 1 ≤ cS v)
    (hχc : ∀ v ∈ S, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v (cS v),
      NumberField.TateGlobal.localChar χ v u = 1)
    (mS : ℕ) (hmS : 1 ≤ mS) (n : ℕ)
    (A B : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hA : ∀ (j : Fin n), ∀ v ∈ S, ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → A j v y = A j v x)
    (hB : ∀ (j : Fin n), ∀ v ∈ S, ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → B j v y = B j v x)
    (h : Fin n → (v : HeightOneSpectrum (𝓞 F)) → ℂ → v.adicCompletion F → ℂ)
    (hoff : ∀ (j : Fin n), ∀ v ∉ S, ∀ (s : ℂ) (x : v.adicCompletion F),
      h j v s x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
    (hon : ∀ (j : Fin n), ∀ v ∈ S, ∀ (s : ℂ) (x : v.adicCompletion F),
      h j v s x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A j v) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B j v y⁻¹) x)
    (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ) (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ)
    (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ)
    (habm : ∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}), (abm j w).1 + (abm j w).2.1 ≤ (abm j w).2.2)
    (Wr : Fin n → {w : InfinitePlace F // w.IsReal} → ℂ → ℝ → ℂ)
    (hWr : ∀ (j : Fin n) (i : {w : InfinitePlace F // w.IsReal}) (s : ℂ) (x : ℝ),
      Wr j i s x = ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ (kdat j i)
        * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2)))
    (Wc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ → ℂ)
    (hWc : ∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}) (s z : ℂ),
      Wc j w s z = z ^ (abm j w).1 * (starRingEnd ℂ) z ^ (abm j w).2.1
        * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2)))
    (a : (AdeleRing (𝓞 F) F)ˣ) (u : AdeleRing (𝓞 F) F) (C : Fin n → ℂ → ℂ)
    (hC : ∀ j, Differentiable ℂ (C j))
    (Ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hΨ : ∀ s, ∃ χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, IsInducedSection (𝓞 F) F χ₁ χ₂ (Ψ s))
    (g : AdelicGL2 (𝓞 F) F)
    (hfac : ∀ (s : ℂ) (y : AdeleRing (𝓞 F) F),
      Ψ s (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)
        = ∑ j : Fin n, C j s
          * (∏ i : {w : InfinitePlace F // w.IsReal},
              Wr j i s ((InfiniteAdeleRing.ringEquiv_mixedSpace F (a • (y + u)).1).1 i))
          * (∏ w : {w : InfinitePlace F // w.IsComplex},
              Wc j w s ((InfiniteAdeleRing.ringEquiv_mixedSpace F (a • (y + u)).1).2 w))
          * ∏ᶠ v : HeightOneSpectrum (𝓞 F), h j v s ((a • (y + u)).2 v)) :
    ∀ s : ℂ, 1 < s.re →
      Integrable (fun y => Ψ s (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)) (adelicAddHaar (𝓞 F) F) := by
  have _ := hψ; have _ := hnψfin; have _ := hψv; have _ := hψv'; have _ := hψfin; have _ := hθr; have _ := hθc
  have _ := hψarch; have _ := hΨ
  exact EisensteinGeneral.Piece.integrable_weyl_unipotent_mul_of_factorization F ψv nψ χ S ϖ hϖ Ψ g
    ⟨cS, mS, n, A, B, h, kdat, τr, abm, τc, Wr, Wc, a, u, C, hχϖ, hχS, hnψ, hcS, hχc, hmS, hA, hB, hoff, hon, habm,
      hWr, hWc, hC, hfac⟩

p2m_export "EgenPiece" "integrable_weyl_unipotent_mul_of_factorization"
open scoped Classical in

private theorem _root_.EgenPiece.exists_entire_partialEulerProduct_mul_eq_whittakerCoefficient_and_summable_majorant
    (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ) (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
    (hnψfin : (Function.support nψ).Finite)
    (hψv : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
      Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1)
    (hψv' : ∀ v : HeightOneSpectrum (𝓞 F),
      ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (nψ v + 1) ∧ ψv v x ≠ 1)
    (hψfin : ∀ x : FiniteAdeleRing (𝓞 F) F,
      ψ (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) x)
        = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ψv v (x v))
    (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (hθr : ∀ i, θr i ≠ 0)
    (θc : {w : InfinitePlace F // w.IsComplex} → ℂ) (hθc : ∀ w, θc w ≠ 0)
    (hψarch : ∀ p : mixedEmbedding.mixedSpace F,
      ψ (AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p))
        = (∏ i : {w : InfinitePlace F // w.IsReal},
              Complex.exp (-(((2 * Real.pi * θr i * p.1 i : ℝ) : ℂ) * Complex.I)))
          * ∏ w : {w : InfinitePlace F // w.IsComplex},
              Complex.exp (-(((4 * Real.pi * (θc w * p.2 w).re : ℝ) : ℂ) * Complex.I)))
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (hχϖ : ∀ v, ‖((NumberField.TateGlobal.localChar χ v (ϖ v) : ℂˣ) : ℂ)‖ = 1)
    (hχS : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 →
      NumberField.TateGlobal.localChar χ v u = 1)
    (hnψ : ∀ v ∉ S, nψ v = 0)
    (cS : HeightOneSpectrum (𝓞 F) → ℕ) (hcS : ∀ v ∈ S, 1 ≤ cS v)
    (hχc : ∀ v ∈ S, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v (cS v),
      NumberField.TateGlobal.localChar χ v u = 1)
    (mS : ℕ) (hmS : 1 ≤ mS) (n : ℕ)
    (A B : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hA : ∀ (j : Fin n), ∀ v ∈ S, ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → A j v y = A j v x)
    (hB : ∀ (j : Fin n), ∀ v ∈ S, ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → B j v y = B j v x)
    (h : Fin n → (v : HeightOneSpectrum (𝓞 F)) → ℂ → v.adicCompletion F → ℂ)
    (hoff : ∀ (j : Fin n), ∀ v ∉ S, ∀ (s : ℂ) (x : v.adicCompletion F),
      h j v s x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
    (hon : ∀ (j : Fin n), ∀ v ∈ S, ∀ (s : ℂ) (x : v.adicCompletion F),
      h j v s x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A j v) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B j v y⁻¹) x)
    (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ) (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ)
    (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ)
    (habm : ∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}), (abm j w).1 + (abm j w).2.1 ≤ (abm j w).2.2)
    (Wr : Fin n → {w : InfinitePlace F // w.IsReal} → ℂ → ℝ → ℂ)
    (hWr : ∀ (j : Fin n) (i : {w : InfinitePlace F // w.IsReal}) (s : ℂ) (x : ℝ),
      Wr j i s x = ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ (kdat j i)
        * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2)))
    (Wc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ → ℂ)
    (hWc : ∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}) (s z : ℂ),
      Wc j w s z = z ^ (abm j w).1 * (starRingEnd ℂ) z ^ (abm j w).2.1
        * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2)))
    (a : (AdeleRing (𝓞 F) F)ˣ) (u : AdeleRing (𝓞 F) F) (C : Fin n → ℂ → ℂ)
    (hC : ∀ j, Differentiable ℂ (C j))
    (Ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hΨ : ∀ s, ∃ χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, IsInducedSection (𝓞 F) F χ₁ χ₂ (Ψ s))
    (g : AdelicGL2 (𝓞 F) F)
    (hfac : ∀ (s : ℂ) (y : AdeleRing (𝓞 F) F),
      Ψ s (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)
        = ∑ j : Fin n, C j s
          * (∏ i : {w : InfinitePlace F // w.IsReal},
              Wr j i s ((InfiniteAdeleRing.ringEquiv_mixedSpace F (a • (y + u)).1).1 i))
          * (∏ w : {w : InfinitePlace F // w.IsComplex},
              Wc j w s ((InfiniteAdeleRing.ringEquiv_mixedSpace F (a • (y + u)).1).2 w))
          * ∏ᶠ v : HeightOneSpectrum (𝓞 F), h j v s ((a • (y + u)).2 v)) :
    ∃ Q : {ξ : F // ξ ≠ 0} → ℂ → ℂ,
      (∀ ξ : {ξ : F // ξ ≠ 0}, Differentiable ℂ (Q ξ)) ∧
      (∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ), 1 < s.re →
        whittakerCoefficient F (productionPins F) ψ
            (fun g' => Ψ s g' + ∑' ξ' : F, Ψ s (adelicWeyl (𝓞 F) F
                * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) (ξ : F) g
          = (∏' v : {v // v ∉ S},
              (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * Q ξ s) ∧
      (∀ R : ℝ, ∃ M : {ξ : F // ξ ≠ 0} → ℝ, Summable M ∧
        ∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ), ‖s‖ ≤ R → ‖Q ξ s‖ ≤ M ξ) := by
  have _ := hnψfin
  exact EisensteinGeneral.Piece.exists_entire_partialEulerProduct_mul_eq_whittakerCoefficient_and_summable_majorant
    F ψ hψ ψv nψ hψv hψv' hψfin θr hθr θc hθc hψarch χ S ϖ hϖ Ψ hΨ g
    ⟨cS, mS, n, A, B, h, kdat, τr, abm, τc, Wr, Wc, a, u, C, hχϖ, hχS, hnψ, hcS, hχc, hmS, hA, hB, hoff, hon, habm,
      hWr, hWc, hC, hfac⟩

p2m_export "EgenPiece" "exists_entire_partialEulerProduct_mul_eq_whittakerCoefficient_and_summable_majorant"

private theorem _root_.EgenPiece.continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero (F : Type) [Field F]
    [NumberField F] (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((α x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s₀ : ℂ) (φ₀ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ₀ : IsInducedSection (𝓞 F) F (etaFst μ α hα s₀) (etaSnd ν α hα s₀) φ₀) (hφ₀c : Continuous φ₀)
    (g₀ : AdelicGL2 (𝓞 F) F) (hne : φ₀ g₀ ≠ 0) :
    Continuous μ ∧ Continuous ν :=
  EisensteinGeneral.Piece.continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero
    F α hα hαc μ ν s₀ φ₀ hφ₀ hφ₀c g₀ hne

p2m_export "EgenPiece" "continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero"
open NumberField.AdelicLevel AutomorphicForm.WindowedSiegel in
open scoped Classical in

private theorem exists_sum_factorization_weyl_unipotent_mul_of_flat
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμc : Continuous μ) (_hνc : Continuous ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
      (_hψ : IsGlobalAddChar F ψ)
      (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ)
      (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
      (_hnψfin : (Function.support nψ).Finite)
      (_hψv : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
        Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1)
      (_hψv' : ∀ v : HeightOneSpectrum (𝓞 F),
        ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (nψ v + 1) ∧ ψv v x ≠ 1)
      (_hψfin : ∀ x : FiniteAdeleRing (𝓞 F) F,
        ψ (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) x)
        = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ψv v (x v))
      (θr : {w : InfinitePlace F // w.IsReal} → ℝ)
      (_hθr : ∀ i, θr i ≠ 0)
      (θc : {w : InfinitePlace F // w.IsComplex} → ℂ)
      (_hθc : ∀ w, θc w ≠ 0)
      (_hψarch : ∀ p : mixedEmbedding.mixedSpace F,
        ψ (AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p))
        = (∏ i : {w : InfinitePlace F // w.IsReal},
        Complex.exp (-(((2 * Real.pi * θr i * p.1 i : ℝ) : ℂ) * Complex.I)))
        * ∏ w : {w : InfinitePlace F // w.IsComplex},
        Complex.exp (-(((4 * Real.pi * (θc w * p.2 w).re : ℝ) : ℂ) * Complex.I)))
      (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hχ : χ = μ * ν⁻¹)
      (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
      (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
      (Ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hΨ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (Ψ s))
      (_hΨK : ∀ s, IsArchKFinite F (Ψ s))
      (_hΨf : ∀ s, IsKfSmooth F (Ψ s))
      (_hΨjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => Ψ p.1 p.2))
      (_hΨhol : ∀ g, Differentiable ℂ (fun s => Ψ s g))
      (_hΨflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          Ψ s k = Ψ s' k)
      (_hΨne : ∃ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), Ψ s g ≠ 0)
      (g : AdelicGL2 (𝓞 F) F),
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S →
      ∃ (cS : HeightOneSpectrum (𝓞 F) → ℕ)
        (mS : ℕ)
        (n : ℕ)
        (A B : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
        (h : Fin n → (v : HeightOneSpectrum (𝓞 F)) → ℂ → v.adicCompletion F → ℂ)
        (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ)
        (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ)
        (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
        (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ)
        (Wr : Fin n → {w : InfinitePlace F // w.IsReal} → ℂ → ℝ → ℂ)
        (Wc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ → ℂ)
        (a : (AdeleRing (𝓞 F) F)ˣ)
        (u : AdeleRing (𝓞 F) F)
        (C : Fin n → ℂ → ℂ),
      (∀ v, ‖((NumberField.TateGlobal.localChar χ v (ϖ v) : ℂˣ) : ℂ)‖ = 1) ∧
      (∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 →
        NumberField.TateGlobal.localChar χ v u = 1) ∧
      (∀ v ∉ S, nψ v = 0) ∧
      (∀ v ∈ S, 1 ≤ cS v) ∧
      (∀ v ∈ S, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v (cS v),
        NumberField.TateGlobal.localChar χ v u = 1) ∧
      (1 ≤ mS) ∧
      (∀ (j : Fin n), ∀ v ∈ S, ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
        Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → A j v y = A j v x) ∧
      (∀ (j : Fin n), ∀ v ∈ S, ∀ x y : v.adicCompletion F,
        Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → B j v y = B j v x) ∧
      (∀ (j : Fin n), ∀ v ∉ S, ∀ (s : ℂ) (x : v.adicCompletion F),
        h j v s x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
        (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v)⁻¹ y
        * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x) ∧
      (∀ (j : Fin n), ∀ v ∈ S, ∀ (s : ℂ) (x : v.adicCompletion F),
        h j v s x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A j v) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
        (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v)⁻¹ y
        * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B j v y⁻¹) x) ∧
      (∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}), (abm j w).1 + (abm j w).2.1 ≤ (abm j w).2.2) ∧
      (∀ (j : Fin n) (i : {w : InfinitePlace F // w.IsReal}) (s : ℂ) (x : ℝ),
        Wr j i s x = ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ (kdat j i)
        * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2))) ∧
      (∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}) (s z : ℂ),
        Wc j w s z = z ^ (abm j w).1 * (starRingEnd ℂ) z ^ (abm j w).2.1
        * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2))) ∧
      (∀ j, Differentiable ℂ (C j)) ∧
      (∀ s, ∃ χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, IsInducedSection (𝓞 F) F χ₁ χ₂ (Ψ s)) ∧
      ∀ (s : ℂ) (y : AdeleRing (𝓞 F) F),
        Ψ s (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)
        = ∑ j : Fin n, C j s
        * (∏ i : {w : InfinitePlace F // w.IsReal},
        Wr j i s ((InfiniteAdeleRing.ringEquiv_mixedSpace F (a • (y + u)).1).1 i))
        * (∏ w : {w : InfinitePlace F // w.IsComplex},
        Wc j w s ((InfiniteAdeleRing.ringEquiv_mixedSpace F (a • (y + u)).1).2 w))
        * ∏ᶠ v : HeightOneSpectrum (𝓞 F), h j v s ((a • (y + u)).2 v) := by
  intro α hα μ ν _hμ _hν _hμc _hνc ψ _hψ ψv nψ _hnψfin _hψv _hψv' _hψfin θr _hθr θc _hθc _hψarch χ _hχ ϖ _hϖ Ψ _hΨ _hΨK
    _hΨf _hΨjc _hΨhol _hΨflat _hΨne g
  obtain ⟨S₀, hS₀⟩ :=
    EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum F hα μ ν _hμ _hν _hμc _hνc ψ _hψ ψv nψ _hnψfin
      _hψv _hψv' _hψfin θr _hθr θc _hθc _hψarch χ _hχ ϖ _hϖ Ψ _hΨ _hΨK _hΨf _hΨjc _hΨhol _hΨflat _hΨne g
  refine ⟨S₀, fun S hS => ?_⟩
  obtain ⟨D⟩ := hS₀ S hS
  exact ⟨D.cS, D.mS, D.n, D.A, D.B, D.h, D.kdat, D.τr, D.abm, D.τc, D.Wr, D.Wc, D.a, D.u, D.C, D.hχϖ, D.hχS, D.hnψ,
    D.hcS, D.hχc, D.hmS, D.hA, D.hB, D.hoff, D.hon, D.habm, D.hWr, D.hWc, D.hC, fun s => ⟨_, _, _hΨ s⟩, D.hfac⟩

end EgenPiece

end PieceLayer

section Target

open MeasureTheory NumberField IsDedekindDomain
open scoped NNReal

open AutomorphicForm in

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (_hprin : IsPrincipalTrivial (R := 𝓞 F) (K := F) α)
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
      (_hψ : IsGlobalAddChar F ψ)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (g : AdelicGL2 (𝓞 F) F),
    ∃ χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ,
      Continuous χ ∧ IsUnitaryChar (𝓞 F) F χ ∧ IsIdeleClassChar (𝓞 F) F χ ∧
      ∃ (S : Finset (HeightOneSpectrum (𝓞 F)))
        (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ),
        (∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) ∧
        ∃ Nc : ℂ → ℂ, Differentiable ℂ Nc ∧
          ∀ s : ℂ, 1 < s.re →
            (∏' v : {v // v ∉ S},
              (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * Nc s =
            ∑' ξ : {ξ : F // ξ ≠ 0},
              whittakerCoefficient F (productionPins F) ψ
                (fun g' => φ s g' + ∑' ξ' : F, φ s (adelicWeyl (𝓞 F) F
                    * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) (ξ : F) g := by
  intro α hα _hprin μ ν hμ hν hμic hνic ψ hψ φ hφ hφK hφf hφjc hφhol g
  classical

  choose ϖ hϖ using fun v : HeightOneSpectrum (𝓞 F) => EgenGlue.exists_uniformizer_valued_eq F v
  by_cases hzero : ∀ (s : ℂ) (g' : AdelicGL2 (𝓞 F) F), φ s g' = 0
  ·

    obtain ⟨hμu, hμic', -⟩ := EgenGlue.isUnitaryChar_and_isIdeleClassChar_mul_inv F μ μ hμ hμ hμic hμic
    refine ⟨μ * μ⁻¹, (continuous_const : Continuous fun _ : (AdeleRing (𝓞 F) F)ˣ => (1 : ℂˣ)).congr fun x => ?_,
      hμu, hμic', ∅, ϖ, hϖ, fun _ => 0, differentiable_const 0, fun s _ => ?_⟩
    · simp
    · simp [hzero]
  · push Not at hzero
    obtain ⟨s₀, g₀, hne₀⟩ := hzero

    have hφ₀c : Continuous (φ s₀) :=
      hφjc.comp (continuous_const.prodMk continuous_id)
    have hαc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((α x : ℝˣ) : ℝ) := by
      refine (NumberField.TateGlobal.continuous_ideleNorm F).congr fun x => ?_
      simp [α, NumberField.TateGlobal.ideleNorm]
    obtain ⟨hμc, hνc⟩ := EgenPiece.continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero F α hα
      hαc μ ν s₀ (φ s₀) (hφ s₀) hφ₀c g₀ hne₀
    obtain ⟨hχu, hχic, hχc⟩ := EgenGlue.isUnitaryChar_and_isIdeleClassChar_mul_inv F μ ν hμ hν hμic hνic

    obtain ⟨ψv, nψ, θr, θc, hψv, hψv', hnψfin, hψfin, hθr, hθc, hψarch'⟩ :=
      exists_localComponents_of_isGlobalAddChar F ψ hψ
    have hψarch : ∀ p : mixedEmbedding.mixedSpace F,
        ψ (AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p))
          = (∏ i : {w : InfinitePlace F // w.IsReal},
                Complex.exp (-(((2 * Real.pi * θr i * p.1 i : ℝ) : ℂ) * Complex.I)))
            * ∏ w : {w : InfinitePlace F // w.IsComplex},
                Complex.exp (-(((4 * Real.pi * (θc w * p.2 w).re : ℝ) : ℂ) * Complex.I)) := by
      intro p
      rw [hψarch' p, finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype]

    obtain ⟨n, c, pcs, hc, hind, hK, hf, hjc, hhol, hflat, hsum⟩ :=
      exists_flat_isInducedSection_sum_eq_of_differentiable_family F hα μ ν φ hφ hφK hφf hφjc hφhol

    have hdat := fun (i : Fin n) (hne : ∃ (s : ℂ) (g' : AdelicGL2 (𝓞 F) F), pcs i s g' ≠ 0) =>
      EgenPiece.exists_sum_factorization_weyl_unipotent_mul_of_flat F hα μ ν hμ hν hμc hνc ψ hψ ψv nψ hnψfin
        hψv hψv' hψfin θr hθr θc hθc hψarch (μ * ν⁻¹) rfl ϖ hϖ (pcs i) (hind i) (hK i) (hf i) (hjc i) (hhol i)
        (hflat i) hne g

    let S₀ : Fin n → Finset (HeightOneSpectrum (𝓞 F)) := fun i =>
      if hne : ∃ (s : ℂ) (g' : AdelicGL2 (𝓞 F) F), pcs i s g' ≠ 0 then (hdat i hne).choose else ∅
    let S : Finset (HeightOneSpectrum (𝓞 F)) := Finset.univ.biUnion S₀

    have hpiece : ∀ i : Fin n, ∃ Q : {ξ : F // ξ ≠ 0} → ℂ → ℂ,
        (∀ ξ : {ξ : F // ξ ≠ 0}, Differentiable ℂ (Q ξ)) ∧
        (∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ), 1 < s.re →
          whittakerCoefficient F (productionPins F) ψ
              (fun g' => pcs i s g' + ∑' ξ' : F, pcs i s (adelicWeyl (𝓞 F) F
                  * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) (ξ : F) g
            = (∏' v : {v // v ∉ S},
                (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                  * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * Q ξ s) ∧
        (∀ R : ℝ, ∃ M : {ξ : F // ξ ≠ 0} → ℝ, Summable M ∧
          ∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ), ‖s‖ ≤ R → ‖Q ξ s‖ ≤ M ξ) ∧
        (∀ s : ℂ, 1 < s.re →
          Integrable (fun y => pcs i s (adelicWeyl (𝓞 F) F * unipotentGL2 y * g))
            (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F)) := by
      intro i
      by_cases hne : ∃ (s : ℂ) (g' : AdelicGL2 (𝓞 F) F), pcs i s g' ≠ 0
      · have hsub : S₀ i ⊆ S := Finset.subset_biUnion_of_mem S₀ (Finset.mem_univ i)
        have hsub' : (hdat i hne).choose ⊆ S := by simpa only [S₀, dif_pos hne] using hsub
        obtain ⟨cS, mS, m, A, B, h, kdat, τr, abm, τc, Wr, Wc, a, u, C, hχϖ, hχS, hnψ, hcS, hχc', hmS, hA, hB,
          hoff, hon, habm, hWr, hWc, hC, hind', hfac⟩ := (hdat i hne).choose_spec S hsub'
        obtain ⟨Q, hQ₁, hQ₂, hQ₃⟩ :=
          EgenPiece.exists_entire_partialEulerProduct_mul_eq_whittakerCoefficient_and_summable_majorant F ψ hψ
            ψv nψ hnψfin hψv hψv' hψfin θr hθr θc hθc hψarch (μ * ν⁻¹) S ϖ hϖ hχϖ hχS hnψ cS hcS hχc' mS hmS m A B
            hA hB h hoff hon kdat τr abm τc habm Wr hWr Wc hWc a u C hC (pcs i) hind' g hfac
        refine ⟨Q, hQ₁, hQ₂, hQ₃, ?_⟩
        exact EgenPiece.integrable_weyl_unipotent_mul_of_factorization F ψ hψ ψv nψ hnψfin hψv hψv' hψfin θr hθr
          θc hθc hψarch (μ * ν⁻¹) S ϖ hϖ hχϖ hχS hnψ cS hcS hχc' mS hmS m A B hA hB h hoff hon kdat τr abm τc habm
          Wr hWr Wc hWc a u C hC (pcs i) hind' g hfac
      · push Not at hne
        refine ⟨fun _ _ => 0, fun _ => differentiable_const 0, fun ξ s _ => ?_,
          fun _ => ⟨fun _ => 0, summable_zero, fun _ _ _ => by simp⟩, fun s _ => ?_⟩
        · simp [hne]
        · simp [hne]
    choose Q hQ using hpiece

    have hW : ∀ s : ℂ, 1 < s.re → ∀ ξ : {ξ : F // ξ ≠ 0},
        whittakerCoefficient F (productionPins F) ψ
            (fun g' => φ s g' + ∑' ξ' : F, φ s (adelicWeyl (𝓞 F) F
                * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) (ξ : F) g
          = ∑ i : Fin n, c i s
              * ((∏' v : {v // v ∉ S},
                  (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                    * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * Q i ξ s) := by
      intro s hs ξ
      rw [EgenGlue.whittakerCoefficient_bruhatSeries_eq_finset_sum F ψ hψ.continuous
        (fun x => NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ x) n (fun i => c i s)
        (fun i => pcs i s) (φ s) (fun i => ⟨_, _, hind i s⟩) (fun g' => hsum s g') (ξ : F) g
        (fun i => (hQ i).2.2.2 s hs)]
      exact Finset.sum_congr rfl fun i _ => by rw [(hQ i).2.1 ξ s hs]
    obtain ⟨Nc, hNc, hid⟩ := EgenGlue.exists_differentiable_mul_eq_tsum_of_pieces n c hc
      (fun s => ∏' v : {v // v ∉ S},
        (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
          * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))))
      (fun (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ) => whittakerCoefficient F (productionPins F) ψ
        (fun g' => φ s g' + ∑' ξ' : F, φ s (adelicWeyl (𝓞 F) F
            * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) (ξ : F) g)
      Q (fun i ξ => (hQ i).1 ξ) (fun i R => (hQ i).2.2.1 R) hW
    exact ⟨μ * ν⁻¹, hχc hμc hνc, hχu, hχic, S, ϖ, hϖ, Nc, hNc, hid⟩

end Target

#print axioms solution

end S_AutomorphicForm_exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein
end P2MW
export P2MW.S_AutomorphicForm_exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein (solution)
