-- Prove2me | solution 1 for AutomorphicForm.exists_shapedRaw_bundle_forall_shellSupport_transl_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/5e382033-241c-5f02-a2a0-cdffdc4671dc

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_ConverseData
import Mathlib.Analysis.MellinTransform
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization

import Theorems.Thm_AutomorphicForm_shapedRaw_rawBundle_transl_rat
import Theorems.Thm_AutomorphicForm_exists_unipotent_shellSupport_of_shapedRaw_bundle_transl_rat
import Theorems.Thm_AutomorphicForm_shapedRaw_bundle_sub_translate_unipotent_transl_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_shapedRaw_bundle_forall_shellSupport_transl_rat
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply"
p2m_attr_erase "simp" "LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalConstituent.rightRegular_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk"
p2m_attr_erase "simp" "TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent"

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

namespace SIterateDefs

def INV (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (φ₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (WA₀ : GL (Fin 2) ℝ → ℂ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wf : finiteAdelicGL2Subgroup ℚ → ℂ) : Prop :=
  Continuous φ ∧
        IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ ∧
        (∃ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → AdelicGL2 (𝓞 ℚ) ℚ),
          (∀ i, g i ∈ finiteAdelicGL2Subgroup ℚ) ∧ φ = fun x => ∑ i, c i * φ₀ (x * g i)) ∧
        (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ.comp Subgroup.topEquiv.symm.toMonoidHom z : ℂˣ) : ℂ) * φ g) ∧
        (∀ g, whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 0 g = 0) ∧
        (∀ g, Summable fun a : ℚ => ‖whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ a g‖) ∧
        (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 1 g = WA₀ (ratArchGL2 g) * Wf (finFactor g)) ∧
        Measurable Wf ∧
        (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ), ‖Wf ((n : finiteAdelicGL2Subgroup ℚ) * g)‖ = ‖Wf g‖) ∧
        (∃ U : Subgroup (finiteAdelicGL2Subgroup ℚ), IsOpen (U : Set (finiteAdelicGL2Subgroup ℚ)) ∧
          ∀ (g : finiteAdelicGL2Subgroup ℚ) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U → Wf (g * u) = Wf g) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
          (∀ x : v.adicCompletion ℚ, ‖ψ x‖ = 1) ∧
          (∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) ∧
          (∃ r : v.adicCompletionIntegers ℚ,
            ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
              algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1) ∧
          ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
            Wf (finFactor (placeEmbed ℚ v (unipotent x) * g)) = ψ x * Wf (finFactor g)) ∧
        (∀ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), localAt ℚ p g = 1 →
          (fun h : GL (Fin 2) (p.adicCompletion ℚ) => Wf (finFactor (g * placeEmbed ℚ p h))) ∈
            AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p φ₀) ∧
        (∃ U' : Subgroup (finiteAdelicGL2Subgroup ℚ), IsOpen (U' : Set (finiteAdelicGL2Subgroup ℚ)) ∧
          ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U' → φ (g * (u : AdelicGL2 (𝓞 ℚ) ℚ)) = φ g) ∧
        (∃ n : ℤ, HasArchCharacterAt₀ ℚ (default : InfinitePlace ℚ)
          (archWeightCharAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) n) φ) ∧
        (∀ (a : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          WhittakerCoefficientIntegrable ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ a g)

def OFFS (Θ : HeckeEigensystem ℚ ℂ) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hπall : ∀ v : HeightOneSpectrum (𝓞 ℚ), algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
    (Wf : finiteAdelicGL2Subgroup ℚ → ℂ) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → Wf (finFactor (g * placeEmbed ℚ v x)) = Wf (finFactor g)) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (r : v.adicCompletionIntegers ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          Wf (finFactor (g * placeEmbed ℚ v
            (unipotent (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r)))) = Wf (finFactor g)) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
          ∃ b : Fin (Ideal.absNorm v.asIdeal) → v.adicCompletionIntegers ℚ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
            (∑ i, Wf (finFactor (g * placeEmbed ℚ v
                (repSome (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)
                  (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (b i)))))) +
              Wf (finFactor (g * placeEmbed ℚ v
                (repInf (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
            Θ.a v * Wf (finFactor g)) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          Wf (finFactor (g * placeEmbed ℚ v
            (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
            (Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) * Wf (finFactor g))

def LEVELAT (Θ : HeckeEigensystem ℚ ℂ) (p : HeightOneSpectrum (𝓞 ℚ)) (Wf : finiteAdelicGL2Subgroup ℚ → ℂ) : Prop :=
  ∀ (k : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p Θ.level → Wf (finFactor (g * placeEmbed ℚ p k)) = Wf (finFactor g)

def SHELLAT (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hπall : ∀ v : HeightOneSpectrum (𝓞 ℚ), algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
    (q : HeightOneSpectrum (𝓞 ℚ)) (mq : ℕ) (Wf : finiteAdelicGL2Subgroup ℚ → ℂ) : Prop :=
  ∀ (g : finiteAdelicGL2Subgroup ℚ) (x : q.adicCompletion ℚ) (n : ℤ) (k : GL (Fin 2) (q.adicCompletion ℚ)),
            k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ q (q.asIdeal ^ mq) → n ≠ 0 →
            localAt ℚ q (g : AdelicGL2 (𝓞 ℚ) ℚ) =
              unipotent x * diagZ (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ) (ϖ q)) (hπall q) n * k →
            Wf g = 0

end SIterateDefs

open SIterateDefs in
theorem solution
    (Θ : HeckeEigensystem ℚ ℂ) (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (S₀ S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS₀ : S₀ ⊆ S)
    (hSlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ¬ v.asIdeal ∣ Θ.level)
    (φ₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ Θ.level S₀ Θ φ₀) (hne0 : φ₀ ≠ 0)
    (hloc : (∀ p : HeightOneSpectrum (𝓞 ℚ),
              ((∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                  NumberField.StandardAddChar.psiQ p φ₀,
                W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                  NumberField.StandardAddChar.psiQ p φ₀,
                  W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
                    fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
              (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
                ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
                  ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                    NumberField.StandardAddChar.psiQ p φ₀,
                    (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) →
                      W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
              (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                  NumberField.StandardAddChar.psiQ p φ₀,
                ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
                  ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g))))
    (hrep : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₀ α = φ₀)
    (hwt : ∃ n : ℤ, HasArchCharacterAt₀ ℚ (default : InfinitePlace ℚ)
      (archWeightCharAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) n) φ₀)
    (WA₀ : GL (Fin 2) ℝ → ℂ) (Wf₀ : finiteAdelicGL2Subgroup ℚ → ℂ)
    (hfac₀ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₀ 1 g =
        WA₀ (ratArchGL2 g) * Wf₀ (finFactor g))
    (hWA₀ : ∃ h : GL (Fin 2) ℝ, WA₀ h ≠ 0) (hWf1 : Wf₀ 1 ≠ 0)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ))
    (hπall : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0) :
    ∃ (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wf₁ : finiteAdelicGL2Subgroup ℚ → ℂ) (mS : HeightOneSpectrum (𝓞 ℚ) → ℕ),
      (Continuous φ₁ ∧
      IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ₁ ∧
      (∃ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → AdelicGL2 (𝓞 ℚ) ℚ),
        (∀ i, g i ∈ finiteAdelicGL2Subgroup ℚ) ∧ φ₁ = fun x => ∑ i, c i * φ₀ (x * g i)) ∧
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ₁ (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ.comp Subgroup.topEquiv.symm.toMonoidHom z : ℂˣ) : ℂ) * φ₁ g) ∧
      (∀ g, whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₁ 0 g = 0) ∧
      (∀ g, Summable fun a : ℚ => ‖whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₁ a g‖) ∧
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₁ 1 g = WA₀ (ratArchGL2 g) * Wf₁ (finFactor g)) ∧
      Measurable Wf₁ ∧
      (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ), ‖Wf₁ ((n : finiteAdelicGL2Subgroup ℚ) * g)‖ = ‖Wf₁ g‖) ∧
      (∃ U : Subgroup (finiteAdelicGL2Subgroup ℚ), IsOpen (U : Set (finiteAdelicGL2Subgroup ℚ)) ∧
        ∀ (g : finiteAdelicGL2Subgroup ℚ) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U → Wf₁ (g * u) = Wf₁ g) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
        (∀ x : v.adicCompletion ℚ, ‖ψ x‖ = 1) ∧
        (∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) ∧
        (∃ r : v.adicCompletionIntegers ℚ,
          ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
            algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1) ∧
        ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          Wf₁ (finFactor (placeEmbed ℚ v (unipotent x) * g)) = ψ x * Wf₁ (finFactor g)) ∧
      (∀ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), localAt ℚ p g = 1 →
        (fun h : GL (Fin 2) (p.adicCompletion ℚ) => Wf₁ (finFactor (g * placeEmbed ℚ p h))) ∈
          AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p φ₀) ∧
      (∃ U' : Subgroup (finiteAdelicGL2Subgroup ℚ), IsOpen (U' : Set (finiteAdelicGL2Subgroup ℚ)) ∧
        ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U' → φ₁ (g * (u : AdelicGL2 (𝓞 ℚ) ℚ)) = φ₁ g) ∧
      (∃ n : ℤ, HasArchCharacterAt₀ ℚ (default : InfinitePlace ℚ)
        (archWeightCharAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) n) φ₁) ∧
      (∀ (a : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        WhittakerCoefficientIntegrable ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₁ a g)) ∧
      ((∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → Wf₁ (finFactor (g * placeEmbed ℚ v x)) = Wf₁ (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (r : v.adicCompletionIntegers ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        Wf₁ (finFactor (g * placeEmbed ℚ v
          (unipotent (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r)))) = Wf₁ (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        ∃ b : Fin (Ideal.absNorm v.asIdeal) → v.adicCompletionIntegers ℚ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          (∑ i, Wf₁ (finFactor (g * placeEmbed ℚ v
              (repSome (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (b i)))))) +
            Wf₁ (finFactor (g * placeEmbed ℚ v
              (repInf (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
          Θ.a v * Wf₁ (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        Wf₁ (finFactor (g * placeEmbed ℚ v
          (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
          (Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) * Wf₁ (finFactor g))) ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S → 1 ≤ mS p ∧
        (∀ (g : finiteAdelicGL2Subgroup ℚ) (x : p.adicCompletion ℚ) (n : ℤ) (k : GL (Fin 2) (p.adicCompletion ℚ)),
          k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ mS p) → n ≠ 0 →
          localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) =
            unipotent x * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπall p) n * k →
          Wf₁ g = 0)) ∧
      Wf₁ 1 ≠ 0 := by
  classical
  obtain ⟨⟨hφ₀c, hφ₀cusp, -⟩, -⟩ :=
    AutomorphicForm.shapedRaw_rawBundle_transl_rat Θ ξ S₀ S hS₀ hSlev φ₀ hiso hne0 hloc hrep hwt
      WA₀ Wf₀ hfac₀ hWA₀ hWf1 ϖ hϖ hπall
  have main : ∀ T' : Finset (HeightOneSpectrum (𝓞 ℚ)), T' ⊆ S →
      ∃ (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wf : finiteAdelicGL2Subgroup ℚ → ℂ) (m : HeightOneSpectrum (𝓞 ℚ) → ℕ),
        INV ξ φ₀ WA₀ ϖ φ Wf ∧ OFFS Θ S ϖ hπall Wf ∧
        (∀ q : HeightOneSpectrum (𝓞 ℚ), q ∈ S → q ∉ T' → LEVELAT Θ q Wf) ∧
        (∀ q : HeightOneSpectrum (𝓞 ℚ), q ∈ T' → 1 ≤ m q ∧ SHELLAT ϖ hπall q (m q) Wf) ∧
        Wf 1 ≠ 0 := by
    intro T'
    induction T' using Finset.induction_on with
    | empty =>
      intro _
      obtain ⟨hinv, hoff, hlev, hne⟩ :=
        AutomorphicForm.shapedRaw_rawBundle_transl_rat Θ ξ S₀ S hS₀ hSlev φ₀ hiso hne0 hloc hrep hwt
          WA₀ Wf₀ hfac₀ hWA₀ hWf1 ϖ hϖ hπall
      exact ⟨φ₀, Wf₀, fun _ => 0, hinv, hoff, fun q _ _ => hlev q, fun q hq => absurd hq (Finset.notMem_empty q), hne⟩
    | insert p T₀ hpT₀ ih =>
      intro hsub
      have hp : p ∈ S := hsub (Finset.mem_insert_self p T₀)
      have hT₀ : T₀ ⊆ S := fun q hq => hsub (Finset.mem_insert_of_mem hq)
      obtain ⟨φ, Wf, m, hinv, hoff, hlev, hsh, hne⟩ := ih hT₀
      obtain ⟨x₀, -, hne', m₀, hm₀, hsh'⟩ :=
        AutomorphicForm.exists_unipotent_shellSupport_of_shapedRaw_bundle_transl_rat Θ ξ φ₀ hloc WA₀ hWA₀ ϖ hϖ hπall φ Wf p
          hinv (hlev p hp hpT₀) hne
      obtain ⟨hinv', hoff', hlev', hsh''⟩ :=
        AutomorphicForm.shapedRaw_bundle_sub_translate_unipotent_transl_rat Θ ξ S φ₀ hφ₀c hφ₀cusp hrep WA₀ hWA₀ ϖ hϖ hπall φ Wf p hp x₀
          (S \ T₀) T₀ hpT₀ m hinv hoff
          (fun q hq => hlev q (Finset.mem_sdiff.mp hq).1 (Finset.mem_sdiff.mp hq).2)
          (fun q hq => (hsh q hq).2)
      refine ⟨fun g : AdelicGL2 (𝓞 ℚ) ℚ => φ (g * placeEmbed ℚ p (unipotent x₀)) - φ g,
        fun g : finiteAdelicGL2Subgroup ℚ => Wf (finFactor ((g : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p (unipotent x₀))) - Wf g,
        fun q => if q = p then m₀ else m q, hinv', hoff', ?_, ?_, hne'⟩
      · intro q hqS hqT
        have hqp : q ≠ p := fun h => hqT (h ▸ Finset.mem_insert_self p T₀)
        have hqT₀ : q ∉ T₀ := fun h => hqT (Finset.mem_insert_of_mem h)
        exact hlev' q (Finset.mem_sdiff.mpr ⟨hqS, hqT₀⟩) hqp
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq₀
        · simp only [if_true]
          exact ⟨hm₀, hsh' m₀ le_rfl⟩
        · have hqp : q ≠ p := fun h => hpT₀ (h ▸ hq₀)
          simp only [if_neg hqp]
          exact ⟨(hsh q hq₀).1, hsh'' q hq₀⟩
  obtain ⟨φ₁, Wf₁, mS, hinv, hoff, -, hsh, hne⟩ := main S Finset.Subset.rfl
  exact ⟨φ₁, Wf₁, mS, hinv, hoff, hsh, hne⟩

#print axioms solution

end S_AutomorphicForm_exists_shapedRaw_bundle_forall_shellSupport_transl_rat
end P2MW
export P2MW.S_AutomorphicForm_exists_shapedRaw_bundle_forall_shellSupport_transl_rat (solution)
