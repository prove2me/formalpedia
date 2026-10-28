-- Prove2me | Definitions.Def_OAIQ064A008
-- name    : OAIQ064A008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T00:36:18.176761+00:00
-- url     : https://prove2.me/theorems/a549662d-6f25-49a0-8833-9dd38e847824
-- title:
--   Definitions bundle OAIQ064A008 of the split of OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 162 declarations of OpenAI's Lean: 97 definitions, 1 instance and 64 theorems. The definitions and types are `OAI.TuringRigidity.BoundedSetTheory.LevySigma.normalize`, `OAI.TuringRigidity.BoundedSetTheory.SigmaFormula.allDomainMatrix`, `OAI.TuringRigidity.BoundedSetTheory.SigmaFormula.allMem`, `OAI.TuringRigidity.CategorySearch.success`, `OAI.TuringRigidity.CategorySearch.value`, `OAI.TuringRigidity.ElementaryModel.collapsed`, `OAI.TuringRigidity.ElementaryModel.modelIdeal`, `OAI.TuringRigidity.InternalProjectedGeneric.projected`, `OAI.TuringRigidity.InternalQuotientGeneric.quotient`, `OAI.TuringRigidity.InternalRegularAlgebra.interpret`, `OAI.TuringRigidity.InternalUncountableSentence.countableSentence`, `OAI.TuringRigidity.InternalUncountableSentence.uncountableOrdinalSentence`, `OAI.TuringRigidity.IrrationalDegreeCoverage`, `OAI.TuringRigidity.LocalComputability.advance`, `OAI.TuringRigidity.LocalComputability.candidate`, `OAI.TuringRigidity.LocalComputability.construction`, `OAI.TuringRigidity.LocalComputability.scan`, `OAI.TuringRigidity.LocalComputability.scanStep`, `OAI.TuringRigidity.LocalComputability.stageAction`, `OAI.TuringRigidity.LocalComputability.stageWord`, `OAI.TuringRigidity.LocalInputs.Data.pairProcedure`, `OAI.TuringRigidity.LocalLimits.G₀`, `OAI.TuringRigidity.LocalLimits.G₁`, `OAI.TuringRigidity.LocalStage.Changes`, `OAI.TuringRigidity.LocalStage.advance`, `OAI.TuringRigidity.LocalStage.candidate`, `OAI.TuringRigidity.LocalStage.conditions`, `OAI.TuringRigidity.LocalStage.construction`, `OAI.TuringRigidity.LocalStage.pairProcedure`, `OAI.TuringRigidity.LocalStage.proposal`, `OAI.TuringRigidity.LocalStage.scan`, `OAI.TuringRigidity.LocalStage.stageAction`, `OAI.TuringRigidity.LocalStage.stageWord`, `OAI.TuringRigidity.NumericSyntax.bindNumbers`, `OAI.TuringRigidity.NumericalIdeal.decode`, `OAI.TuringRigidity.OrdinalArithmetic.boundedOmegaNextPairSentence`, `OAI.TuringRigidity.OrdinalArithmetic.doubleSentence`, `OAI.TuringRigidity.OrdinalArithmetic.omegaGraphSentence`, `OAI.TuringRigidity.OrdinalArithmetic.omegaNextPairSentence`, `OAI.TuringRigidity.OrdinalArithmetic.omegaPowerBody` and 57 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DegreeRigidity_CohenForcing_CohenGroundPoset`, `DegreeRigidity_CohenForcing_CohenInternalDecision`, `DegreeRigidity_CohenForcing_ForcingWitnessCollection`, `DegreeRigidity_CohenForcing_InternalCohenConditions`, `DegreeRigidity_CohenForcing_SparseCohenRealName`, `DegreeRigidity_CohenForcing_TaggedProductGeneric`, `DegreeRigidity_Computability_ArithmeticFreeConstruction`, `DegreeRigidity_Computability_CutTranscript`, `DegreeRigidity_Computability_RealProjectionSyntax`, `DegreeRigidity_Constructibility_DecodedConstructionSyntax`, `DegreeRigidity_Constructibility_PersistentLocality`, `DegreeRigidity_Constructibility_SingleRealConstruction`, `DegreeRigidity_Constructibility_UniformFragmentHull`, `DegreeRigidity_Constructibility_UniformSigmaHull`, `DegreeRigidity_Effective_FiniteCodeBound`, `DegreeRigidity_Effective_LocalComputability`, `DegreeRigidity_Effective_LocalInputs`, `DegreeRigidity_Effective_LocalLimits`, `DegreeRigidity_Effective_LocalPair`, `DegreeRigidity_Effective_LocalScan`, `DegreeRigidity_Effective_LocalStage`, `DegreeRigidity_OrdinalCodes_CanonicalOmegaSyntax`, `DegreeRigidity_OrdinalCodes_CanonicalRealsSyntax`, `DegreeRigidity_OrdinalCodes_LargestOrdinalSyntax`, `DegreeRigidity_OrdinalCodes_LimitOmegaGraphSyntax`, `DegreeRigidity_OrdinalCodes_NumericBinding`, `DegreeRigidity_OrdinalCodes_NumericalIdeal`, `DegreeRigidity_OrdinalCodes_OmegaGraphSyntax`, `DegreeRigidity_OrdinalCodes_OmegaPowerSyntax`, `DegreeRigidity_OrdinalCodes_OmegaStageSyntax`, `DegreeRigidity_OrdinalCodes_OrdinalCodeBranch`, `DegreeRigidity_OrdinalCodes_OrdinalCodeOperations`, `DegreeRigidity_OrdinalCodes_OrdinalCut`, `DegreeRigidity_OrdinalCodes_OrdinalDecoderDomains`, `DegreeRigidity_OrdinalCodes_OrdinalEntryBinding`, `DegreeRigidity_OrdinalCodes_OrdinalInputSyntax`, `DegreeRigidity_OrdinalCodes_OrdinalOrderType`, `DegreeRigidity_OrdinalCodes_OrdinalPaddingSyntax`, `DegreeRigidity_OrdinalCodes_OrdinalPairSyntax`, `DegreeRigidity_OrdinalCodes_OrdinalProductSyntax`, `DegreeRigidity_OrdinalCodes_OrdinalSumClosure`, `DegreeRigidity_OrdinalCodes_OrdinalSumSyntax`, `DegreeRigidity_OrdinalCodes_OrdinalVectorSyntax`, `DegreeRigidity_OrdinalCodes_TrimmedOrderDomains`, `DegreeRigidity_OrdinalCodes_TrimmedProductGraph`, `DegreeRigidity_OrdinalCodes_TrimmedSumDomains`, `DegreeRigidity_OrdinalCodes_TrimmedSumGraph`, `DegreeRigidity_Representation_Assembly`, `DegreeRigidity_Representation_CommonExtensionProgram`, `DegreeRigidity_Representation_GlobalJumpRestriction`, `DegreeRigidity_Representation_GroundDegreePresentation`, `DegreeRigidity_Representation_GroundInclusion`, `DegreeRigidity_Representation_OriginalRealDefinitionTransport`, `DegreeRigidity_Representation_OwnRealsConstruction`, `DegreeRigidity_Representation_PairGenericSelection`, `DegreeRigidity_Representation_PrescribedGenericRestriction`, `DegreeRigidity_Representation_SourceTheory`, `DegreeRigidity_SetModels_BindCanonicalArithmetic`, `DegreeRigidity_SetModels_ElementaryCollapse`, `DegreeRigidity_SetModels_ElementaryModelIdeal`, `DegreeRigidity_SetModels_ExtensionSigmaReplacement`, `DegreeRigidity_SetModels_ExtensionWitnessCover`, `DegreeRigidity_SetModels_InternalBooleanDense`, `DegreeRigidity_SetModels_InternalBooleanProjection`, `DegreeRigidity_SetModels_InternalCollapseConditions`, `DegreeRigidity_SetModels_InternalFiniteSubsets`, `DegreeRigidity_SetModels_InternalProjectedGeneric`, `DegreeRigidity_SetModels_InternalQuotientConditions`, `DegreeRigidity_SetModels_InternalQuotientGeneric`, `DegreeRigidity_SetModels_InternalRegularAlgebra`, `DegreeRigidity_SetModels_InternalRegularOperations`, `DegreeRigidity_SetModels_InternalSameNameGeneric`, `DegreeRigidity_SetModels_InternalStructureCollapse`, `DegreeRigidity_SetModels_InternalUncountableSentence`, `DegreeRigidity_SetModels_ModelArithmeticComprehension`, `DegreeRigidity_SetModels_ModelNaturalNumbers`, `DegreeRigidity_SetModels_ModelRealOperations`, `DegreeRigidity_SetModels_MostowskiCollapse`, `DegreeRigidity_SetModels_NameValueCover`, `DegreeRigidity_SetModels_SmallWitnessBound`, `DegreeRigidity_Syntax_BoundedOmegaGraph`, `DegreeRigidity_Syntax_LevySigmaNormalization`, `DegreeRigidity_Syntax_LevySigmaSchemas`, `DegreeRigidity_Syntax_SentenceInlining`, `DegreeRigidity_Syntax_SigmaBoundedUniversal`, `DegreeRigidity_Syntax_SigmaCollection`, `DegreeRigidity_Syntax_SigmaDomainCollection`, `DegreeRigidity_Syntax_SigmaTransitiveWitness`, `DegreeRigidity_Syntax_TermCertificate`, `DegreeRigidity_Syntax_TermEvaluationGraph`.
--
--   **Imports.** It imports the published bundle `Def_DegreeRigidity`; the bundles `OAIQ064A005`, `OAIQ064A006` and `OAIQ064A007` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.TuringRigidity.FullSetForcing.prescribed_one_real_names`, `OAI.TuringRigidity.OrdinalArithmetic.omega_certificates_at_levels`, `OAI.TuringRigidity.OrdinalArithmetic.uniform_omega_certificates_at_levels`, `OAI.TuringRigidity.OriginalRealDefinitionTransport.original_definition_transport`, `OAI.TuringRigidity.PersistentRestrictionCode.restriction`, `OAI.TuringRigidity.PrescribedFirstUncountable.prescribed_covering_model_with_omega_one`, `OAI.TuringRigidity.RealGeneratedModel.hull_properties`, `OAI.TuringRigidity.RealGeneratedModel.projected_extension_eq_hull`, `OAI.TuringRigidity.RelativeConstructible.Construction.cofinal_one_real_definition`, `OAI.TuringRigidity.RelativeConstructible.Construction.inlined_at_level`, `OAI.TuringRigidity.RelativeConstructible.Construction.largest_domain_definition`, `OAI.TuringRigidity.RelativeConstructible.ground_idealSet_mem_relativeModel`, `OAI.TuringRigidity.RelativeConstructible.persistent_modelIdeal_graph_mem_relativeModel`, `OAI.TuringRigidity.RelativeConstructible.prescribed_real_hull_extension`, `OAI.TuringRigidity.RelativeConstructible.prescribed_unrestricted_ground_program`, `OAI.TuringRigidity.RelativeConstructible.real_hull_generic_column_realizes` and `OAI.TuringRigidity.RelativeConstructible.real_hull_shuffled_column_realizes`; the proofs of `OAI.TuringRigidity.ArithmeticPersistence.persistent_iff`, `OAI.TuringRigidity.ArithmeticTree.native_internal_matrix`, `OAI.TuringRigidity.ArithmeticTree.setGenericallyPersistent_iff`, `OAI.TuringRigidity.ArithmeticTree.sourceT_piOneOne_matrix`, `OAI.TuringRigidity.BoundedForcing.projected_arithmetic_output_cone`, `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.real_collapse_reconstructs`, `OAI.TuringRigidity.CohenAbsorptionGeneric.product_generic_absorption`, `OAI.TuringRigidity.CohenDisjointPrefixPair.exists_iterated_pair`, `OAI.TuringRigidity.CohenManyAbsorption.same_generics_absorption`, `OAI.TuringRigidity.CohenNiceNameConstruction.internal_nice_name`, `OAI.TuringRigidity.CohenProjectedNameLift.lift_projected_real_name`, `OAI.TuringRigidity.CohenRemainderTransport.transport_to_remainder`, `OAI.TuringRigidity.FullSetForcing.prescribed_one_real_names`, `OAI.TuringRigidity.GroundIteratedTriple.generic_triple_of_arithmetic`, `OAI.TuringRigidity.GroundPrefixOverwrite.overwrite_generic`, `OAI.TuringRigidity.InternalBooleanIntermediate.internal_boolean_intermediate`, `OAI.TuringRigidity.InternalCohen.groundGeneric_table_simulation`, `OAI.TuringRigidity.InternalCohen.prefix_extension_eq_hull`, `OAI.TuringRigidity.IteratedGenericCommonIdeal.ideal_of_iterated_generics`, `OAI.TuringRigidity.LocalCoding.selected_antichain`, `OAI.TuringRigidity.ManuscriptMain.rigidity`, `OAI.TuringRigidity.OrdinalArithmetic.internal_explicit_omega_threshold`, `OAI.TuringRigidity.OrdinalArithmetic.omega_certificates_at_levels`, `OAI.TuringRigidity.OrdinalArithmetic.relative_omega_power_internal`, `OAI.TuringRigidity.OrdinalArithmetic.uniform_omega_certificates_at_levels`, `OAI.TuringRigidity.OrdinalCoding.cofinal_padded_code_certificates`, `OAI.TuringRigidity.OrdinalCoding.padded_certificates_of_lower_closure`, `OAI.TuringRigidity.OrdinalCoding.vectorCode_certificates_at_levels`, `OAI.TuringRigidity.OriginalRealCohenFactorization.real_factorization`, `OAI.TuringRigidity.OriginalRealDefinitionTransport.original_definition_transport`, `OAI.TuringRigidity.OriginalRealFullIteration.original_name_full_iteration`, `OAI.TuringRigidity.OriginalRealQuotientModel.original_name_quotient`, `OAI.TuringRigidity.PersistentRestrictionCode.restriction`, `OAI.TuringRigidity.PrescribedFirstUncountable.prescribed_covering_model_with_omega_one`, `OAI.TuringRigidity.ProjectedArithmeticOutputName.representative_in_model`, `OAI.TuringRigidity.RealGeneratedModel.hull_properties`, `OAI.TuringRigidity.RealGeneratedModel.projected_extension_eq_hull`, `OAI.TuringRigidity.RealHullGenericTriple.exists_generic_prefix_triple`, `OAI.TuringRigidity.RealHullGenericTriple.exists_prefix_real`, `OAI.TuringRigidity.RealHullIteration.exists_iterated_pair`, `OAI.TuringRigidity.RealHullIteration.exists_iterated_prefix_pair`, `OAI.TuringRigidity.RelativeConstructible.Construction.cofinal_one_real_definition`, `OAI.TuringRigidity.RelativeConstructible.Construction.inlined_at_level`, `OAI.TuringRigidity.RelativeConstructible.Construction.largest_domain_definition`, `OAI.TuringRigidity.RelativeConstructible.definablePower_mem`, `OAI.TuringRigidity.RelativeConstructible.global_arithmetic_generic_program`, `OAI.TuringRigidity.RelativeConstructible.ground_idealSet_mem_relativeModel`, `OAI.TuringRigidity.RelativeConstructible.ground_relativeModel_ordinal_iff`, `OAI.TuringRigidity.RelativeConstructible.ground_relative_context`, `OAI.TuringRigidity.RelativeConstructible.hierarchyGraph_sigmaDefinable`, `OAI.TuringRigidity.RelativeConstructible.hierarchy_checked_at_levels`, `OAI.TuringRigidity.RelativeConstructible.internal_defSystem`, `OAI.TuringRigidity.RelativeConstructible.persistent_modelIdeal_graph_mem_relativeModel`, `OAI.TuringRigidity.RelativeConstructible.prescribed_real_hull_extension`, `OAI.TuringRigidity.RelativeConstructible.prescribed_unrestricted_ground_program`, `OAI.TuringRigidity.RelativeConstructible.real_hull_generic_column_realizes`, `OAI.TuringRigidity.RelativeConstructible.real_hull_prescribed_transfer`, `OAI.TuringRigidity.RelativeConstructible.real_hull_shuffled_column_realizes`, `OAI.TuringRigidity.RelativeConstructible.seed_bound_stage_at_levels`, `OAI.TuringRigidity.RelativeConstructible.stageCertificate_uniformSigma`, `OAI.TuringRigidity.RelativeConstructible.uniform_cohen_definition_extension`, `OAI.TuringRigidity.RelativeConstructible.uniform_hierarchy_certificate_collection`, `OAI.TuringRigidity.RelativeConstructible.uniform_ordinal_definition_symmetric`, `OAI.TuringRigidity.SetModelCountability.persistent_countable_extensions`, `OAI.TuringRigidity.SetModelPersistence.persistent_decoding`, `OAI.TuringRigidity.TwoRealHull.joined_factorization` and `OAI.TuringRigidity.main_of_representation`.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A005
import Definitions.Def_OAIQ064A006
import Definitions.Def_OAIQ064A007

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_Assembly
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Topology
namespace TuringRigidity

def IrrationalDegreeCoverage : Prop := ∀ a : Degree, a ≠ ⊥ →
  ∃ t : ℝ, Irrational t ∧ 0 < t ∧ t < 1 ∧ realDegree t = a

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_PairGenericSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.PairGenericSelection
open FiniteShuffle ShuffleRequirements GenericTopology GenericCoding Set

def PairRequirements (D : ℕ → List Bool → Prop) (n : ℕ) : List Bool → Prop :=
  ColumnRequirement (Requirements D (n/2)) (decide (n%2 = 1))

end TuringRigidity.PairGenericSelection

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_CutTranscript
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set
namespace TuringRigidity

namespace CategorySearch

noncomputable def value (A : Oracle) (p : ℝ × ℝ) (k : ℕ) : ℕ := if pairOracle A p k then 1 else 0

def success (A Y : Oracle) (c : OracleCode) : Set (ℝ × ℝ) :=
  {p | OracleCode.eval (oracleFunction (pairOracle A p)) c = oracleFunction Y}

end CategorySearch
end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GroundInclusion
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open RecursiveNames BoundedSetTheory CountableForcing
universe u

theorem extension_infinity (M p : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hR : SigmaReplacement M)
    (hI : Infinity M) (hp : p ∈ M) (G : Set (Conditions p)) (hG : ⊤ ∈ G) :
    Infinity (genericExtensionSet M p G) :=
  infinity_of_omega _ (genericExtensionSet_transitive M p hM G)
    (ground_inclusion_set M p hM hP hU hPow hS hR hI hp G hG (omega_mem M hM hS hI))

end TuringRigidity.TransitiveNameModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_MostowskiCollapse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory
universe u

theorem value_injective {d r : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (he : Extensional d r) (x : ZFSet.{u}) (hx : x ∈ d) (y : ZFSet.{u}) (hy : y ∈ d)
    (hxy : value d r wf x = value d r wf y) : x = y := by
  induction x using wf.induction generalizing y with
  | h x ih =>
    apply he x hx y hy
    intro z hz
    constructor
    · intro hzx
      have hm : value d r wf z ∈ value d r wf y := hxy ▸
        (mem_value d r wf x _).mpr ⟨z,hz,hzx,rfl⟩
      obtain ⟨w,hw,hwy,hzw⟩ := (mem_value d r wf y _).mp hm
      have hzw' := ih z ⟨hz,hzx⟩ hz w hw hzw
      exact hzw' ▸ hwy
    · intro hzy
      have hm : value d r wf z ∈ value d r wf x := hxy.symm ▸
        (mem_value d r wf y _).mpr ⟨z,hz,hzy,rfl⟩
      obtain ⟨w,hw,hwx,hzw⟩ := (mem_value d r wf x _).mp hm
      have hwz := ih w ⟨hw,hwx⟩ hw z hz hzw.symm
      exact hwz ▸ hwx

theorem value_mem_iff {d r : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (he : Extensional d r) {x y : ZFSet.{u}} (hx : x ∈ d) :
    value d r wf x ∈ value d r wf y ↔ ZFSet.pair x y ∈ r := by
  rw [mem_value]
  constructor
  · rintro ⟨z,hz,hzy,hxz⟩
    have hxz := value_injective wf he x hx z hz hxz
    exact hxz ▸ hzy
  · intro hxy
    exact ⟨x,hx,hxy,rfl⟩

theorem Graph.range_iff {d r b f : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (hf : Graph d r d b f) (v : ZFSet.{u}) :
    v ∈ graphRange d f ↔ ∃ x ∈ d, v = value d r wf x := by
  rw [mem_graphRange]
  constructor
  · rintro ⟨x,hx,hxv⟩
    obtain ⟨y,hy,heq⟩ := (hf.mem_iff wf _).mp hxv
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
    exact ⟨x,hx,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x,hx,(hf.mem_iff wf _).mpr ⟨x,hx,rfl⟩⟩

theorem Graph.range_transitive {d r b f : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (hf : Graph d r d b f) : Transitive (graphRange d f) := by
  intro v hv w hw
  obtain ⟨x,_,rfl⟩ := (hf.range_iff wf v).mp hv
  obtain ⟨y,hy,_,rfl⟩ := (mem_value d r wf x w).mp hw
  exact (hf.range_iff wf _).mpr ⟨y,hy,rfl⟩

theorem internal_mostowski (M d r : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hd : d ∈ M) (hr : r ∈ M) (wf : WellFounded (Rel d r)) (he : Extensional d r) :
    ∃ b ∈ M, ∃ f ∈ M,
      Presents d f (value d r wf) ∧ Transitive b ∧
      (∀ v, v ∈ b ↔ ∃ x ∈ d, v = value d r wf x) ∧
      (∀ x ∈ d, ∀ y ∈ d, value d r wf x = value d r wf y → x = y) ∧
      (∀ x ∈ d, ∀ y ∈ d, value d r wf x ∈ value d r wf y ↔ ZFSet.pair x y ∈ r) := by
  obtain ⟨f,hf,hfg⟩ := internal_graph M d r hM hP hU hPow hS hR hd hr wf
  exact ⟨graphRange d f,graphRange_mem M hM hU hS hd hf,f,hf,
    hfg.mem_iff wf,hfg.range_transitive wf,hfg.range_iff wf,
    value_injective wf he,fun _ hx _ _ => value_mem_iff wf he hx⟩

end TuringRigidity.RelationCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalStructureCollapse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory
universe u

theorem structureMap_fixed {d t : ZFSet.{u}} (ht : Transitive t) (htd : t ⊆ d)
    (x : ZFSet.{u}) (hx : x ∈ t) : structureMap d x = x := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    apply ZFSet.ext
    intro z
    rw [structureMap,mem_value]
    constructor
    · rintro ⟨y,_,hyx,hz⟩
      have hyx' := ((membershipRelation_pair d y x).mp hyx).2.2
      have hyv := ih y hyx' (ht x hx y hyx')
      change structureMap d y = y at hyv
      change z = structureMap d y at hz
      rw [hyv] at hz
      exact hz ▸ hyx'
    · intro hz
      have hzt := ht x hx z hz
      refine ⟨z,htd hzt,(membershipRelation_pair d z x).mpr ⟨htd hzt,htd hx,hz⟩,?_⟩
      exact (ih z hz hzt).symm

theorem internal_structure_collapse (M d : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hd : d ∈ M) (he : StructureExtensional d) :
    ∃ b ∈ M, ∃ f ∈ M, Presents d f (structureMap d) ∧ Transitive b ∧
      (∀ y, y ∈ b ↔ ∃ x ∈ d, y = structureMap d x) ∧
      (∀ φ : SigmaFormula, ∀ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ d) →
        (φ.Realize d e ↔ φ.Realize b (fun i => structureMap d (e i)))) := by
  obtain ⟨b,hb,f,hf,hfg,hbt,hbdef,hi,hm⟩ := internal_mostowski M d (membershipRelation d)
    hM hP hU hPow hS hR hd (membershipRelation_mem M hM hP hU hPow hS hd)
    (membershipRelation_wellFounded d) (membershipRelation_extensional he)
  refine ⟨b,hb,f,hf,hfg,hbt,hbdef,?_⟩
  intro φ e henv
  apply φ.realize_isomorphism d b (structureMap d)
  · intro x hx
    exact (hbdef _).mpr ⟨x,hx,rfl⟩
  · intro y hy
    obtain ⟨x,hx,hyx⟩ := (hbdef y).mp hy
    exact ⟨x,hx,hyx.symm⟩
  · exact hi
  · intro x hx y hy
    exact (hm x hx y hy).trans
      ((membershipRelation_pair d x y).trans (and_iff_right hx |>.trans (and_iff_right hy)))
  · exact henv

end TuringRigidity.RelationCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteCodeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse
universe u
namespace FiniteTuple

theorem FiniteCode.finite_transitive_extension (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (h0 : (∅ : ZFSet.{u}) ∈ M)
    {t x : ZFSet.{u}} (ht : t ∈ M) (htt : Transitive t) (hx : FiniteCode t x) :
    ∃ xs : List ZFSet.{u}, (∀ y ∈ xs, y ∈ M) ∧ x ∈ t ∪ elements xs ∧
      Transitive (t ∪ elements xs) := by
  induction hx with
  | atom x hx =>
    refine ⟨[],by simp,?_,?_⟩
    · exact ZFSet.mem_union.mpr (Or.inl hx)
    · have heq : t ∪ elements [] = t := by
        apply ZFSet.ext; intro z; simp [ZFSet.mem_union,elements]
      exact heq.symm ▸ htt
  | empty =>
    refine ⟨[∅],?_,?_,?_⟩
    · intro y hy; obtain rfl := List.mem_singleton.mp hy; exact h0
    · exact ZFSet.mem_union.mpr (Or.inr ((mem_elements _ _).mpr List.mem_cons_self))
    · have heq : t ∪ elements [∅] = t ∪ ({∅} : ZFSet.{u}) := by
        apply ZFSet.ext; intro z; simp [ZFSet.mem_union,elements]
      rw [heq]
      exact transitive_adjoin htt (by simp)
  | @pair x y hx hy ihx ihy =>
    obtain ⟨xs,hxs,hxxs,htxs⟩ := ihx
    obtain ⟨ys,hys,hyys,htys⟩ := ihy
    let zs := xs ++ ys
    have hb : t ∪ elements zs = (t ∪ elements xs) ∪ (t ∪ elements ys) := by
      apply ZFSet.ext; intro z
      simp only [ZFSet.mem_union,mem_elements,List.mem_append,zs]
      tauto
    have hbt : Transitive (t ∪ elements zs) := hb.symm ▸ transitive_union htxs htys
    have hxb : x ∈ t ∪ elements zs := hb.symm ▸ ZFSet.mem_union.mpr (Or.inl hxxs)
    have hyb : y ∈ t ∪ elements zs := hb.symm ▸ ZFSet.mem_union.mpr (Or.inr hyys)
    have hp : ({x,y} : ZFSet.{u}) ⊆ t ∪ elements zs := by
      intro z hz; rcases ZFSet.mem_pair.mp hz with rfl|rfl
      · exact hxb
      · exact hyb
    refine ⟨({x,y} : ZFSet.{u}) :: zs,?_,?_,?_⟩
    · intro z hz; rcases List.mem_cons.mp hz with rfl|hz
      · exact pair_mem M hM hP (hx.mem_model M hM hP h0 ht) (hy.mem_model M hM hP h0 ht)
      · rcases List.mem_append.mp hz with hz|hz
        · exact hxs z hz
        · exact hys z hz
    · exact ZFSet.mem_union.mpr (Or.inr ((mem_elements _ _).mpr List.mem_cons_self))
    · have heq : t ∪ elements (({x,y} : ZFSet.{u})::zs) =
          (t ∪ elements zs) ∪ ({({x,y} : ZFSet.{u})} : ZFSet.{u}) := by
        apply ZFSet.ext; intro z
        simp only [ZFSet.mem_union,mem_elements,List.mem_cons,ZFSet.mem_singleton]
        tauto
      rw [heq]
      exact transitive_adjoin hbt hp

theorem internal_finite_code_bound (M t : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M)
    (ht : t ∈ M) (htt : Transitive t) :
    ∃ K ∈ M, ∀ x, FiniteCode t x → x ∈ K := by
  have hω := omega_mem M hM hS.bounded hI
  have h0 : (∅ : ZFSet.{u}) ∈ M := hM _ hω _ ZFSet.omega_zero
  have hk := indexSpace_mem M hM hP hU hPow hS.bounded hω ht
  obtain ⟨K,hK,hbound⟩ := internal_small_transitive_bound M (indexSpace t) hM hP hU hPow hS hR hk
  refine ⟨K,hK,?_⟩
  intro x hx
  obtain ⟨xs,hxs,hxD,hDT⟩ := hx.finite_transitive_extension M hM hP h0 ht htt
  have hD := binary_union_mem M hM hP hU ht (elements_mem M hM hP hU h0 xs hxs)
  obtain ⟨f,hf,hfg⟩ := internal_finite_extension_injection M hM hP hU hPow hS.bounded hR hω ht xs hxs
  exact hbound _ hD hDT f hf (finiteIndex t xs) hfg
    (fun y _ => finiteIndex_mem t xs y) (finiteIndex_injective t xs) hxD

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_TermCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace FiniteTerm

theorem internal_certificate (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    {A B L O K D : ZFSet.{u}} (hK : K ∈ M) (hD : D ∈ M)
    (hcode : ∀ c v, Eval A B L O D c v → c ∈ K)
    {c v : ZFSet.{u}} (h : Eval A B L O D c v) :
    ∃ f ∈ M, Certificate A B L O K D f ∧ ZFSet.pair c v ∈ f := by
  induction h with
  | @leaf a x ha hx hax =>
    have ev : Eval A B L O D (tag 0 a) x := .leaf ha hx hax
    have hc := hcode _ _ ev
    let f := ({ZFSet.pair (tag 0 a) x} : ZFSet.{u})
    have hf : f ∈ M := singleton_mem M hM hP
      (orderedPair_mem M hM hP (hM K hK _ hc) (hM D hD _ hx))
    refine ⟨f,hf,?_,ZFSet.mem_singleton.mpr rfl⟩
    intro z hz; obtain rfl := ZFSet.mem_singleton.mp hz
    exact ⟨_,hc,x,hx,rfl,Or.inl ⟨a,ha,rfl,hax⟩⟩
  | @app o a x y ho ev hy hoy ih =>
    obtain ⟨f,hf,hfc,hax⟩ := ih
    have hc := hcode _ _ (Eval.app ho ev hy hoy)
    have hroot : ZFSet.pair (tag 1 (ZFSet.pair o a)) y ∈ M :=
      orderedPair_mem M hM hP (hM K hK _ hc) (hM D hD _ hy)
    refine ⟨f ∪ {ZFSet.pair (tag 1 (ZFSet.pair o a)) y},
      binary_union_mem M hM hP hU hf (singleton_mem M hM hP hroot),?_,
      ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_singleton.mpr rfl))⟩
    apply hfc.adjoin hc hy
    exact Or.inr (Or.inl ⟨o,ho,a,hcode _ _ ev,x,ev.value_mem,rfl,
      ZFSet.mem_union.mpr (Or.inl hax),hoy⟩)
  | @pair a b x y eva evb hxy iha ihb =>
    obtain ⟨f,hf,hfc,hax⟩ := iha
    obtain ⟨g,hg,hgc,hby⟩ := ihb
    have hc := hcode _ _ (Eval.pair eva evb hxy)
    have hroot : ZFSet.pair (tag 2 (ZFSet.pair a b)) (ZFSet.pair x y) ∈ M :=
      orderedPair_mem M hM hP (hM K hK _ hc) (hM D hD _ hxy)
    refine ⟨(f ∪ g) ∪ {ZFSet.pair (tag 2 (ZFSet.pair a b)) (ZFSet.pair x y)},
      binary_union_mem M hM hP hU (binary_union_mem M hM hP hU hf hg)
        (singleton_mem M hM hP hroot),?_,
      ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_singleton.mpr rfl))⟩
    apply (hfc.union hgc).adjoin hc hxy
    exact Or.inr (Or.inr ⟨a,hcode _ _ eva,b,hcode _ _ evb,x,eva.value_mem,y,evb.value_mem,rfl,
      ZFSet.mem_union.mpr (Or.inl (ZFSet.mem_union.mpr (Or.inl hax))),
      ZFSet.mem_union.mpr (Or.inl (ZFSet.mem_union.mpr (Or.inr hby))),rfl⟩)

end FiniteTerm
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_TermEvaluationGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace FiniteTerm

theorem internal_evaluation_graph (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hω : ZFSet.omega.{u} ∈ M) {A B L O K D : ZFSet.{u}}
    (hA : A ∈ M) (hB : B ∈ M) (hL : L ∈ M) (hO : O ∈ M) (hK : K ∈ M) (hD : D ∈ M)
    (hcode : ∀ c v, Eval A B L O D c v → c ∈ K) :
    ∃ E ∈ M, E ⊆ ZFSet.prod K D ∧
      ∀ c v, ZFSet.pair c v ∈ E ↔ Eval A B L O D c v := by
  have hprod := product_mem M hM hP hU hPow hS hK hD
  obtain ⟨q,hq,hqdef⟩ := internal_power M hM hPow hprod
  have hn (n : ℕ) : natSet.{u} n ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)
  let e := cons q (cons A (cons B (cons L (cons O (cons K (cons D
      (cons (natSet 0) (cons (natSet 1) (fun _ => natSet 2)))))))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|i; exact hq
    rcases i with _|i; exact hA
    rcases i with _|i; exact hB
    rcases i with _|i; exact hL
    rcases i with _|i; exact hO
    rcases i with _|i; exact hK
    rcases i with _|i; exact hD
    rcases i with _|i; exact hn 0
    rcases i with _|i; exact hn 1
    exact hn 2
  let E := ZFSet.sep (fun z => graphFormula.Eval (cons z e)) (ZFSet.prod K D)
  have hE : E ∈ M := sep_mem M hM hS graphFormula e he hprod
  refine ⟨E,hE,fun _ hz => (ZFSet.mem_sep.mp hz).1,?_⟩
  intro c v
  change ZFSet.pair c v ∈ ZFSet.sep _ _ ↔ _
  rw [ZFSet.mem_sep,eval_graphFormula]
  constructor
  · rintro ⟨_,c',_,v',_,hp,f,_,hfc,hcv⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
    exact hfc.sound c v hcv
  · intro hv
    obtain ⟨f,hf,hfc,hcv⟩ := internal_certificate M hM hP hU hK hD hcode hv
    have hfq := (hqdef f).mpr ⟨hf,hfc.subset⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨c,hcode c v hv,v,hv.value_mem,rfl⟩,
      c,hcode c v hv,v,hv.value_mem,rfl,f,hfq,hfc,hcv⟩

theorem uniform_internal_evaluation_graph (M t : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M)
    (ht : t ∈ M) (htt : Transitive t) (hnt : ∀ n, natSet.{u} n ∈ t) :
    ∃ K ∈ M, ∀ A ∈ M, A ⊆ t → ∀ B ∈ M, B ⊆ t →
      ∀ L ∈ M, ∀ O ∈ M, ∀ D ∈ M, ∃ E ∈ M, E ⊆ ZFSet.prod K D ∧
        ∀ c v, ZFSet.pair c v ∈ E ↔ Eval A B L O D c v := by
  obtain ⟨K,hK,hbound⟩ := FiniteTuple.internal_finite_code_bound M t hM hP hU hPow hS hR hI ht htt
  refine ⟨K,hK,?_⟩
  intro A hA hAt B hB hBt L hL O hO D hD
  exact internal_evaluation_graph M hM hP hU hPow hS.bounded (omega_mem M hM hS.bounded hI)
    hA hB hL hO hK hD (fun c v hv => hbound c (hv.code_finite hAt hBt hnt))

end FiniteTerm
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformFragmentHull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse
universe u
namespace FiniteTuple

theorem uniform_internal_fragment_hull (M t : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M)
    (ht : t ∈ M) (h0t : (∅ : ZFSet.{u}) ∈ t) :
    ∃ K ∈ M, ∀ xs : List ZFSet.{u}, (∀ x ∈ xs, x ∈ M) →
      ∀ d ∈ M, Transitive d → (t ∪ elements xs) ⊆ d → ∀ φ : Formula,
        ∃ h ∈ M, (t ∪ elements xs) ⊆ h ∧ h ⊆ d ∧ StructureExtensional h ∧
          (∀ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ h) → (φ.Realize h e ↔ φ.Realize d e)) ∧
          ∃ f ∈ M, ∃ j : ZFSet.{u} → ZFSet.{u}, Presents h f j ∧
            (∀ x ∈ h, j x ∈ K) ∧ (∀ x ∈ h, ∀ y ∈ h, j x = j y → x = y) := by
  have hω := omega_mem M hM hS.bounded hI
  have hA := indexSpace_mem M hM hP hU hPow hS.bounded hω ht
  obtain ⟨T,hT,hTT,hpair⟩ := internal_transitive_container M hM hP hU hS.bounded hR hI
    (pair_mem M hM hP hA hω)
  have hAT : indexSpace t ⊆ T := fun x hx => hTT _
    (hTT _ hpair _ (ZFSet.mem_pair.mpr (Or.inl rfl))) x hx
  have hωT : ZFSet.omega.{u} ⊆ T := fun x hx => hTT _
    (hTT _ hpair _ (ZFSet.mem_pair.mpr (Or.inr rfl))) x hx
  have hnT : ∀ n, natSet.{u} n ∈ T := fun n => hωT ((mem_omega _).mpr ⟨n,rfl⟩)
  obtain ⟨K,hK,hgraphs⟩ := FiniteTerm.uniform_internal_evaluation_graph M T hM hP hU hPow hS hR hI hT hTT hnT
  refine ⟨K,hK,?_⟩
  intro xs hxs d hd hdt hsd φ
  let n := max 2 φ.width
  have hspace := space_mem M hM hP hU hPow hS.bounded hd n
  obtain ⟨V,hV,hVT,hpairV⟩ := internal_transitive_container M hM hP hU hS.bounded hR hI
    (pair_mem M hM hP hd hspace)
  have hdV : d ⊆ V := fun x hx => hVT _
    (hVT _ hpairV _ (ZFSet.mem_pair.mpr (Or.inl rfl))) x hx
  have hspaceV : space d n ⊆ V := fun x hx => hVT _
    (hVT _ hpairV _ (ZFSet.mem_pair.mpr (Or.inr rfl))) x hx
  obtain ⟨L,hL,hLf,hLc⟩ := FiniteTerm.internal_leaf_graph M hM hP hU hPow hS.bounded hR hω ht xs hxs
  obtain ⟨O,hO,hOf,_,hOps⟩ := FiniteTerm.internal_skolem_operations M hM hP hU hPow hS.bounded hR hI hAC
    hd n (differenceBody :: fragment n φ) 0
  obtain ⟨E,hE,hEsub,hEgraph⟩ := hgraphs (indexSpace t) hA hAT ZFSet.omega hω hωT L hL O hO V hV
  let h := FiniteTerm.generatedRange d K E
  have hh : h ∈ M := FiniteTerm.generatedRange_mem M hM hS.bounded hd hK hE
  have hevalSeed (x : ZFSet.{u}) (hx : x ∈ t ∪ elements xs) :
      ∃ c, FiniteTerm.Eval (indexSpace t) ZFSet.omega L O V c x := by
    obtain ⟨a,ha,hax⟩ := hLc x hx
    exact ⟨_,FiniteTerm.Eval.leaf ha (hdV (hsd hx)) hax⟩
  have hsh : t ∪ elements xs ⊆ h := fun x hx =>
    (FiniteTerm.mem_generatedRange hEgraph hEsub x).mpr ⟨hsd hx,hevalSeed x hx⟩
  have hhd : h ⊆ d := fun x hx => ((FiniteTerm.mem_generatedRange hEgraph hEsub x).mp hx).1
  have hzero := hevalSeed ∅ (ZFSet.mem_union.mpr (Or.inl h0t))
  have hclosed (ψ : Formula) (hψ : ψ ∈ differenceBody :: fragment n φ) :
      ∃ g, SkolemGraph d n ψ (fun _ => d) g ∧ Closed n g h := by
    obtain ⟨i,g,_,hgs,hgo⟩ := hOps ψ hψ
    exact ⟨g,hgs,FiniteTerm.generatedRange_closed n hVT hdV hspaceV hEgraph hEsub hzero
      (fun z hz => (ZFSet.mem_sep.mp (hgs.1 hz)).1) i hgo⟩
  have hext : StructureExtensional h := by
    obtain ⟨g,hgs,hcl⟩ := hclosed differenceBody List.mem_cons_self
    exact closed_extensional d h g n (Nat.le_max_left _ _) hdt hhd hcl ⟨g,fun _ hx => hx,hgs⟩
  have htransfer : ∀ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ h) → (φ.Realize h e ↔ φ.Realize d e) := by
    intro e he
    exact realize_of_witnesses d h hhd φ
      (witnesses_of_closed_graphs d h n φ (Nat.le_max_right _ _) hhd
        (fun ψ hψ => hclosed ψ (List.mem_cons_of_mem _ hψ))) e he
  obtain ⟨f,hf,j,hfj,hj,hi⟩ := FiniteTerm.internal_evaluated_injection M hM hP hU hPow hS.bounded hAC
    hh hK hE hLf hOf hEsub hEgraph
    (fun x hx => ((FiniteTerm.mem_generatedRange hEgraph hEsub x).mp hx).2)
  exact ⟨h,hh,hsh,hhd,hext,htransfer,f,hf,j,hfj,hj,hi⟩

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SmallWitnessBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory
universe u

theorem codedRelation_structureMap {k d f : ZFSet.{u}} {j : ZFSet.{u} → ZFSet.{u}}
    (hf : Presents d f j) (hj : ∀ x ∈ d, j x ∈ k)
    (hi : ∀ x ∈ d, ∀ y ∈ d, j x = j y → x = y)
    (wf : WellFounded (Rel k (codedRelation k d f)))
    (x : ZFSet.{u}) (hx : x ∈ d) :
    value k (codedRelation k d f) wf (j x) = structureMap d x := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    apply ZFSet.ext
    intro z
    rw [structureMap,mem_value,mem_value]
    constructor
    · rintro ⟨u,_,hux,hz⟩
      obtain ⟨y,hy,w,hw,hyw,rfl,hwx⟩ := (codedRelation_pair hf hj u (j x)).mp hux
      have hwx' : x = w := hi x hx w hw hwx
      subst w
      rw [ih y hyw hy] at hz
      exact ⟨y,hy,(membershipRelation_pair d y x).mpr ⟨hy,hx,hyw⟩,hz⟩
    · rintro ⟨y,hy,hyx,hz⟩
      have hyx' := ((membershipRelation_pair d y x).mp hyx).2.2
      exact ⟨j y,hj y hy,(codedRelation_pair hf hj _ _).mpr
        ⟨y,hy,x,hx,hyx',rfl,rfl⟩,hz.trans (ih y hyx' hy).symm⟩

theorem internal_structure_value_bound (M k : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hk : k ∈ M) :
    ∃ W ∈ M, ∀ d ∈ M, ∀ f ∈ M, ∀ j : ZFSet.{u} → ZFSet.{u},
      Presents d f j → (∀ x ∈ d, j x ∈ k) →
      (∀ x ∈ d, ∀ y ∈ d, j x = j y → x = y) →
      ∀ x ∈ d, structureMap d x ∈ W := by
  obtain ⟨W,hW,hbound⟩ := internal_value_bound M k hM hP hU hPow hS hR hk
  refine ⟨W,hW,?_⟩
  intro d hd f hf j hfj hj hi x hx
  have hr := codedRelation_mem M hM hP hU hPow hS.bounded hk hd hf
  have wf := codedRelation_wellFounded hfj hj hi
  have hv := hbound _ hr (codedRelation_on k d f) wf (j x) (hj x hx)
  rwa [codedRelation_structureMap hfj hj hi wf x hx] at hv

theorem internal_small_witness_bound (M k : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hk : k ∈ M) :
    ∃ W ∈ M, ∀ d ∈ M, StructureExtensional d →
      ∀ f ∈ M, ∀ j : ZFSet.{u} → ZFSet.{u}, Presents d f j →
      (∀ x ∈ d, j x ∈ k) → (∀ x ∈ d, ∀ y ∈ d, j x = j y → x = y) →
      ∀ t : ZFSet.{u}, Transitive t → t ⊆ d → ∀ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ t) →
      ∀ φ : SigmaFormula, ∀ x ∈ d, φ.Realize d (cons x e) →
        ∃ y ∈ W, φ.Realize M (cons y e) := by
  obtain ⟨W,hW,hbound⟩ := internal_structure_value_bound M k hM hP hU hPow hS hR hk
  refine ⟨W,hW,?_⟩
  intro d hd hext f hf j hfj hj hi t ht htd e he φ x hx hφ
  obtain ⟨b,hb,g,_,_,hbt,hbdef,htransfer⟩ :=
    internal_structure_collapse M d hM hP hU hPow hS.bounded hR hd hext
  have henv : ∀ i, cons x e i ∈ d := by
    intro i; cases i with
    | zero => exact hx
    | succ i => exact htd (he i)
  have hcollapse := (htransfer φ (cons x e) henv).mp hφ
  have hfix : (fun i => structureMap d (cons x e i)) = cons (structureMap d x) e := by
    funext i
    cases i with
    | zero => rfl
    | succ i => exact structureMap_fixed ht htd (e i) (he i)
  have henvb : ∀ i, (fun i => structureMap d (cons x e i)) i ∈ b :=
    fun i => (hbdef _).mpr ⟨cons x e i,henv i,rfl⟩
  have hup := φ.upward b M hbt hM (fun y hy => hM b hb y hy) _ henvb hcollapse
  rw [hfix] at hup
  exact ⟨structureMap d x,hbound d hd f hf j hfj hj hi x hx,hup⟩

end TuringRigidity.RelationCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformSigmaHull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse
universe u
namespace FiniteTuple

theorem uniform_internal_sigma_hull (M t : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M)
    (ht : t ∈ M) (h0t : (∅ : ZFSet.{u}) ∈ t) :
    ∃ K ∈ M, ∀ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ t) → ∀ φ : SigmaFormula,
      ∀ x ∈ M, φ.Realize M (cons x e) →
        ∃ h ∈ M, t ⊆ h ∧ x ∈ h ∧ StructureExtensional h ∧ φ.Realize h (cons x e) ∧
          ∃ f ∈ M, ∃ j : ZFSet.{u} → ZFSet.{u}, Presents h f j ∧
            (∀ x ∈ h, j x ∈ K) ∧ (∀ x ∈ h, ∀ y ∈ h, j x = j y → x = y) := by
  obtain ⟨K,hK,hsmall⟩ := uniform_internal_fragment_hull M t hM hP hU hPow hS hR hI hAC ht h0t
  refine ⟨K,hK,?_⟩
  intro e he φ x hx hφ
  obtain ⟨xs,hlen,hxs,hmat⟩ := (φ.realize_iff_prefix M (cons x e)).mp hφ
  have h0 : (∅ : ZFSet.{u}) ∈ M := hM t ht _ h0t
  let s := t ∪ elements (x::xs)
  have hxsM : ∀ y ∈ x::xs, y ∈ M := by
    intro y hy; rcases List.mem_cons.mp hy with rfl|hy
    · exact hx
    · exact hxs y hy
  have hs : s ∈ M := binary_union_mem M hM hP hU ht (elements_mem M hM hP hU h0 (x::xs) hxsM)
  have hts : t ⊆ s := fun _ hy => ZFSet.mem_union.mpr (Or.inl hy)
  have hxsS : ∀ y ∈ x::xs, y ∈ s :=
    fun y hy => ZFSet.mem_union.mpr (Or.inr ((mem_elements y (x::xs)).mpr hy))
  obtain ⟨d,hd,hdt,hsd⟩ := internal_transitive_container M hM hP hU hS.bounded hR hI hs
  have hsd' : s ⊆ d := fun y hy => hdt _ hsd y hy
  have henvS : ∀ i, cons x e i ∈ s := by
    intro i; cases i with
    | zero => exact hxsS x List.mem_cons_self
    | succ i => exact hts (he i)
  have hfeedS := SigmaFormula.feed_mem xs (cons x e) s
    (fun y hy => hxsS y (List.mem_cons_of_mem _ hy)) henvS
  have hfeedM : ∀ i, SigmaFormula.feed xs (cons x e) i ∈ M := fun i => hM s hs _ (hfeedS i)
  have hfeedD : ∀ i, SigmaFormula.feed xs (cons x e) i ∈ d := fun i => hsd' (hfeedS i)
  have hmatD : φ.matrix.Realize d (SigmaFormula.feed xs (cons x e)) :=
    (φ.matrix.absolute d hdt _ hfeedD).mpr ((φ.matrix.absolute M hM _ hfeedM).mp hmat)
  obtain ⟨h,hh,hsh,_,hext,htransfer,f,hf,j,hfj,hj,hi⟩ := hsmall (x::xs) hxsM d hd hdt hsd' φ.matrix
  refine ⟨h,hh,fun y hy => hsh (hts hy),hsh (hxsS x List.mem_cons_self),hext,?_,f,hf,j,hfj,hj,hi⟩
  apply (φ.realize_iff_prefix h (cons x e)).mpr
  exact ⟨xs,hlen,fun y hy => hsh (hxsS y (List.mem_cons_of_mem _ hy)),
    (htransfer _ (fun i => hsh (hfeedS i))).mpr hmatD⟩

theorem internal_uniform_sigma_witness_bound (M t : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M)
    (ht : t ∈ M) (htt : Transitive t) (h0t : (∅ : ZFSet.{u}) ∈ t) :
    ∃ W ∈ M, ∀ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ t) → ∀ φ : SigmaFormula,
      (∃ x ∈ M, φ.Realize M (cons x e)) → ∃ y ∈ W, φ.Realize M (cons y e) := by
  obtain ⟨K,hK,hsmall⟩ := uniform_internal_sigma_hull M t hM hP hU hPow hS hR hI hAC ht h0t
  obtain ⟨W,hW,hbound⟩ := internal_small_witness_bound M K hM hP hU hPow hS hR hK
  refine ⟨W,hW,?_⟩
  intro e he φ hφ
  obtain ⟨x,hx,hφ⟩ := hφ
  obtain ⟨h,hh,hth,hxh,hext,hφh,f,hf,j,hfj,hj,hi⟩ := hsmall e he φ x hx hφ
  exact hbound h hh hext f hf j hfj hj hi t htt hth e he φ x hxh hφh

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SigmaCollection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace SigmaFormula

theorem realize_congr (φ : SigmaFormula) (d : ZFSet.{u}) (e f : ℕ → ZFSet.{u})
    (h : ∀ i, i < φ.scope → e i = f i) : φ.Realize d e ↔ φ.Realize d f := by
  induction φ generalizing e f with
  | bounded φ => exact φ.realize_congr d e f h
  | existsSet φ ih =>
    simp only [Realize]
    apply exists_congr; intro x
    apply and_congr_right; intro _
    apply ih; intro j hj
    cases j with
    | zero => rfl
    | succ j => exact h j (by change j < φ.scope-1; omega)
end SigmaFormula

theorem internal_sigma_request_bound (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M)
    (φ : SigmaFormula) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    {a : ZFSet.{u}} (ha : a ∈ M) :
    ∃ W ∈ M, ∀ x ∈ a, (∃ y ∈ M, φ.Realize M (cons y (cons x e))) →
      ∃ y ∈ W, φ.Realize M (cons y (cons x e)) := by
  have hω := omega_mem M hM hS.bounded hI
  let ee := cons a (cons ZFSet.omega e)
  have hee : ∀ i, ee i ∈ M := by
    intro i; rcases i with _|i; exact ha
    rcases i with _|i; exact hω
    exact he i
  obtain ⟨t,ht,htt,hat,hentries⟩ := BoundedForcing.finite_container M hM hP hU hS.bounded hR hI
    ee hee (φ.scope+2)
  have hωt : ZFSet.omega.{u} ∈ t := hentries 1 (by omega)
  have h0t : (∅ : ZFSet.{u}) ∈ t := htt _ hωt _ ZFSet.omega_zero
  let e' := fun i => if i < φ.scope then e i else ∅
  have he' : ∀ i, e' i ∈ t := by
    intro i; dsimp [e']; split_ifs with hi
    · exact hentries (i+2) (by omega)
    · exact h0t
  have congr (x y : ZFSet.{u}) : φ.Realize M (cons y (cons x e)) ↔
      φ.Realize M (cons y (cons x e')) := by
    apply φ.realize_congr; intro i hi
    rcases i with _|i; rfl
    rcases i with _|i; rfl
    exact (ite_eq_left (show i < φ.scope by omega)).symm
  obtain ⟨W,hW,hbound⟩ := FiniteTuple.internal_uniform_sigma_witness_bound M t hM hP hU hPow hS hR hI hAC ht htt h0t
  refine ⟨W,hW,?_⟩
  intro x hx hy
  have henv : ∀ i, cons x e' i ∈ t := by
    intro i; cases i with
    | zero => exact htt a hat x hx
    | succ i => exact he' i
  obtain ⟨z,hz,hφ⟩ := hbound (cons x e') henv φ (by
    obtain ⟨y,hy,hφ⟩ := hy
    exact ⟨y,hy,(congr x y).mp hφ⟩)
  exact ⟨z,hz,(congr x z).mpr hφ⟩

theorem sigma_collection (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M) :
    SigmaCollection M := by
  intro φ e he a ha htotal
  obtain ⟨W,hW,hbound⟩ := internal_sigma_request_bound M hM hP hU hPow hS hR hI hAC φ e he ha
  exact ⟨W,hW,fun x hx => hbound x hx (htotal x hx)⟩

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_ForcingWitnessCollection
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem forcing_witness_bound (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (φ : SigmaFormula) (e : ℕ → Name (Conditions c)) (he : ∀ i, (e i).encode (label c) ∈ M)
    {d : ZFSet.{u}} (hd : d ∈ M) :
    ∃ W ∈ M, ∀ a : Name (Conditions c), a.encode (label c) ∈ d → ∀ p : Conditions c,
      (∃ b : Name (Conditions c), b.encode (label c) ∈ M ∧ SigmaForces M (push b (push a e)) φ p) →
        ∃ b : Name (Conditions c), b.encode (label c) ∈ W ∧ SigmaForces M (push b (push a e)) φ p := by
  let env := cons c (cons o (fun i => (e i).encode (label c)))
  have henv : ∀ i, env i ∈ M := by
    intro i; rcases i with _|i; exact hc
    rcases i with _|i; exact hoM
    exact he i
  have hrequests := product_mem M hM hP hU hPow hS.bounded hd hc
  obtain ⟨W,hW,hbound⟩ := internal_sigma_request_bound M hM hP hU hPow hS hR hI hAC
    (WitnessCode.request φ) env henv hrequests
  refine ⟨W,hW,?_⟩
  intro a ha p hb
  have haM := hM d hd _ ha
  have hreq := ZFSet.mem_prod.mpr ⟨_,ha,_,label_mem c p,rfl⟩
  obtain ⟨x,hx,hφ⟩ := hbound _ hreq (by
    obtain ⟨b,hb,hφ⟩ := hb
    exact ⟨_,hb,(realize_witnessRequest M hM hP hU hPow hS.bounded hR hI hc hoM ho φ e he a haM p hb).mpr
      ⟨b,rfl,hφ⟩⟩)
  obtain ⟨b,hb,hforce⟩ := (realize_witnessRequest M hM hP hU hPow hS.bounded hR hI hc hoM ho φ e he a haM p
    (hM W hW x hx)).mp hφ
  exact ⟨b,hb ▸ hx,hforce⟩

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_NameValueCover
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}}

variable [Preorder (Conditions c)]

theorem internal_name_value_cover (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {W : ZFSet.{u}} (hW : W ∈ M) (G : GenericFilter (Conditions c)) :
    ∃ N : Name (Conditions c), N.encode (label c) ∈ M ∧
      ∀ b : Name (Conditions c), b.encode (label c) ∈ W → b.val G.carrier ∈ N.val G.carrier := by
  let V := ZFSet.sep (fun x => (NameValidity.Code.valid 1 0).Realize M (cons x (fun _ => c))) W
  have hV : V ∈ M := sigma_sep_mem M hM hS (NameValidity.Code.valid 1 0) (fun _ => c) (fun _ => hc) hW
  have valid (x : ZFSet.{u}) (hx : x ∈ M) :
      (NameValidity.Code.valid 1 0).Realize M (cons x (fun _ => c)) ↔
        ∃ a : Name (Conditions c), a.encode (label c) = x :=
    NameValidity.realize_valid M hM hP hU hPow hS.bounded hR hI _
      (by intro i; cases i <;> assumption) 1 0
  have hvalid (x : ZFSet.{u}) (hx : x ∈ V) : ∃ a : Name (Conditions c), a.encode (label c) = x :=
    (valid x (hM V hV x hx)).mp (ZFSet.mem_sep.mp hx).2
  obtain ⟨p,hp⟩ := G.nonempty
  have hN : (coverName V hvalid p).encode (label c) ∈ M := by
    rw [encode_coverName]
    exact product_mem M hM hP hU hPow hS.bounded hV
      (singleton_mem M hM hP (hM c hc _ (label_mem c p)))
  refine ⟨coverName V hvalid p,hN,?_⟩
  intro b hb
  apply val_mem_coverName V hvalid G.carrier p hp b
  exact ZFSet.mem_sep.mpr ⟨hb,(valid _ (hM W hW _ hb)).mpr ⟨b,rfl⟩⟩

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ExtensionWitnessCover
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}}

variable [Preorder (Conditions c)]

theorem extension_witness_cover (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G)
    (φ : SigmaFormula) (e : ℕ → Name (Conditions c)) (he : ∀ i, (e i).encode (label c) ∈ M)
    (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) :
    ∃ N : Name (Conditions c), N.encode (label c) ∈ M ∧
      ∀ x ∈ a.val G.carrier,
        (∃ y ∈ genericExtensionSet M c G.carrier,
          φ.Realize (genericExtensionSet M c G.carrier) (cons y (cons x (fun i => (e i).val G.carrier)))) →
        ∃ y ∈ N.val G.carrier,
          φ.Realize (genericExtensionSet M c G.carrier) (cons y (cons x (fun i => (e i).val G.carrier))) := by
  obtain ⟨d,hd,hdt,had⟩ := internal_transitive_container M hM hP hU hS.bounded hR hI ha
  obtain ⟨W,hW,hbound⟩ := forcing_witness_bound M hM hP hU hPow hS hR hI hAC hc hoM ho φ e he hd
  obtain ⟨N,hN,hcover⟩ := internal_name_value_cover M hM hP hU hPow hS hR hI hc hW G
  refine ⟨N,hN,?_⟩
  intro x hx hw
  obtain ⟨b,hbd,rfl⟩ := name_of_value_member d hdt a had G.carrier x hx
  have hb := hM d hd _ hbd
  obtain ⟨y,hy,hφ⟩ := hw
  obtain ⟨v,hv,rfl⟩ := (mem_extensionSet M c G.carrier y).mp hy
  have env (v : Name (Conditions c)) (hv : v.encode (label c) ∈ M) :
      ∀ i, (push v (push b e) i).encode (label c) ∈ M := by
    intro i; rcases i with _|i; exact hv
    rcases i with _|i; exact hb
    exact he i
  have values (v : Name (Conditions c)) : (fun i => (push v (push b e) i).val G.carrier) =
      cons (v.val G.carrier) (cons (b.val G.carrier) (fun i => (e i).val G.carrier)) := by
    funext i; rcases i with _|i; rfl
    rcases i with _|i <;> rfl
  rw [← values v] at hφ
  obtain ⟨p,hp,hforce⟩ := (internal_sigma_truth M hM hP hU hPow hS.bounded hR hI hc hoM ho G hG
    φ (push v (push b e)) (env v hv)).mp hφ
  obtain ⟨w,hw,hforcew⟩ := hbound b hbd p ⟨v,hv,hforce⟩
  have hwM := hM W hW _ hw
  have hφw := (internal_sigma_truth M hM hP hU hPow hS.bounded hR hI hc hoM ho G hG
    φ (push w (push b e)) (env w hwM)).mpr ⟨p,hp,hforcew⟩
  rw [values w] at hφw
  exact ⟨w.val G.carrier,hcover w hw,hφw⟩

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ExtensionSigmaReplacement
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem extension_sigmaReplacement (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) :
    SigmaReplacement (genericExtensionSet M c G.carrier) := by
  classical
  intro φ env henv X hX htotal
  obtain ⟨a,ha,rfl⟩ := (mem_extensionSet M c G.carrier X).mp hX
  have names_exist (i) := (mem_extensionSet M c G.carrier (env i)).mp (henv i)
  choose e he hval using names_exist
  have hev : (fun i => (e i).val G.carrier) = env := funext hval
  obtain ⟨N,hN,hcover⟩ := extension_witness_cover M hM hP hU hPow hS hR hI hAC hc hoM ho G hG φ e he a ha
  rw [hev] at hcover
  have hNExt := (mem_extensionSet M c G.carrier _).mpr ⟨N,hN,rfl⟩
  have hAExt := (mem_extensionSet M c G.carrier _).mpr ⟨a,ha,rfl⟩
  have hExtT := genericExtensionSet_transitive M c hM G.carrier
  have hcovered : ∀ x ∈ a.val G.carrier, ∃ y ∈ N.val G.carrier,
      φ.Realize (genericExtensionSet M c G.carrier) (cons y (cons x env)) := by
    intro x hx
    obtain ⟨y,hy,hφ,_⟩ := htotal x hx
    exact hcover x hx ⟨y,hy,hφ⟩
  have hsep := extension_sigmaSeparation M hM hP hU hPow hS hR hI hc hoM ho G hG
  have he' : ∀ i, cons (a.val G.carrier) env i ∈ genericExtensionSet M c G.carrier := by
    intro i; cases i with
    | zero => exact hAExt
    | succ i => exact henv i
  obtain ⟨b,hb,hbdef⟩ := hsep φ.image (cons (a.val G.carrier) env) he' (N.val G.carrier) hNExt
  refine ⟨b,hb,?_⟩
  intro y hy
  rw [hbdef y hy,SigmaFormula.realize_image]
  constructor
  · rintro ⟨_,x,_,hx,hφ⟩
    exact ⟨x,hx,hφ⟩
  · rintro ⟨x,hx,hφ⟩
    obtain ⟨z,hz,hφz⟩ := hcovered x hx
    obtain ⟨v,_,_,hu⟩ := htotal x hx
    have hzy : z = y := (hu z (hExtT _ hNExt z hz) hφz).trans (hu y hy hφ).symm
    exact ⟨hzy ▸ hz,x,hExtT _ hAExt x hx,hx,hφ⟩

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SigmaTransitiveWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace SigmaFormula

theorem internal_transitive_witness (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) {t : ZFSet.{u}} (ht : t ∈ M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ t) (φ : SigmaFormula) (hφ : φ.Realize M e) :
    ∃ d ∈ M, Transitive d ∧ t ⊆ d ∧ φ.Realize d e := by
  obtain ⟨xs,hlen,hxs,hmat⟩ := (φ.realize_iff_prefix M e).mp hφ
  have hω := omega_mem M hM hS hI
  have h0 := hM _ hω _ ZFSet.omega_zero
  let s := t ∪ FiniteTuple.elements xs
  have hs : s ∈ M := binary_union_mem M hM hP hU ht (FiniteTuple.elements_mem M hM hP hU h0 xs hxs)
  obtain ⟨d,hdM,hd,hsd⟩ := internal_transitive_container M hM hP hU hS hR hI hs
  have hsD : s ⊆ d := fun y hy => hd s hsd y hy
  have htD : t ⊆ d := fun y hy => hsD (ZFSet.mem_union.mpr (Or.inl hy))
  have hxsD : ∀ y ∈ xs, y ∈ d := fun y hy =>
    hsD (ZFSet.mem_union.mpr (Or.inr ((FiniteTuple.mem_elements y xs).mpr hy)))
  have heM := fun i => hM t ht _ (he i)
  have heD := fun i => htD (he i)
  refine ⟨d,hdM,hd,htD,(φ.realize_iff_prefix d e).mpr ⟨xs,hlen,hxsD,?_⟩⟩
  exact (φ.matrix.absolute d hd _ (feed_mem xs e d hxsD heD)).mpr
    ((φ.matrix.absolute M hM _ (feed_mem xs e M hxs heM)).mp hmat)
end SigmaFormula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SigmaDomainCollection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace SigmaFormula

theorem internal_bounded_domain (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hC : SigmaCollection M)
    {a t : ZFSet.{u}} (ha : a ∈ M) (ht : t ∈ M) (htt : Transitive t) (hat : a ∈ t)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ t) (φ : SigmaFormula)
    (hφ : ∀ x ∈ a, φ.Realize M (cons x e)) :
    ∃ D ∈ M, Transitive D ∧ t ⊆ D ∧ ∀ x ∈ a, φ.Realize D (cons x e) := by
  have heM := fun i => hM t ht _ (he i)
  have hxe (x : ZFSet.{u}) (hx : x ∈ a) : ∀ i, cons x e i ∈ t := by
    intro i; cases i with
    | zero => exact htt a hat x hx
    | succ i => exact he i
  obtain ⟨B,hB,hbound⟩ := hC φ.domainRequest (cons t e)
    (by intro i; cases i <;> simp [cons,ht,heM]) a ha (by
      intro x hx
      obtain ⟨d,hd,hdt,htd,hdφ⟩ := internal_transitive_witness M hM hP hU hS hR hI ht
        (cons x e) (hxe x hx) φ (hφ x hx)
      exact ⟨d,hd,(realize_domainRequest φ M hM e heM hd (hM a ha x hx) ht).mpr ⟨hdt,htd,hdφ⟩⟩)
  let C := ZFSet.sep (fun d => Transitive d ∧ t ⊆ d) B
  have hCmem : C ∈ M := by
    simpa only [Formula.Eval,Formula.eval_transitive,Formula.eval_subset,cons_zero,cons_succ] using
      sep_mem M hM hS (.conj (.transitive 0) (.subset 1 0)) (fun _ => t) (fun _ => ht) hB
  let D := t ∪ ZFSet.sUnion C
  have hDM : D ∈ M := binary_union_mem M hM hP hU ht (union_mem M hM hU hCmem)
  have htD : t ⊆ D := fun _ hy => ZFSet.mem_union.mpr (Or.inl hy)
  have hDT : Transitive D := by
    intro x hx y hy
    rcases ZFSet.mem_union.mp hx with hx|hx
    · exact htD (htt x hx y hy)
    · obtain ⟨d,hd,hxd⟩ := ZFSet.mem_sUnion.mp hx
      have hdt := (ZFSet.mem_sep.mp hd).2.1
      exact ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_sUnion.mpr ⟨d,hd,hdt x hxd y hy⟩))
  refine ⟨D,hDM,hDT,htD,?_⟩
  intro x hx
  obtain ⟨d,hdB,hdφ⟩ := hbound x hx
  have hdM := hM B hB d hdB
  obtain ⟨hdt,htd,hdφ⟩ := (realize_domainRequest φ M hM e heM hdM (hM a ha x hx) ht).mp hdφ
  have hdC : d ∈ C := ZFSet.mem_sep.mpr ⟨hdB,hdt,htd⟩
  have hdD : d ⊆ D := fun y hy => ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_sUnion.mpr ⟨d,hdC,hy⟩))
  exact φ.transitive_upward hdt hDT hdD (cons x e) (fun i => htd (hxe x hx i)) hdφ
end SigmaFormula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SigmaBoundedUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace SigmaFormula

def allDomainMatrix (a : ℕ) (φ : SigmaFormula) : Formula :=
  .conj (.transitive 0) (.conj (.existsMem 0 (.empty 0))
    (.conj (.envBound φ.scope) (.conj (.member (a+1) 0)
      (.allMem (a+1) (FiniteTuple.relativizeSigma 1 (φ.rename skipDomain))))))

def allMem (a : ℕ) (φ : SigmaFormula) : SigmaFormula := .existsSet (.bounded (allDomainMatrix a φ))

theorem eval_allDomainMatrix (a : ℕ) (φ : SigmaFormula) (d : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (allDomainMatrix a φ).Eval (cons d e) ↔ Transitive d ∧ (∅ : ZFSet.{u}) ∈ d ∧
      (∀ i, i < φ.scope → e i ∈ d) ∧ e a ∈ d ∧ ∀ x ∈ e a, φ.Realize d (cons x e) := by
  simp only [allDomainMatrix,Formula.Eval,Formula.eval_transitive,Formula.eval_empty,
    Formula.eval_envBound,Formula.eval_allMem,FiniteTuple.eval_relativizeSigma,
    realize_rename,cons_zero,cons_succ]
  have eq (x : ZFSet.{u}) : (fun i => cons x (cons d e) (skipDomain i)) = cons x e := by
    funext i; cases i <;> rfl
  simp only [eq,exists_eq_right]

theorem realize_allMem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hC : SigmaCollection M)
    (a : ℕ) (φ : SigmaFormula) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (allMem a φ).Realize M e ↔ ∀ x ∈ e a, φ.Realize M (cons x e) := by
  classical
  let e' := fun i => if i < φ.scope then e i else (∅ : ZFSet.{u})
  have congr (d x : ZFSet.{u}) : φ.Realize d (cons x e) ↔ φ.Realize d (cons x e') := by
    apply φ.realize_congr; intro i hi
    cases i with
    | zero => rfl
    | succ i => exact (ite_eq_left (show i < φ.scope by omega)).symm
  have matrix (d : ZFSet.{u}) (hd : d ∈ M) :
      (allDomainMatrix a φ).Realize M (cons d e) ↔ Transitive d ∧ (∅ : ZFSet.{u}) ∈ d ∧
        (∀ i, i < φ.scope → e i ∈ d) ∧ e a ∈ d ∧ ∀ x ∈ e a, φ.Realize d (cons x e) := by
    rw [Formula.absolute _ M hM _ (by intro i; cases i <;> simp [cons,he,hd])]
    exact eval_allDomainMatrix a φ d e
  change (∃ d ∈ M, _) ↔ _
  constructor
  · rintro ⟨d,hd,h⟩
    obtain ⟨hdt,h0,heD,haD,hφ⟩ := (matrix d hd).mp h
    have he' : ∀ i, e' i ∈ d := by
      intro i; dsimp [e']; split_ifs with hi
      · exact heD i hi
      · exact h0
    intro x hx
    apply (congr M x).mpr
    exact φ.transitive_upward hdt hM (fun y hy => hM d hd y hy) (cons x e')
      (by intro i; cases i with
          | zero => exact hdt _ haD x hx
          | succ i => exact he' i) ((congr d x).mp (hφ x hx))
  · intro hφ
    have hω := omega_mem M hM hS hI
    let ee := cons (e a) (cons ZFSet.omega e)
    have hee : ∀ i, ee i ∈ M := by
      intro i; rcases i with _|i; exact he a
      rcases i with _|i; exact hω
      exact he i
    obtain ⟨t,ht,htt,hat,hentries⟩ := BoundedForcing.finite_container M hM hP hU hS hR hI
      ee hee (φ.scope+2)
    have hωt : ZFSet.omega.{u} ∈ t := hentries 1 (by omega)
    have h0t : (∅ : ZFSet.{u}) ∈ t := htt _ hωt _ ZFSet.omega_zero
    have he' : ∀ i, e' i ∈ t := by
      intro i; dsimp [e']; split_ifs with hi
      · exact hentries (i+2) (by omega)
      · exact h0t
    obtain ⟨D,hD,hDT,htD,hφD⟩ := internal_bounded_domain M hM hP hU hS hR hI hC
      (he a) ht htt hat e' he' φ (fun x hx => (congr M x).mp (hφ x hx))
    refine ⟨D,hD,(matrix D hD).mpr ⟨hDT,htD h0t,?_,htD hat,?_⟩⟩
    · intro i hi
      exact htD (hentries (i+2) (by omega))
    · intro x hx
      exact (congr D x).mpr (hφD x hx)
end SigmaFormula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_LevySigmaNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

namespace LevySigma

def normalize : LevySigma → SigmaFormula
  | .bounded φ => .bounded φ
  | .conj φ ψ => .conj φ.normalize ψ.normalize
  | .disj φ ψ => .disj φ.normalize ψ.normalize
  | .existsSet φ => .existsSet φ.normalize
  | .existsMem a φ => .existsMem a φ.normalize
  | .allMem a φ => .allMem a φ.normalize

theorem normalize_correct (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hC : SigmaCollection M)
    (φ : LevySigma) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    φ.normalize.Realize M e ↔ φ.Realize M e := by
  have hω := omega_mem M hM hS hI
  have h0 := hM _ hω _ ZFSet.omega_zero
  induction φ generalizing e with
  | bounded φ => rfl
  | conj φ ψ ihφ ihψ => exact (SigmaFormula.realize_conj _ _ _ _).trans (and_congr (ihφ e he) (ihψ e he))
  | disj φ ψ ihφ ihψ => exact (SigmaFormula.realize_disj M h0 _ _ _).trans (or_congr (ihφ e he) (ihψ e he))
  | existsSet φ ih =>
    simp only [normalize,SigmaFormula.Realize,Realize]
    apply exists_congr; intro x
    apply and_congr_right; intro hx
    exact ih (cons x e) (by intro i; cases i <;> simp [cons,he,hx])
  | existsMem a φ ih =>
    rw [normalize,SigmaFormula.realize_existsMem]
    change (∃ x ∈ M, x ∈ e a ∧ _) ↔ ∃ x ∈ M, x ∈ e a ∧ _
    apply exists_congr; intro x
    apply and_congr_right; intro hx
    exact and_congr_right (fun _ => ih (cons x e) (by intro i; cases i <;> simp [cons,he,hx]))
  | allMem a φ ih =>
    rw [normalize,SigmaFormula.realize_allMem M hM hP hU hS hR hI hC _ _ _ he]
    change (∀ x ∈ e a, _) ↔ ∀ x ∈ M, x ∈ e a → _
    constructor
    · intro h x hx hxa
      exact (ih (cons x e) (by intro i; cases i <;> simp [cons,he,hx])).mp (h x hxa)
    · intro h x hxa
      have hx := hM _ (he a) x hxa
      exact (ih (cons x e) (by intro i; cases i <;> simp [cons,he,hx])).mpr (h x hx hxa)
end LevySigma

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_LevySigmaSchemas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem levy_sigma_schemas (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M) :
    LevySigmaSeparation M ∧ LevySigmaReplacement M := by
  have hC := sigma_collection M hM hP hU hPow hS hR hI hAC
  have correct := LevySigma.normalize_correct M hM hP hU hS.bounded hR hI hC
  constructor
  · intro φ e he a ha
    obtain ⟨b,hb,hbdef⟩ := hS φ.normalize e he a ha
    refine ⟨b,hb,?_⟩
    intro x hx
    rw [hbdef x hx,correct φ (cons x e) (by intro i; cases i <;> simp [cons,he,hx])]
  · intro φ e he a ha htotal
    have eq (x y : ZFSet.{u}) (hx : x ∈ M) (hy : y ∈ M) :
        φ.normalize.Realize M (cons y (cons x e)) ↔ φ.Realize M (cons y (cons x e)) :=
      correct φ _ (by
        intro i; rcases i with _|i; exact hy
        rcases i with _|i; exact hx
        exact he i)
    obtain ⟨b,hb,hbdef⟩ := hR φ.normalize e he a ha (by
      intro x hx
      have hxM := hM a ha x hx
      obtain ⟨y,hy,hφ,hu⟩ := htotal x hx
      exact ⟨y,hy,(eq x y hxM hy).mpr hφ,fun z hz h => hu z hz ((eq x z hxM hz).mp h)⟩)
    refine ⟨b,hb,?_⟩
    intro y hy
    rw [hbdef y hy]
    apply exists_congr; intro x
    exact and_congr_right (fun hx => eq x y (hM a ha x hx) hy)

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_SourceTheory
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem sourceT_of_finite_schemas (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M) : SourceT M := by
  obtain ⟨hLS,hLR⟩ := levy_sigma_schemas M hM hP hU hPow hS hR hI hAC
  have hω := omega_mem M hM hS.bounded hI
  have h0 := hM _ hω _ ZFSet.omega_zero
  exact ⟨BasicAxioms.extensionality M hM,⟨∅,h0,fun x _ => ZFSet.notMem_empty x⟩,
    hP,hU,hPow,hI,BasicAxioms.foundation M hM,hAC,hLS,hLR⟩

theorem extension_sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)] (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : CountableForcing.GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G)
    (htop : ⊤ ∈ G.carrier) :
    SourceT (genericExtensionSet M c G.carrier) := by
  have hS := hT.separation.finitePrefix
  have hR := hT.replacement.finitePrefix
  have hP := hT.pairing
  have hU := hT.union
  have hPow := hT.powerSet
  have hI := hT.infinity
  have hAC := hT.choice
  apply sourceT_of_finite_schemas _ (genericExtensionSet_transitive M c hM G.carrier)
    (extension_pairing M c hM hP hc G.carrier htop)
    (extension_union M c o hM hP hU hPow hS.bounded hc hoM ho G)
    (AtomicForcing.extension_powerSet M hM hP hU hPow hS.bounded hR hI hc hoM ho G hG htop)
    (BoundedForcing.extension_sigmaSeparation M hM hP hU hPow hS hR hI hc hoM ho G hG)
    (BoundedForcing.extension_sigmaReplacement M hM hP hU hPow hS hR hI hAC hc hoM ho G hG)
    (extension_infinity M c hM hP hU hPow hS.bounded hR hI hc G.carrier htop)
    (BoundedForcing.extension_choice M hM hP hU hPow hS hR hI hAC hc hoM ho G hG htop)

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelNaturalNumbers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem sourceT_omega_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ZFSet.omega.{u} ∈ M := omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCollapseConditions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalCollapse
open TransitiveNameModel
universe u

attribute [local instance] order

attribute [local instance] collapsePreorder

theorem orderSet_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c : ZFSet.{u}} (hc : c ∈ M) : orderSet c ∈ M := by
  let e : ℕ → ZFSet.{u} := fun _ => c
  simpa only [orderSet,Formula.Eval,Formula.eval_orderedPair,Formula.eval_subset,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 2 (.conj (.orderedPair 2 1 0) (.subset 0 1)))) e (fun _ => hc)
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hc hc)

end TuringRigidity.BoundedSetTheory.InternalCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenConditions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory InternalCollapse CohenBorelForcing

theorem alphabet_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) : alphabet ∈ M := by
  have hn (n : ℕ) : natSet n ∈ M :=
    hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨n,rfl⟩)
  exact pair_mem M hM hT.pairing (hn 0) (hn 1)

attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalFiniteSubsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalFiniteSubsets
open Set TransitiveNameModel BoundedSetTheory InternalCollapse RelativeConstructible
universe u

theorem finite_subset_mem (M A x : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (hx : x ∈ finiteSubsets A) : x ∈ M := by
  obtain ⟨n,v,hv,rfl⟩ := (mem_finiteSubsets A x).mp hx
  exact finite_range_mem M hM hT.pairing hT.union
    (hM _ (sourceT_omega_mem M hM hT) _ ZFSet.omega_zero) n v
    (fun i => hM A hA _ (hv i))

theorem finiteSubsets_mem (M A : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) : finiteSubsets A ∈ M := by
  obtain ⟨C,hC,hCdef⟩ := conditions_exist_absolute_without_choice M hM hT.pairing
    hT.union hT.powerSet hT.separation.finitePrefix.bounded (sourceT_omega_mem M hM hT) hA
  obtain ⟨Q,hQ,hQdef⟩ := internal_power M hM hT.powerSet hA
  let e := cons ZFSet.omega (cons A (fun _ => C))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    exact sourceT_omega_mem M hM hT
    exact hA
    exact hC
  let φ : Formula := .existsMem 3 (rangeFormula 2 3 1 0)
  have hφ (x : ZFSet.{u}) : φ.Eval (cons x e) ↔ x ∈ finiteSubsets A := by
    change (∃ g ∈ C, (rangeFormula 2 3 1 0).Eval (cons g (cons x e))) ↔ _
    constructor
    · rintro ⟨g,hg,h⟩
      obtain ⟨n,hn⟩ := (hCdef g).mp hg
      obtain ⟨v,hv,rfl⟩ := functionGraph_tuple A g n hn
      exact (mem_finiteSubsets A x).mpr ⟨n,v,hv,
        (rangeFormula_spec 2 3 1 0 _ rfl hv rfl).mp h⟩
    · intro hx
      obtain ⟨n,v,hv,rfl⟩ := (mem_finiteSubsets A x).mp hx
      exact ⟨tupleGraph v,(hCdef _).mpr ⟨n,tupleGraph_function A v hv⟩,
        (rangeFormula_spec 2 3 1 0 _ rfl hv rfl).mpr rfl⟩
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded φ e he hQ
  have heq : Q.sep (fun x => φ.Eval (cons x e)) = finiteSubsets A := by
    apply ZFSet.ext; intro x
    rw [ZFSet.mem_sep,hφ,hQdef]
    exact ⟨fun h => h.2,fun hx => ⟨⟨finite_subset_mem M A x hM hT hA hx,
      ((mem_finiteSubsets_iff A x).mp hx).1⟩,hx⟩⟩
  exact heq ▸ hs

end TuringRigidity.InternalFiniteSubsets

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenGroundPoset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenGroundPoset
open Set TransitiveNameModel BoundedSetTheory InternalFiniteSubsets CohenConditionCode
open CohenSymmetry CohenCoordinates CohenChainCondition
open InternalCohen (alphabet mem_alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem conditions_mem (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) : conditions A ∈ M := by
  have hB := InternalCohen.alphabet_mem M hM hT
  have hP := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hA hB
  let e := cons A (fun _ => alphabet)
  have he : ∀ i, e i ∈ M := by intro i; cases i; exact hA; exact hB
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (singleValuedFormula 1 2 0) e he (finiteSubsets_mem M _ hM hT hP)
  have heq : (finiteSubsets (ZFSet.prod A alphabet)).sep
      (fun p => (singleValuedFormula 1 2 0).Eval (cons p e)) = conditions A := by
    apply ZFSet.ext; intro p
    rw [ZFSet.mem_sep,mem_conditions]
    exact and_congr Iff.rfl (singleValuedFormula_spec 1 2 0 _ rfl)
  exact heq ▸ hs

theorem poset_internal (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) :
    conditions A ∈ M ∧ InternalCollapse.orderSet (conditions A) ∈ M :=
  ⟨conditions_mem M A hM hT hA,
    InternalCollapse.orderSet_mem M hM hT (conditions_mem M A hM hT hA)⟩

theorem manyColumn_internal (M K : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hK : K ∈ M) :
    conditions (ZFSet.prod K ZFSet.omega) ∈ M ∧
    InternalCollapse.orderSet (conditions (ZFSet.prod K ZFSet.omega)) ∈ M :=
  poset_internal M _ hM hT (product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK (sourceT_omega_mem M hM hT))

end TuringRigidity.CohenGroundPoset

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelArithmeticComprehension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel UniformArithmetic
universe u

theorem sourceT_arithmetic_comprehension (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {P : Predicate} (hP : Arith P) (O : Oracles) (hO : ∀ i, O i ∈ modelReals M) :
    arithmeticReal P O ∈ modelReals M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨Q,hQ,_,hbound⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union hT.powerSet hS hω
  obtain ⟨φ,hφ⟩ := arithmetic_bounded_definition.{u} hP
  let e := cons ZFSet.omega (cons Q (fun i => realCode (O i)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|i; exact hω
    rcases i with _|i; exact hQ
    exact hO i
  let B := ZFSet.sep (fun x => φ.Eval (cons x e)) ZFSet.omega
  have hB : B ∈ M := sep_mem M hM hS φ e he hω
  have hBdef (n : ℕ) : natSet.{u} n ∈ B ↔ P O n := by
    rw [ZFSet.mem_sep]
    change (natSet n ∈ ZFSet.omega ∧ φ.Eval (arithmeticEnv Q O n)) ↔ P O n
    rw [hφ Q hbound O n]
    exact and_iff_right ((mem_omega _).mpr ⟨n,rfl⟩)
  have hcode : realCode (arithmeticReal P O) = B := by
    apply ZFSet.ext; intro x
    by_cases hx : x ∈ ZFSet.omega.{u}
    · obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
      rw [natSet_mem_realCode,arithmeticReal_true,hBdef]
    · exact ⟨fun h => False.elim (hx (realCode_subset _ h)),
        fun h => False.elim (hx (ZFSet.mem_sep.mp h).1)⟩
  change realCode (arithmeticReal P O) ∈ M
  rw [hcode]
  exact hB

theorem sourceT_arithmetic_real (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {P : Predicate} (hP : Arith P) (O : Oracles) (hO : ∀ i, O i ∈ modelReals M)
    (A : Oracle) (hA : ∀ n, A n = true ↔ P O n) : A ∈ modelReals M := by
  have he : A = arithmeticReal P O := by
    funext n
    have h := (hA n).trans (arithmeticReal_true P O n).symm
    cases ha : A n <;> cases hb : arithmeticReal P O n <;> simp_all
  rw [he]
  exact sourceT_arithmetic_comprehension M hM hT hP O hO

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelRealOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel UniformArithmetic Encodable TableIndices OracleJump IndexMatrix
universe u

theorem sourceT_arithmetic_oracle (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {B : OracleFamily} (hB : ArithmeticOracle B) (O : Oracles)
    (hO : ∀ i, O i ∈ modelReals M) (v : ℕ) : B O v ∈ modelReals M := by
  have hp := Arith.comp (fun n => Nat.pair v n) hB (Primrec₂.natPair.comp (Primrec.const v) Primrec.id)
  exact sourceT_arithmetic_real M hM hT hp O hO (B O v)
    (fun n => by simp only [left,right,Nat.unpair_pair])

theorem sourceT_real_lower (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A B : Oracle} (hB : B ∈ modelReals M) (hAB : Reduces A B) : A ∈ modelReals M := by
  obtain ⟨d,hd⟩ := reduces_represents hAB
  have hd' : Represents B (machine (encode d)) A := by simpa using hd
  have h := sourceT_arithmetic_oracle M hM hT
    (tableOracle_arith (parameter_arith 0) (Primrec.const (encode d))) (fun _ => B) (fun _ => hB) 0
  change tableOracle B (encode d) ∈ modelReals M at h
  rw [tableOracle_eq hd'] at h
  exact h

theorem sourceT_real_join (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A B : Oracle} (hA : A ∈ modelReals M) (hB : B ∈ modelReals M) :
    TuringRigidity.join A B ∈ modelReals M := by
  let O : Oracles := fun i => if i = 0 then A else B
  have hO : ∀ i, O i ∈ modelReals M := by
    intro i; dsimp [O]; split <;> assumption
  have h := sourceT_arithmetic_oracle M hM hT
    (join_arith (parameter_arith 0) (parameter_arith 1)) O hO 0
  simpa [O] using h

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenInternalDecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenInternalDecision
open Set TransitiveNameModel BoundedSetTheory CohenAntichainStages CohenGroundPoset
open CohenConditionCode CohenSymmetry CohenCoordinates

theorem below_mem (M c U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hU : U ∈ M) : below c U ∈ M := by
  let e := cons U (fun _ => c)
  have he : ∀ i, e i ∈ M := by intro i; cases i; exact hU; exact hc
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded (.existsMem 1 (.subset 0 1)) e he hc
  simpa only [below,Formula.Eval,Formula.eval_subset,cons_zero,cons_succ,e] using hs

end TuringRigidity.CohenInternalDecision

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_SparseCohenRealName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SparseCohenRealName
open TransitiveNameModel BoundedSetTheory InternalCollapse CountableForcing RecursiveNames
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop
open InternalCohen (bitSet realNameFormula )

noncomputable abbrev poset : ZFSet.{0} := CohenGroundPoset.conditions ZFSet.omega

noncomputable def realName : Name (Conditions poset) :=
  .mk {t : Conditions poset × ℕ //
    ZFSet.pair (natSet t.2) (bitSet true) ∈ label poset t.1}
    (fun t => Name.check (natSet t.val.2)) (fun t => t.val.1)

noncomputable def realNameCode (f : ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.sep (fun z => ∃ q ∈ poset, ∃ n ∈ ZFSet.omega, ∃ v ∈ iterUnion 2 f,
    ZFSet.pair n v ∈ f ∧ ZFSet.pair n (bitSet true) ∈ q ∧ z = ZFSet.pair v q)
    (ZFSet.prod (iterUnion 2 f) poset)

end TuringRigidity.SparseCohenRealName

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalRegularOperations
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalRegularOperations
open Set TransitiveNameModel BoundedSetTheory RegularCompletion
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem neg_mem (M c U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hU : U ∈ M) : neg c U ∈ M := by
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.allMem 1 (.neg (.subset 1 0))) (fun _ => U) (fun _ => hU) hc
  simpa only [neg,Formula.Eval,Formula.eval_allMem,Formula.eval_subset,
    cons_zero,cons_succ] using hs

theorem regular_mem (M c U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hU : U ∈ M) : regular c U ∈ M :=
  neg_mem M c _ hM hT hc (neg_mem M c U hM hT hc hU)

theorem decode_regular (c U : ZFSet.{0}) (hUc : U ⊆ c) (hU : Lower c U) :
    decode c (regular c U) (neg_lower c (neg c U)) =
      (Heyting.Regular.toRegular (decode c U hU) : LowerSet (Conditions c)) := by
  change decode c (neg c (neg c U)) _ = _
  rw [decode_neg c _ (neg_subset c U) (neg_lower c U),decode_neg c U hUc hU]
  rfl

theorem bitCode_mem (M c E : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hE : E ∈ M) : bitCode c E ∈ M :=
  regular_mem M c _ hM hT hc (CohenInternalDecision.below_mem M c E hM hT hc hE)

end TuringRigidity.InternalRegularOperations

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalRegularAlgebra
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalRegularAlgebra
open Set TransitiveNameModel BoundedSetTheory RegularCompletion InternalRegularOperations
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

def interpret (c U : ZFSet.{0}) (hU : IsCode c U) : Algebra (Conditions c) :=
  ⟨decode c U (code_lower c U hU),by
    change (decode c U _)ᶜᶜ = decode c U _
    have h := decode_regular c U hU.1 (code_lower c U hU)
    change decode c (regular c U) _ = (decode c U _)ᶜᶜ at h
    apply h.symm.trans
    apply SetLike.ext
    intro p
    change label c p ∈ regular c U ↔ label c p ∈ U
    rw [hU.2]⟩

end TuringRigidity.InternalRegularAlgebra

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanProjection
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalRegularOrder InternalBooleanSyntax InternalGeneratedAlgebra

theorem complements_mem (M c B F : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : B ∈ M) (hF : F ∈ M) : complements c B F ∈ M := by
  let e := cons c (fun _ => F)
  have he : ∀ i, e i ∈ M := by intro i; cases i; exact hc; exact hF
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 2 (negFormula 2 0 1)) e he hB
  simpa only [complements,Formula.Eval,negFormula_spec,cons_zero,cons_succ,e] using hs

theorem closed_inf (M c B Q A F : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B)
    (hA : Closed c B Q A) (hFM : F ∈ M) (hFA : F ⊆ A) : infCode c F ∈ A := by
  have hFB : F ⊆ B := fun _ h => hA.1 (hFA h)
  have hNF : complements c B F ⊆ A := by
    intro V hV
    obtain ⟨_,U,hU,rfl⟩ := ZFSet.mem_sep.mp hV
    exact hA.2.1 U (hFA hU)
  have hNQ : complements c B F ∈ Q := (hQ _).mpr
    ⟨complements_mem M c B F hM hT hc hBM hFM,fun _ h => (ZFSet.mem_sep.mp h).1⟩
  rw [inf_eq_neg_sup c B F (fun U hU => ((hB U).mp hU).2) hFB
    (fun U hU => hA.1 (hA.2.1 U (hFA hU)))]
  exact hA.2.1 _ (hA.2.2 _ hNQ hNF)

theorem uppers_mem (M A U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hU : U ∈ M) : uppers A U ∈ M := by
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.subset 1 0) (fun _ => U) (fun _ => hU) hA
  simpa only [uppers,Formula.eval_subset,cons_zero,cons_succ] using hs

theorem project_mem_part (M c B Q A U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M) (hUM : U ∈ M)
    (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A) : project c A U ∈ A :=
  closed_inf M c B Q A _ hM hT hc hBM hB hQ hA
    (uppers_mem M A U hM hT hAM hUM) (fun _ h => (ZFSet.mem_sep.mp h).1)

end TuringRigidity.InternalBooleanProjection

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanDense
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanDense
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalGeneratedAlgebra InternalBooleanProjection InternalBooleanGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem basicCode_mem (M c p : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hp : p ∈ c) : basicCode c p ∈ M :=
  bitCode_mem M c _ hM hT hc (singleton_mem M hM hT.pairing (hM c hc p hp))

end TuringRigidity.InternalBooleanDense

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalProjectedGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalProjectedGeneric
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalGeneratedAlgebra InternalBooleanProjection InternalBooleanGeneric InternalBooleanDense
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

attribute [local instance] codeOrder codePreorder

noncomputable def projected (M c B Q A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) : GenericFilter (Conditions (positive A)) where
  carrier := {p | Hit G (label (positive A) p)}
  nonempty := by
    obtain ⟨p,hp⟩ := G.nonempty
    let b := basicCode c (label c p)
    have hbM : b ∈ M := basicCode_mem M c _ hM hT hc (label_mem c p)
    have hbc : IsCode c b := regular_isCode c _
    have hb : label c p ∈ b := mem_basicCode c _ (label_mem c p)
    have hpb := subset_project c A b hbc.1 hb
    have hPA := project_mem_part M c B Q A b hM hT hc hBM hAM hbM hB hQ hA
    have hn : project c A b ≠ ∅ := fun h => ZFSet.notMem_empty _ (h ▸ hpb)
    obtain ⟨q,hq⟩ := label_surjective (positive A) (ZFSet.mem_sep.mpr ⟨hPA,hn⟩)
    exact ⟨q,p,hp,hq.symm ▸ hpb⟩
  upper := by
    intro p q hpq hp
    obtain ⟨r,hr,hrp⟩ := hp
    exact ⟨r,hr,hpq hrp⟩
  directed := by
    intro p q hp hq
    let U := label (positive A) p
    let V := label (positive A) q
    have hU := (label_info A p).1
    have hV := (label_info A q).1
    have hUc := ((hB U).mp (hA.1 hU)).2
    have hVc := ((hB V).mp (hA.1 hV)).2
    let F : ZFSet.{0} := {U,V}
    have hFM : F ∈ M := pair_mem M hM hT.pairing (hM A hAM U hU) (hM A hAM V hV)
    have hFA : F ⊆ A := by
      intro W hW
      exact (ZFSet.mem_pair.mp hW).elim (fun h => h ▸ hU) (fun h => h ▸ hV)
    have hWA := closed_inf M c B Q A F hM hT hc hBM hB hQ hA hFM hFA
    obtain ⟨r,hr,hrU⟩ := hp
    obtain ⟨s,hs,hsV⟩ := hq
    obtain ⟨t,ht,htr,hts⟩ := G.directed hr hs
    have htU := code_lower c U hUc _ hrU _ (label_mem c t) htr
    have htV := code_lower c V hVc _ hsV _ (label_mem c t) hts
    have htW : label c t ∈ infCode c F := by
      refine ZFSet.mem_sep.mpr ⟨label_mem c t,fun W hW => ?_⟩
      exact (ZFSet.mem_pair.mp hW).elim (fun h => h ▸ htU) (fun h => h ▸ htV)
    have hn : infCode c F ≠ ∅ := fun h => ZFSet.notMem_empty _ (h ▸ htW)
    obtain ⟨w,hw⟩ := label_surjective (positive A) (ZFSet.mem_sep.mpr ⟨hWA,hn⟩)
    refine ⟨w,⟨t,ht,hw.symm ▸ htW⟩,?_,?_⟩
    · change label (positive A) w ⊆ U
      rw [hw]
      exact inf_subset c F (ZFSet.mem_pair.mpr (Or.inl rfl))
    · change label (positive A) w ⊆ V
      rw [hw]
      exact inf_subset c F (ZFSet.mem_pair.mpr (Or.inr rfl))

end TuringRigidity.InternalProjectedGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_TaggedProductGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TaggedProductGeneric
open TransitiveNameModel BoundedSetTheory CountableForcing TaggedProductConditions
open CohenProductSplitting
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def joint (a b c : ZFSet.{0})
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (G : GenericFilter (Conditions a)) (H : GenericFilter (Conditions b)) :
    GenericFilter (Conditions c) :=
  AutomorphismName.mapFilter (productIso a b c hcs) (SourceEquationTail.productFilter G H)

end TuringRigidity.TaggedProductGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ElementaryCollapse
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse
universe u

noncomputable def collapsed (d : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun x : Conditions d => structureMap d (label d x))

instance collapsed_countable (d : ZFSet.{u}) [Countable (Conditions d)] :
    Countable (Conditions (collapsed d)) := by
  let f : Conditions (collapsed d) → Conditions d := fun z => Classical.choose
    (ZFSet.mem_range.mp (show label (collapsed d) z ∈ collapsed d from label_mem _ z))
  have hf (z : Conditions (collapsed d)) : structureMap d (label d (f z)) = label _ z :=
    Classical.choose_spec (ZFSet.mem_range.mp (label_mem _ z))
  exact Function.Injective.countable (f := f) (fun x y h =>
    label_injective _ ((hf x).symm.trans ((congrArg (fun z => structureMap d (label d z)) h).trans (hf y))))

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_LocalPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.LocalPair
open Encodable UniformOracle ArithmeticHierarchy OracleJump EncodedForcing EffectiveWitness IndexMatrix
open CodingForcing UniformProgram UniformPair LocalColumnCertificates
noncomputable section
attribute [local instance] Classical.propDecidable

theorem raw_spec (B : Oracle) (F : ℕ → Oracle) (x p : ℕ)
    (hnb : NoBad B F x p) :
    let q := condition (EffectiveSplitConditions.update p (UniformSplit.step B (request (Nat.pair x p))))
    Decisive B F x q ∨ (q = condition p ∧ Outcome B F x p) := by
  let raw := UniformSplit.step B (request (Nat.pair x p))
  have hs := UniformSplit.step_spec B (request (Nat.pair x p))
  change UniformSplit.Accept B (Nat.pair (request (Nat.pair x p)) raw) at hs
  simp only [UniformSplit.Accept,Nat.unpair_pair] at hs
  change Decisive B F x (condition (EffectiveSplitConditions.update p raw)) ∨ _
  rcases hs with ⟨ht,hno⟩ | ⟨ht,hpoint⟩ | ⟨ht,hdiv⟩
  · have he : condition (EffectiveSplitConditions.update p raw) = condition p := by
      simp [EffectiveSplitConditions.update,ht,condition_code]
    exact Or.inr ⟨he,Or.inl hno⟩
  · have he : condition (EffectiveSplitConditions.update p raw) = condition p := by
      simp [EffectiveSplitConditions.update,ht,condition_code]
    exact Or.inr ⟨he,Or.inr ⟨_,hpoint,hnb _ hpoint⟩⟩
  · let w := (Nat.unpair raw).2
    have hpq : left p <+: word (item w 1) := by
      simpa [UniformSplit.DivCert,UniformSplit.start,request,item,word] using hdiv.1
    let r := append (condition p) ((word (item w 1)).drop (left p).length)
    have hl : r.left = word (item w 1) := by
      change left p ++ (word (item w 1)).drop (left p).length = _
      rw [List.prefix_iff_eq_take] at hpq
      conv_lhs => lhs; rw [hpq]
      exact List.take_append_drop _ _
    have he : condition (EffectiveSplitConditions.update p raw) = r := by
      simp only [EffectiveSplitConditions.update,ite_eq_left ht,condition_code]
      rfl
    rw [he]
    refine Or.inl (Or.inr ⟨1,item w 0,Or.inl rfl,?_⟩)
    intro q hrq a ha
    simp only [↓reduceIte] at ha
    apply hdiv.2
    refine ⟨encode q.left,a,?_,?_⟩
    · simpa [word,w,hl] using hrq.1
    · simpa [UniformSplit.base,UniformSplit.program,request,item,word] using ha

theorem next_exists (B : Oracle) : ∃ g : ℕ → ℕ,
    Nat.RecursiveIn {oracleFunction (jump B)} (fun v => Part.some (g v)) ∧
    (∀ (F : ℕ → Oracle) req, Extends F (condition (item req 2)) (condition (g req)) ∧
      (condition (g req)).active = active (item req 2)) ∧
    ∀ (F : ℕ → Oracle) codes x p, Presents B F codes (active p) →
      LocalAgreement.NoDisagreement B F x (condition p) →
      Decisive B F x (condition (g (encode [codes,x,p]))) ∨
        (condition (g (encode [codes,x,p])) = condition p ∧ NoBad B F x p ∧ Outcome B F x p) := by
  obtain ⟨search,hs,hsearch⟩ := guarded_search B
  let raw := fun req => UniformSplit.step B (request (Nat.pair (item req 1) (item req 2)))
  let tag := fun req => if search req = 0 then raw req else Nat.pair 2 (search req-1)
  let g := fun req => EffectiveSplitConditions.update (item req 2) (tag req)
  have hrec : Nat.RecursiveIn {oracleFunction (jump B)} (fun v => Part.some (g v)) := by
    let f := Primrec.fst.comp Primrec.unpair
    let r := Primrec.snd.comp Primrec.unpair
    let req (i : ℕ) := item_primrec.comp Primrec.id (Primrec.const i)
    have hr := _root_.OAI.TuringRigidity.UniformOracle.total_comp (UniformSplit.step_recursive B) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec
      (request_primrec.comp (Primrec₂.natPair.comp (req 1) (req 2))))
    have hm := Primrec.ite (Primrec.eq.comp f (Primrec.const 0)) r
      (Primrec₂.natPair.comp (Primrec.const 2) (Primrec.nat_sub.comp f (Primrec.const 1)))
    have ht := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hm) (_root_.OAI.TuringRigidity.UniformOracle.total_pair hs hr)
    exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (EffectiveSplitConditions.update_primrec.comp f r))
      (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (req 2)) ht)).of_eq (fun req => by
        simp only [Nat.unpair_pair]; rfl)
  refine ⟨g,hrec,fun F req => ?_,fun F codes x p hp hn => ?_⟩
  · unfold g EffectiveSplitConditions.update
    split <;> rw [condition_code]
    · exact ⟨append_extends _ _ _,rfl⟩
    · exact ⟨extends_refl _ _,rfl⟩
  · rcases hsearch (encode [codes,x,p]) with ⟨hz,hno⟩ | ⟨hpos,hbad⟩
    · have hnb : NoBad B F x p := by
        intro w hw
        by_contra hnc
        exact hno ⟨w,(bad_condition_iff hp x w).2 ⟨hw,hnc⟩⟩
      have he : g (encode [codes,x,p]) = EffectiveSplitConditions.update p
          (UniformSplit.step B (request (Nat.pair x p))) := by simp only [g,tag,ite_eq_left hz,raw,item,encodek,Option.getD_some,List.getD_cons_zero,List.getD_cons_succ]
      rw [he]
      rcases raw_spec B F x p hnb with hd | ⟨he,ho⟩
      · exact Or.inl hd
      · exact Or.inr ⟨he,hnb,ho⟩
    · have hz : search (encode [codes,x,p]) ≠ 0 := by omega
      have he : g (encode [codes,x,p]) = EffectiveSplitConditions.update p
          (Nat.pair 2 (search (encode [codes,x,p])-1)) := by simp only [g,tag,ite_eq_right hz,item,encodek,Option.getD_some,List.getD_cons_zero,List.getD_cons_succ]
      rw [he]
      exact Or.inl (bad_decisive B F x p _ hn ((bad_condition_iff hp x _).1 hbad))

theorem pair_exists (B : Oracle) : ∃ f : ℕ → ℕ,
    Nat.RecursiveIn {oracleFunction (jump B)} (fun v => Part.some (f v)) ∧
    ∀ (F : ℕ → Oracle) codes x p, Presents B F codes (active p) →
      Extends F (condition p) (condition (f (encode [codes,x,p]))) ∧
      (UniformAgreement.Disagreement B x (condition (f (encode [codes,x,p]))) ∨
        ((condition (f (encode [codes,x,p]))).active = active p ∧
          LocalAgreement.NoDisagreement B F x (condition p) ∧
          (Decisive B F x (condition (f (encode [codes,x,p]))) ∨
            (condition (f (encode [codes,x,p])) = condition p ∧
              NoBad B F x p ∧ Outcome B F x p)))) := by
  obtain ⟨d,hd,hds⟩ := LocalAgreement.decide_exists B
  obtain ⟨g,hg,hge,hgs⟩ := next_exists B
  let out := fun req => if d req = item req 2 then g req else d req
  have hr : Nat.RecursiveIn {oracleFunction (jump B)} (fun req => Part.some (out req)) := by
    let f := Primrec.fst.comp Primrec.unpair
    let r := Primrec.snd.comp Primrec.unpair
    have hm := Primrec.ite (Primrec.eq.comp f (f.comp r)) (r.comp r) f
    exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hm) (_root_.OAI.TuringRigidity.UniformOracle.total_pair hd
      (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (item_primrec.comp Primrec.id (Primrec.const 2))) hg))).of_eq
        (fun req => by simp only [Nat.unpair_pair]; rfl)
  refine ⟨out,hr,fun F codes x p hp => ?_⟩
  have hdsp := hds F codes x p hp
  have hgep := hge F (encode [codes,x,p])
  have hpitem : item (encode [codes,x,p]) 2 = p := by simp [item]
  rw [hpitem] at hgep
  by_cases he : d (encode [codes,x,p]) = p
  · have hout : out (encode [codes,x,p]) = g (encode [codes,x,p]) := by
      simp only [out,hpitem,he,↓reduceIte]
    rw [hout]
    refine ⟨hgep.1,?_⟩
    rcases hdsp.2 with hdis | ⟨_,hn⟩
    · rw [he] at hdis
      exact Or.inl (disagreement_mono hgep.1 hdis)
    · exact Or.inr ⟨hgep.2,hn,hgs F codes x p hp hn⟩
  · have hout : out (encode [codes,x,p]) = d (encode [codes,x,p]) := by
      simp only [out,hpitem,ite_eq_right he]
    rw [hout]
    exact ⟨hdsp.1,Or.inl (hdsp.2.resolve_right (fun h => he h.1))⟩

end
end TuringRigidity.LocalPair

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_LocalInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.LocalInputs
open Encodable UniformOracle ArithmeticHierarchy OracleJump EncodedForcing CodingForcing
noncomputable section

def Data.pairProcedure (D : Data) (v : ℕ) : ℕ :=
  Classical.choose (LocalPair.pair_exists D.B) (D.request v)

end
end TuringRigidity.LocalInputs

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_LocalStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.LocalStage
open Encodable CodingForcing EncodedForcing FiniteInjury
noncomputable section
attribute [local instance] Classical.propDecidable

def pairProcedure (D : LocalInputs.Data) : ℕ → ℕ := D.pairProcedure

def candidate (D : LocalInputs.Data) (t : ℕ) (p : Condition) : Condition :=
  atLevel (condition (pairProcedure D (Nat.pair t (code (atLevel p t))))) t

def Changes (D : LocalInputs.Data) (t : ℕ) (p : Condition) : Prop :=
  (candidate D t p).left ≠ p.left ∨ (candidate D t p).right ≠ p.right

def scan (D : LocalInputs.Data) (p : Condition) (done : Finset ℕ) (t : ℕ) : ℕ → Option ℕ
  | 0 => none
  | n+1 => if t ∉ done ∧ Changes D t p then some t else scan D p done (t+1) n

def stageAction (D : LocalInputs.Data) (s : ℕ) (p : State) : Option ℕ := scan D (generic D p) p.done 0 s

def stageWord (D : LocalInputs.Data) (s : ℕ) (p : State) : Condition :=
  match stageAction D s p with
  | none => generic D p
  | some t => candidate D t (generic D p)

def advance (D : LocalInputs.Data) (s : ℕ) (p : State) : State where
  condition := atLevel (append (stageWord D s p) [false]) (s+1)
  done := FiniteInjury.update p.done (stageAction D s p)
  seen := FiniteInjurySchedule.reset (insert (FiniteInjurySchedule.visit p.seen) p.seen) (stageAction D s p)

def construction (D : LocalInputs.Data) : ℕ → State
  | 0 => ⟨⟨[],[],rfl,0⟩,∅,∅⟩
  | s+1 => advance D s (construction D s)

def conditions (D : LocalInputs.Data) (s : ℕ) := (construction D s).condition

def proposal (D : LocalInputs.Data) (s : ℕ) (_ : Finset ℕ) : Option ℕ :=
  stageAction D s (construction D s)

end
end TuringRigidity.LocalStage

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_LocalScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.LocalComputability
open Encodable UniformOracle EncodedForcing CodingForcing FiniteInjury StageRecords
noncomputable section
attribute [local instance] Classical.propDecidable

def candidate (D : LocalInputs.Data) (v : ℕ) : ℕ :=
  levelCode (LocalStage.pairProcedure D (Nat.pair (Nat.unpair v).1
    (levelCode (Nat.unpair v).2 (Nat.unpair v).1))) (Nat.unpair v).1

def scanStep (D : LocalInputs.Data) (v : ℕ) : ℕ :=
  let p := (Nat.unpair (Nat.unpair v).1).1
  let d := (Nat.unpair (Nat.unpair v).1).2
  let t := (Nat.unpair (Nat.unpair v).2).1
  let prev := (Nat.unpair (Nat.unpair v).2).2
  let c := candidate D (Nat.pair t p)
  if prev = 0 ∧ t ∉ record d ∧ (left c ≠ left p ∨ right c ≠ right p) then t+1 else prev

def scan (D : LocalInputs.Data) (p d n : ℕ) : ℕ := recur (fun _ => 0) (scanStep D) (Nat.pair p d) n

end
end TuringRigidity.LocalComputability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_LocalComputability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.LocalComputability
open Encodable UniformOracle EncodedForcing CodingForcing FiniteInjury StageRecords
noncomputable section
attribute [local instance] Classical.propDecidable

def stageAction (D : LocalInputs.Data) (s v : ℕ) : ℕ :=
  scan D (genericCanonical D v) (Nat.unpair (Nat.unpair v).2).1 s

def stageWord (D : LocalInputs.Data) (z : ℕ) : ℕ :=
  let s := (Nat.unpair z).1
  let v := (Nat.unpair z).2
  let a := stageAction D s v
  let g := genericCanonical D v
  if a = 0 then g else candidate D (Nat.pair (a-1) g)

def advance (D : LocalInputs.Data) (z : ℕ) : ℕ :=
  let s := (Nat.unpair z).1
  let v := (Nat.unpair z).2
  let d := (Nat.unpair (Nat.unpair v).2).1
  let seen := (Nat.unpair (Nat.unpair v).2).2
  let a := stageAction D s v
  Nat.pair (grow (stageWord D z) s)
    (Nat.pair (doneUpdate d a) (seenReset (seenInsert seen (nextVisit seen)) a))

def construction (D : LocalInputs.Data) : ℕ → ℕ :=
  recur (fun _ => initial) (fun v => advance D (Nat.unpair v).2) 0

end
end TuringRigidity.LocalComputability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_LocalLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.LocalLimits
open Encodable UniformOracle ArithmeticHierarchy EncodedForcing CodingForcing FiniteInjury
open LocalStage
noncomputable section
attribute [local instance] Classical.propDecidable

def G₀ (D : LocalInputs.Data) : Oracle := leftLimit (conditions D)
def G₁ (D : LocalInputs.Data) : Oracle := rightLimit (conditions D)

end
end TuringRigidity.LocalLimits

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_PersistentLocality
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.PersistentLocality
open IdealInterpretation IdealLocality PersistentRestrictions OracleJump
noncomputable section

def ideal (I : CountableIdeal) : DegreeIdeal :=
  ⟨I.carrier,I.nonempty,fun {_ _} h hmem => I.lower h hmem,
    fun {_ _} h₁ h₂ => I.join_mem h₁ h₂⟩

def bridge (I : CountableIdeal) : I ≃o ideal I where
  toFun x := ⟨x.val,x.property⟩
  invFun x := ⟨x.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

def lift {I : CountableIdeal} (ρ : I ≃o I) : ideal I ≃o ideal I :=
  (bridge I).symm.trans (ρ.trans (bridge I))

def unlift {I : CountableIdeal} (ρ : ideal I ≃o ideal I) : I ≃o I :=
  (bridge I).trans (ρ.trans (bridge I).symm)

end
end TuringRigidity.PersistentLocality

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericalIdeal
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.NumericalIdeal
open EncodedForcing OracleJump IndexPresentation IdealInterpretation IdealLocality
open PersistentRestrictions PersistentLocality PersistentPresentation
noncomputable section

def decode (H : Oracle) (hc : JumpCode H) : CountableIdeal where
  carrier := Set.range (fun n => degree (columns H n))
  nonempty := ⟨degree (columns H 0),0,rfl⟩
  countable := Set.countable_range _
  lower := by
    intro a b hab hb
    obtain ⟨n,rfl⟩ := hb
    obtain ⟨e,he,hv⟩ := value_surjective (columns H n) a hab
    obtain ⟨m,hm⟩ := hc.lower n e he
    exact ⟨m,hm.symm.trans hv⟩
  join_mem := by
    intro a b ha hb
    obtain ⟨n,rfl⟩ := ha
    obtain ⟨m,rfl⟩ := hb
    obtain ⟨k,hk⟩ := hc.join n m
    exact ⟨k,hk.symm⟩

end
end TuringRigidity.NumericalIdeal

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GroundDegreePresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel EncodedForcing PersistentRestrictions PersistentPresentation OracleJump
universe u

theorem sourceT_zero_real (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    FixedArithmetic.zero ∈ modelReals M := by
  have he : realCode.{u} FixedArithmetic.zero = ∅ := by
    apply ZFSet.ext; intro x
    constructor
    · intro hx
      obtain ⟨n,rfl⟩ := (mem_omega x).mp (realCode_subset _ hx)
      have hn := (natSet_mem_realCode FixedArithmetic.zero n).mp hx
      exact Bool.noConfusion hn
    · exact fun hx => False.elim (ZFSet.notMem_empty _ hx)
  change realCode FixedArithmetic.zero ∈ M
  rw [he]
  exact hM _ (sourceT_omega_mem M hM hT) _ ZFSet.omega_zero

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SentenceInlining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

def bindComputed : ℕ → (ℕ → SentenceForm) → SentenceForm → SentenceForm
  | 0, _, p => p
  | n+1, f, p => .ex (.conj (f n)
      (bindComputed n (fun i => (f i).rename skipValue) p))

noncomputable def subsetBody (n out a : ℕ) (p : SentenceForm) : SentenceForm :=
  SentenceForm.all (SentenceForm.iff (.member 0 (n+out+1))
    (.conj (.member 0 (n+a+1)) (fromBounded (setBounded p (n+a+1) id))))

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_RealProjectionSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelArithmetic SetModelReals
universe u

noncomputable def projectionFormula (bs : List Bool) (out w a d P : ℕ) : SentenceForm :=
  SentenceForm.all (SentenceForm.iff (.member 0 (out+1))
    (fromBounded (projectionMember bs (w+1) (a+1) (d+1) (P+1) 0)))

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_SingleRealConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelArithmetic
universe u

noncomputable def Construction.singleFormula : Construction.{u} → List Bool →
    ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ) → SentenceForm
  | .reals, _, out, R, _, _, _, _, _ => .equal out R
  | .parameter, bs, out, _, P, w, a, d, _ => projectionFormula bs out w a d P
  | .define _ n p c, bs, out, R, P, w, a, d, r => bindComputed n
      (fun i => if h : i < n then
        (c ⟨i,h⟩).singleFormula (bs ++ partBits i) 0 (R+1) (P+1) (w+1) (a+1) (d+1)
          (fun k => r (Nat.pair i k+1)+1)
        else .equal 0 0)
      (subsetBody n out (r 0) p)

noncomputable def Construction.singleMembership (t : Construction.{u}) : SentenceForm :=
  .ex (.conj (t.singleFormula [] 0 2 3 4 5 6 (fun k => k+7)) (.member 1 0))

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_CanonicalOmegaSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

noncomputable def canonicalOmega (w : ℕ) : SentenceForm :=
  .conj (fromBounded (inductiveSetFormula w))
    (SentenceForm.all (SentenceForm.imp (fromBounded (inductiveSetFormula 0))
      (fromBounded (.subset (w+1) 0))))

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_BindCanonicalArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelArithmetic
universe u

noncomputable def bindArithmetic (p : SentenceForm) : SentenceForm :=
  .ex (.conj (canonicalOmega 0)
    (.ex (.conj (fromBounded (squareFormula 1 0))
      (.ex (.conj (fromBounded (additionSystemFormula 2 1 0)) p)))))

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticFreeConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelArithmetic
universe u

noncomputable def Construction.arithmeticFreeMembership (t : Construction.{u}) : SentenceForm :=
  bindArithmetic (t.singleMembership.rename arithmeticSlots)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

noncomputable def ordinalSentence : SentenceForm := fromBounded (ordinalFormula 0)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalOrderType
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory
universe u

noncomputable def ordinalRange (d r : ZFSet.{u}) (wf : WellFounded (Rel d r)) : ZFSet.{u} :=
  ZFSet.range (fun s : Conditions d => value d r wf (label d s))

noncomputable def orderType (d r : ZFSet.{u}) (wf : WellFounded (Rel d r)) : Ordinal.{u} :=
  (ordinalRange d r wf).rank

end TuringRigidity.RelationCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalProductSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel
universe u

noncomputable def productSentence : SentenceForm :=
  .ex (.ex (.ex (fromBounded (productMatrix 3 4 5 2 1 0))))

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OmegaStageSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

noncomputable def ordinalProductAt (v a b : ℕ) : SentenceForm :=
  productSentence.rename (fun i => if i = 0 then v else if i = 1 then a else b)

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OmegaGraphSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

noncomputable def omegaGraphSentence (s w d r f : ℕ) : SentenceForm :=
  .conj (fromBounded (ordinalFormula d))
    (.conj (fromBounded (.functionGraph f d r))
      (ordinalAllMem d (ordinalAllMem (r+1)
        (.imp (fromBounded (.pairMem 1 0 (f+2)))
          (.ex (.conj (fromBounded (omegaStageMatrix (s+3) (f+3) (r+3) 2 0))
            (.conj (fromBounded (ordinalFormula 0)) (ordinalProductAt 1 0 (w+3)))))))))

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OmegaPowerSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

noncomputable def omegaPowerBody : SentenceForm :=
  .conj (canonicalOmega 4)
    (.conj (fromBounded (.conj (ordinalOneMatrix 3) (.equal 0 6)))
      (.conj (omegaGraphSentence 3 4 0 1 2)
        (fromBounded (omegaStageMatrix 3 2 1 6 5))))

noncomputable def omegaPowerSentence : SentenceForm :=
  .ex (.ex (.ex (.ex (.ex omegaPowerBody))))

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_LargestOrdinalSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

noncomputable def largestOrdinalSentence : SentenceForm :=
  .conj ordinalSentence (.all (.imp ordinalSentence (.disj (.member 0 1) (.equal 0 1))))

noncomputable def bindLargestOrdinal (p : SentenceForm) : SentenceForm :=
  .ex (.conj largestOrdinalSentence p)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GlobalJumpRestriction
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.PersistentLocality
open IdealInterpretation IdealLocality PersistentRestrictions OracleJump

def fullIdeal : DegreeIdeal :=
  ⟨Set.univ,⟨⊥,Set.mem_univ _⟩,fun _ _ => Set.mem_univ _,fun _ _ => Set.mem_univ _⟩

def fullEquiv : Degree ≃o fullIdeal where
  toFun a := ⟨a,Set.mem_univ _⟩
  invFun a := a.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

end TuringRigidity.PersistentLocality

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericBinding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.NumericSyntax
open ElementaryModel BoundedSetTheory TransitiveNameModel BoundedDefinability RelativeConstructible
universe u

noncomputable def bindNumbers (p : SentenceForm) : SentenceForm :=
  .ex (.conj (canonicalOmega 0)
    (.ex (.conj (fromBounded (squareFormula 1 0))
      (.ex (.conj (FullSetForcing.ownPower 1 0)
        (.ex (.conj (fromBounded (.empty 0)) p)))))))

end TuringRigidity.NumericSyntax

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ElementaryModelIdeal
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse SetDegreeDecoding PersistentRestrictions OracleJump
universe u

noncomputable def modelIdeal (M : ZFSet.{u}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M) :
    CountableIdeal where
  carrier := {b | ∃ A ∈ modelReals M, degree A = b}
  nonempty := ⟨degree FixedArithmetic.zero,FixedArithmetic.zero,sourceT_zero_real M hM hT,rfl⟩
  countable := (model_reals_countable M).image degree
  lower := by
    intro a b hab hb
    obtain ⟨A,rfl⟩ := degree_surjective a
    obtain ⟨B,hB,rfl⟩ := hb
    exact ⟨A,sourceT_real_lower M hM hT hB hab,rfl⟩
  join_mem := by
    rintro a b ⟨A,hA,rfl⟩ ⟨B,hB,rfl⟩
    exact ⟨TuringRigidity.join A B,sourceT_real_join M hM hT hA hB,rfl⟩

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_CanonicalRealsSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

noncomputable def canonicalReals (r : ℕ) : SentenceForm :=
  .ex (.conj (canonicalOmega 0) (FullSetForcing.ownPower 0 (r+1)))

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_OwnRealsConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

noncomputable def Construction.ownRealsMembership (t : Construction.{u}) : SentenceForm :=
  .ex (.conj (canonicalReals 0) (t.arithmeticFreeMembership.rename t.ownRealsSlots))

noncomputable def Construction.ownRealsInputs (t : Construction.{u}) (R : ZFSet.{u})
    (P : Oracle) : ℕ → ZFSet.{u} :=
  cons (realCode P) (fun k => match t.ordinalData k with
    | none => realCode P
    | some o => level R o)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalInputSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

noncomputable def ownStageFormula (p : SentenceForm) : SentenceForm :=
  .ex (.conj (canonicalReals 0) (p.rename (fun i => match i with | 0 => 1 | 1 => 2 | _ => 0)))

noncomputable def Construction.ordinalInputs (t : Construction.{u}) (P : Oracle) : ℕ → ZFSet.{u} :=
  cons (realCode P) (fun k => if k < t.ownRealsMembership.bound then
    match t.ordinalData k with | none => realCode P | some o => o.toZFSet
    else realCode P)

noncomputable def Construction.ordinalInputFormula (t : Construction.{u}) (p : SentenceForm) (k : ℕ) : SentenceForm :=
  match t.ordinalData k with
  | none => .equal 0 2
  | some _ => (ownStageFormula p).rename (fun i => if i = 0 then 0 else k+3)

noncomputable def Construction.ordinalMembership (t : Construction.{u}) (p : SentenceForm) : SentenceForm :=
  bindComputed t.ownRealsMembership.bound (t.ordinalInputFormula p)
    (t.ownRealsMembership.rename (ordinalBodySlots t.ownRealsMembership.bound))

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalSumSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel
universe u

noncomputable def sumSentence : SentenceForm :=
  .ex (.ex (.ex (.ex (.ex (fromBounded (sumMatrix 5 6 7 4 3 2 1 0))))))

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalSumClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel
universe u

noncomputable def doubleSentence : SentenceForm :=
  sumSentence.rename (fun i => if i = 0 then 0 else 1)

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalCodeOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

noncomputable def codePowerAt (y x : ℕ) : SentenceForm :=
  omegaPowerSentence.rename (fun i => if i = 0 then y else x)

noncomputable def codeSumAt (c a b : ℕ) : SentenceForm :=
  sumSentence.rename (fun i => if i = 0 then c else if i = 1 then a else b)

noncomputable def codeScaleAt (twice : Bool) (y x : ℕ) : SentenceForm :=
  if twice then doubleSentence.rename (fun i => if i = 0 then y else x) else .equal y x

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalCodeBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

noncomputable def codeBranchBody (twice : Bool) : SentenceForm :=
  .conj (fromBounded (.successor 3 5))
    (.conj (codePowerAt 2 3) (.conj (codePowerAt 1 6)
      (.conj (codeScaleAt twice 0 2) (codeSumAt 4 0 1))))

noncomputable def codeBranchSentence (twice : Bool) : SentenceForm :=
  .ex (.ex (.ex (.ex (codeBranchBody twice))))

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalPairSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

noncomputable def pairCodeSentence : SentenceForm :=
  .conj (fromBounded (.conj (ordinalFormula 1) (ordinalFormula 2)))
    (.disj (.conj (fromBounded (.subset 2 1)) (codeBranchSentence false))
      (.conj (.neg (fromBounded (.subset 2 1)))
        ((codeBranchSentence true).rename (fun i => if i = 0 then 0 else if i = 1 then 2 else 1))))

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalVectorSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

noncomputable def vectorCodeSentence : ℕ → SentenceForm
  | 0 => fromBounded (ordinalOneMatrix 0)
  | n+1 => .ex (.conj
      (pairCodeSentence.rename (fun i => if i = 0 then 1 else if i = 1 then 2 else 0))
      ((vectorCodeSentence n).rename vectorTailSlots))

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalPaddingSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

noncomputable def paddedCodeSentence (n : ℕ) : SentenceForm :=
  .ex (.ex (.conj
    (pairCodeSentence.rename (fun i => if i = 0 then 2 else if i = 1 then 1 else 0))
    ((vectorCodeSentence n).rename vectorTailSlots)))

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalEntryBinding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

def codeBindEntries : ℕ → SentenceForm → SentenceForm
  | 0, p => p
  | n+1, p => .ex (codeBindEntries n p)

noncomputable def paddedEntrySentence (n : ℕ) (k : Fin n) : SentenceForm :=
  codeBindEntries n (.conj (.equal n k.val)
    ((paddedCodeSentence n).rename (entryCodeSlots n)))

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalDecoderDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

noncomputable def largestPaddedEntrySentence (n : ℕ) (k : Fin n) : SentenceForm :=
  bindLargestOrdinal ((paddedEntrySentence n k).rename (fun i => if i = 0 then 1 else 0))

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_LimitOmegaGraphSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open OrdinalCoding
universe u

noncomputable def omegaNextPairSentence : SentenceForm :=
  .ex (.ex (.ex (.conj
    (fromBounded (.conj (ordinalFormula 2) (.conj (.successor 0 2) (.orderedPair 3 2 1))))
    (codePowerAt 1 0))))

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_TrimmedOrderDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

noncomputable def trimmedProductDomainSentence : SentenceForm :=
  fromBounded (.existsMem 2 (.existsMem 2 (.orderedPair 2 1 0)))

noncomputable def trimmedProductRelationSentence : SentenceForm :=
  .ex (.ex (fromBounded (.conj (.orderedPair 2 1 0) (productLessFormula 3 4 1 0))))

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_TrimmedProductGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalCoding
universe u

noncomputable def trimmedProductGraphSentence : SentenceForm :=
  .ex (.ex (.ex (.ex (.ex (.conj
    (fromBounded (.conj (.member 4 7) (.conj (.member 3 6)
      (.conj (.orderedPair 2 4 3) (.orderedPair 5 2 1)))))
    (.conj (ordinalProductAt 0 6 4) (codeSumAt 1 0 3)))))))

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_TrimmedSumDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

noncomputable def trimmedSumDomainSentence : SentenceForm := fromBounded
  (.disj (.existsMem 1 (.orderedPair 1 4 0)) (.existsMem 2 (.orderedPair 1 5 0)))

noncomputable def trimmedSumRelationSentence : SentenceForm :=
  .ex (.ex (fromBounded (.conj (.orderedPair 2 1 0) (sumLessFormula 3 4 5 6 1 0))))

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_TrimmedSumGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalCoding
universe u

noncomputable def trimmedSumGraphSentence : SentenceForm := .ex (.ex (.ex
  (.disj (fromBounded (.conj (.member 2 4) (.conj (.orderedPair 1 6 2)
    (.conj (.orderedPair 3 1 0) (.equal 0 2)))))
    (.conj (fromBounded (.conj (.member 2 5) (.conj (.orderedPair 1 7 2)
      (.orderedPair 3 1 0)))) (codeSumAt 0 4 2)))))

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BoundedOmegaGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalCoding
universe u

noncomputable def boundedOmegaNextPairSentence : SentenceForm :=
  .conj (.ex (.conj (.member 0 2) (.ex (fromBounded (.orderedPair 2 1 0))))) omegaNextPairSentence

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_DecodedConstructionSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel OrdinalCoding
universe u
attribute [local irreducible] Construction.ownRealsMembership SentenceForm.bound

noncomputable def Construction.ordinalVector (t : Construction.{u}) :
    Fin t.ownRealsMembership.bound → Ordinal.{u} := fun k => (t.ordinalData k).getD 0

noncomputable def Construction.decodedOrdinalInput (t : Construction.{u}) (k : ℕ) : SentenceForm :=
  if hk : k < t.ownRealsMembership.bound then
    match t.ordinalData k with
    | none => .equal 0 2
    | some _ => largestPaddedEntrySentence t.ownRealsMembership.bound ⟨k,hk⟩
  else .equal 0 2

noncomputable def Construction.decodedOrdinalBody (t : Construction.{u}) (q : SentenceForm) : SentenceForm :=
  bindComputed t.ownRealsMembership.bound t.decodedOrdinalInput
    (q.rename (ordinalBodySlots t.ownRealsMembership.bound))

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_CommonExtensionProgram
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing RecursiveNames
open CohenColumnRealName ElementaryModel PersistentRestrictions SetDegreeDecoding BoundedForcing
open GenericIdentity
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

def ColumnRealizesExtension (M K a E : ZFSet.{0}) (A : Oracle) : Prop :=
  ∃ H : GenericFilter (Conditions (poset K)), GroundGeneric M H ∧
    genericExtensionSet M (poset K) H.carrier = E ∧
    (realName K a).val H.carrier = realCode A

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalSameNameGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalSameNameGeneric
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalGeneratedAlgebra InternalBooleanProjection InternalBooleanGeneric InternalBooleanDense
open InternalBooleanBits InternalProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

theorem projected_condition (M c B Q A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) (p : Conditions c) (hp : p ∈ G.carrier) :
    ∃ q ∈ (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier,
      label (positive A) q = project c A (basicCode c (label c p)) := by
  let b := basicCode c (label c p)
  have hbM := basicCode_mem M c _ hM hT hc (label_mem c p)
  have hbc : IsCode c b := regular_isCode c _
  have hpb := subset_project c A b hbc.1 (mem_basicCode c _ (label_mem c p))
  have hPA := project_mem_part M c B Q A b hM hT hc hBM hAM hbM hB hQ hA
  have hn : project c A b ≠ ∅ := fun h => ZFSet.notMem_empty _ (h ▸ hpb)
  obtain ⟨q,hq⟩ := label_surjective (positive A) (ZFSet.mem_sep.mpr ⟨hPA,hn⟩)
  refine ⟨q,?_,hq⟩
  change Hit G (label (positive A) q)
  rw [hq]
  exact ⟨p,hp,hpb⟩

end TuringRigidity.InternalSameNameGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalQuotientConditions
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalQuotientConditions
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalBooleanProjection InternalBooleanDense InternalProjectedGeneric InternalBooleanGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

theorem original_condition_mem (M c B Q A : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) (p : Conditions c) (hp : p ∈ G.carrier) :
    label c p ∈ conditions c A (genericFilterSet (positive A)
      (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier) := by
  obtain ⟨q,hq,he⟩ := InternalSameNameGeneric.projected_condition M c B Q A
    hM hT hc hBM hAM hB hQ hA G p hp
  exact ZFSet.mem_sep.mpr ⟨label_mem c p,
    (mem_genericFilterSet _ _ _).mpr ⟨q,hq,he⟩⟩

end TuringRigidity.InternalQuotientConditions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalQuotientGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalQuotientGeneric
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AtomicForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalBooleanProjection InternalBooleanDense InternalProjectedGeneric InternalBooleanGeneric
open InternalBooleanTop InternalQuotientRequirement
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

noncomputable def quotient (M c B Q A : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) :
    GenericFilter (Conditions (InternalQuotientConditions.conditions c A
      (genericFilterSet (positive A) (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier))) :=
  RestrictedForcingFilter.restrict c _ (InternalQuotientConditions.conditions_subset c A _) G
    (InternalQuotientConditions.original_condition_mem M c B Q A hM hT hc hBM hAM hB hQ hA G)

end TuringRigidity.InternalQuotientGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_OriginalRealDefinitionTransport
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OriginalRealDefinitionTransport
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open CohenGroundPoset InternalCountableOrdinals RelativeConstructible ElementaryModel
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] CohenNiceNameConstruction.cohenTop

def Transported (M K : ZFSet.{0})
    (G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (f : Name (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (X : ZFSet.{0}) (δ : Ordinal.{0}) (φ : SentenceForm) : Prop :=
    let c := conditions (ZFSet.prod K ZFSet.omega)
    let N := RealGeneratedModel.hull M X
    RealGeneratedModel.Contains M X N ∧
      ∃ GX : GenericFilter (Conditions c), AtomicForcing.GroundGeneric N GX ∧
        genericExtensionSet N c GX.carrier = genericExtensionSet M c G.carrier ∧
        ∃ fX : Name (Conditions c), fX.encode (label c) ∈ N ∧
          fX.val GX.carrier = f.val G.carrier ∧
          (Name.check δ.toZFSet : Name (Conditions c)).encode (label c) ∈ N ∧
          (Name.check X : Name (Conditions c)).encode (label c) ∈ N ∧
          (Name.check δ.toZFSet : Name (Conditions c)).val GX.carrier = δ.toZFSet ∧
          (Name.check X : Name (Conditions c)).val GX.carrier = X ∧
          X ∈ level (groundReals (genericExtensionSet N c GX.carrier)) δ ∧
          fX.val GX.carrier = definedSubset
            (level (groundReals (genericExtensionSet N c GX.carrier)) δ)
              φ (fun _ : Fin φ.bound => X)

end TuringRigidity.OriginalRealDefinitionTransport

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_PrescribedGenericRestriction
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding
open PersistentRestrictions ArithmeticTree CountableForcing
universe u

theorem modelIdeal_inclusion (M N : ZFSet.{u})
    [Countable (Conditions M)] [Countable (Conditions N)]
    (hM : Transitive M) (hTM : SourceT M) (hN : Transitive N) (hTN : SourceT N)
    (hMN : M ⊆ N) : (modelIdeal M hM hTM).carrier ⊆ (modelIdeal N hN hTN).carrier := by
  rintro d ⟨A,hA,rfl⟩
  refine ⟨A,?_,rfl⟩
  change realCode A ∈ N
  exact hMN hA

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalUncountableSentence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalUncountableSentence
open TransitiveNameModel BoundedSetTheory ElementaryModel

noncomputable def countableSentence (A ω : ℕ) : SentenceForm :=
  .ex (fromBounded (ontoMatrix 0 (ω+1) (A+1)))

noncomputable def uncountableOrdinalSentence : SentenceForm :=
  .conj (fromBounded (.conj (.transitive 0) (.allMem 0 (.transitive 0))))
    (.conj (.neg (fromBounded (.empty 0))) (.neg (countableSentence 0 1)))

end TuringRigidity.InternalUncountableSentence

end OAI
end


