-- Prove2me | Definitions.Def_OAIQ064A001
-- name    : OAIQ064A001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T00:28:28.655175+00:00
-- url     : https://prove2.me/theorems/1f5ce23e-6683-4446-a727-06ee71f7c127
-- title:
--   Definitions bundle OAIQ064A001 of the split of OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 478 declarations of OpenAI's Lean: 312 definitions, 10 inductive types or structures, 10 instances and 146 theorems. The definitions and types are `OAI.TuringRigidity.BinarySeries.foldNumeral`, `OAI.TuringRigidity.BooleanExpressionCertificate.children`, `OAI.TuringRigidity.BooleanExpressionTruth.truthSlots`, `OAI.TuringRigidity.BorelGeneric.Ext`, `OAI.TuringRigidity.BorelGeneric.next`, `OAI.TuringRigidity.BorelGeneric.stage`, `OAI.TuringRigidity.BorelGeneric.word`, `OAI.TuringRigidity.BoundedDefinability.bindSlots`, `OAI.TuringRigidity.BoundedDefinability.mix`, `OAI.TuringRigidity.BoundedDefinability.slotMap`, `OAI.TuringRigidity.BoundedForcing.WitnessCode.vars`, `OAI.TuringRigidity.BoundedForcing.push`, `OAI.TuringRigidity.BoundedForcing.truncate`, `OAI.TuringRigidity.BoundedSetTheory.AdditionTrace`, `OAI.TuringRigidity.BoundedSetTheory.Choice`, `OAI.TuringRigidity.BoundedSetTheory.ChoiceGraph`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTerm.Functional`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTerm.generatedRange`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTerm.inverseCover`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTerm.labelGraph`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTuple.Closed`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTuple.FiniteCode`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTuple.code`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTuple.elements`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTuple.outputFirst`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTuple.requests`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTuple.rotate`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTuple.space`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTuple.takeEnv`, `OAI.TuringRigidity.BoundedSetTheory.Formula.arithmeticVars`, `OAI.TuringRigidity.BoundedSetTheory.Formula.iterationOuterVars`, `OAI.TuringRigidity.BoundedSetTheory.Formula.iterationVars`, `OAI.TuringRigidity.BoundedSetTheory.Formula.modelIterationOuterVars`, `OAI.TuringRigidity.BoundedSetTheory.Formula.modelIterationVars`, `OAI.TuringRigidity.BoundedSetTheory.Formula.oracleParameterVars`, `OAI.TuringRigidity.BoundedSetTheory.Formula.pairLeftTerm`, `OAI.TuringRigidity.BoundedSetTheory.Formula.pairRightTerm`, `OAI.TuringRigidity.BoundedSetTheory.Formula.pairVars`, `OAI.TuringRigidity.BoundedSetTheory.Formula.unaryVars`, `OAI.TuringRigidity.BoundedSetTheory.Infinity` and 282 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DegreeRigidity_CohenForcing_BoundedForcing`, `DegreeRigidity_CohenForcing_CohenAntichainSelector`, `DegreeRigidity_CohenForcing_CohenAntichainSequence`, `DegreeRigidity_CohenForcing_CohenAntichainStages`, `DegreeRigidity_CohenForcing_CohenBorelForcing`, `DegreeRigidity_CohenForcing_CohenChainCondition`, `DegreeRigidity_CohenForcing_CohenColumnRealValue`, `DegreeRigidity_CohenForcing_CohenColumns`, `DegreeRigidity_CohenForcing_CohenCoordinates`, `DegreeRigidity_CohenForcing_CohenHalting`, `DegreeRigidity_CohenForcing_CohenInternalDecision`, `DegreeRigidity_CohenForcing_CohenPartitionBridge`, `DegreeRigidity_CohenForcing_CohenProductSplitting`, `DegreeRigidity_CohenForcing_CohenRecursiveName`, `DegreeRigidity_CohenForcing_CohenSizeLevels`, `DegreeRigidity_CohenForcing_CohenSymmetry`, `DegreeRigidity_CohenForcing_ForcingWitnessCollection`, `DegreeRigidity_Computability_ArithmeticFreeConstruction`, `DegreeRigidity_Computability_ArithmeticParameterFormula`, `DegreeRigidity_Computability_ArithmeticSetSyntax`, `DegreeRigidity_Computability_ArithmeticTables`, `DegreeRigidity_Computability_BinaryMachine`, `DegreeRigidity_Computability_BranchFrequency`, `DegreeRigidity_Computability_BranchMachine`, `DegreeRigidity_Computability_CutTranscript`, `DegreeRigidity_Computability_Cuts`, `DegreeRigidity_Computability_EffectiveRecovery`, `DegreeRigidity_Computability_Introreducible`, `DegreeRigidity_Computability_OracleEnumeration`, `DegreeRigidity_Computability_RealProjectionSyntax`, `DegreeRigidity_Constructibility_ConstructibleBase`, `DegreeRigidity_Constructibility_ConstructibleGroundReals`, `DegreeRigidity_Constructibility_ConstructibleSeparation`, `DegreeRigidity_Constructibility_ConstructionInputData`, `DegreeRigidity_Constructibility_HierarchyCertificatePower`, `DegreeRigidity_Constructibility_HierarchyGraph`, `DegreeRigidity_Constructibility_RelativeSigmaSchemas`, `DegreeRigidity_Constructibility_UniformHeightDomains`, `DegreeRigidity_Effective_CodingColumns`, `DegreeRigidity_Effective_CodingForcing`, `DegreeRigidity_Effective_CodingOnePoint`, `DegreeRigidity_Effective_CodingSplitSearch`, `DegreeRigidity_Effective_CodingSplitting`, `DegreeRigidity_Effective_FiniteCodeBound`, `DegreeRigidity_Effective_FiniteInjury`, `DegreeRigidity_Effective_FiniteInjurySchedule`, `DegreeRigidity_Effective_FiniteTuple`, `DegreeRigidity_Effective_GuardedScan`, `DegreeRigidity_Effective_LocalColumnIndices`, `DegreeRigidity_Effective_LocalScan`, `DegreeRigidity_Effective_OrderMatrixRecursive`, `DegreeRigidity_Effective_PartialComputability`, `DegreeRigidity_Effective_PrefixComputability`, `DegreeRigidity_Effective_ProgramSelection`, `DegreeRigidity_Effective_ProgramTopology`, `DegreeRigidity_Effective_RecursiveInfiniteSubset`, `DegreeRigidity_Effective_StageRecords`, `DegreeRigidity_Effective_TupleLookupAdequacy`, `DegreeRigidity_Effective_TupleRelation`, `DegreeRigidity_Effective_UniformCohenJump`, `DegreeRigidity_Effective_UniformJumpSimulation`, `DegreeRigidity_Effective_UniformOracle`, `DegreeRigidity_Effective_UniformPair`, `DegreeRigidity_Effective_UniformProgram`, `DegreeRigidity_Effective_UniformPrograms`, `DegreeRigidity_Model`, `DegreeRigidity_OrdinalCodes_CanonicalAdditionSyntax`, `DegreeRigidity_OrdinalCodes_CodeBranchCertificates`, `DegreeRigidity_OrdinalCodes_IndexTuples`, `DegreeRigidity_OrdinalCodes_NaturalAdditionTrace`, `DegreeRigidity_OrdinalCodes_NaturalDefinitions`, `DegreeRigidity_OrdinalCodes_NaturalIterationFormula`, `DegreeRigidity_OrdinalCodes_NaturalIterationTrace`, `DegreeRigidity_OrdinalCodes_NaturalMultiplicationFormula`, `DegreeRigidity_OrdinalCodes_NaturalPairingFormula`, `DegreeRigidity_OrdinalCodes_NaturalTermFormula`, `DegreeRigidity_OrdinalCodes_NumericStage`, `DegreeRigidity_OrdinalCodes_OmegaPowerCertificates`, `DegreeRigidity_OrdinalCodes_OmegaPowerStage`, `DegreeRigidity_OrdinalCodes_OrdinalCodeBranch`, `DegreeRigidity_OrdinalCodes_OrdinalCodeOperations`, `DegreeRigidity_OrdinalCodes_OrdinalCut`, `DegreeRigidity_OrdinalCodes_OrdinalEntryBinding`, `DegreeRigidity_OrdinalCodes_OrdinalInputSyntax`, `DegreeRigidity_OrdinalCodes_OrdinalOrderType`, `DegreeRigidity_OrdinalCodes_OrdinalOrderTypeSyntax`, `DegreeRigidity_OrdinalCodes_OrdinalPairCode`, `DegreeRigidity_OrdinalCodes_OrdinalProductPresentation`, `DegreeRigidity_OrdinalCodes_OrdinalProductSets`, `DegreeRigidity_OrdinalCodes_OrdinalSumPresentation`, `DegreeRigidity_OrdinalCodes_OrdinalSumSets`, `DegreeRigidity_OrdinalCodes_OrdinalVectorSyntax`, `DegreeRigidity_OrdinalCodes_RankGraphConstruction`, `DegreeRigidity_OrdinalCodes_RankOrdinal`, `DegreeRigidity_OrdinalCodes_RankRecursion`, `DegreeRigidity_OrdinalCodes_Recurrence`, `DegreeRigidity_OrdinalCodes_SumCertificates`, `DegreeRigidity_OrdinalCodes_VectorCodeCertificates`, `DegreeRigidity_Representation_BorelGeneric`, `DegreeRigidity_Representation_Category`, `DegreeRigidity_Representation_CategoryReduction`, `DegreeRigidity_Representation_GenericCoding`, `DegreeRigidity_Representation_GenericFilterName`, `DegreeRigidity_Representation_NativePersistenceSyntax`, `DegreeRigidity_Representation_RealGeneratedPart`, `DegreeRigidity_SetModels_ChoiceFromOrdinalCover`, `DegreeRigidity_SetModels_ChoiceTrace`, `DegreeRigidity_SetModels_ChoiceTraceExtension`, `DegreeRigidity_SetModels_ChoiceTraceFormula`, `DegreeRigidity_SetModels_CollapseCertificate`, `DegreeRigidity_SetModels_CollapseCoding`, `DegreeRigidity_SetModels_CountableElementaryHull`, `DegreeRigidity_SetModels_CountableSetReal`, `DegreeRigidity_SetModels_DenseInclusionExtension`, `DegreeRigidity_SetModels_ElementaryLanguage`, `DegreeRigidity_SetModels_ElementarySchemas`, `DegreeRigidity_SetModels_ExtensionBasicAxioms`, `DegreeRigidity_SetModels_ExtensionSigmaReplacement`, `DegreeRigidity_SetModels_FiniteClosure`, `DegreeRigidity_SetModels_FiniteOrdinalCode`, `DegreeRigidity_SetModels_FiniteSkolem`, `DegreeRigidity_SetModels_GeneratedHull`, `DegreeRigidity_SetModels_IdealInterpretation`, `DegreeRigidity_SetModels_InternalBooleanBits`, `DegreeRigidity_SetModels_InternalBooleanDense`, `DegreeRigidity_SetModels_InternalBooleanGeneric`, `DegreeRigidity_SetModels_InternalBooleanGraph`, `DegreeRigidity_SetModels_InternalBooleanProjection`, `DegreeRigidity_SetModels_InternalBooleanSyntax`, `DegreeRigidity_SetModels_InternalChoice`, `DegreeRigidity_SetModels_InternalCollapseConditions`, `DegreeRigidity_SetModels_InternalCollapseDense`, `DegreeRigidity_SetModels_InternalColumnProjection`, `DegreeRigidity_SetModels_InternalCountableClosure`, `DegreeRigidity_SetModels_InternalCountableEnumeration`, `DegreeRigidity_SetModels_InternalCountableFiniteUnion`, `DegreeRigidity_SetModels_InternalCountableMap`, `DegreeRigidity_SetModels_InternalCountableOrdinals`, `DegreeRigidity_SetModels_InternalCoverInjection`, `DegreeRigidity_SetModels_InternalDenseInclusion`, `DegreeRigidity_SetModels_InternalFiniteEnumeration`, `DegreeRigidity_SetModels_InternalFiniteExhaustion`, `DegreeRigidity_SetModels_InternalGeneratedAlgebra`, `DegreeRigidity_SetModels_InternalInfinity`, `DegreeRigidity_SetModels_InternalInverseGraph`, `DegreeRigidity_SetModels_InternalMinimalSelector`, `DegreeRigidity_SetModels_InternalNameEvaluation`, `DegreeRigidity_SetModels_InternalOrderIsoTransport`, `DegreeRigidity_SetModels_InternalOrdinalSubset`, `DegreeRigidity_SetModels_InternalProductBijection`, `DegreeRigidity_SetModels_InternalProjectedGeneric`, `DegreeRigidity_SetModels_InternalQuotientConditions`, `DegreeRigidity_SetModels_InternalQuotientRequirement`, `DegreeRigidity_SetModels_InternalRegularAlgebra`, `DegreeRigidity_SetModels_InternalRegularOperations`, `DegreeRigidity_SetModels_InternalRegularOrder`, `DegreeRigidity_SetModels_InternalRelationCollapse`, `DegreeRigidity_SetModels_InternalRelationSelection`, `DegreeRigidity_SetModels_InternalSequenceRange`, `DegreeRigidity_SetModels_InternalSingletonColumn`, `DegreeRigidity_SetModels_InternalStructureCollapse`, `DegreeRigidity_SetModels_InternalUniformization`, `DegreeRigidity_SetModels_ModelIterationFormula`, `DegreeRigidity_SetModels_ModelIterationTrace`, `DegreeRigidity_SetModels_MostowskiCollapse`, `DegreeRigidity_SetModels_NameUnionCode`, `DegreeRigidity_SetModels_NameValidity`, `DegreeRigidity_SetModels_OrderedNameCode`, `DegreeRigidity_SetModels_RegularCodeSplitting`, `DegreeRigidity_SetModels_RegularCompletion`, `DegreeRigidity_SetModels_RegularDecisionPartition`, `DegreeRigidity_SetModels_RegularTreeCompatibility`, `DegreeRigidity_SetModels_RegularTreeFilter`, `DegreeRigidity_SetModels_RegularTreeRecovery`, `DegreeRigidity_SetModels_RelationCollapse`, `DegreeRigidity_SetModels_RelationHull`, `DegreeRigidity_SetModels_RelationPresentation`, `DegreeRigidity_SetModels_SetModelAddition`, `DegreeRigidity_SetModels_SetModelArithmeticSyntax`, `DegreeRigidity_SetModels_SetModelPrimrec`, `DegreeRigidity_SetModels_ShuffleRequirements`, `DegreeRigidity_SetModels_SkolemOperations`, `DegreeRigidity_SetModels_UnionIteration`, `DegreeRigidity_Syntax_BooleanEvaluationWitness`, `DegreeRigidity_Syntax_BooleanExpressionAssembly`, `DegreeRigidity_Syntax_BooleanExpressionTruth`, `DegreeRigidity_Syntax_BoundedDefinability`, `DegreeRigidity_Syntax_BoundedSetTheory`, `DegreeRigidity_Syntax_BoundedSupport`, `DegreeRigidity_Syntax_BoundedTruthRecursion`, `DegreeRigidity_Syntax_CertificateMatrix`, `DegreeRigidity_Syntax_CheckGraphConstruction`, `DegreeRigidity_Syntax_CheckedCode`, `DegreeRigidity_Syntax_DefinablePower`, `DegreeRigidity_Syntax_FiniteFragment`, `DegreeRigidity_Syntax_FiniteTerm`, `DegreeRigidity_Syntax_SentenceCode`, `DegreeRigidity_Syntax_SentenceInlining`, `DegreeRigidity_Syntax_SigmaDomainCollection`, `DegreeRigidity_Syntax_SigmaHull`, `DegreeRigidity_Syntax_SigmaSequenceTrace`, `DegreeRigidity_Syntax_TermFunctionality`.
--
--   **Imports.** It imports the published bundle `Def_DegreeRigidity`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ064A002`, `OAIQ064A003` and `OAIQ064A004`.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity

section
-- module Solutions.OAIQ064_DR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

instance oraclePreorder : Preorder Oracle where
  le := Reduces
  lt A B := Reduces A B ∧ ¬ Reduces B A
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_refl A := TuringReducible.refl (oracleFunction A)
  le_trans _ _ _ h k := TuringReducible.trans h k

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BoundedSetTheory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open Set
universe u

def Pairing (M : ZFSet.{u}) : Prop :=
  ∀ a ∈ M, ∀ b ∈ M, ∃ c ∈ M, ∀ x ∈ M, x ∈ c ↔ x = a ∨ x = b

def Union (M : ZFSet.{u}) : Prop :=
  ∀ a ∈ M, ∃ b ∈ M, ∀ x ∈ M, x ∈ b ↔ ∃ y ∈ M, y ∈ a ∧ x ∈ y

def PowerSet (M : ZFSet.{u}) : Prop :=
  ∀ a ∈ M, ∃ b ∈ M, ∀ x ∈ M, x ∈ b ↔ ∀ y ∈ M, y ∈ x → y ∈ a

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_BoundedForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open Set
universe u
variable {P : Type u} [Preorder P]

def push {α : Sort*} (x : α) (e : ℕ → α) : ℕ → α
  | 0 => x
  | n+1 => e n

@[simp] theorem push_zero {α : Sort*} (x : α) (e : ℕ → α) : push x e 0 = x := rfl
@[simp] theorem push_succ {α : Sort*} (x : α) (e : ℕ → α) (n : ℕ) : push x e (n+1) = e n := rfl

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenSymmetry
open Set

@[ext] structure Condition (ι : Type*) where
  val : ι → Option Bool
  finite : {i | val i ≠ none}.Finite

variable {ι : Type*}

instance instPartialOrderCondition : PartialOrder (Condition ι) where
  le p q := ∀ i b, q.val i = some b → p.val i = some b
  le_refl _ := fun _ _ h => h
  le_trans _ _ _ hpq hqr := fun i b h => hpq i b (hqr i b h)
  le_antisymm p q hpq hqp := by
    apply Condition.ext
    funext i
    cases hp : p.val i with
    | none =>
      cases hq : q.val i with
      | none => rfl
      | some b => have h := hpq i b hq; simp [hp] at h
    | some b => exact (hqp i b hp).symm

instance instOrderTopCondition : OrderTop (Condition ι) where
  top := ⟨fun _ => none, by simp⟩
  le_top _ := by intro i b h; cases h

def flip (m : ι → Bool) (p : Condition ι) : Condition ι where
  val i := (p.val i).map (fun b => b.xor (m i))
  finite := p.finite.subset (by intro i hi; simpa using hi)

theorem flip_involutive (m : ι → Bool) (p : Condition ι) : flip m (flip m p) = p := by
  apply Condition.ext
  funext i
  cases h : p.val i with
  | none => simp [flip,h]
  | some b => cases b <;> cases hm : m i <;> simp [flip,h,hm]

theorem flip_mono (m : ι → Bool) {p q : Condition ι} (hpq : p ≤ q) :
    flip m p ≤ flip m q := by
  intro i b hb
  cases hq : q.val i with
  | none => simp [flip,hq] at hb
  | some c =>
    have hp := hpq i c hq
    simpa [flip,hp] using (show (some c).map (fun d => d.xor (m i)) = some b from by
      simpa [flip,hq] using hb)

def flipIso (m : ι → Bool) : Condition ι ≃o Condition ι where
  toFun := flip m
  invFun := flip m
  left_inv := flip_involutive m
  right_inv := flip_involutive m
  map_rel_iff' := by
    intro p q
    change flip m p ≤ flip m q ↔ p ≤ q
    exact ⟨fun h => by simpa only [flip_involutive] using flip_mono m h,flip_mono m⟩

def Compatible (p q : Condition ι) : Prop :=
  ∀ i a b, p.val i = some a → q.val i = some b → a = b

def merge (p q : Condition ι) : Condition ι where
  val i := (p.val i).orElse (fun _ => q.val i)
  finite := (p.finite.union q.finite).subset (by
    intro i hi
    by_cases hp : p.val i = none
    · exact Or.inr (by simpa [hp] using hi)
    · exact Or.inl hp)

def matchingMask (p q : Condition ι) (i : ι) : Bool :=
  (p.val i).getD false |>.xor ((q.val i).getD false)

end TuringRigidity.CohenSymmetry

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenCoordinates
open Set CohenSymmetry
universe u v
variable {ι : Type u} {κ : Type v}

def restrict (f : κ ↪ ι) (p : Condition ι) : Condition κ where
  val i := p.val (f i)
  finite := p.finite.preimage_embedding f

theorem restrict_mono (f : κ ↪ ι) {p q : Condition ι} (h : p ≤ q) :
    restrict f p ≤ restrict f q := fun i b hb => h (f i) b hb

def reindex (e : ι ≃ κ) : Condition ι ≃o Condition κ where
  toFun := restrict e.symm.toEmbedding
  invFun := restrict e.toEmbedding
  left_inv p := by ext i; simp [restrict]
  right_inv p := by ext i; simp [restrict]
  map_rel_iff' := by
    intro p q
    constructor
    · intro h i b hb
      simpa [restrict] using h (e i) b (by simpa [restrict] using hb)
    · exact restrict_mono _

noncomputable def support (p : Condition ι) : Finset ι := p.finite.toFinset

theorem mem_support (p : Condition ι) (i : ι) : i ∈ support p ↔ p.val i ≠ none :=
  p.finite.mem_toFinset

noncomputable def erase (i : ι) (p : Condition ι) : Condition ι := by
  classical
  exact ⟨fun j => if j = i then none else p.val j,
    p.finite.subset (by intro j hj; by_cases h : j = i <;> simp_all)⟩

end TuringRigidity.CohenCoordinates

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenChainCondition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenChainCondition
open Set CohenSymmetry CohenCoordinates
universe u
variable {ι : Type u}

def Antichain (A : Set (Condition ι)) : Prop :=
  A.Pairwise (fun p q => ¬ Compatible p q)

end TuringRigidity.CohenChainCondition

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_PartialComputability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
open Computable

theorem partrec_fixed_point {α : Type*} [Primcodable α]
    {f : Nat.Partrec.Code → α →. ℕ} (hf : Partrec₂ f) :
    ∃ c : Nat.Partrec.Code, ∀ a, c.eval (Encodable.encode a) = f c a := by
  have hh : Partrec₂ (fun c n => (Encodable.decode (α := α) n : Part α).bind (f c)) :=
    (Computable.ofOption (Computable.decode.comp snd)).bind
      (hf.comp (fst.comp fst) snd)
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.fixed_point₂ hh
  refine ⟨c,fun a => ?_⟩
  simp [hc, Encodable.encodek]
  exact Part.bind_some a (f c)

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_BranchMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
open Computable

namespace BranchMachine

def initial (g : ℕ →. ℕ) (k : ℕ) : Part ℕ := g (8*k)
def anchor (g : ℕ →. ℕ) (k : ℕ) : Part ℕ := g (8*k+4)
def increment (g : ℕ →. ℕ) (h b k : ℕ) : Part ℕ :=
  g (if b = h then 2*k+1 else 4*k+2)

end BranchMachine
end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
open Encodable

namespace UniformOracle
variable {O : Set (ℕ →. ℕ)}

def flag (e : ℕ) : ℕ :=
  if ((decode (α := Option ℕ) e).getD none).isSome then 0 else 1
def answer (e : ℕ) : ℕ := ((decode (α := Option ℕ) e).getD none).getD 0

end UniformOracle
end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_ProgramTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set
namespace TuringRigidity

def OpenFiber {X α : Type*} [TopologicalSpace X] (f : X → Part α) : Prop :=
  ∀ a, IsOpen {x | a ∈ f x}

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_Recurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

def choiceBit (test : ℝ → Bool) (s : ℝ) : ℝ := if test s then 1 else 0

def state (test : ℝ → Bool) (δ t : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => state test δ t n + δ * (t - choiceBit test (state test δ t n))

def branch (test : ℝ → Bool) (δ t : ℝ) (n : ℕ) : ℝ :=
  choiceBit test (state test δ t n)

def rationalSpan (t : ℝ) : Set ℝ := {s | ∃ a b : ℚ, s = a + b * t}

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_Category
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Topology

namespace TuringRigidity

def forwardShift (s a : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun p := (p.1 + s, p.2 - p.1 + a)
  invFun p := (p.1 - s, p.2 + (p.1 - s) - a)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv p := by ext <;> dsimp <;> ring
  continuous_toFun :=
    (continuous_fst.add continuous_const).prodMk
      ((continuous_snd.sub continuous_fst).add continuous_const)
  continuous_invFun :=
    (continuous_fst.sub continuous_const).prodMk
      ((continuous_snd.add (continuous_fst.sub continuous_const)).sub continuous_const)

def backwardShift (s : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun p := (p.2 + s, p.1 - p.2)
  invFun p := (p.2 + (p.1 - s), p.1 - s)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv p := by ext <;> dsimp <;> ring
  continuous_toFun :=
    (continuous_snd.add continuous_const).prodMk (continuous_fst.sub continuous_snd)
  continuous_invFun :=
    (continuous_snd.add (continuous_fst.sub continuous_const)).prodMk
      (continuous_fst.sub continuous_const)

def goodPairs (t : ℝ) (D : Set ℝ) (E : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {p | ∀ s ∈ rationalSpan t,
    p.1 + s ∈ D ∧ (∀ a ∈ rationalSpan t, (p.1+s, p.2-p.1+a) ∈ E) ∧
      (p.2+s, p.1-p.2) ∈ E}

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_ProgramSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Topology
namespace TuringRigidity

noncomputable def leastSuccess {X : Type*} (R : X → ℕ → Prop)
    (hex : ∀ x, ∃ n, R x n) (x : X) : ℕ := by
  classical
  exact Nat.find (hex x)

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_BorelGeneric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BorelGeneric
open Set

def word (n : ℕ) : List Bool := (Encodable.decode (α := List Bool) n).getD []

def Ext (s t : ℕ) : Prop := word s <+: word t ∧ (word s).length < (word t).length

variable {X : Type*} [MeasurableSpace X]
variable (R : X → ℕ → ℕ → Prop)
variable (hd : ∀ x n s, ∃ t, Ext s t ∧ R x n t)

noncomputable def next (n : ℕ) (z : X × ℕ) : ℕ :=
  leastSuccess (fun z t => Ext z.2 t ∧ R z.1 n t) (fun z => hd z.1 n z.2) z

noncomputable def stage : ℕ → X → ℕ
  | 0 => fun _ => Encodable.encode ([] : List Bool)
  | n+1 => fun x => next R hd n (x,stage n x)

end TuringRigidity.BorelGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_Cuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Topology
namespace TuringRigidity

def rationalEnumeration (n : ℕ) : ℚ := (Encodable.decode (α := ℚ) n).getD 0

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_BinaryMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BinarySeries
open UniformOracle Encodable

def foldNumeral (L : List ℕ) : ℕ := L.foldl (fun a b => 2*a+b) 0

end TuringRigidity.BinarySeries

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_BranchFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

namespace UniformOracle

def runningSum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => runningSum f n + f n

end UniformOracle

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GenericCoding
open UniformOracle BinarySeries Encodable

def recoverDecision (z : ℕ × ℕ × ℕ × ℕ) : Option ℕ :=
  if z.1=z.2.1 ∧ z.2.2.1=1 then some z.2.2.2 else none

end TuringRigidity.GenericCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ShuffleRequirements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ShuffleRequirements
open GenericCoding Set

theorem getD_of_prefix {s t : List Bool} (h : s <+: t) (i : ℕ) (hi : i < s.length) :
    s.getD i false = t.getD i false := by
  obtain ⟨u,rfl⟩ := h
  simp [List.getD,List.getElem?_append,hi]

def OddHit (N : ℕ) (s : List Bool) : Prop :=
  ∃ i, N ≤ i ∧ 2*i+1 < s.length ∧ s.getD (2*i+1) false = true

end TuringRigidity.ShuffleRequirements

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_CutTranscript
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set
namespace TuringRigidity

namespace CategorySearch

def rectangle (l r : ℚ × ℚ) : Set (ℝ × ℝ) :=
  Ioo (l.1 : ℝ) (r.1 : ℝ) ×ˢ Ioo (l.2 : ℝ) (r.2 : ℝ)

end CategorySearch
end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_CategoryReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CategorySearch
open Encodable Set

def trialInput (z : ℕ) : ℕ :=
  let n := (Nat.unpair z).1
  let s := (Nat.unpair z).2
  let i := (Nat.unpair s).1
  let j := (Nat.unpair (Nat.unpair s).2).1
  let t := (Nat.unpair (Nat.unpair s).2).2
  Nat.pair (Nat.pair i (Nat.pair j n)) t

end TuringRigidity.CategorySearch

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_EffectiveRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

namespace EffectiveRecovery

def window (A B : ℕ) (z : Bool × (ℕ × ℕ) × (ℕ × ℕ)) : Option ℕ :=
  if z.1 then some 1 else
  if z.2.1.1*z.2.2.1*A + z.2.1.2*B < z.2.1.2*z.2.2.2*A then some 1 else
  if z.2.1.2*(z.2.2.2*A+B) < z.2.1.1*z.2.2.1*A then some 0 else none

end EffectiveRecovery

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.UniformPrograms
open Encodable

variable {X : Type*} {O : X → ℕ →. ℕ}

def flag (e : ℕ) : ℕ :=
  if ((decode (α := Option ℕ) e).getD none).isSome then 0 else 1
def answer (e : ℕ) : ℕ := ((decode (α := Option ℕ) e).getD none).getD 0

end TuringRigidity.UniformPrograms

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenBorelForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenBorelForcing
open Set ShuffleRequirements

@[ext] structure Condition where
  word : List Bool

instance instPartialOrderCondition : PartialOrder Condition where
  le p q := q.word <+: p.word
  le_refl _ := List.prefix_rfl
  le_trans _ _ _ h₁ h₂ := h₂.trans h₁
  le_antisymm _ _ h₁ h₂ := Condition.ext (List.Sublist.antisymm h₂.sublist h₁.sublist)

end TuringRigidity.CohenBorelForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenRecursiveName
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenRecursiveName
open Set CohenBorelForcing ShuffleRequirements

instance instOrderTopCondition : OrderTop Condition where
  top := ⟨[]⟩
  le_top _ := List.nil_prefix

end TuringRigidity.CohenRecursiveName

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_NameUnionCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open Set BoundedSetTheory
universe u

def iterUnion : ℕ → ZFSet.{u} → ZFSet.{u}
  | 0, a => a
  | n+1, a => ZFSet.sUnion (iterUnion n a)

theorem first_mem_doubleUnion {a b c : ZFSet.{u}} (h : ZFSet.pair a b ∈ c) :
    a ∈ iterUnion 2 c := by
  apply ZFSet.mem_sUnion.mpr
  refine ⟨({a} : ZFSet.{u}),?_,ZFSet.mem_singleton.mpr rfl⟩
  apply ZFSet.mem_sUnion.mpr
  exact ⟨ZFSet.pair a b,h,ZFSet.mem_pair.mpr (Or.inl rfl)⟩

theorem iterUnion_lift {a b : ZFSet.{u}} (h : a ∈ b) (n : ℕ) :
    iterUnion n a ⊆ iterUnion (n+1) b := by
  induction n with
  | zero => exact fun x hx => ZFSet.mem_sUnion.mpr ⟨a,h,hx⟩
  | succ n ih =>
    intro x hx
    obtain ⟨y,hy,hxy⟩ := ZFSet.mem_sUnion.mp hx
    exact ZFSet.mem_sUnion.mpr ⟨y,ih hy,hxy⟩

theorem iterUnion_add (m n : ℕ) (a : ZFSet.{u}) :
    iterUnion m (iterUnion n a) = iterUnion (m+n) a := by
  induction m with
  | zero => simp only [iterUnion,Nat.zero_add]
  | succ m ih => simp only [iterUnion,ih,Nat.succ_add]

theorem second_child_bound {a b c d t : ZFSet.{u}}
    (hab : ZFSet.pair a b ∈ t) (hcd : ZFSet.pair c d ∈ a) : c ∈ iterUnion 5 t := by
  have ha := first_mem_doubleUnion hab
  have hc := first_mem_doubleUnion hcd
  have ht := iterUnion_lift ha 2 hc
  simpa only [iterUnion_add] using ht

def unionPredicate (t p r z : ZFSet.{u}) : Prop :=
  ∃ d ∈ iterUnion 5 t, ∃ s ∈ p, z = ZFSet.pair d s ∧
    ∃ c ∈ iterUnion 2 t, ∃ q ∈ p, ∃ v ∈ p,
      ZFSet.pair c q ∈ t ∧ ZFSet.pair d v ∈ c ∧
        ZFSet.pair s q ∈ r ∧ ZFSet.pair s v ∈ r

noncomputable def unionCode (t p r : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (unionPredicate t p r) (ZFSet.prod (iterUnion 5 t) p)

theorem mem_unionCode (t p r z : ZFSet.{u}) :
    z ∈ unionCode t p r ↔ unionPredicate t p r z := by
  rw [unionCode,ZFSet.mem_sep]
  constructor
  · exact And.right
  · intro h
    have hh := h
    obtain ⟨d,hd,s,hs,hz,_⟩ := hh
    exact ⟨ZFSet.mem_prod.mpr ⟨d,hd,s,hs,hz⟩,h⟩

end TuringRigidity.TransitiveNameModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_CheckedCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open BoundedSetTheory
universe u

noncomputable def checkedCode (t x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun y : Shrink x =>
    ZFSet.pair (checkedCode t ((equivShrink x).symm y).val) t)
termination_by x
decreasing_by exact ((equivShrink x).symm y).property

theorem mem_checkedCode (t x z : ZFSet.{u}) :
    z ∈ checkedCode t x ↔ ∃ y ∈ x, z = ZFSet.pair (checkedCode t y) t := by
  rw [checkedCode, ZFSet.mem_range]
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨_,((equivShrink x).symm y).property,hy.symm⟩
  · rintro ⟨y,hy,hz⟩
    refine ⟨equivShrink x ⟨y,hy⟩,?_⟩
    simpa using hz.symm

def RecursionStep (f r t x v : ZFSet.{u}) : Prop :=
  (∀ z ∈ v, ∃ y ∈ x, ∃ w ∈ r, ZFSet.pair y w ∈ f ∧ z = ZFSet.pair w t) ∧
  (∀ y ∈ x, ∀ w ∈ r, ZFSet.pair y w ∈ f → ZFSet.pair w t ∈ v)

end TuringRigidity.TransitiveNameModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_CheckGraphConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open BoundedSetTheory
universe u

theorem second_mem_doubleUnion {a b f : ZFSet.{u}} (h : ZFSet.pair a b ∈ f) :
    b ∈ iterUnion 2 f := by
  apply ZFSet.mem_sUnion.mpr
  refine ⟨({a,b} : ZFSet.{u}),?_,ZFSet.mem_pair.mpr (Or.inr rfl)⟩
  exact ZFSet.mem_sUnion.mpr ⟨_,h,ZFSet.mem_pair.mpr (Or.inr rfl)⟩

noncomputable def taggedImage (x f t : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ y ∈ x, ∃ w ∈ iterUnion 2 f,
    ZFSet.pair y w ∈ f ∧ z = ZFSet.pair w t)
    (ZFSet.prod (iterUnion 2 f) ({t} : ZFSet.{u}))

theorem mem_taggedImage (x f t z : ZFSet.{u}) :
    z ∈ taggedImage x f t ↔ ∃ y ∈ x, ∃ w, ZFSet.pair y w ∈ f ∧ z = ZFSet.pair w t := by
  rw [taggedImage,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,y,hy,w,_,hfw,hz⟩
    exact ⟨y,hy,w,hfw,hz⟩
  · rintro ⟨y,hy,w,hfw,rfl⟩
    have hw := second_mem_doubleUnion hfw
    exact ⟨ZFSet.mem_prod.mpr ⟨w,hw,t,ZFSet.mem_singleton.mpr rfl,rfl⟩,
      y,hy,w,hw,hfw,rfl⟩

end TuringRigidity.TransitiveNameModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ExtensionBasicAxioms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open Set BoundedSetTheory
universe u

namespace BasicAxioms

def Extensionality (M : ZFSet.{u}) : Prop :=
  ∀ a ∈ M, ∀ b ∈ M, (∀ x ∈ M, x ∈ a ↔ x ∈ b) → a = b

def EmptySet (M : ZFSet.{u}) : Prop := ∃ a ∈ M, ∀ x ∈ M, x ∉ a

def Foundation (M : ZFSet.{u}) : Prop :=
  ∀ a ∈ M, (∃ x ∈ M, x ∈ a) →
    ∃ y ∈ M, y ∈ a ∧ ∀ z ∈ M, ¬ (z ∈ y ∧ z ∈ a)

end BasicAxioms

end TuringRigidity.TransitiveNameModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalInfinity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

def Infinity (M : ZFSet.{u}) : Prop :=
  ∃ a ∈ M, (∃ e ∈ M, e ∈ a ∧ ∀ z ∈ M, z ∉ e) ∧
    ∀ x ∈ M, x ∈ a → ∃ s ∈ M, s ∈ a ∧
      ∀ z ∈ M, z ∈ s ↔ z = x ∨ z ∈ x

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_UnionIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open BoundedSetTheory
universe u

def FunctionGraph (d r f : ZFSet.{u}) : Prop :=
  (∀ z ∈ f, ∃ x ∈ d, ∃ y ∈ r, z = ZFSet.pair x y) ∧
  (∀ x ∈ d, ∃ y ∈ r, ZFSet.pair x y ∈ f ∧
    ∀ z ∈ r, ZFSet.pair x z ∈ f → z = y)

theorem FunctionGraph.value_mem {d r f x y : ZFSet.{u}}
    (h : FunctionGraph d r f) (hp : ZFSet.pair x y ∈ f) : y ∈ r := by
  obtain ⟨a,_,b,hb,he⟩ := h.1 _ hp
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  exact hb

theorem FunctionGraph.functional {d r f x y z : ZFSet.{u}}
    (h : FunctionGraph d r f) (hx : x ∈ d)
    (hy : ZFSet.pair x y ∈ f) (hz : ZFSet.pair x z ∈ f) : y = z := by
  obtain ⟨v,_,_,hu⟩ := h.2 x hx
  exact (hu y (h.value_mem hy) hy).trans (hu z (h.value_mem hz) hz).symm

def UnionIteration (k r f a : ZFSet.{u}) : Prop := FunctionGraph k r f ∧
  ZFSet.pair ∅ a ∈ f ∧
  ∀ i ∈ k, ∀ j ∈ k, j = insert i i → ∀ v ∈ r, ∀ w ∈ r,
    ZFSet.pair i v ∈ f → ZFSet.pair j w ∈ f → w = ZFSet.sUnion v

end TuringRigidity.TransitiveNameModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericFilterName
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open BoundedSetTheory
universe u

noncomputable def filterCode (p f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ p, ∃ v ∈ iterUnion 2 f,
    ZFSet.pair x v ∈ f ∧ z = ZFSet.pair v x) (ZFSet.prod (iterUnion 2 f) p)

end TuringRigidity.TransitiveNameModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BoundedSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open Set TransitiveNameModel BoundedSetTheory
universe u

def truncate {α : Sort*} (n : ℕ) (e : ℕ → α) (i : ℕ) : α := if i < n then e i else e 0

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_NameValidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.NameValidity
open TransitiveNameModel BoundedSetTheory
universe u

def Step (c h x : ZFSet.{u}) : Prop :=
  ∀ z ∈ x, ∃ y ∈ h, ∃ q ∈ c, z = ZFSet.pair y q

def Certificate (d c h : ZFSet.{u}) : Prop :=
  h ⊆ d ∧ ∀ x ∈ d, x ∈ h ↔ Step c h x

def Child (y x : ZFSet.{u}) : Prop := ∃ q, ZFSet.pair y q ∈ x

theorem child_wellFounded : WellFounded (Child : ZFSet.{u} → ZFSet.{u} → Prop) := by
  apply ZFSet.mem_wf.transGen.mono
  intro y x h
  obtain ⟨q,hq⟩ := h
  exact Relation.TransGen.tail
    (Relation.TransGen.tail (Relation.TransGen.single (ZFSet.mem_singleton.mpr rfl))
      (show ({y} : ZFSet.{u}) ∈ ZFSet.pair y q from ZFSet.mem_pair.mpr (Or.inl rfl))) hq

end TuringRigidity.NameValidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

def ChoiceGraph (a f : ZFSet.{u}) : Prop :=
  (∀ z ∈ f, ∃ x ∈ a, ∃ y ∈ x, z = ZFSet.pair x y) ∧
  (∀ x ∈ a, ∃ y ∈ x, ZFSet.pair x y ∈ f ∧
    ∀ z ∈ x, ZFSet.pair x z ∈ f → z = y)

def Choice (M : ZFSet.{u}) : Prop :=
  ∀ a ∈ M, (∀ x ∈ a, ∃ y, y ∈ x) → ∃ f ∈ M, ChoiceGraph a f

theorem ChoiceGraph.functional {a f : ZFSet.{u}} (hf : ChoiceGraph a f)
    {x y z : ZFSet.{u}} (hxy : ZFSet.pair x y ∈ f) (hxz : ZFSet.pair x z ∈ f) : y = z := by
  obtain ⟨a',ha,b,hb,he⟩ := hf.1 _ hxy
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  obtain ⟨a',_,b,hb',he⟩ := hf.1 _ hxz
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  obtain ⟨v,_,hxv,hunique⟩ := hf.2 x ha
  exact (hunique y hb hxy).trans (hunique z hb' hxz).symm

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_RankRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalRank
open TransitiveNameModel BoundedSetTheory
universe u

noncomputable def rankSet (x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sUnion (ZFSet.range (fun y : Shrink x =>
    insert (rankSet ((equivShrink x).symm y).val) (rankSet ((equivShrink x).symm y).val)))
termination_by x
decreasing_by exact ((equivShrink x).symm y).property

theorem mem_rankSet (x z : ZFSet.{u}) :
    z ∈ rankSet x ↔ ∃ y ∈ x, z = rankSet y ∨ z ∈ rankSet y := by
  rw [rankSet,ZFSet.mem_sUnion]
  constructor
  · rintro ⟨v,hv,hz⟩
    obtain ⟨y,rfl⟩ := ZFSet.mem_range.mp hv
    exact ⟨_,((equivShrink x).symm y).property,ZFSet.mem_insert_iff.mp hz⟩
  · rintro ⟨y,hy,hz⟩
    refine ⟨_,ZFSet.mem_range.mpr ⟨equivShrink x ⟨y,hy⟩,rfl⟩,?_⟩
    simpa using ZFSet.mem_insert_iff.mpr hz

def Step (f r x v : ZFSet.{u}) : Prop :=
  (∀ z ∈ v, ∃ y ∈ x, ∃ w ∈ r, ZFSet.pair y w ∈ f ∧ (z = w ∨ z ∈ w)) ∧
  (∀ y ∈ x, ∀ w ∈ r, ZFSet.pair y w ∈ f → w ∈ v ∧ w ⊆ v)

end TuringRigidity.InternalRank

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_RankGraphConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalRank
open TransitiveNameModel BoundedSetTheory
universe u

noncomputable def rankImage (x f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ y ∈ x, ∃ w ∈ iterUnion 2 f,
    ZFSet.pair y w ∈ f ∧ (z = w ∨ z ∈ w))
    (iterUnion 2 f ∪ ZFSet.sUnion (iterUnion 2 f))

theorem mem_rankImage (x f z : ZFSet.{u}) :
    z ∈ rankImage x f ↔ ∃ y ∈ x, ∃ w, ZFSet.pair y w ∈ f ∧ (z = w ∨ z ∈ w) := by
  rw [rankImage,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,y,hy,w,_,hfw,hz⟩; exact ⟨y,hy,w,hfw,hz⟩
  · rintro ⟨y,hy,w,hfw,hz⟩
    have hw := second_mem_doubleUnion hfw
    refine ⟨?_,y,hy,w,hw,hfw,hz⟩
    apply ZFSet.mem_union.mpr
    exact hz.elim (fun h => Or.inl (h ▸ hw))
      (fun h => Or.inr (ZFSet.mem_sUnion.mpr ⟨w,hw,h⟩))

end TuringRigidity.InternalRank

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_RankOrdinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalRank
open TransitiveNameModel BoundedSetTheory
universe u

theorem rankSet_eq_ordinal (x : ZFSet.{u}) : rankSet x = x.rank.toZFSet := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    apply ZFSet.ext
    intro z
    rw [mem_rankSet]
    constructor
    · rintro ⟨y,hy,rfl|hz⟩
      · rw [ih y hy]
        exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (ZFSet.rank_lt_of_mem hy)
      · rw [ih y hy] at hz
        exact Ordinal.toZFSet_monotone (ZFSet.rank_lt_of_mem hy).le hz
    · intro hz
      obtain ⟨a,ha,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
      obtain ⟨y,hy,hay⟩ := ZFSet.lt_rank_iff.mp ha
      refine ⟨y,hy,?_⟩
      rw [ih y hy]
      rcases lt_or_eq_of_le hay with hay|rfl
      · exact Or.inr (Ordinal.toZFSet_mem_toZFSet_iff.mpr hay)
      · exact Or.inl rfl

theorem rankSet_isOrdinal (x : ZFSet.{u}) : (rankSet x).IsOrdinal := by
  rw [rankSet_eq_ordinal]
  exact ZFSet.isOrdinal_toZFSet _

end TuringRigidity.InternalRank

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RelationHull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelationHull
open TransitiveNameModel BoundedSetTheory
universe u

def Closed (d r b : ZFSet.{u}) : Prop :=
  ∀ x ∈ b, ∀ y ∈ d, ZFSet.pair y x ∈ r → y ∈ b

noncomputable def hull (d r q x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∀ b ∈ q, Closed d r b → x ∈ b → z ∈ b) d

theorem mem_hull (d r q x z : ZFSet.{u}) :
    z ∈ hull d r q x ↔ z ∈ d ∧ ∀ b ∈ q, Closed d r b → x ∈ b → z ∈ b := ZFSet.mem_sep

theorem hull_subset (d r q x : ZFSet.{u}) : hull d r q x ⊆ d :=
  fun _ h => (mem_hull _ _ _ _ _).mp h |>.1

theorem self_mem (d r q : ZFSet.{u}) {x : ZFSet.{u}} (hx : x ∈ d) :
    x ∈ hull d r q x := (mem_hull _ _ _ _ _).mpr ⟨hx,fun _ _ _ h => h⟩

theorem hull_closed (d r q x : ZFSet.{u}) : Closed d r (hull d r q x) := by
  intro y hy z hz hzy
  exact (mem_hull _ _ _ _ _).mpr ⟨hz,fun b hb hbc hxb =>
    hbc y (((mem_hull _ _ _ _ _).mp hy).2 b hb hbc hxb) z hz hzy⟩

theorem hull_least (d r q x b : ZFSet.{u}) (hb : b ∈ q)
    (hc : Closed d r b) (hx : x ∈ b) : hull d r q x ⊆ b :=
  fun _ hz => (mem_hull _ _ _ _ _).mp hz |>.2 b hb hc hx

noncomputable def predecessors (d r x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun y => ZFSet.pair y x ∈ r) d

theorem mem_predecessors (d r x y : ZFSet.{u}) :
    y ∈ predecessors d r x ↔ y ∈ d ∧ ZFSet.pair y x ∈ r := ZFSet.mem_sep

end TuringRigidity.RelationHull

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RelationCollapse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory RelationHull
universe u

def Rel (d r : ZFSet.{u}) (y x : ZFSet.{u}) : Prop := y ∈ d ∧ ZFSet.pair y x ∈ r

def Graph (d r a b f : ZFSet.{u}) : Prop :=
  a ⊆ d ∧ Closed d r a ∧
  (∀ z ∈ f, ∃ x ∈ a, ∃ y ∈ b, z = ZFSet.pair x y) ∧
  (∀ x ∈ a, ∃ y ∈ b, ZFSet.pair x y ∈ f ∧
    ∀ z ∈ b, ZFSet.pair x z ∈ f → z = y) ∧
  (∀ x ∈ a, ∀ v ∈ b, ZFSet.pair x v ∈ f →
    (∀ z ∈ v, ∃ y ∈ d, ZFSet.pair y x ∈ r ∧ ZFSet.pair y z ∈ f) ∧
    (∀ y ∈ d, ZFSet.pair y x ∈ r → ∀ z ∈ b, ZFSet.pair y z ∈ f → z ∈ v))

end TuringRigidity.RelationCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalRelationCollapse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory
universe u

noncomputable def nextValue (d r x f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ y ∈ d, ZFSet.pair y x ∈ r ∧ ZFSet.pair y z ∈ f) (iterUnion 2 f)

theorem mem_nextValue (d r x f z : ZFSet.{u}) :
    z ∈ nextValue d r x f ↔ ∃ y ∈ d, ZFSet.pair y x ∈ r ∧ ZFSet.pair y z ∈ f := by
  rw [nextValue,ZFSet.mem_sep]
  constructor
  · exact And.right
  · intro h
    obtain ⟨y,hy,hyx,hyz⟩ := h
    exact ⟨second_mem_doubleUnion hyz,y,hy,hyx,hyz⟩

end TuringRigidity.RelationCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_CollapseCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory
universe u

def On (d r : ZFSet.{u}) : Prop := r ⊆ ZFSet.prod d d

theorem right_mem {d r x y : ZFSet.{u}} (hr : On d r) (hyx : ZFSet.pair y x ∈ r) : x ∈ d := by
  obtain ⟨a,_,b,hb,heq⟩ := ZFSet.mem_prod.mp (hr hyx)
  exact (ZFSet.pair_inj.mp heq).2 ▸ hb

theorem Graph.wellFounded {d r b f : ZFSet.{u}} (hr : On d r)
    (hg : Graph d r d b f) : WellFounded (Rel d r) := by
  classical
  let F : ZFSet.{u} → ZFSet.{u} := fun x =>
    if hx : x ∈ d then (hg.2.2.2.1 x hx).choose else ∅
  have hF (x : ZFSet.{u}) (hx : x ∈ d) :
      F x ∈ b ∧ ZFSet.pair x (F x) ∈ f := by
      simpa only [F,dite_eq_left hx] using (hg.2.2.2.1 x hx).choose_spec |>.imp_right And.left
  have wf : WellFounded (fun y x => F y ∈ F x) := InvImage.wf F ZFSet.mem_wf
  apply wf.mono
  intro y x hyx
  have hx := right_mem hr hyx.2
  exact (hg.2.2.2.2 x hx (F x) (hF x hx).1 (hF x hx).2).2
    y hyx.1 hyx.2 (F y) (hF y hyx.1).1 (hF y hyx.1).2

end TuringRigidity.RelationCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_CollapseCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory
universe u

def Presents (a f : ZFSet.{u}) (j : ZFSet.{u} → ZFSet.{u}) : Prop :=
  ∀ z, z ∈ f ↔ ∃ x ∈ a, z = ZFSet.pair x (j x)

theorem Presents.pair_iff {a f : ZFSet.{u}} {j : ZFSet.{u} → ZFSet.{u}}
    (hf : Presents a f j) (x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ f ↔ x ∈ a ∧ y = j x := by
  rw [hf]
  constructor
  · rintro ⟨z,hz,he⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hz,rfl⟩
  · rintro ⟨hx,rfl⟩
    exact ⟨x,hx,rfl⟩

noncomputable def codedRelation (d a f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ u ∈ d, ∃ v ∈ d, z = ZFSet.pair u v ∧
    ∃ x ∈ a, ∃ y ∈ a, x ∈ y ∧ ZFSet.pair x u ∈ f ∧ ZFSet.pair y v ∈ f) (ZFSet.prod d d)

theorem codedRelation_on (d a f : ZFSet.{u}) : On d (codedRelation d a f) :=
  fun _ hz => (ZFSet.mem_sep.mp hz).1

theorem codedRelation_pair {d a f : ZFSet.{u}} {j : ZFSet.{u} → ZFSet.{u}}
    (hf : Presents a f j) (hj : ∀ x ∈ a, j x ∈ d) (u v : ZFSet.{u}) :
    ZFSet.pair u v ∈ codedRelation d a f ↔
      ∃ x ∈ a, ∃ y ∈ a, x ∈ y ∧ u = j x ∧ v = j y := by
  rw [codedRelation,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,u',_,v',_,hp,x,hx,y,hy,hxy,hxu,hyv⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
    exact ⟨x,hx,y,hy,hxy,((hf.pair_iff x u).mp hxu).2,((hf.pair_iff y v).mp hyv).2⟩
  · rintro ⟨x,hx,y,hy,hxy,rfl,rfl⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨_,hj x hx,_,hj y hy,rfl⟩,
      _,hj x hx,_,hj y hy,rfl,x,hx,y,hy,hxy,
      (hf.pair_iff x _).mpr ⟨hx,rfl⟩,(hf.pair_iff y _).mpr ⟨hy,rfl⟩⟩

theorem codedRelation_wellFounded {d a f : ZFSet.{u}} {j : ZFSet.{u} → ZFSet.{u}}
    (hf : Presents a f j) (hj : ∀ x ∈ a, j x ∈ d)
    (hi : ∀ x ∈ a, ∀ y ∈ a, j x = j y → x = y) :
    WellFounded (Rel d (codedRelation d a f)) := by
  classical
  let F : ZFSet.{u} → ZFSet.{u} := fun u =>
    if h : ∃ x ∈ a, j x = u then h.choose else ∅
  have hF (x : ZFSet.{u}) (hx : x ∈ a) : F (j x) = x := by
    have h : ∃ y ∈ a, j y = j x := ⟨x,hx,rfl⟩
    simp only [F,dite_eq_left h]
    exact hi _ h.choose_spec.1 x hx h.choose_spec.2
  apply (show WellFounded (fun y x => F y ∈ F x) from InvImage.wf F ZFSet.mem_wf).mono
  intro u v huv
  obtain ⟨x,hx,y,hy,hxy,rfl,rfl⟩ := (codedRelation_pair hf hj u v).mp huv.2
  simpa only [hF x hx,hF y hy] using hxy

end TuringRigidity.RelationCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteTuple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

namespace FiniteTuple
noncomputable def code : List ZFSet.{u} → ZFSet.{u}
  | [] => ∅
  | x :: xs => ZFSet.pair x (code xs)

noncomputable def space (d : ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => {∅}
  | n+1 => ZFSet.prod d (space d n)

theorem mem_space (d t : ZFSet.{u}) (n : ℕ) :
    t ∈ space d n ↔ ∃ xs : List ZFSet.{u}, xs.length = n ∧
      (∀ x ∈ xs, x ∈ d) ∧ t = code xs := by
  induction n generalizing t with
  | zero =>
    simp only [space,ZFSet.mem_singleton,List.length_eq_zero_iff]
    constructor
    · intro h; exact ⟨[],rfl,by simp,h⟩
    · rintro ⟨xs,rfl,_,h⟩; exact h
  | succ n ih =>
    rw [space,ZFSet.mem_prod]
    constructor
    · rintro ⟨x,hx,t,ht,rfl⟩
      obtain ⟨xs,hlen,hxs,rfl⟩ := (ih t).mp ht
      exact ⟨x::xs,by simp [hlen],by intro y hy; rcases List.mem_cons.mp hy with rfl | hy; exact hx; exact hxs y hy,rfl⟩
    · rintro ⟨xs,hlen,hxs,rfl⟩
      cases xs with
      | nil => simp at hlen
      | cons x xs =>
        refine ⟨x,hxs x (by simp),code xs,(ih _).mpr ?_,rfl⟩
        exact ⟨xs,Nat.succ.inj hlen,fun y hy => hxs y (by simp [hy]),rfl⟩

theorem code_mem_space (d : ZFSet.{u}) (xs : List ZFSet.{u})
    (hx : ∀ x ∈ xs, x ∈ d) : code xs ∈ space d xs.length :=
  (mem_space d _ _).mpr ⟨xs,rfl,hx,rfl⟩

theorem code_injective_length (xs ys : List ZFSet.{u}) (hlen : xs.length = ys.length)
    (h : code xs = code ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons => simp at hlen
  | cons x xs ih => cases ys with
    | nil => simp at hlen
    | cons y ys =>
      obtain ⟨rfl,ht⟩ := ZFSet.pair_inj.mp h
      rw [ih ys (Nat.succ.inj hlen) ht]

def rotate (n : ℕ) : ℕ → ℕ
  | 0 => n+1
  | i+1 => if i < n then i else i+2

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_TupleRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace FiniteTuple

def outputFirst (n k : ℕ) : ℕ → ℕ
  | 0 => n
  | i+1 => if i < n then i else i+k+1

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalUniformization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

noncomputable def relationFiber (b r x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun y => ZFSet.pair x y ∈ r) b

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_FiniteSkolem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace FiniteTuple

noncomputable def requests (d : ZFSet.{u}) (n : ℕ) (r : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun t => ∃ y ∈ d, ZFSet.pair t y ∈ r) (space d n)

end FiniteTuple
end TuringRigidity.BoundedSetTheory

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

def Extensional (d r : ZFSet.{u}) : Prop :=
  ∀ x ∈ d, ∀ y ∈ d, (∀ z ∈ d, ZFSet.pair z x ∈ r ↔ ZFSet.pair z y ∈ r) → x = y

noncomputable def graphRange (d f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun v => ∃ x ∈ d, ZFSet.pair x v ∈ f) (iterUnion 2 f)

theorem mem_graphRange (d f v : ZFSet.{u}) :
    v ∈ graphRange d f ↔ ∃ x ∈ d, ZFSet.pair x v ∈ f := by
  rw [graphRange,ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨x,hx,hxv⟩
    exact ⟨second_mem_doubleUnion hxv,x,hx,hxv⟩

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

noncomputable def membershipRelation (d : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ d, ∃ y ∈ d, z = ZFSet.pair x y ∧ x ∈ y) (ZFSet.prod d d)

theorem membershipRelation_pair (d x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ membershipRelation d ↔ x ∈ d ∧ y ∈ d ∧ x ∈ y := by
  rw [membershipRelation,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,a,ha,b,hb,he,hab⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨ha,hb,hab⟩
  · rintro ⟨hx,hy,hxy⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩,x,hx,y,hy,rfl,hxy⟩

theorem membershipRelation_wellFounded (d : ZFSet.{u}) :
    WellFounded (Rel d (membershipRelation d)) := by
  apply ZFSet.mem_wf.mono
  intro x y h
  exact ((membershipRelation_pair d x y).mp h.2).2.2

def StructureExtensional (d : ZFSet.{u}) : Prop :=
  ∀ x ∈ d, ∀ y ∈ d, (∀ z ∈ d, z ∈ x ↔ z ∈ y) → x = y

theorem membershipRelation_extensional {d : ZFSet.{u}} (he : StructureExtensional d) :
    Extensional d (membershipRelation d) := by
  intro x hx y hy hxy
  apply he x hx y hy
  intro z hz
  simpa only [membershipRelation_pair,and_iff_right hz,and_iff_right hx,and_iff_right hy] using hxy z hz

end TuringRigidity.RelationCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_FiniteClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace FiniteTuple

def Closed (n : ℕ) (g h : ZFSet.{u}) : Prop :=
  ∀ xs : List ZFSet.{u}, xs.length = n → (∀ x ∈ xs, x ∈ h) →
    ∀ y, ZFSet.pair (code xs) y ∈ g → y ∈ h

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_FiniteFragment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace FiniteTuple

def takeEnv : ℕ → (ℕ → ZFSet.{u}) → List ZFSet.{u}
  | 0,_ => []
  | n+1,e => e 0 :: takeEnv n (fun i => e (i+1))

@[simp] theorem length_takeEnv (n : ℕ) (e : ℕ → ZFSet.{u}) : (takeEnv n e).length = n := by
  induction n generalizing e with
  | zero => rfl
  | succ n ih => simp only [takeEnv,List.length_cons,ih]

theorem takeEnv_mem (n : ℕ) (e : ℕ → ZFSet.{u}) (h : ZFSet.{u}) (he : ∀ i, e i ∈ h) :
    ∀ x ∈ takeEnv n e, x ∈ h := by
  induction n generalizing e with
  | zero => simp [takeEnv]
  | succ n ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl|hx
    · exact he 0
    · exact ih (fun i => e (i+1)) (fun i => he (i+1)) x hx

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SigmaHull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace FiniteTuple

noncomputable def elements : List ZFSet.{u} → ZFSet.{u}
  | [] => ∅
  | x::xs => ({x} : ZFSet.{u}) ∪ elements xs

theorem mem_elements (x : ZFSet.{u}) (xs : List ZFSet.{u}) : x ∈ elements xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [elements]
  | cons y xs ih => simp only [elements,ZFSet.mem_union,ZFSet.mem_singleton,ih,List.mem_cons]

end FiniteTuple
end TuringRigidity.BoundedSetTheory

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

inductive FiniteCode (t : ZFSet.{u}) : ZFSet.{u} → Prop
  | atom (x : ZFSet.{u}) (hx : x ∈ t) : FiniteCode t x
  | empty : FiniteCode t ∅
  | pair {x y : ZFSet.{u}} : FiniteCode t x → FiniteCode t y → FiniteCode t {x,y}

theorem FiniteCode.orderedPair {t x y : ZFSet.{u}} (hx : FiniteCode t x) (hy : FiniteCode t y) :
    FiniteCode t (ZFSet.pair x y) := by
  have hs : FiniteCode t ({x} : ZFSet.{u}) := by simpa using hx.pair hx
  exact hs.pair (hx.pair hy)

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_FiniteTerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace FiniteTerm

theorem pair_rank_left (x y : ZFSet.{u}) : ZFSet.rank x < ZFSet.rank (ZFSet.pair x y) := by
  have ha : x ∈ ({x,y} : ZFSet.{u}) := ZFSet.mem_pair.mpr (Or.inl rfl)
  have hb : ({x,y} : ZFSet.{u}) ∈ ZFSet.pair x y := ZFSet.mem_pair.mpr (Or.inr rfl)
  exact (ZFSet.rank_lt_of_mem ha).trans (ZFSet.rank_lt_of_mem hb)

theorem pair_rank_right (x y : ZFSet.{u}) : ZFSet.rank y < ZFSet.rank (ZFSet.pair x y) := by
  have ha : y ∈ ({x,y} : ZFSet.{u}) := ZFSet.mem_pair.mpr (Or.inr rfl)
  have hb : ({x,y} : ZFSet.{u}) ∈ ZFSet.pair x y := ZFSet.mem_pair.mpr (Or.inr rfl)
  exact (ZFSet.rank_lt_of_mem ha).trans (ZFSet.rank_lt_of_mem hb)

end FiniteTerm
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_TermFunctionality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace FiniteTerm

def Functional (f : ZFSet.{u}) : Prop :=
  ∀ a x y, ZFSet.pair a x ∈ f → ZFSet.pair a y ∈ f → x = y

end FiniteTerm
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ChoiceTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace InternalWellOrder

def Remaining (a f i r : ZFSet.{u}) : Prop := r ⊆ a ∧
  ∀ x ∈ a, x ∈ r ↔ ¬ ∃ j ∈ i, ZFSet.pair j x ∈ f

structure Trace (α a q s f : ZFSet.{u}) : Prop where
  shape : ∀ z ∈ f, ∃ i ∈ α, ∃ x ∈ a, z = ZFSet.pair i x
  initial : ∀ i ∈ α, ∀ x ∈ a, ZFSet.pair i x ∈ f →
    ∀ j ∈ i, ∃ y ∈ a, ZFSet.pair j y ∈ f
  choice : ∀ i ∈ α, ∀ x ∈ a, ZFSet.pair i x ∈ f →
    ∃ r ∈ q, Remaining a f i r ∧ ZFSet.pair r x ∈ s

theorem Trace.pair_mem {α a q s f i x : ZFSet.{u}} (hf : Trace α a q s f)
    (hix : ZFSet.pair i x ∈ f) : i ∈ α ∧ x ∈ a := by
  obtain ⟨j,hj,y,hy,he⟩ := hf.shape _ hix
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  exact ⟨hj,hy⟩

theorem choice_value_mem {q s r x : ZFSet.{u}} (hs : ChoiceGraph q s)
    (hrx : ZFSet.pair r x ∈ s) : x ∈ r := by
  obtain ⟨r',_,x',hx,he⟩ := hs.1 _ hrx
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  exact hx

theorem Remaining.eq {a f g i r t : ZFSet.{u}} (hr : Remaining a f i r)
    (ht : Remaining a g i t)
    (hfg : ∀ j ∈ i, ∀ x ∈ a, ZFSet.pair j x ∈ f ↔ ZFSet.pair j x ∈ g) : r = t := by
  apply ZFSet.ext; intro x
  constructor
  · intro hx
    have hxa := hr.1 hx
    apply (ht.2 x hxa).mpr
    rintro ⟨j,hji,hjx⟩
    exact (hr.2 x hxa).mp hx ⟨j,hji,(hfg j hji x hxa).mpr hjx⟩
  · intro hx
    have hxa := ht.1 hx
    apply (hr.2 x hxa).mpr
    rintro ⟨j,hji,hjx⟩
    exact (ht.2 x hxa).mp hx ⟨j,hji,(hfg j hji x hxa).mp hjx⟩

theorem Trace.injective {α a q s f : ZFSet.{u}} (hα : α.IsOrdinal)
    (hs : ChoiceGraph q s) (hf : Trace α a q s f)
    (i j x : ZFSet.{u}) (hix : ZFSet.pair i x ∈ f) (hjx : ZFSet.pair j x ∈ f) : i = j := by
  have hi := (hf.pair_mem hix).1
  have hj := (hf.pair_mem hjx).1
  have hx := (hf.pair_mem hix).2
  rcases (hα.mem hi).mem_trichotomous (hα.mem hj) with hij|he|hji
  · obtain ⟨r,_,hr,hrx⟩ := hf.choice j hj x hx hjx
    exact False.elim ((hr.2 x hx).mp (choice_value_mem hs hrx) ⟨i,hij,hix⟩)
  · exact he
  · obtain ⟨r,_,hr,hrx⟩ := hf.choice i hi x hx hix
    exact False.elim ((hr.2 x hx).mp (choice_value_mem hs hrx) ⟨j,hji,hjx⟩)

end InternalWellOrder
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ChoiceTraceFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace InternalWellOrder

theorem Trace.subset {α a q s f : ZFSet.{u}} (hf : Trace α a q s f) : f ⊆ ZFSet.prod α a :=
  fun z hz => ZFSet.mem_prod.mpr (hf.shape z hz)

noncomputable def residual (a f i : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => ¬ ∃ j ∈ i, ZFSet.pair j x ∈ f) a

theorem residual_remaining (a f i : ZFSet.{u}) : Remaining a f i (residual a f i) := by
  refine ⟨fun _ hx => (ZFSet.mem_sep.mp hx).1,?_⟩
  intro x hx
  exact ZFSet.mem_sep.trans (and_iff_right hx)

end InternalWellOrder
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ChoiceTraceExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse
universe u
namespace InternalWellOrder

theorem adjoin_prior (f i x k y : ZFSet.{u}) (hk : k ∈ i) :
    ZFSet.pair k y ∈ f ∪ ({ZFSet.pair i x} : ZFSet.{u}) ↔ ZFSet.pair k y ∈ f := by
  rw [ZFSet.mem_union,ZFSet.mem_singleton]
  constructor
  · rintro (h|h)
    · exact h
    · obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp h
      exact False.elim ((lt_irrefl _) (ZFSet.rank_lt_of_mem hk))
  · exact Or.inl

theorem Trace.domain_before {α a q s f i : ZFSet.{u}} (hα : α.IsOrdinal)
    (hf : Trace α a q s f) (hi : i ∈ α) (hmissing : ¬ ∃ x ∈ a, ZFSet.pair i x ∈ f)
    (j y : ZFSet.{u}) (hjy : ZFSet.pair j y ∈ f) : j ∈ i := by
  have hj := (hf.pair_mem hjy).1
  have hy := (hf.pair_mem hjy).2
  rcases (hα.mem hj).mem_trichotomous (hα.mem hi) with hji|he|hij
  · exact hji
  · subst j; exact False.elim (hmissing ⟨y,hy,hjy⟩)
  · exact False.elim (hmissing (hf.initial j hj y hy hjy i hij))

theorem FunctionGraph.exists_presentation {d r f : ZFSet.{u}} (hf : TransitiveNameModel.FunctionGraph d r f) :
    ∃ j : ZFSet.{u} → ZFSet.{u}, Presents d f j ∧ ∀ x ∈ d, j x ∈ r := by
  classical
  let j := fun x => if hx : x ∈ d then (hf.2 x hx).choose else ∅
  have hj (x : ZFSet.{u}) (hx : x ∈ d) : j x ∈ r ∧ ZFSet.pair x (j x) ∈ f := by
    simp only [j,dite_eq_left hx]
    exact ⟨(hf.2 x hx).choose_spec.1,(hf.2 x hx).choose_spec.2.1⟩
  refine ⟨j,?_,fun x hx => (hj x hx).1⟩
  intro z
  constructor
  · intro hz
    obtain ⟨x,hx,y,_,rfl⟩ := hf.1 z hz
    exact ⟨x,hx,congrArg (ZFSet.pair x) (hf.functional hx hz (hj x hx).2)⟩
  · rintro ⟨x,hx,rfl⟩
    exact (hj x hx).2

end InternalWellOrder
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ChoiceFromOrdinalCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace InternalWellOrder

def LeastValue (δ V F H x y : ZFSet.{u}) : Prop := y ∈ x ∧
  ∃ i ∈ δ, ∃ v ∈ V, ZFSet.pair i v ∈ F ∧ ZFSet.pair v y ∈ H ∧
    ∀ j ∈ i, ∀ w ∈ V, ∀ z ∈ x, ¬ (ZFSet.pair j w ∈ F ∧ ZFSet.pair w z ∈ H)

theorem leastValue_exists {δ V F H x : ZFSet.{u}} (hδ : δ.IsOrdinal)
    (hex : ∃ i ∈ δ, ∃ v ∈ V, ∃ y ∈ x, ZFSet.pair i v ∈ F ∧ ZFSet.pair v y ∈ H) :
    ∃ y ∈ x, LeastValue δ V F H x y := by
  classical
  have minimal (i : ZFSet.{u}) : i ∈ δ →
      (∃ v ∈ V, ∃ y ∈ x, ZFSet.pair i v ∈ F ∧ ZFSet.pair v y ∈ H) →
      ∃ y ∈ x, LeastValue δ V F H x y := by
    induction i using ZFSet.inductionOn with
    | h i ih =>
      intro hi hs
      by_cases hp : ∃ j ∈ i, ∃ w ∈ V, ∃ z ∈ x, ZFSet.pair j w ∈ F ∧ ZFSet.pair w z ∈ H
      · obtain ⟨j,hji,hw⟩ := hp
        exact ih j hji (hδ.subset_of_mem hi hji) hw
      · obtain ⟨v,hv,y,hy,hiv,hvy⟩ := hs
        exact ⟨y,hy,hy,i,hi,v,hv,hiv,hvy,fun j hj w hw z hz hp' => hp ⟨j,hj,w,hw,z,hz,hp'⟩⟩
  obtain ⟨i,hi,hs⟩ := hex
  exact minimal i hi hs

theorem LeastValue.unique {δ V F H x y z : ZFSet.{u}} (hδ : δ.IsOrdinal)
    (hF : TransitiveNameModel.FunctionGraph δ V F) (hH : FiniteTerm.Functional H)
    (hy : LeastValue δ V F H x y) (hz : LeastValue δ V F H x z) : y = z := by
  obtain ⟨hyx,i,hi,v,hv,hiv,hvy,hmin⟩ := hy
  obtain ⟨hzx,j,hj,w,hw,hjw,hwz,hmin'⟩ := hz
  rcases (hδ.mem hi).mem_trichotomous (hδ.mem hj) with hij|he|hji
  · exact False.elim (hmin' i hij v hv y hyx ⟨hiv,hvy⟩)
  · subst j
    have hvw := hF.functional hi hiv hjw
    subst w
    exact hH v y z hvy hwz
  · exact False.elim (hmin j hji w hw z hzx ⟨hjw,hwz⟩)

end InternalWellOrder
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCoverInjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse
universe u
namespace FiniteTerm

noncomputable def inverseCover (h K E : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ h, ∃ c ∈ K, z = ZFSet.pair x c ∧ ZFSet.pair c x ∈ E) (ZFSet.prod h K)

theorem inverseCover_pair (h K E x c : ZFSet.{u}) :
    ZFSet.pair x c ∈ inverseCover h K E ↔ x ∈ h ∧ c ∈ K ∧ ZFSet.pair c x ∈ E := by
  rw [inverseCover,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,y,hy,d,hd,he,hdy⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hy,hd,hdy⟩
  · rintro ⟨hx,hc,hcx⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨x,hx,c,hc,rfl⟩,x,hx,c,hc,rfl,hcx⟩

end FiniteTerm
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SkolemOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace FiniteTerm

noncomputable def labelGraph (a b g o : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ a, ∃ y ∈ b, z = ZFSet.pair (ZFSet.pair o x) y ∧ ZFSet.pair x y ∈ g)
    (ZFSet.prod (ZFSet.prod {o} a) b)

theorem labelGraph_shape {a b g o z : ZFSet.{u}} (hz : z ∈ labelGraph a b g o) :
    ∃ x ∈ a, ∃ y ∈ b, z = ZFSet.pair (ZFSet.pair o x) y ∧ ZFSet.pair x y ∈ g :=
  (ZFSet.mem_sep.mp hz).2

theorem labelGraph_contains {a b g o x y : ZFSet.{u}} (hg : g ⊆ ZFSet.prod a b)
    (hxy : ZFSet.pair x y ∈ g) : ZFSet.pair (ZFSet.pair o x) y ∈ labelGraph a b g o := by
  obtain ⟨x',hx,y',hy,hp⟩ := ZFSet.mem_prod.mp (hg hxy)
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
  exact ZFSet.mem_sep.mpr ⟨ZFSet.mem_prod.mpr
    ⟨_,ZFSet.mem_prod.mpr ⟨o,ZFSet.mem_singleton.mpr rfl,x,hx,rfl⟩,y,hy,rfl⟩,x,hx,y,hy,rfl,hxy⟩

theorem labelGraph_functional {a b g o : ZFSet.{u}} (hg : Functional g) :
    Functional (labelGraph a b g o) := by
  intro c x y hx hy
  obtain ⟨u,_,v,_,he,huv⟩ := labelGraph_shape hx
  obtain ⟨hcu,rfl⟩ := ZFSet.pair_inj.mp he
  obtain ⟨u',_,v',_,he,huv'⟩ := labelGraph_shape hy
  obtain ⟨hcu',rfl⟩ := ZFSet.pair_inj.mp he
  have huu := (ZFSet.pair_inj.mp (hcu.symm.trans hcu')).2
  subst u'
  exact hg u x y huv huv'

theorem Functional.union {f g : ZFSet.{u}} (hf : Functional f) (hg : Functional g)
    (hdis : ∀ a x y, ZFSet.pair a x ∈ f → ZFSet.pair a y ∈ g → False) : Functional (f ∪ g) := by
  intro a x y hx hy
  rcases ZFSet.mem_union.mp hx with hx|hx <;> rcases ZFSet.mem_union.mp hy with hy|hy
  · exact hf a x y hx hy
  · exact False.elim (hdis a x y hx hy)
  · exact False.elim (hdis a y x hy hx)
  · exact hg a x y hx hy

end FiniteTerm
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_GeneratedHull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse
universe u
namespace FiniteTerm

noncomputable def generatedRange (d K E : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∃ c ∈ K, ZFSet.pair c x ∈ E) d

end FiniteTerm
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_ForcingWitnessCollection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedForcing
open TransitiveNameModel BoundedSetTheory
universe u
variable {c : ZFSet.{u}}
namespace WitnessCode

def vars : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | i+2 => i+6

end WitnessCode

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ExtensionSigmaReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace SigmaFormula

def imageVars : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | i+2 => i+3

end SigmaFormula
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_OrderedNameCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.TransitiveNameModel
open BoundedSetTheory
universe u

noncomputable def pairNameCode (t x y : ZFSet.{u}) : ZFSet.{u} :=
  {ZFSet.pair x t, ZFSet.pair y t}

noncomputable def orderedNameCode (t x y : ZFSet.{u}) : ZFSet.{u} :=
  pairNameCode t (pairNameCode t x x) (pairNameCode t x y)

end TuringRigidity.TransitiveNameModel

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

def domainVars : ℕ → ℕ
  | 0 => 1
  | i+1 => i+3

end SigmaFormula

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

noncomputable def orderSet (c : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ p ∈ c, ∃ q ∈ c, z = ZFSet.pair p q ∧ q ⊆ p) (ZFSet.prod c c)

end TuringRigidity.BoundedSetTheory.InternalCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ElementaryLanguage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory
universe u

inductive SentenceForm where
  | equal (i j : ℕ)
  | member (i j : ℕ)
  | conj (p q : SentenceForm)
  | neg (p : SentenceForm)
  | ex (p : SentenceForm)
  deriving Encodable

namespace SentenceForm

def bound : SentenceForm → ℕ
  | .equal i j | .member i j => max i j + 1
  | .conj p q => max p.bound q.bound
  | .neg p => p.bound
  | .ex p => p.bound - 1

def disj (p q : SentenceForm) : SentenceForm := .neg (.conj (.neg p) (.neg q))
def imp (p q : SentenceForm) : SentenceForm := .neg (.conj p (.neg q))
def iff (p q : SentenceForm) : SentenceForm := .conj (imp p q) (imp q p)
def all (p : SentenceForm) : SentenceForm := .neg (.ex (.neg p))

end SentenceForm

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_DefinablePower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

noncomputable def tupleEnv {n : ℕ} (v : Fin n → ZFSet.{u}) (i : ℕ) : ZFSet.{u} :=
  if h : i < n then v ⟨i,h⟩ else ∅

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenSizeLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenSizeLevels
open Set TransitiveNameModel BoundedSetTheory
open RelativeConstructible CohenSymmetry CohenCoordinates

def Small (n : ℕ) (p : ZFSet.{0}) : Prop :=
  ∃ k < n, ∃ v : Fin k → ZFSet.{0}, p = ZFSet.range v

end TuringRigidity.CohenSizeLevels

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenAntichainStages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenAntichainStages
open Set TransitiveNameModel BoundedSetTheory
open CohenSymmetry CohenCoordinates
open CohenChainCondition

def Comp (c p q : ZFSet.{0}) : Prop := ∃ r ∈ c, p ⊆ r ∧ q ⊆ r

def Anti (c E : ZFSet.{0}) : Prop :=
  ∀ p ∈ E, ∀ q ∈ E, p ≠ q → ¬ Comp c p q

end TuringRigidity.CohenAntichainStages

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalMinimalSelector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace InternalWellOrder

def MinimalIn (r a x : ZFSet.{u}) : Prop := x ∈ a ∧ ∀ y ∈ a, ¬ ZFSet.pair y x ∈ r

def InternallyWellFounded (M d r : ZFSet.{u}) : Prop :=
  ∀ a ∈ M, a ⊆ d → (∃ x, x ∈ a) → ∃ x, MinimalIn r a x

def LeastMinimal (δ F r a x : ZFSet.{u}) : Prop := MinimalIn r a x ∧
  ∃ i ∈ δ, ZFSet.pair i x ∈ F ∧
    ∀ j ∈ i, ∀ y ∈ a, ZFSet.pair j y ∈ F → ¬ MinimalIn r a y

end InternalWellOrder
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelIterationTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

def ModelIterationTrace (o R z k n b f : ZFSet.{u}) (S : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  TransitiveNameModel.FunctionGraph k R f ∧ k = insert n n ∧ z = ∅ ∧ ZFSet.pair z b ∈ f ∧
    ∀ i ∈ n, ∀ j ∈ o, j = insert i i → ∀ v ∈ R, ∀ w ∈ R,
      ZFSet.pair i v ∈ f → ZFSet.pair j w ∈ f → S i v w

namespace Formula
def modelIterationVars : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | i+3 => i+4

end Formula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelIterationFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace Formula

def modelIterationOuterVars : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | i+3 => i+6

end Formula
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenAntichainSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenAntichainSequence
open Set TransitiveNameModel BoundedSetTheory CohenAntichainStages
open CohenSizeLevels

def Step (s c U L x y : ZFSet.{0}) : Prop :=
  ∃ n ∈ ZFSet.omega, ∃ E ∈ s, ∃ m ∈ ZFSet.omega, ∃ F ∈ s,
    x = ZFSet.pair n E ∧ y = ZFSet.pair m F ∧ m = insert n n ∧ E ⊆ F ∧
      ∀ p ∈ U, ZFSet.pair n p ∈ L → ∃ q ∈ F, Comp c p q

noncomputable def relation (s c U L : ZFSet.{0}) : ZFSet.{0} :=
  let d := ZFSet.prod ZFSet.omega s
  (ZFSet.prod d d).sep (fun z => ∃ x ∈ d, ∃ y ∈ d,
    z = ZFSet.pair y x ∧ Step s c U L x y)

end TuringRigidity.CohenAntichainSequence

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_PrefixComputability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.PrefixComputability
open Encodable

variable {O : Set (ℕ →. ℕ)}

theorem total_comp {f g : ℕ → ℕ}
    (hf : Nat.RecursiveIn O (fun n => Part.some (f n)))
    (hg : Nat.RecursiveIn O (fun n => Part.some (g n))) :
    Nat.RecursiveIn O (fun n => Part.some (f (g n))) := by
  simpa using Nat.RecursiveIn.comp hf hg

theorem total_primrec {f : ℕ → ℕ} (hf : Primrec f) :
    Nat.RecursiveIn O (fun n => Part.some (f n)) :=
  RecursiveIn.iff_nat.mp hf.computableIn

def appendEncoded (a b : ℕ) : ℕ := encode ((decode (α := List ℕ) a).getD [] ++ [b])

def flag (e : ℕ) : ℕ :=
  if ((decode (α := Option ℕ) e).getD none).isSome then 0 else 1
def answer (e : ℕ) : ℕ := ((decode (α := Option ℕ) e).getD none).getD 0

end TuringRigidity.PrefixComputability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_Introreducible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
namespace Introreducible
open Encodable PrefixComputability

def equalBit (c : ℕ) : ℕ :=
  if (Nat.unpair c).1 = (Nat.unpair c).2 then 1 else 0

end Introreducible
end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CodingForcing

theorem getD_of_prefix {s t : List Bool} (h : s <+: t) {m : ℕ}
    (hm : m < s.length) : t.getD m false = s.getD m false := by
  obtain ⟨u, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append, hm]

end TuringRigidity.CodingForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_CertificateMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CertificateMatrix
open Encodable UniformOracle

def table (c : ℕ) : List (ℕ × ℕ) := (decode c).getD []

def entry (c j : ℕ) : ℕ × ℕ := (table c).getD j (0, 0)

end TuringRigidity.CertificateMatrix

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_OrderMatrixRecursive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrderNormalForm
open UniformOracle CertificateMatrix

def combine (v : ℕ) : ℕ :=
  let t := (Nat.unpair v).1
  let h := (Nat.unpair (Nat.unpair v).2).1
  let c₀ := (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).1
  let c₁ := (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).2).1
  let a := (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).2).2).1
  let b := (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).2).2).2
  if t = 1 ∧ h = 1 ∧ (c₀ ≠ 1 ∨ c₁ ≠ 1 ∨ a = b) then 1 else 0

end TuringRigidity.OrderNormalForm

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.UniformArithmetic
open Encodable UniformOracle

def table (c : ℕ) : List ℕ := (decode c).getD []
def item (c k : ℕ) : ℕ := (table c).getD k 0

theorem table_primrec : Primrec table :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])
theorem item_primrec : Primrec₂ item :=
  (Primrec.list_getD 0).comp (table_primrec.comp Primrec.fst) Primrec.snd

end TuringRigidity.UniformArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NaturalAdditionTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

def AdditionTrace (o z k n x f : ZFSet.{u}) : Prop :=
  TransitiveNameModel.FunctionGraph k o f ∧ k = insert n n ∧ z = ∅ ∧ ZFSet.pair z x ∈ f ∧
    ∀ i ∈ n, ∀ j ∈ o, j = insert i i → ∀ v ∈ o, ∀ w ∈ o,
      ZFSet.pair i v ∈ f → ZFSet.pair j w ∈ f → w = insert v v

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NaturalIterationTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

def IterationTrace (o z k n b f : ZFSet.{u}) (S : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  TransitiveNameModel.FunctionGraph k o f ∧ k = insert n n ∧ z = ∅ ∧ ZFSet.pair z b ∈ f ∧
    ∀ i ∈ n, ∀ j ∈ o, j = insert i i → ∀ v ∈ o, ∀ w ∈ o,
      ZFSet.pair i v ∈ f → ZFSet.pair j w ∈ f → S i v w

namespace Formula
def iterationVars : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | i+3 => i+4

end Formula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NaturalIterationFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace Formula

def iterationOuterVars : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | i+3 => i+6

end Formula
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NaturalMultiplicationFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u

theorem nat_iteration_add (a n : ℕ) : Nat.rec 0 (fun _ v => v+a) n = a*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    change Nat.rec 0 (fun _ v => v+a) n + a = a*(n+1)
    rw [ih,Nat.mul_succ]

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NaturalTermFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u

inductive NaturalTerm where
  | var (i : ℕ)
  | binary (mul : Bool) (a b : NaturalTerm)

namespace NaturalTerm
def eval (v : ℕ → ℕ) : NaturalTerm → ℕ
  | .var i => v i
  | .binary m a b => if m then eval v a * eval v b else eval v a + eval v b

end NaturalTerm
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NaturalPairingFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u
namespace Formula

def pairVars (a b : ℕ) : ℕ → ℕ
  | 0 => a
  | _+1 => b

def pairLeftTerm : NaturalTerm := .binary false (.binary true (.var 1) (.var 1)) (.var 0)
def pairRightTerm : NaturalTerm := .binary false
  (.binary false (.binary true (.var 0) (.var 0)) (.var 0)) (.var 1)

end Formula
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NaturalDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u

namespace Formula
def unaryVars (o Q x y : ℕ) : ℕ → ℕ
  | 0 => y
  | 1 => x
  | 2 => o
  | _+3 => Q

end Formula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticSetSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open UniformArithmetic
universe u

namespace Formula
def arithmeticVars (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => i+k+1

end Formula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticParameterFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open UniformArithmetic
universe u
namespace Formula

def oracleParameterVars (o Q n : ℕ) (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => n
  | 1 => o
  | 2 => Q
  | i+3 => r i

end Formula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_CountableSetReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

def InternallyCountable (M I : ZFSet.{u}) : Prop :=
  ∃ E ∈ M, TransitiveNameModel.FunctionGraph ZFSet.omega I E ∧
    ∀ D ∈ I, ∃ n ∈ ZFSet.omega, ZFSet.pair n D ∈ E

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalFiniteEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalFiniteEnumeration
open Set TransitiveNameModel BoundedSetTheory RelativeConstructible

def Ranges (U E g : ZFSet.{0}) : Prop := E ⊆ U ∧
  ∀ p ∈ U, p ∈ E ↔ ∃ i ∈ ZFSet.omega, ZFSet.pair i p ∈ g

noncomputable def candidates (U C E : ZFSet.{0}) : ZFSet.{0} := C.sep (Ranges U E)

end TuringRigidity.InternalFiniteEnumeration

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCountableFiniteUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCountableFiniteUnion
open Set TransitiveNameModel BoundedSetTheory InternalFiniteEnumeration

def Entry (U g d k x : ZFSet.{0}) : Prop := ZFSet.pair k x ∈ g ∨
  (x = d ∧ ∀ y ∈ U, ¬ ZFSet.pair k y ∈ g)

end TuringRigidity.InternalCountableFiniteUnion

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
open Set TransitiveNameModel BoundedSetTheory CohenAntichainStages
open CohenSymmetry CohenCoordinates

noncomputable def below (c U : ZFSet.{0}) : ZFSet.{0} :=
  c.sep (fun q => ∃ p ∈ U, p ⊆ q)

noncomputable def decision (c U E : ZFSet.{0}) : ZFSet.{0} :=
  c.sep (fun q => (∃ p ∈ E, p ⊆ q) ∨ ∀ p ∈ U, ¬ q ⊆ p)

end TuringRigidity.CohenInternalDecision

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalRelationSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalRelationSelection
open TransitiveNameModel BoundedSetTheory

noncomputable def fiber (Y R x : ZFSet.{0}) : ZFSet.{0} :=
  Y.sep (fun y => ZFSet.pair x y ∈ R)

end TuringRigidity.InternalRelationSelection

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenAntichainSelector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenAntichainSelector
open TransitiveNameModel BoundedSetTheory CohenAntichainStages
open InternalRelationSelection

def Selected (c U E : ZFSet.{0}) : Prop := E ⊆ U ∧ Anti c E ∧
  ∀ p ∈ U, ∃ q ∈ E, Comp c p q

noncomputable def selectionRelation (c Q : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod Q Q).sep (fun z => ∃ U ∈ Q, ∃ E ∈ Q, z = ZFSet.pair U E ∧ Selected c U E)

end TuringRigidity.CohenAntichainSelector

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCollapseDense
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalCollapse
open TransitiveNameModel
universe u

noncomputable def covers (c x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun p => ∃ n ∈ ZFSet.omega, ZFSet.pair n x ∈ p) c

end TuringRigidity.BoundedSetTheory.InternalCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCountableEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCountableEnumeration
open TransitiveNameModel BoundedSetTheory InternalRelationSelection
open InternalCountableFiniteUnion InternalFiniteEnumeration

def Enumerates (E g : ZFSet.{0}) : Prop :=
  (E = ∅ ∧ g = ∅) ∨ (FunctionGraph ZFSet.omega E g ∧
    ∀ x ∈ E, ∃ n ∈ ZFSet.omega, ZFSet.pair n x ∈ g)

end TuringRigidity.InternalCountableEnumeration

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalSequenceRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalSequenceRange
open TransitiveNameModel BoundedSetTheory

noncomputable def rangeSet (X B : ZFSet.{0}) : ZFSet.{0} :=
  X.sep (fun x => ∃ n ∈ ZFSet.omega, ZFSet.pair n x ∈ B)

noncomputable def unionSet (U S : ZFSet.{0}) : ZFSet.{0} :=
  U.sep (fun x => ∃ E ∈ S, x ∈ E)

end TuringRigidity.InternalSequenceRange

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenColumnRealValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenColumnRealName
open TransitiveNameModel BoundedSetTheory InternalCollapse

theorem singleton_coordinates_subset (K a : ZFSet.{0}) (ha : a ∈ K) :
    ZFSet.prod {a} ZFSet.omega ⊆ ZFSet.prod K ZFSet.omega := by
  intro z hz
  obtain ⟨x,hx,n,hn,rfl⟩ := ZFSet.mem_prod.mp hz
  obtain rfl := ZFSet.mem_singleton.mp hx
  exact ZFSet.pair_mem_prod.mpr ⟨ha,hn⟩

end TuringRigidity.CohenColumnRealName

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenHalting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenHalting
open Encodable UniformOracle

def table (c : ℕ) : List ℕ := (decode c).getD []

end TuringRigidity.CohenHalting

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingOnePoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CodingOnePoint
open CodingForcing

theorem prefix_set_of_le {s t : List Bool} (h : s <+: t) (m : ℕ)
    (hm : s.length ≤ m) (b : Bool) : s <+: t.set m b := by
  obtain ⟨u, rfl⟩ := h
  rw [List.set_append_right _ _ hm]
  exact List.prefix_append _ _

theorem set_prefix_set {s t : List Bool} (h : s <+: t) (m : ℕ)
    (hm : m < s.length) (b : Bool) : s.set m b <+: t.set m b := by
  obtain ⟨u, rfl⟩ := h
  rw [List.set_append_left _ _ hm]
  exact List.prefix_append _ _

end TuringRigidity.CodingOnePoint

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingSplitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CodingSplitting
open CodingForcing

def OnePoint (base : List Bool) (f : List Bool → Part ℕ) : Prop :=
  ∃ s m b v w, base <+: s ∧ base.length ≤ m ∧ m < s.length ∧ v ≠ w ∧
    v ∈ f s ∧ w ∈ f (s.set m b)

theorem interpolate (base : List Bool) (f : List Bool → Part ℕ)
    (hmono : ∀ {s t}, s <+: t → ∀ v, v ∈ f s → v ∈ f t)
    (hdense : ∀ s, base <+: s → ∃ u v, v ∈ f (s ++ u))
    (u : List Bool) : ∀ v : List Bool, u.length = v.length →
      ∀ pre tail, base <+: pre → ∀ a b,
        a ∈ f (pre ++ u ++ tail) → b ∈ f (pre ++ v ++ tail) → a ≠ b → OnePoint base f := by
  induction u with
  | nil =>
    intro v hlen pre tail hpre a b ha hb hab
    have hv : v = [] := List.length_eq_zero_iff.mp hlen.symm
    subst v
    exact False.elim (hab (Part.mem_unique ha hb))
  | cons x u ih =>
    intro v hlen pre tail hpre a b ha hb hab
    cases v with
    | nil => simp at hlen
    | cons y v =>
      have hlen' : u.length = v.length := Nat.succ.inj hlen
      let mid := pre ++ (x :: v) ++ tail
      have hmid : base <+: mid := by
        simpa only [mid, List.append_assoc] using hpre.trans (List.prefix_append pre ((x :: v) ++ tail))
      obtain ⟨extra, c, hc⟩ := hdense mid hmid
      have ha' : a ∈ f ((pre ++ (x :: u) ++ tail) ++ extra) :=
        hmono (List.prefix_append _ _) a ha
      have hb' : b ∈ f ((pre ++ (y :: v) ++ tail) ++ extra) :=
        hmono (List.prefix_append _ _) b hb
      by_cases hcb : c = b
      · apply ih v hlen' (pre ++ [x]) (tail ++ extra)
          (hpre.trans (List.prefix_append _ _)) a c
        · simpa only [List.append_assoc, List.cons_append, List.nil_append] using ha'
        · simpa only [mid, List.append_assoc, List.cons_append, List.nil_append] using hc
        · simpa only [hcb] using hab
      · refine ⟨mid ++ extra, pre.length, y, c, b,
          hmid.trans (List.prefix_append _ _), hpre.length_le, ?_, hcb, hc, ?_⟩
        · simp [mid]
        · have heq : (mid ++ extra).set pre.length y =
              (pre ++ (y :: v) ++ tail) ++ extra := by
            simp [mid, List.append_assoc, List.set_append_right]
          rw [heq]
          exact hb'

theorem onePoint_of_dense {base s t : List Bool} {f : List Bool → Part ℕ}
    (hmono : ∀ {s t}, s <+: t → ∀ v, v ∈ f s → v ∈ f t)
    (hdense : ∀ s, base <+: s → ∃ u v, v ∈ f (s ++ u))
    (hs : base <+: s) (ht : base <+: t) (a b : ℕ)
    (ha : a ∈ f s) (hb : b ∈ f t) (hab : a ≠ b) : OnePoint base f := by
  obtain ⟨u, rfl⟩ := hs
  obtain ⟨v, rfl⟩ := ht
  let L := max u.length v.length
  let u' := u ++ List.replicate (L - u.length) false
  let v' := v ++ List.replicate (L - v.length) false
  have hlu : u'.length = L := by simp only [u', List.length_append, List.length_replicate]; omega
  have hlv : v'.length = L := by simp only [v', List.length_append, List.length_replicate]; omega
  have ha' : a ∈ f (base ++ u') := by
    apply hmono (show base ++ u <+: base ++ u' from ?_) a ha
    exact ⟨List.replicate (L-u.length) false, by simp [u', List.append_assoc]⟩
  have hb' : b ∈ f (base ++ v') := by
    apply hmono (show base ++ v <+: base ++ v' from ?_) b hb
    exact ⟨List.replicate (L-v.length) false, by simp [v', List.append_assoc]⟩
  exact interpolate base f hmono hdense u' v' (hlu.trans hlv.symm)
    base [] List.prefix_rfl a b (by simpa using ha') (by simpa using hb') hab

end TuringRigidity.CodingSplitting

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingSplitSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CodingSplitSearch
open Encodable PrefixComputability

abbrev Witness := (List Bool × (ℕ × Bool)) × (ℕ × (ℕ × ℕ))

def finiteTrial (d : Nat.Partrec.Code) (base : List Bool) (L : List ℕ) (w : Witness) : Option ℕ :=
  let a := d.evaln w.2.2.1 (Nat.pair (encode L) (Nat.pair (encode w.1.1) w.2.1))
  let b := d.evaln w.2.2.2 (Nat.pair (encode L) (Nat.pair (encode (w.1.1.set w.1.2.1 w.1.2.2)) w.2.1))
  if w.1.2.1 < w.1.1.length ∧ a ≠ none ∧ b ≠ none ∧ a.getD 0 ≠ b.getD 0
  then some (base.length + w.1.2.1) else none

end TuringRigidity.CodingSplitSearch

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_OracleEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OracleEnumeration
open PrefixComputability

def searchFlag (p : ℕ) : ℕ :=
  if (Nat.unpair p).1 ≤ (Nat.unpair (Nat.unpair p).2).1 ∧
    (Nat.unpair (Nat.unpair p).2).2 = 1 then 0 else 1

end TuringRigidity.OracleEnumeration

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_RecursiveInfiniteSubset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RecursiveInfiniteSubset
open Encodable PrefixComputability

def Unbounded (E : ℕ → Option ℕ) : Prop := ∀ n, ∃ z m, n ≤ m ∧ m ∈ E z

theorem accepted_exists (E : ℕ → Option ℕ) (h : Unbounded E) (n : ℕ) :
    ∃ z, E z ≠ none ∧ n ≤ (E z).getD 0 := by
  obtain ⟨z, m, hm, hz⟩ := h n
  exact ⟨z, by simp [Option.mem_def.mp hz, hm]⟩

noncomputable def index (E : ℕ → Option ℕ) (h : Unbounded E) (n : ℕ) : ℕ :=
  Nat.find (accepted_exists E h n)

noncomputable def above (E : ℕ → Option ℕ) (h : Unbounded E) (n : ℕ) : ℕ :=
  (E (index E h n)).getD 0

def flag (p : ℕ) : ℕ :=
  let v := (decode (α := Option ℕ) (Nat.unpair p).2).getD none
  if v ≠ none ∧ (Nat.unpair p).1 ≤ v.getD 0 then 0 else 1

noncomputable def growing (E : ℕ → Option ℕ) (h : Unbounded E) : ℕ → ℕ
  | 0 => above E h 0
  | n+1 => above E h (growing E h n + 1)

end TuringRigidity.RecursiveInfiniteSubset

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenColumns
open Encodable UniformOracle CohenHalting

def eraseWord (i : ℕ) (s : List Bool) : List Bool :=
  (List.range s.length).map (fun m => if (Nat.unpair m).1 = i then false else s.getD m false)

@[simp] theorem eraseWord_length (i : ℕ) (s : List Bool) : (eraseWord i s).length = s.length := by
  simp [eraseWord]

end TuringRigidity.CohenColumns

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCountableMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCountableMap
open TransitiveNameModel BoundedSetTheory

noncomputable def composite (A B C f g : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod A C).sep (fun z => ∃ x ∈ A, ∃ y ∈ C,
    z = ZFSet.pair x y ∧ ∃ t ∈ B, ZFSet.pair x t ∈ f ∧ ZFSet.pair t y ∈ g)

end TuringRigidity.InternalCountableMap

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCountableClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCountableClosure
open TransitiveNameModel BoundedSetTheory

noncomputable def retractGraph (A B d : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod A B).sep (fun z => ∃ x ∈ A, ∃ y ∈ B,
    z = ZFSet.pair x y ∧ ((x ∈ B ∧ y = x) ∨ (x ∉ B ∧ y = d)))

end TuringRigidity.InternalCountableClosure

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalFiniteExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalFiniteExhaustion
open TransitiveNameModel BoundedSetTheory

noncomputable def initial (f : ℕ → ZFSet.{0}) (n : ℕ) : ZFSet.{0} :=
  ZFSet.range (fun i : Fin n => f i.val)

end TuringRigidity.InternalFiniteExhaustion

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenProductSplitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenProductSplitting
open TransitiveNameModel BoundedSetTheory
open CohenSymmetry

noncomputable def putBit {ι : Type} (p : Condition ι) (i : ι) (b : Bool) : Condition ι := by
  classical
  exact ⟨fun j => if j = i then some b else p.val j,
    (p.finite.insert i).subset (by intro j hj; by_cases h : j = i <;> simp_all)⟩

end TuringRigidity.CohenProductSplitting

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalNameEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalNameEvaluation
open TransitiveNameModel RelationCollapse
universe u

noncomputable def activeRelation (d g : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ d, ∃ y ∈ d, z = ZFSet.pair x y ∧
    ∃ p ∈ g, ZFSet.pair x p ∈ y) (ZFSet.prod d d)

theorem active_pair (d g x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ activeRelation d g ↔ x ∈ d ∧ y ∈ d ∧ ∃ p ∈ g, ZFSet.pair x p ∈ y := by
  rw [activeRelation,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,a,ha,b,hb,he,hrest⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨ha,hb,hrest⟩
  · rintro ⟨hx,hy,hrest⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩,x,hx,y,hy,rfl,hrest⟩

theorem active_wellFounded (d g : ZFSet.{u}) : WellFounded (Rel d (activeRelation d g)) := by
  apply (InvImage.wf ZFSet.rank Ordinal.lt_wf).mono
  intro x y hxy
  obtain ⟨_,_,p,_,hpair⟩ := (active_pair d g x y).mp hxy.2
  exact (FiniteTerm.pair_rank_left x p).trans (ZFSet.rank_lt_of_mem hpair)

end TuringRigidity.BoundedSetTheory.InternalNameEvaluation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RegularCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RegularCompletion
open Set
universe u
variable {P : Type u} [Preorder P]

abbrev Algebra (P : Type u) [Preorder P] := Heyting.Regular (LowerSet P)

noncomputable instance algebraCompleteBoolean : CompleteBooleanAlgebra (Algebra P) where
  __ := (inferInstance : BooleanAlgebra (Algebra P))
  sSup := (Heyting.Regular.gi (α := LowerSet P)).liftCompleteLattice.sSup
  sInf := (Heyting.Regular.gi (α := LowerSet P)).liftCompleteLattice.sInf
  isLUB_sSup := (Heyting.Regular.gi (α := LowerSet P)).liftCompleteLattice.isLUB_sSup
  isGLB_sInf := (Heyting.Regular.gi (α := LowerSet P)).liftCompleteLattice.isGLB_sInf

theorem mem_compl (U : LowerSet P) (p : P) :
    p ∈ Uᶜ ↔ ∀ q, q ≤ p → q ∉ U := by
  rw [← LowerSet.Iic_le,le_compl_iff_disjoint_left,disjoint_iff]
  constructor
  · intro h q hqp hq
    have hx : q ∈ U ⊓ LowerSet.Iic p := ⟨hq,hqp⟩
    rw [h] at hx
    exact hx
  · intro h
    apply le_antisymm _ bot_le
    intro q hq
    exact False.elim (h q hq.2 hq.1)

end TuringRigidity.RegularCompletion

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalRegularOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalRegularOperations
open Set TransitiveNameModel BoundedSetTheory RegularCompletion

noncomputable def neg (c U : ZFSet.{0}) : ZFSet.{0} :=
  c.sep (fun p => ∀ q ∈ U, ¬ p ⊆ q)

noncomputable def regular (c U : ZFSet.{0}) : ZFSet.{0} := neg c (neg c U)

def Lower (c U : ZFSet.{0}) : Prop :=
  ∀ p ∈ U, ∀ q ∈ c, p ⊆ q → q ∈ U

theorem neg_subset (c U : ZFSet.{0}) : neg c U ⊆ c :=
  fun _ h => (ZFSet.mem_sep.mp h).1

theorem neg_lower (c U : ZFSet.{0}) : Lower c (neg c U) := by
  intro p hp q hq hpq
  refine ZFSet.mem_sep.mpr ⟨hq,?_⟩
  intro r hr hqr
  exact (ZFSet.mem_sep.mp hp).2 r hr (fun z hz => hqr (hpq hz))

theorem union_lower (c F : ZFSet.{0}) (hF : ∀ U ∈ F, Lower c U) :
    Lower c (ZFSet.sUnion F) := by
  intro p hp q hq hpq
  obtain ⟨U,hU,hp⟩ := ZFSet.mem_sUnion.mp hp
  exact ZFSet.mem_sUnion.mpr ⟨U,hU,hF U hU p hp q hq hpq⟩

noncomputable def supCode (c F : ZFSet.{0}) : ZFSet.{0} := regular c (ZFSet.sUnion F)

noncomputable def bitCode (c E : ZFSet.{0}) : ZFSet.{0} :=
  regular c (CohenInternalDecision.below c E)

end TuringRigidity.InternalRegularOperations

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalRegularAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalRegularAlgebra
open Set TransitiveNameModel BoundedSetTheory RegularCompletion InternalRegularOperations

def IsCode (c U : ZFSet.{0}) : Prop := U ⊆ c ∧ regular c U = U

theorem mem_regular (c U p : ZFSet.{0}) :
    p ∈ regular c U ↔ p ∈ c ∧ ∀ q ∈ c, p ⊆ q → ∃ r ∈ U, q ⊆ r := by
  classical
  simp only [regular,neg,ZFSet.mem_sep]
  constructor
  · rintro ⟨hp,h⟩
    refine ⟨hp,fun q hq hpq => ?_⟩
    by_contra hn
    exact h q ⟨hq,fun r hr hqr => hn ⟨r,hr,hqr⟩⟩ hpq
  · rintro ⟨hp,h⟩
    refine ⟨hp,fun q hq hpq => ?_⟩
    obtain ⟨r,hr,hqr⟩ := h q hq.1 hpq
    exact hq.2 r hr hqr

theorem code_lower (c U : ZFSet.{0}) (hU : IsCode c U) : Lower c U := by
  rw [← hU.2]
  exact neg_lower c _

end TuringRigidity.InternalRegularAlgebra

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanSyntax
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra

def Closed (c B Q A : ZFSet.{0}) : Prop :=
  A ⊆ B ∧ (∀ U ∈ A, neg c U ∈ A) ∧
    ∀ F ∈ Q, F ⊆ A → supCode c F ∈ A

noncomputable def candidates (c B Q S : ZFSet.{0}) : ZFSet.{0} :=
  Q.sep (fun A => S ⊆ A ∧ Closed c B Q A)

end TuringRigidity.InternalBooleanSyntax

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalGeneratedAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalGeneratedAlgebra
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalBooleanSyntax

noncomputable def generated (c B Q S : ZFSet.{0}) : ZFSet.{0} :=
  B.sep (fun U => ∀ A ∈ candidates c B Q S, U ∈ A)

end TuringRigidity.InternalGeneratedAlgebra

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalRegularOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalRegularOrder
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra

theorem neg_antitone (c U V : ZFSet.{0}) (h : U ⊆ V) : neg c V ⊆ neg c U := by
  intro p hp
  obtain ⟨hpc,hp⟩ := ZFSet.mem_sep.mp hp
  exact ZFSet.mem_sep.mpr ⟨hpc,fun q hq => hp q (h hq)⟩

theorem regular_mono (c U V : ZFSet.{0}) (h : U ⊆ V) : regular c U ⊆ regular c V :=
  neg_antitone c _ _ (neg_antitone c U V h)

theorem subset_regular (c U : ZFSet.{0}) (hUc : U ⊆ c) (hU : Lower c U) : U ⊆ regular c U := by
  intro p hp
  exact (mem_regular c U p).mpr ⟨hUc hp,fun q hq hpq => ⟨q,hU p hp q hq hpq,fun _ h => h⟩⟩

theorem regular_le_iff (c U V : ZFSet.{0}) (hUc : U ⊆ c) (hU : Lower c U)
    (hV : IsCode c V) : regular c U ⊆ V ↔ U ⊆ V := by
  constructor
  · intro h p hp; exact h (subset_regular c U hUc hU hp)
  · intro h p hp
    have hx := regular_mono c U V h hp
    rwa [hV.2] at hx

theorem union_subset (c F : ZFSet.{0}) (hF : ∀ U ∈ F, IsCode c U) : ZFSet.sUnion F ⊆ c := by
  intro p hp
  obtain ⟨U,hU,hp⟩ := ZFSet.mem_sUnion.mp hp
  exact (hF U hU).1 hp

theorem supCode_le_iff (c F V : ZFSet.{0}) (hF : ∀ U ∈ F, IsCode c U)
    (hV : IsCode c V) : supCode c F ⊆ V ↔ ∀ U ∈ F, U ⊆ V := by
  rw [supCode,regular_le_iff c _ V (union_subset c F hF)
    (union_lower c F (fun U hU => code_lower c U (hF U hU))) hV]
  constructor
  · intro h U hU p hp; exact h (ZFSet.mem_sUnion.mpr ⟨U,hU,hp⟩)
  · intro h p hp
    obtain ⟨U,hU,hp⟩ := ZFSet.mem_sUnion.mp hp
    exact h U hU hp

noncomputable def infCode (c F : ZFSet.{0}) : ZFSet.{0} :=
  c.sep (fun p => ∀ U ∈ F, p ∈ U)

theorem inf_subset (c F : ZFSet.{0}) {U : ZFSet.{0}} (hU : U ∈ F) : infCode c F ⊆ U :=
  fun _ hp => (ZFSet.mem_sep.mp hp).2 U hU

theorem subset_inf (c F U : ZFSet.{0}) (hUc : U ⊆ c) (h : ∀ V ∈ F, U ⊆ V) :
    U ⊆ infCode c F := fun _ hp => ZFSet.mem_sep.mpr ⟨hUc hp,fun V hV => h V hV hp⟩

theorem inf_isCode (c F : ZFSet.{0}) (hF : ∀ U ∈ F, IsCode c U) : IsCode c (infCode c F) := by
  have hc : infCode c F ⊆ c := fun _ h => (ZFSet.mem_sep.mp h).1
  have hl : Lower c (infCode c F) := by
    intro p hp q hq hpq
    exact ZFSet.mem_sep.mpr ⟨hq,fun U hU => code_lower c U (hF U hU)
      p ((ZFSet.mem_sep.mp hp).2 U hU) q hq hpq⟩
  refine ⟨hc,ZFSet.ext (fun p => ⟨?_,fun hp => subset_regular c _ hc hl hp⟩)⟩
  intro hp
  refine ZFSet.mem_sep.mpr ⟨neg_subset c _ hp,fun U hU => ?_⟩
  have hx := regular_mono c (infCode c F) U (inf_subset c F hU) hp
  rwa [(hF U hU).2] at hx

end TuringRigidity.InternalRegularOrder

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

noncomputable def complements (c B F : ZFSet.{0}) : ZFSet.{0} :=
  B.sep (fun V => ∃ U ∈ F, V = neg c U)

noncomputable def uppers (A U : ZFSet.{0}) : ZFSet.{0} := A.sep (fun V => U ⊆ V)

noncomputable def project (c A U : ZFSet.{0}) : ZFSet.{0} := infCode c (uppers A U)

theorem subset_project (c A U : ZFSet.{0}) (hUc : U ⊆ c) : U ⊆ project c A U :=
  subset_inf c _ U hUc (fun _ h => (ZFSet.mem_sep.mp h).2)

end TuringRigidity.InternalBooleanProjection

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_RealGeneratedPart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RealGeneratedPart
open Set RegularCompletion
universe u
variable {P : Type u} [Preorder P]

def tagLower (U : Set P) : LowerSet P where
  carrier := {p | ∃ q ∈ U, p ≤ q}
  lower' := by rintro p q hpq ⟨r,hr,hqr⟩; exact ⟨r,hr,hpq.trans hqr⟩

def bit (N : ℕ → Set P) (n : ℕ) : Algebra P :=
  Heyting.Regular.toRegular (tagLower (N n))

def decision (N : ℕ → Set P) (n : ℕ) : Set P :=
  {p | p ∈ tagLower (N n) ∨ p ∈ (tagLower (N n))ᶜ}

end TuringRigidity.RealGeneratedPart

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanBits
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalBooleanSyntax InternalGeneratedAlgebra

noncomputable def seeds (c B : ZFSet.{0}) (E : ℕ → ZFSet.{0}) : ZFSet.{0} :=
  B.sep (fun U => ∃ n, U = bitCode c (E n))

end TuringRigidity.InternalBooleanBits

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanGeneric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanGeneric
open Set TransitiveNameModel BoundedSetTheory
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder

noncomputable def decision (c U : ZFSet.{0}) : ZFSet.{0} := U ∪ neg c U

end TuringRigidity.InternalBooleanGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanGraph
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalRegularOrder InternalBooleanSyntax InternalBooleanProjection

noncomputable def inclusionOrder (A : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod A A).sep (fun z => ∃ U ∈ A, ∃ V ∈ A, z = ZFSet.pair U V ∧ U ⊆ V)

end TuringRigidity.InternalBooleanGraph

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
open Set TransitiveNameModel BoundedSetTheory
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalGeneratedAlgebra InternalBooleanProjection InternalBooleanGeneric

noncomputable def basicCode (c p : ZFSet.{0}) : ZFSet.{0} := bitCode c {p}

theorem below_lower (c U : ZFSet.{0}) : Lower c (CohenInternalDecision.below c U) := by
  intro p hp q hq hpq
  obtain ⟨_,r,hr,hrp⟩ := ZFSet.mem_sep.mp hp
  exact ZFSet.mem_sep.mpr ⟨hq,r,hr,fun z hz => hpq (hrp hz)⟩

theorem mem_basicCode (c p : ZFSet.{0}) (hp : p ∈ c) : p ∈ basicCode c p := by
  apply subset_regular c _ (fun _ h => (ZFSet.mem_sep.mp h).1) (below_lower c {p})
  exact ZFSet.mem_sep.mpr ⟨hp,p,ZFSet.mem_singleton.mpr rfl,fun _ h => h⟩

def DenseCodes (A D : ZFSet.{0}) : Prop :=
  ∀ U ∈ A, U ≠ ∅ → ∃ V ∈ D, V ∈ A ∧ V ≠ ∅ ∧ V ⊆ U

end TuringRigidity.InternalBooleanDense

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalProjectedGeneric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalProjectedGeneric
open Set TransitiveNameModel BoundedSetTheory
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalGeneratedAlgebra InternalBooleanProjection InternalBooleanGeneric InternalBooleanDense

noncomputable def positive (A : ZFSet.{0}) : ZFSet.{0} := A.sep (fun U => U ≠ ∅)

end TuringRigidity.InternalProjectedGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RegularCodeSplitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RegularCodeSplitting
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalRegularOrder InternalBooleanDense

noncomputable def remainder (U : ZFSet.{0}) (c V : ZFSet.{0}) : ZFSet.{0} :=
  U.sep (fun p => p ∈ neg c V)

def Partition (U V W : ZFSet.{0}) : Prop :=
  V ⊆ U ∧ W ⊆ U ∧ V ≠ ∅ ∧ W ≠ ∅ ∧
    (∀ p ∈ V, p ∉ W) ∧
    ∀ p ∈ U, ∃ r ∈ U, p ⊆ r ∧ (r ∈ V ∨ r ∈ W)

end TuringRigidity.RegularCodeSplitting

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RegularDecisionPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RegularDecisionPartition
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalRegularOrder RegularCodeSplitting

noncomputable def meet (U V : ZFSet.{0}) : ZFSet.{0} := U.sep (fun p => p ∈ V)

def Refines (c U D V W : ZFSet.{0}) : Prop :=
  Partition U V W ∧ (V ⊆ D ∨ V ⊆ neg c D) ∧ (W ⊆ D ∨ W ⊆ neg c D)

end TuringRigidity.RegularDecisionPartition

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RegularTreeCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RegularTreeCompatibility

theorem words_compare (s t : List Bool) :
    s <+: t ∨ t <+: s ∨ ∃ a u v : List Bool,
      (s = a ++ [false] ++ u ∧ t = a ++ [true] ++ v) ∨
      (s = a ++ [true] ++ u ∧ t = a ++ [false] ++ v) := by
  induction s generalizing t with
  | nil => exact Or.inl List.nil_prefix
  | cons b s ih =>
    cases t with
    | nil => exact Or.inr (Or.inl List.nil_prefix)
    | cons d t =>
      by_cases h : b = d
      · subst d
        rcases ih t with h|h|⟨a,u,v,h|h⟩
        · exact Or.inl (by simpa only [List.cons_prefix_cons, true_and] using h)
        · exact Or.inr (Or.inl (by simpa only [List.cons_prefix_cons, true_and] using h))
        · exact Or.inr (Or.inr ⟨b::a,u,v,Or.inl ⟨by simp [h.1],by simp [h.2]⟩⟩)
        · exact Or.inr (Or.inr ⟨b::a,u,v,Or.inr ⟨by simp [h.1],by simp [h.2]⟩⟩)
      · cases b <;> cases d
        · exact False.elim (h rfl)
        · exact Or.inr (Or.inr ⟨[],s,t,Or.inl ⟨rfl,rfl⟩⟩)
        · exact Or.inr (Or.inr ⟨[],s,t,Or.inr ⟨rfl,rfl⟩⟩)
        · exact False.elim (h rfl)

theorem comparable_of_overlap (f : List Bool → ZFSet.{0})
    (hd : ∀ a u v : List Bool, ∀ p ∈ f (a ++ [false] ++ u),
      p ∉ f (a ++ [true] ++ v))
    (s t : List Bool) (p : ZFSet.{0}) (hp : p ∈ f s) (hq : p ∈ f t) :
    s <+: t ∨ t <+: s := by
  rcases words_compare s t with h|h|⟨a,u,v,h|h⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact False.elim (hd a u v p (h.1 ▸ hp) (h.2 ▸ hq))
  · exact False.elim (hd a v u p (h.2 ▸ hq) (h.1 ▸ hp))

end TuringRigidity.RegularTreeCompatibility

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RegularTreeFilter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RegularTreeFilter
open TransitiveNameModel BoundedSetTheory InternalRegularOperations
open InternalRegularAlgebra InternalBooleanGeneric InternalBooleanDense InternalBooleanSyntax

noncomputable def nodeFamily (B A D : ZFSet.{0}) : ZFSet.{0} :=
  B.sep (fun U => ∃ w ∈ D, ZFSet.pair w U ∈ A)

end TuringRigidity.RegularTreeFilter

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RegularTreeRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RegularTreeRecovery
open TransitiveNameModel BoundedSetTheory InternalRegularOperations
open InternalRegularAlgebra InternalBooleanGeneric InternalBooleanDense RegularTreeFilter

noncomputable def recoverySet (c B A S k w : ZFSet.{0}) : ZFSet.{0} :=
  c.sep (fun p => ∃ U ∈ B, ∃ V ∈ S, ∃ s ∈ w,
    ZFSet.pair s U ∈ A ∧ ZFSet.pair p V ∈ k ∧ U ⊆ V)

end TuringRigidity.RegularTreeRecovery

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenPartitionBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenPartitionBridge
open TransitiveNameModel BoundedSetTheory
open CohenProductSplitting

noncomputable def bridge (a b T f g : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod a b).sep (fun z => ∃ x ∈ a, ∃ y ∈ b,
    z = ZFSet.pair x y ∧ ∃ t ∈ T, ZFSet.pair t x ∈ f ∧ ZFSet.pair y t ∈ g)

end TuringRigidity.CohenPartitionBridge

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel
universe u

noncomputable def seed (R : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sUnion (ZFSet.range (fun n : ℕ => iterUnion n ({R} : ZFSet)))

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_CountableElementaryHull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory
universe u

noncomputable def listEnv : List ZFSet.{u} → ℕ → ZFSet.{u}
  | [], _ => ∅
  | x :: _, 0 => x
  | _ :: xs, n+1 => listEnv xs n

noncomputable def envPrefix : ℕ → (ℕ → ZFSet.{u}) → List ZFSet.{u}
  | 0, _ => []
  | n+1, e => e 0 :: envPrefix n (fun i => e (i+1))

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel SentenceForm BoundedSetTheory TransitiveNameModel
universe u

def parameterShift : ℕ → ℕ | 0 => 0 | i+1 => i+2

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleGroundReals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel
universe u

noncomputable def groundReals (M : ZFSet.{u}) : ZFSet.{u} :=
  (ZFSet.powerset ZFSet.omega).sep (fun x => x ∈ M)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelAddition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel
universe u
noncomputable section

def setSucc (x : ZFSet.{u}) : ZFSet.{u} := insert x x

def successorSet : ZFSet.{u} := ZFSet.sep
  (fun z => ∃ x ∈ ZFSet.omega, z = ZFSet.pair x (setSucc x))
  (ZFSet.prod ZFSet.omega ZFSet.omega)

end
end TuringRigidity.SetModelArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CodingColumns
open PrefixComputability OracleEnumeration

def columnStep (k cutoff : ℕ) (p : ℕ) : ℕ :=
  if cutoff ≤ (Nat.unpair p).1 ∧ (Nat.unpair (Nat.unpair p).1).1 = k
  then (Nat.unpair p).2 else 0

end TuringRigidity.CodingColumns

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.UniformProgram
open Encodable Computable
abbrev Code := Nat.Partrec.Code
local instance instDecidableEqCode : DecidableEq Code := Encodable.decidableEqOfEncodable Code

def first : Code → Code
  | .pair c _ | .comp c _ | .prec c _ | .rfind' c => c
  | _ => .zero

def second : Code → Code
  | .pair _ d | .comp _ d | .prec _ d => d
  | _ => .zero

theorem first_primrec : Primrec first := by
  have h := Nat.Partrec.Code.primrec_recOn (α := Code) (σ := Code) Primrec.id
    (Primrec.const Nat.Partrec.Code.zero) (Primrec.const Nat.Partrec.Code.zero)
    (Primrec.const Nat.Partrec.Code.zero) (Primrec.const Nat.Partrec.Code.zero)
    (pr := fun _ c _ _ _ => c) (Primrec.fst.comp Primrec.snd)
    (co := fun _ c _ _ _ => c) (Primrec.fst.comp Primrec.snd)
    (pc := fun _ c _ _ _ => c) (Primrec.fst.comp Primrec.snd)
    (rf := fun _ c _ => c) (Primrec.fst.comp Primrec.snd)
  exact h.of_eq (fun e => by cases e <;> rfl)

theorem second_primrec : Primrec second := by
  have h := Nat.Partrec.Code.primrec_recOn (α := Code) (σ := Code) Primrec.id
    (Primrec.const Nat.Partrec.Code.zero) (Primrec.const Nat.Partrec.Code.zero)
    (Primrec.const Nat.Partrec.Code.zero) (Primrec.const Nat.Partrec.Code.zero)
    (pr := fun _ _ d _ _ => d) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (co := fun _ _ d _ _ => d) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (pc := fun _ _ d _ _ => d) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (rf := fun _ _ _ => Nat.Partrec.Code.zero) (Primrec.const Nat.Partrec.Code.zero)
  exact h.of_eq (fun e => by cases e <;> rfl)

end TuringRigidity.UniformProgram

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.UniformPair
open Encodable UniformOracle
open CodingForcing UniformProgram

def retag (w : ℕ) : ℕ :=
  if (Nat.unpair w).1 = 3 then Nat.pair 2 (Nat.unpair w).2 else w

theorem retag_primrec : Primrec retag := Primrec.ite
  (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 3))
  (Primrec₂.natPair.comp (Primrec.const 2) (Primrec.snd.comp Primrec.unpair)) Primrec.id

end TuringRigidity.UniformPair

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteInjury
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.FiniteInjury

def accept (done : Finset ℕ) (proposal : Option ℕ) : Option ℕ :=
  proposal.bind (fun t => if t ∈ done then none else some t)

def update (done : Finset ℕ) (action : Option ℕ) : Finset ℕ :=
  match action with
  | none => done
  | some t => insert t (done.filter (fun i => i < t))

def state (proposal : ℕ → Finset ℕ → Option ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | s+1 => update (state proposal s) (accept (state proposal s) (proposal s (state proposal s)))

def action (proposal : ℕ → Finset ℕ → Option ℕ) (s : ℕ) : Option ℕ :=
  accept (state proposal s) (proposal s (state proposal s))

open CodingForcing

end TuringRigidity.FiniteInjury

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteInjurySchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.FiniteInjurySchedule
open FiniteInjury

def reset (seen : Finset ℕ) (a : Option ℕ) : Finset ℕ := match a with
  | none => seen
  | some t => seen.filter (fun i => i ≤ t)

end TuringRigidity.FiniteInjurySchedule

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_LocalColumnIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.LocalColumnIndices
open Encodable UniformOracle

def specialized (d : Nat.Partrec.Code) (k : ℕ) : Nat.Partrec.Code :=
  (Nat.Partrec.Code.comp d (.pair (.comp .left .right) (.pair .left (.comp .right .right)))).curry k

end TuringRigidity.LocalColumnIndices

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_StageRecords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.StageRecords
open Encodable UniformOracle FiniteInjurySchedule

def recur (z : ℕ → ℕ) (f : ℕ → ℕ) (a : ℕ) : ℕ → ℕ
  | 0 => z a
  | n+1 => f (Nat.pair a (Nat.pair n (recur z f a n)))

def action (n : ℕ) : Option ℕ := if n = 0 then none else some (n-1)
def actionCode : Option ℕ → ℕ | none => 0 | some n => n+1

@[simp] theorem action_actionCode (a : Option ℕ) : action (actionCode a) = a := by
  cases a <;> simp [action,actionCode]

end TuringRigidity.StageRecords

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
open Encodable UniformOracle CodingForcing FiniteInjury StageRecords
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev f := Primrec.fst.comp Primrec.unpair
abbrev r := Primrec.snd.comp Primrec.unpair

end
end TuringRigidity.LocalComputability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_IndexTuples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IndexTuples
open Encodable

def zeroIndex : ℕ := encode Nat.Partrec.Code.zero

end TuringRigidity.IndexTuples

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RelationPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelationPresentation
open IndexTuples

structure ACode where
  bound : ℕ
  left : ℕ
  right : ℕ

structure SCode where
  bound : ℕ
  tags : ACode
  decorated : ACode

structure RCode (n : ℕ) where
  coordinates : Fin n → SCode
  tuples : ACode

end TuringRigidity.RelationPresentation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_GuardedScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GuardedComputability
open Encodable UniformOracle CodingForcing FiniteInjury StageRecords
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev f := Primrec.fst.comp Primrec.unpair
abbrev r := Primrec.snd.comp Primrec.unpair

end
end TuringRigidity.GuardedComputability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_IdealInterpretation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IdealInterpretation

section Formula
variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]

def nontrivial (b g₀ g₁ x : α) : Prop :=
  x ≤ b ∧ ∃ z, z ≤ g₀ ⊔ x ∧ z ≤ g₁ ⊔ x ∧ ¬ z ≤ x

def antichain (b g₀ g₁ x : α) : Prop :=
  nontrivial b g₀ g₁ x ∧ ∀ y, nontrivial b g₀ g₁ y → y ≤ x → x ≤ y

end Formula

end TuringRigidity.IdealInterpretation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelPrimrec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelFunctions
open BoundedSetTheory TransitiveNameModel SetModelArithmetic
universe u
noncomputable section

variable {M : ZFSet.{u}}

def recValue (f g : ℕ → ℕ) (z n : ℕ) : ℕ :=
  n.rec (f z) (fun y ih => g (Nat.pair z (Nat.pair y ih)))

def recStep (g : ℕ → ℕ) (s : ℕ) : ℕ :=
  Nat.pair (Nat.unpair s).1 (Nat.pair ((Nat.unpair (Nat.unpair s).2).1+1) (g s))

def recStart (f : ℕ → ℕ) (z : ℕ) : ℕ := Nat.pair z (Nat.pair 0 (f z))

end
end TuringRigidity.SetModelFunctions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BoundedDefinability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedDefinability
open BoundedSetTheory TransitiveNameModel SetModelFunctions
universe u
noncomputable section

def mix (e d : ℕ → ZFSet.{u}) (n : ℕ) : ZFSet.{u} :=
  if n % 2 = 0 then e (n/2) else d (n/2)

@[simp] theorem mix_even (e d : ℕ → ZFSet.{u}) (n : ℕ) : mix e d (2*n) = e n := by
  simp [mix]

@[simp] theorem mix_odd (e d : ℕ → ZFSet.{u}) (n : ℕ) : mix e d (2*n+1) = d n := by
  simp [mix,Nat.add_div]

def slotMap (r s : ℕ → ℕ) (n : ℕ) : ℕ :=
  if n%2=0 then 2*r (n/2) else 2*s (n/2)+1

@[simp] theorem slotMap_even (r s : ℕ → ℕ) (n : ℕ) : slotMap r s (2*n) = 2*r n := by
  simp [slotMap]
@[simp] theorem slotMap_odd (r s : ℕ → ℕ) (n : ℕ) : slotMap r s (2*n+1) = 2*s n+1 := by
  simp [slotMap,Nat.add_div]

variable {M : ZFSet.{u}} {P Q : (ℕ → ZFSet.{u}) → Prop}

def bindSlots (n : ℕ) : ℕ :=
  if n%2=0 then if n/2=0 then 0 else 2*(n/2-1)+1 else 2*(n/2)+2

@[simp] theorem bindSlots_zero : bindSlots 0 = 0 := rfl
@[simp] theorem bindSlots_even_succ (n : ℕ) : bindSlots (2*(n+1)) = 2*n+1 := by
  simp [bindSlots]
@[simp] theorem bindSlots_odd (n : ℕ) : bindSlots (2*n+1) = 2*n+2 := by
  simp [bindSlots,Nat.add_div]

end
end TuringRigidity.BoundedDefinability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelArithmeticSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelSyntax
open BoundedSetTheory TransitiveNameModel SetModelArithmetic SetModelFunctions
open BoundedDefinability UniformArithmetic Encodable
universe u
noncomputable section

variable {M : ZFSet.{u}}

def skipInput (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => i+k+1

@[simp] theorem skipInput_zero (k : ℕ) : skipInput k 0 = 0 := rfl
@[simp] theorem skipInput_succ (k i : ℕ) : skipInput k (i+1) = i+k+1 := rfl

end
end TuringRigidity.SetModelSyntax

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SentenceCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.SentenceCoding
open ElementaryModel

def atom (n : ℕ) : ℕ := Nat.pair 0 n
def cell (a b : ℕ) : ℕ := Nat.pair (a+1) b
def binary (tag a b : ℕ) : ℕ := cell (atom tag) (cell a (cell b (atom 0)))
def unary (tag a : ℕ) : ℕ := cell (atom tag) (cell a (atom 0))

def Step (C : ℕ → Prop) (c : ℕ) : Prop :=
  (∃ i j, c = binary 0 (atom i) (atom j)) ∨
  (∃ i j, c = binary 1 (atom i) (atom j)) ∨
  (∃ a b, c = binary 2 a b ∧ C a ∧ C b) ∨
  (∃ a, c = unary 3 a ∧ C a) ∨
  (∃ a, c = unary 4 a ∧ C a)

def Closed (C : ℕ → Prop) : Prop := ∀ c, C c → Step C c

end TuringRigidity.SentenceCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_TupleLookupAdequacy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

variable {M : ZFSet.{u}}

def TupleLookup (G t i x : ZFSet.{u}) : Prop :=
  ∃ n ∈ ZFSet.omega, ∃ g ∈ G, t = ZFSet.pair n g ∧ ZFSet.pair i x ∈ g

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_HierarchyGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

def StageStep (s f r x A : ZFSet.{u}) : Prop :=
  s ⊆ A ∧
  (∀ z ∈ A, z ∈ s ∨ ∃ y ∈ x, ∃ w ∈ r, ZFSet.pair y w ∈ f ∧ z ∈ w) ∧
  ∀ y ∈ x, ∀ w ∈ r, ZFSet.pair y w ∈ f → w ⊆ A

noncomputable def stageImage (s x f : ZFSet.{u}) : ZFSet.{u} :=
  s ∪ (ZFSet.sUnion (iterUnion 2 f)).sep
    (fun z => ∃ y ∈ x, ∃ w ∈ iterUnion 2 f, ZFSet.pair y w ∈ f ∧ z ∈ w)

end TuringRigidity.RelativeConstructible

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

def skipValue (i : ℕ) : ℕ := match i with | 0 => 0 | j+1 => j+2

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructionInputData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

inductive ConstructionInput : Type (u+1)
  | reals
  | stage (o : Ordinal.{u})
  | realPath (path : List ℕ)

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
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelArithmetic
universe u

def bitIndex : List Bool → ℕ → ℕ
  | [], n => n
  | b::bs, n => 2 * bitIndex bs n + if b then 1 else 0

def partBits : ℕ → List Bool
  | 0 => [false]
  | i+1 => true :: partBits i

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_CanonicalAdditionSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelArithmetic
universe u

def AdditionSystem (w d A : ZFSet.{u}) : Prop :=
  TransitiveNameModel.FunctionGraph d w A ∧
  (∃ z ∈ w, z = ∅ ∧ ∀ x ∈ w, ZFSet.pair (ZFSet.pair x z) x ∈ A) ∧
  ∀ x ∈ w, ∀ y ∈ w, ∀ v ∈ w,
    ZFSet.pair (ZFSet.pair x y) v ∈ A →
    ∀ y' ∈ w, ∀ v' ∈ w, y' = insert y y → v' = insert v v →
      ZFSet.pair (ZFSet.pair x y') v' ∈ A

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

def arithmeticSlots : ℕ → ℕ
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | i+6 => i+6

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_HierarchyCertificatePower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding BoundedDefinability SetModelFunctions
universe u

def PowerBound (M a Q : ZFSet.{u}) : Prop :=
  ∀ x, x ∈ Q ↔ x ∈ M ∧ x ⊆ a

def CertificateBounds (M Q B : ZFSet.{u}) : Prop :=
  PowerBound M ZFSet.omega Q ∧ PowerBound M (ZFSet.prod ZFSet.omega ZFSet.omega) B

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeSigmaSchemas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel ElementaryModel SentenceForm
universe u

def replacementImageVars : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n+2 => n+3

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

noncomputable def ordinalCut (A : ZFSet.{u}) : ZFSet.{u} := A.sep ZFSet.IsOrdinal

noncomputable def ordinalHeight (A : ZFSet.{u}) : Ordinal.{u} := (ordinalCut A).rank

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_NativePersistenceSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelSatisfaction
open BoundedSetTheory TransitiveNameModel SetModelFunctions SetModelSyntax
universe u
noncomputable section

def nativeSlots : ℕ → ℕ
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | _+4 => 4

end
end TuringRigidity.SetModelSatisfaction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ElementarySchemas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel SentenceForm
universe u

def sepMap : ℕ → ℕ | 0 => 0 | i+1 => i+3
def relationMap : ℕ → ℕ | 0 => 0 | 1 => 1 | i+2 => i+3
def uniqueMap : ℕ → ℕ | 0 => 0 | 1 => 2 | i+2 => i+4
def imageMap : ℕ → ℕ | 0 => 1 | 1 => 0 | i+2 => i+4

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.NumericSyntax
open ElementaryModel BoundedSetTheory TransitiveNameModel BoundedDefinability RelativeConstructible
universe u

def stageSlots (n : ℕ) : ℕ :=
  if n % 2 = 0 then
    match n / 2 with | 0 => 4 | 1 => 5 | 2 => 6 | 3 => 3 | _ => 2
  else match n / 2 with | 0 => 3 | 1 => 1 | _ => 0

end TuringRigidity.NumericSyntax

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

def ordinalBodySlots (n : ℕ) : ℕ → ℕ
  | 0 => n
  | 1 => n+1
  | k+2 => if k < n then k else n+1

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformHeightDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u
attribute [local irreducible] SentenceForm.bound

noncomputable def realSeedOffset : Ordinal.{u} :=
  (insert ZFSet.omega ZFSet.omega : ZFSet.{u}).rank

noncomputable def heightDomainIndex (a : Ordinal.{u}) : Ordinal.{u} := a - realSeedOffset + 1

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformCohenJump
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.UniformCohenJump
open Encodable UniformPrograms
open CohenHalting
noncomputable section
attribute [local instance] Classical.propDecidable

def trialAnswer (v : ℕ) : Option ℕ :=
  if (Nat.unpair v).1 = 1 ∧
      ((Nat.unpair (Nat.unpair v).2).1 = 1 ∨ (Nat.unpair (Nat.unpair v).2).2 = 0)
    then some (Nat.unpair (Nat.unpair v).2).1 else none

end
end TuringRigidity.UniformCohenJump

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformJumpSimulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.UniformPrograms
open Encodable
noncomputable section
variable {X : Type*}

def haltFlag (v : ℕ) : ℕ :=
  if ((decode (α := Option ℕ) v).getD none).isSome then 0 else 1

end
end TuringRigidity.UniformPrograms

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalOrderType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory
universe u

def TransitiveOn (d r : ZFSet.{u}) : Prop :=
  ∀ x ∈ d, ∀ y ∈ d, ∀ z ∈ d,
    ZFSet.pair x y ∈ r → ZFSet.pair y z ∈ r → ZFSet.pair x z ∈ r

def TotalOn (d r : ZFSet.{u}) : Prop :=
  ∀ x ∈ d, ∀ y ∈ d, x = y ∨ ZFSet.pair x y ∈ r ∨ ZFSet.pair y x ∈ r

end TuringRigidity.RelationCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalOrderTypeSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory ElementaryModel RelativeConstructible
universe u

def OrderTypeCertificate (d r a f : ZFSet.{u}) : Prop :=
  a.IsOrdinal ∧ Graph d r d a f ∧
    ∀ z ∈ a, ∃ x ∈ d, ZFSet.pair x z ∈ f

end TuringRigidity.RelationCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalProductSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse
universe u

def ProductLess (a b x y : ZFSet.{u}) : Prop :=
  ∃ s ∈ b, ∃ t ∈ a, ∃ v ∈ b, ∃ w ∈ a,
    x = ZFSet.pair s t ∧ y = ZFSet.pair v w ∧ (s ∈ v ∨ (s = v ∧ t ∈ w))

noncomputable def productRelation (a b : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun p => ∃ x ∈ ZFSet.prod b a, ∃ y ∈ ZFSet.prod b a,
    p = ZFSet.pair x y ∧ ProductLess a b x y)
      (ZFSet.prod (ZFSet.prod b a) (ZFSet.prod b a))

theorem productRelation_on (a b : ZFSet.{u}) :
    On (ZFSet.prod b a) (productRelation a b) := fun _ h => (ZFSet.mem_sep.mp h).1

theorem pair_mem_productRelation (a b x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ productRelation a b ↔
      x ∈ ZFSet.prod b a ∧ y ∈ ZFSet.prod b a ∧ ProductLess a b x y := by
  rw [productRelation,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,s,hs,t,ht,he,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hs,ht,h⟩
  · rintro ⟨hx,hy,h⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩,x,hx,y,hy,rfl,h⟩

theorem productLess_pair (a b s t v w : ZFSet.{u}) :
    ProductLess a b (ZFSet.pair s t) (ZFSet.pair v w) ↔
      s ∈ b ∧ t ∈ a ∧ v ∈ b ∧ w ∈ a ∧ (s ∈ v ∨ (s = v ∧ t ∈ w)) := by
  simp only [ProductLess,ZFSet.pair_inj]
  constructor
  · rintro ⟨s',hs,t',ht,v',hv,w',hw,⟨rfl,rfl⟩,⟨rfl,rfl⟩,h⟩
    exact ⟨hs,ht,hv,hw,h⟩
  · rintro ⟨hs,ht,hv,hw,h⟩
    exact ⟨s,hs,t,ht,v,hv,w,hw,⟨rfl,rfl⟩,⟨rfl,rfl⟩,h⟩

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalProductPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse
universe u

noncomputable def productValue (a : Ordinal.{u}) (x : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if h : ∃ s t, x = ZFSet.pair s t then
    (a * h.choose.rank + h.choose_spec.choose.rank).toZFSet else ∅

theorem productValue_pair (a : Ordinal.{u}) (s t : ZFSet.{u}) :
    productValue a (ZFSet.pair s t) = (a*s.rank+t.rank).toZFSet := by
  classical
  have h : ∃ v w, ZFSet.pair s t = ZFSet.pair v w := ⟨s,t,rfl⟩
  simp only [productValue,dite_eq_left h]
  obtain ⟨hs,ht⟩ := ZFSet.pair_inj.mp h.choose_spec.choose_spec
  exact congrArg Ordinal.toZFSet (congrArg₂ (fun c d : ZFSet.{u} => a*c.rank+d.rank) hs ht).symm

theorem productValue_lt_iff (a s t v w : Ordinal.{u}) (ht : t < a) (hw : w < a) :
    a*s+t < a*v+w ↔ s < v ∨ (s = v ∧ t < w) := by
  have step (s t v w : Ordinal.{u}) (ht : t < a) (hsv : s < v) :
      a*s+t < a*v+w := by
    have h := (Ordinal.lt_mul_iff.mpr ⟨s,hsv,t,ht,rfl⟩ : a*s+t < a*v)
    exact h.trans_le le_self_add
  constructor
  · intro h
    rcases lt_trichotomy s v with hsv|rfl|hvs
    · exact Or.inl hsv
    · exact Or.inr ⟨rfl,(add_lt_add_iff_left _).mp h⟩
    · exact False.elim ((not_lt_of_gt (step v w s t hw hvs)) h)
  · rintro (hsv|⟨rfl,htw⟩)
    · exact step s t v w ht hsv
    · exact (add_lt_add_iff_left _).mpr htw

theorem productValue_relation (a b : Ordinal.{u}) (x : ZFSet.{u})
    (hx : x ∈ ZFSet.prod b.toZFSet a.toZFSet) (y : ZFSet.{u})
    (hy : y ∈ ZFSet.prod b.toZFSet a.toZFSet) :
    ZFSet.pair x y ∈ productRelation a.toZFSet b.toZFSet ↔
      productValue a x ∈ productValue a y := by
  rw [pair_mem_productRelation,and_iff_right hx,and_iff_right hy]
  obtain ⟨s,hs,t,ht,rfl⟩ := ZFSet.mem_prod.mp hx
  obtain ⟨v,hv,w,hw,rfl⟩ := ZFSet.mem_prod.mp hy
  rw [productLess_pair]
  simp only [hs,ht,hv,hw,true_and,productValue_pair]
  obtain ⟨s,hs,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hs
  obtain ⟨t,ht,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
  obtain ⟨v,hv,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hv
  obtain ⟨w,hw,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hw
  simp only [Ordinal.rank_toZFSet,Ordinal.toZFSet_mem_toZFSet_iff,Ordinal.toZFSet_injective.eq_iff]
  exact (productValue_lt_iff a s t v w (Ordinal.toZFSet_mem_toZFSet_iff.mp ht) (Ordinal.toZFSet_mem_toZFSet_iff.mp hw)).symm

theorem productRelation_wellFounded (a b : Ordinal.{u}) :
    WellFounded (Rel (ZFSet.prod b.toZFSet a.toZFSet) (productRelation a.toZFSet b.toZFSet)) := by
  apply (InvImage.wf (productValue a) ZFSet.mem_wf).mono
  intro x y h
  exact (productValue_relation a b x h.1 y (right_mem (productRelation_on _ _) h.2)).mp h.2

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OmegaPowerStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions
universe u

noncomputable def omegaNext (x : ZFSet.{u}) : ZFSet.{u} :=
  (Ordinal.omega0 ^ (x.rank+1)).toZFSet

def OmegaGraph (M d r f : ZFSet.{u}) : Prop :=
  d.IsOrdinal ∧ FunctionGraph d r f ∧
  ∀ x ∈ d, ∀ v ∈ r, ZFSet.pair x v ∈ f →
    ∃ A ∈ M, StageStep (1 : Ordinal.{u}).toZFSet f r x A ∧
      A.IsOrdinal ∧ v = (A.rank*Ordinal.omega0).toZFSet

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OmegaPowerCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

def ProductCertificates (M : ZFSet.{u}) (a b : Ordinal.{u}) : Prop :=
  ZFSet.prod b.toZFSet a.toZFSet ∈ M ∧ productRelation a.toZFSet b.toZFSet ∈ M ∧
    ∃ f ∈ M, OrderTypeCertificate (ZFSet.prod b.toZFSet a.toZFSet)
      (productRelation a.toZFSet b.toZFSet) (a*b).toZFSet f

def OmegaPowerCertificates (M x : ZFSet.{u}) : Prop :=
  x ∈ M ∧ ∃ f ∈ M, ∃ r ∈ M, OmegaGraph M (x) r f ∧
    ∀ t ∈ x, ProductCertificates M (Ordinal.omega0 ^ t.rank) Ordinal.omega0

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalPairCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
universe u
open Ordinal

noncomputable def pairCode (x y : Ordinal.{u}) : Ordinal.{u} :=
  if y ≤ x then omega0 ^ (x+1) + omega0 ^ y
  else omega0 ^ (y+1) * 2 + omega0 ^ x

noncomputable def unpairCode (a : Ordinal.{u}) : Ordinal.{u} × Ordinal.{u} :=
  let h := (CNF omega0 a).getD 0 (0,0)
  let t := (CNF omega0 a).getD 1 (0,0)
  if h.2 = 1 then (Ordinal.pred h.1,t.1) else (t.1,Ordinal.pred h.1)

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_FiniteOrdinalCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
universe u

noncomputable def vectorCode : {n : ℕ} → (Fin n → Ordinal.{u}) → Ordinal.{u}
  | 0, _ => 1
  | _+1, v => pairCode (v 0) (vectorCode (fun i => v i.succ))

noncomputable def vectorDecode : (n : ℕ) → Ordinal.{u} → Fin n → Ordinal.{u}
  | 0, _, i => Fin.elim0 i
  | n+1, a, i => Fin.cases (unpairCode a).1
      (vectorDecode n (unpairCode a).2) i

noncomputable def paddedCode {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u}) : Ordinal.{u} :=
  pairCode β (vectorCode v)

noncomputable def paddedDecode (n : ℕ) (a : Ordinal.{u}) : Fin n → Ordinal.{u} :=
  vectorDecode n (unpairCode a).2

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalSumSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse
universe u

def leftNode (x : ZFSet.{u}) : ZFSet.{u} := ZFSet.pair ∅ x
def rightNode (x : ZFSet.{u}) : ZFSet.{u} := ZFSet.pair {∅} x

theorem leftNode_inj {x y : ZFSet.{u}} : leftNode x = leftNode y ↔ x = y := by
  simp [leftNode, ZFSet.pair_inj]

theorem rightNode_inj {x y : ZFSet.{u}} : rightNode x = rightNode y ↔ x = y := by
  simp [rightNode, ZFSet.pair_inj]

theorem leftNode_ne_rightNode (x y : ZFSet.{u}) : leftNode x ≠ rightNode y := by
  intro h
  have hz := (ZFSet.pair_inj.mp h).1
  have hm : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := ZFSet.mem_singleton.mpr rfl
  rw [← hz] at hm
  exact ZFSet.notMem_empty _ hm

noncomputable def sumDomain (a b : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod {∅} a ∪ ZFSet.prod {{∅}} b

theorem mem_sumDomain (a b x : ZFSet.{u}) : x ∈ sumDomain a b ↔
    (∃ s ∈ a, x = leftNode s) ∨ (∃ t ∈ b, x = rightNode t) := by
  simp only [sumDomain, ZFSet.mem_union, ZFSet.mem_prod, ZFSet.mem_singleton,
    exists_eq_left, leftNode, rightNode]

def SumLess (a b x y : ZFSet.{u}) : Prop :=
  (∃ s ∈ a, ∃ t ∈ a, x = leftNode s ∧ y = leftNode t ∧ s ∈ t) ∨
  (∃ s ∈ a, ∃ t ∈ b, x = leftNode s ∧ y = rightNode t) ∨
  (∃ s ∈ b, ∃ t ∈ b, x = rightNode s ∧ y = rightNode t ∧ s ∈ t)

noncomputable def sumRelation (a b : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun p => ∃ x ∈ sumDomain a b, ∃ y ∈ sumDomain a b,
    p = ZFSet.pair x y ∧ SumLess a b x y) (ZFSet.prod (sumDomain a b) (sumDomain a b))

theorem sumRelation_on (a b : ZFSet.{u}) : On (sumDomain a b) (sumRelation a b) :=
  fun _ h => (ZFSet.mem_sep.mp h).1

theorem pair_mem_sumRelation (a b x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ sumRelation a b ↔
      x ∈ sumDomain a b ∧ y ∈ sumDomain a b ∧ SumLess a b x y := by
  rw [sumRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_,s,hs,t,ht,he,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hs,ht,h⟩
  · rintro ⟨hx,hy,h⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩,x,hx,y,hy,rfl,h⟩

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalSumPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse
universe u

theorem rightNode_ne_leftNode (x y : ZFSet.{u}) : rightNode x ≠ leftNode y :=
  (leftNode_ne_rightNode y x).symm

attribute [local simp] leftNode_inj rightNode_inj leftNode_ne_rightNode rightNode_ne_leftNode

theorem sumLess_left_left (a b s t : ZFSet.{u}) :
    SumLess a b (leftNode s) (leftNode t) ↔ s ∈ a ∧ t ∈ a ∧ s ∈ t := by
  simp [SumLess]

theorem sumLess_left_right (a b s t : ZFSet.{u}) :
    SumLess a b (leftNode s) (rightNode t) ↔ s ∈ a ∧ t ∈ b := by
  simp [SumLess]

theorem sumLess_right_left (a b s t : ZFSet.{u}) :
    ¬ SumLess a b (rightNode s) (leftNode t) := by
  simp [SumLess]

theorem sumLess_right_right (a b s t : ZFSet.{u}) :
    SumLess a b (rightNode s) (rightNode t) ↔ s ∈ b ∧ t ∈ b ∧ s ∈ t := by
  simp [SumLess]

noncomputable def sumValue (a : Ordinal.{u}) (x : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if h : ∃ s, x = leftNode s then h.choose
    else if k : ∃ s, x = rightNode s then (a + k.choose.rank).toZFSet else ∅

theorem sumValue_left (a : Ordinal.{u}) (s : ZFSet.{u}) :
    sumValue a (leftNode s) = s := by
  classical
  have h : ∃ t, leftNode s = leftNode t := ⟨s,rfl⟩
  simp only [sumValue, dite_eq_left h]
  exact (leftNode_inj.mp h.choose_spec).symm

theorem sumValue_right (a : Ordinal.{u}) (s : ZFSet.{u}) :
    sumValue a (rightNode s) = (a+s.rank).toZFSet := by
  classical
  have h : ¬ ∃ t, rightNode s = leftNode t := by simp
  have k : ∃ t, rightNode s = rightNode t := ⟨s,rfl⟩
  simp only [sumValue, dite_eq_right h, dite_eq_left k]
  rw [← rightNode_inj.mp k.choose_spec]

theorem sumValue_relation (a b : Ordinal.{u}) (x : ZFSet.{u})
    (hx : x ∈ sumDomain a.toZFSet b.toZFSet) (y : ZFSet.{u})
    (hy : y ∈ sumDomain a.toZFSet b.toZFSet) :
    ZFSet.pair x y ∈ sumRelation a.toZFSet b.toZFSet ↔ sumValue a x ∈ sumValue a y := by
  rw [pair_mem_sumRelation, and_iff_right hx, and_iff_right hy]
  rcases (mem_sumDomain _ _ _).mp hx with ⟨s,hs,rfl⟩|⟨s,hs,rfl⟩ <;>
    rcases (mem_sumDomain _ _ _).mp hy with ⟨t,ht,rfl⟩|⟨t,ht,rfl⟩
  · simp only [sumLess_left_left,hs,ht,true_and,sumValue_left]
  · rw [sumLess_left_right,sumValue_left,sumValue_right]
    exact iff_of_true ⟨hs,ht⟩ (Ordinal.toZFSet_monotone le_self_add hs)
  · rw [iff_false_left (sumLess_right_left _ _ _ _),sumValue_right,sumValue_left]
    obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
    rw [Ordinal.toZFSet_mem_toZFSet_iff]
    exact not_lt_of_ge (hc.le.trans le_self_add)
  · rw [sumLess_right_right,sumValue_right,sumValue_right]
    obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hs
    obtain ⟨d,hd,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
    simp only [Ordinal.toZFSet_mem_toZFSet_iff,hc,hd,true_and,Ordinal.rank_toZFSet,
      add_lt_add_iff_left]

theorem sumRelation_wellFounded (a b : Ordinal.{u}) :
    WellFounded (Rel (sumDomain a.toZFSet b.toZFSet) (sumRelation a.toZFSet b.toZFSet)) := by
  apply (InvImage.wf (sumValue a) ZFSet.mem_wf).mono
  intro x y h
  exact (sumValue_relation a b x h.1 y (right_mem (sumRelation_on _ _) h.2)).mp h.2

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

noncomputable def codeScale (twice : Bool) (a : Ordinal.{u}) : Ordinal.{u} :=
  if twice then a*2 else a

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_SumCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions
universe u

def SumCertificates (M : ZFSet.{u}) (a b : Ordinal.{u}) : Prop :=
  sumDomain a.toZFSet b.toZFSet ∈ M ∧ sumRelation a.toZFSet b.toZFSet ∈ M ∧
    ∃ f ∈ M, OrderTypeCertificate (sumDomain a.toZFSet b.toZFSet)
      (sumRelation a.toZFSet b.toZFSet) (a+b).toZFSet f

end TuringRigidity.OrdinalArithmetic

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

noncomputable def codeBranchValue (twice : Bool) (a b : Ordinal.{u}) : Ordinal.{u} :=
  codeScale twice (Ordinal.omega0 ^ (a+1)) + Ordinal.omega0 ^ b

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_CodeBranchCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

def CodeBranchCertificates (M : ZFSet.{u}) (twice : Bool) (a b : Ordinal.{u}) : Prop :=
  (a+1).toZFSet ∈ M ∧ (Ordinal.omega0 ^ (a+1)).toZFSet ∈ M ∧
    (Ordinal.omega0 ^ b).toZFSet ∈ M ∧
    (codeScale twice (Ordinal.omega0 ^ (a+1))).toZFSet ∈ M ∧
    OmegaPowerCertificates M (a+1).toZFSet ∧ OmegaPowerCertificates M b.toZFSet ∧
    (twice = true → SumCertificates M (Ordinal.omega0 ^ (a+1)) (Ordinal.omega0 ^ (a+1))) ∧
    SumCertificates M (codeScale twice (Ordinal.omega0 ^ (a+1))) (Ordinal.omega0 ^ b)

def PairCodeCertificates (M : ZFSet.{u}) (a b : Ordinal.{u}) : Prop :=
  if b ≤ a then CodeBranchCertificates M false a b else CodeBranchCertificates M true b a

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

def vectorTailSlots : ℕ → ℕ
  | 0 => 0
  | i+1 => i+3

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

def entryCodeSlots (n : ℕ) : ℕ → ℕ
  | 0 => n+1
  | i+1 => if i < n then i else n+1

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_VectorCodeCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

def VectorCodeCertificates (M : ZFSet.{u}) : {n : ℕ} → (Fin n → Ordinal.{u}) → Prop
  | 0, _ => True
  | _+1, v =>
    (vectorCode (fun i => v i.succ)).toZFSet ∈ M ∧
      PairCodeCertificates M (v 0) (vectorCode (fun i => v i.succ)) ∧
      VectorCodeCertificates M (fun i => v i.succ)

def PaddedCodeCertificates (M : ZFSet.{u}) {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u}) : Prop :=
  β.toZFSet ∈ M ∧ (vectorCode v).toZFSet ∈ M ∧
    PairCodeCertificates M β (vectorCode v) ∧ VectorCodeCertificates M v

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalDenseInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalDenseInclusion
open TransitiveNameModel BoundedSetTheory

noncomputable def densePull (a b D : ZFSet.{0}) : ZFSet.{0} :=
  a.sep (fun p => ∃ q ∈ b, q ∈ D ∧ q ⊆ p)

end TuringRigidity.InternalDenseInclusion

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_DenseInclusionExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.DenseInclusionExtension
open TransitiveNameModel BoundedSetTheory InternalDenseInclusion

noncomputable def upperSet (b g : ZFSet.{0}) : ZFSet.{0} :=
  b.sep (fun q => ∃ p ∈ g, q ⊆ p)

noncomputable def restrictSet (a k : ZFSet.{0}) : ZFSet.{0} := a.sep (fun p => p ∈ k)

end TuringRigidity.DenseInclusionExtension

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalColumnProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalColumnProjection
open TransitiveNameModel BoundedSetTheory InternalCountableMap

noncomputable def columns (K S : ZFSet.{0}) : ZFSet.{0} :=
  K.sep (fun x => ∃ n ∈ ZFSet.omega, ZFSet.pair x n ∈ S)

noncomputable def projection (K S : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod S (columns K S)).sep (fun z => ∃ s ∈ S, ∃ x ∈ columns K S,
    z = ZFSet.pair s x ∧ ∃ n ∈ ZFSet.omega, s = ZFSet.pair x n)

end TuringRigidity.InternalColumnProjection

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCountableOrdinals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCountableOrdinals
open TransitiveNameModel BoundedSetTheory InternalCountableClosure

def FirstUncountable (M K : ZFSet.{0}) : Prop :=
  K.IsOrdinal ∧ K ∈ M ∧ ¬ (K = ∅ ∨ InternallyCountable M K) ∧
    ∀ a ∈ K, a = ∅ ∨ InternallyCountable M a

end TuringRigidity.InternalCountableOrdinals

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalInverseGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalInverseGraph
open TransitiveNameModel BoundedSetTheory

noncomputable def inverse (A B f : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod B A).sep (fun z => ∃ y ∈ B, ∃ x ∈ A,
    z = ZFSet.pair y x ∧ ZFSet.pair x y ∈ f)

end TuringRigidity.InternalInverseGraph

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalOrderIsoTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalOrderIsoTransport
open TransitiveNameModel BoundedSetTheory

noncomputable def imageSet (b f g : ZFSet.{0}) : ZFSet.{0} :=
  b.sep (fun y => ∃ x ∈ g, ZFSet.pair x y ∈ f)

noncomputable def preimageSet (a f k : ZFSet.{0}) : ZFSet.{0} :=
  a.sep (fun x => ∃ y ∈ k, ZFSet.pair x y ∈ f)

end TuringRigidity.InternalOrderIsoTransport

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalOrdinalSubset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalOrdinalSubset
open TransitiveNameModel BoundedSetTheory RelationCollapse

noncomputable def memberOrder (D : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod D D).sep (fun z => ∃ x ∈ D, ∃ y ∈ D, z = ZFSet.pair x y ∧ x ∈ y)

theorem pair_memberOrder (D x y : ZFSet.{0}) :
    ZFSet.pair x y ∈ memberOrder D ↔ x ∈ D ∧ y ∈ D ∧ x ∈ y := by
  simp only [memberOrder,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,x',hx,y',hy,he,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hx,hy,h⟩
  · rintro ⟨hx,hy,h⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hx,hy⟩,x,hx,y,hy,rfl,h⟩

theorem memberOrder_wf (D : ZFSet.{0}) : WellFounded (Rel D (memberOrder D)) :=
  ZFSet.mem_wf.mono (fun _ _ h => ((pair_memberOrder D _ _).mp h.2).2.2)

end TuringRigidity.InternalOrdinalSubset

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalProductBijection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalProductBijection
open TransitiveNameModel BoundedSetTheory

noncomputable def productGraph (A B W f : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod (ZFSet.prod A W) (ZFSet.prod B W)).sep (fun z =>
    ∃ u ∈ ZFSet.prod A W, ∃ v ∈ ZFSet.prod B W, z = ZFSet.pair u v ∧
      ∃ x ∈ A, ∃ y ∈ B, ∃ n ∈ W, u = ZFSet.pair x n ∧ v = ZFSet.pair y n ∧ ZFSet.pair x y ∈ f)

end TuringRigidity.InternalProductBijection

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalQuotientConditions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalQuotientConditions
open TransitiveNameModel BoundedSetTheory
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalBooleanProjection InternalBooleanDense InternalProjectedGeneric InternalBooleanGeneric

noncomputable def cover (c A p : ZFSet.{0}) : ZFSet.{0} :=
  c.sep (fun r => ∀ U ∈ A, p ∈ U → r ∈ U)

noncomputable def conditions (c A h : ZFSet.{0}) : ZFSet.{0} :=
  c.sep (fun p => project c A (basicCode c p) ∈ h)

theorem conditions_subset (c A h : ZFSet.{0}) : conditions c A h ⊆ c :=
  fun _ hp => (ZFSet.mem_sep.mp hp).1

end TuringRigidity.InternalQuotientConditions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalQuotientRequirement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalQuotientRequirement
open TransitiveNameModel BoundedSetTheory
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax

noncomputable def requirement (c a R : ZFSet.{0}) : ZFSet.{0} :=
  c.sep (fun p => ∃ r ∈ c, r ⊆ p ∧ ∃ V ∈ a, p ∈ V ∧ ZFSet.pair r V ∈ R)

end TuringRigidity.InternalQuotientRequirement

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalSingletonColumn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalSingletonColumn
open TransitiveNameModel BoundedSetTheory

noncomputable def graph (a W : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod (ZFSet.prod {a} W) W).sep (fun z =>
    ∃ u ∈ ZFSet.prod {a} W, ∃ n ∈ W, z = ZFSet.pair u n ∧ u = ZFSet.pair a n)

end TuringRigidity.InternalSingletonColumn

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BooleanExpressionAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BooleanExpressionCertificate
open TransitiveNameModel BoundedSetTheory InternalBooleanSyntax
open InternalRegularOperations InternalRegularAlgebra

noncomputable def children (K F g : ZFSet.{0}) : ZFSet.{0} :=
  K.sep (fun t => ∃ U ∈ F, ZFSet.pair t U ∈ g)

end TuringRigidity.BooleanExpressionCertificate

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BoundedTruthRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedTruthRecursion
open TransitiveNameModel BoundedSetTheory

def dropSlots : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n+2 => n+4

def candidateSlots : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n+2 => n+4

end TuringRigidity.BoundedTruthRecursion

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BooleanExpressionTruth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BooleanExpressionTruth
open TransitiveNameModel BoundedSetTheory

theorem rankWF : WellFounded (fun a b : ZFSet.{0} => ZFSet.rank a < ZFSet.rank b) :=
  InvImage.wf ZFSet.rank Ordinal.lt_wf

end TuringRigidity.BooleanExpressionTruth

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BooleanEvaluationWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BooleanExpressionTruth
open TransitiveNameModel BoundedSetTheory BooleanExpressionCertificate

def truthSlots (t Y K B R z0 z1 z2 : ℕ) : ℕ → ℕ
  | 0 => t
  | 1 => Y
  | 2 => K
  | 3 => B
  | 4 => R
  | 5 => z0
  | 6 => z1
  | _ => z2

end TuringRigidity.BooleanExpressionTruth

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SigmaSequenceTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel BoundedDefinability SetModelFunctions RelativeConstructible
universe u

def SequenceTrace (M : ZFSet.{u}) (S : ZFSet.{u} → ZFSet.{u} → Prop)
    (n x y d r f z : ZFSet.{u}) : Prop :=
  d = insert n n ∧ FunctionGraph d r f ∧ z = ∅ ∧
    ZFSet.pair z x ∈ f ∧ ZFSet.pair n y ∈ f ∧
    ∀ i ∈ n, ∃ j ∈ M, j = insert i i ∧ ∀ v ∈ r, ∀ w ∈ r,
      (ZFSet.pair i v ∈ f ∧ ZFSet.pair j w ∈ f) → S v w

end TuringRigidity.BoundedSetTheory

end OAI
end


