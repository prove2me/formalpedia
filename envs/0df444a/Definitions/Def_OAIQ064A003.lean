-- Prove2me | Definitions.Def_OAIQ064A003
-- name    : OAIQ064A003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T00:30:18.059523+00:00
-- url     : https://prove2.me/theorems/c084747a-b053-4db6-ad10-130f2534cdf0
-- title:
--   Definitions bundle OAIQ064A003 of the split of OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 415 declarations of OpenAI's Lean: 248 definitions, 2 inductive types or structures, 2 instances and 163 theorems. The definitions and types are `OAI.TuringRigidity.BoundedSetTheory.ChoiceCode.graph`, `OAI.TuringRigidity.BoundedSetTheory.DefinesNatural`, `OAI.TuringRigidity.BoundedSetTheory.DefinesPredicate`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTerm.certificateFormula`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTerm.graphFormula`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTerm.stepFormula`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTuple.SkolemGraph`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTuple.Witnesses`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTuple.differenceBody`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTuple.finiteIndex`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTuple.fragment`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTuple.indexSpace`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTuple.occurrences`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTuple.relation`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTuple.relationFormula`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTuple.relativizeBounded`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTuple.unpack`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTuple.witnessBody`, `OAI.TuringRigidity.BoundedSetTheory.Formula.addition`, `OAI.TuringRigidity.BoundedSetTheory.Formula.additionTrace`, `OAI.TuringRigidity.BoundedSetTheory.Formula.appMem`, `OAI.TuringRigidity.BoundedSetTheory.Formula.arithmeticComp`, `OAI.TuringRigidity.BoundedSetTheory.Formula.arithmeticExists`, `OAI.TuringRigidity.BoundedSetTheory.Formula.degreeLE`, `OAI.TuringRigidity.BoundedSetTheory.Formula.degreeOrderMember`, `OAI.TuringRigidity.BoundedSetTheory.Formula.degreeSet`, `OAI.TuringRigidity.BoundedSetTheory.Formula.degreeUniverseMember`, `OAI.TuringRigidity.BoundedSetTheory.Formula.envBound`, `OAI.TuringRigidity.BoundedSetTheory.Formula.isHull`, `OAI.TuringRigidity.BoundedSetTheory.Formula.iteration`, `OAI.TuringRigidity.BoundedSetTheory.Formula.iterationTrace`, `OAI.TuringRigidity.BoundedSetTheory.Formula.leftPair`, `OAI.TuringRigidity.BoundedSetTheory.Formula.modelIteration`, `OAI.TuringRigidity.BoundedSetTheory.Formula.modelIterationTrace`, `OAI.TuringRigidity.BoundedSetTheory.Formula.multiplication`, `OAI.TuringRigidity.BoundedSetTheory.Formula.naturalPair`, `OAI.TuringRigidity.BoundedSetTheory.Formula.naturalProjection`, `OAI.TuringRigidity.BoundedSetTheory.Formula.naturalRelationBit`, `OAI.TuringRigidity.BoundedSetTheory.Formula.numericComposition`, `OAI.TuringRigidity.BoundedSetTheory.Formula.numericPair` and 210 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DegreeRigidity_CohenForcing_CheckedForcingRelation`, `DegreeRigidity_CohenForcing_CohenAntichainSelector`, `DegreeRigidity_CohenForcing_CohenAntichainSequence`, `DegreeRigidity_CohenForcing_CohenAntichainStages`, `DegreeRigidity_CohenForcing_CohenBorelForcing`, `DegreeRigidity_CohenForcing_CohenColumnRealName`, `DegreeRigidity_CohenForcing_CohenColumns`, `DegreeRigidity_CohenForcing_CohenConditionCode`, `DegreeRigidity_CohenForcing_CohenFactorRequirement`, `DegreeRigidity_CohenForcing_CohenFiniteFlip`, `DegreeRigidity_CohenForcing_CohenGenericUnion`, `DegreeRigidity_CohenForcing_CohenGroundGeneric`, `DegreeRigidity_CohenForcing_CohenGroundPoset`, `DegreeRigidity_CohenForcing_CohenHalting`, `DegreeRigidity_CohenForcing_CohenInternalSupport`, `DegreeRigidity_CohenForcing_CohenLowness`, `DegreeRigidity_CohenForcing_CohenProductFilters`, `DegreeRigidity_CohenForcing_CohenSizeLevels`, `DegreeRigidity_CohenForcing_CountableForcing`, `DegreeRigidity_CohenForcing_InternalCohenBitFlip`, `DegreeRigidity_CohenForcing_InternalCohenConditions`, `DegreeRigidity_CohenForcing_InternalCohenRestriction`, `DegreeRigidity_CohenForcing_TaggedProductConditions`, `DegreeRigidity_Computability_ArithmeticOracles`, `DegreeRigidity_Computability_ArithmeticParameterFormula`, `DegreeRigidity_Computability_ArithmeticRelations`, `DegreeRigidity_Computability_ArithmeticSetSyntax`, `DegreeRigidity_Computability_ArithmeticTables`, `DegreeRigidity_Computability_BranchMachine`, `DegreeRigidity_Computability_OracleCode`, `DegreeRigidity_Computability_OracleEnumeration`, `DegreeRigidity_Computability_OracleJump`, `DegreeRigidity_Computability_UniformArithmetic`, `DegreeRigidity_Constructibility_ConstructibleTupleSpace`, `DegreeRigidity_Effective_CodingAgreement`, `DegreeRigidity_Effective_CodingColumns`, `DegreeRigidity_Effective_CodingExtraction`, `DegreeRigidity_Effective_CodingForcing`, `DegreeRigidity_Effective_CodingLocations`, `DegreeRigidity_Effective_CodingOnePoint`, `DegreeRigidity_Effective_CodingSplitSearch`, `DegreeRigidity_Effective_EffectiveCohen`, `DegreeRigidity_Effective_EffectiveFamilies`, `DegreeRigidity_Effective_EffectivePresentation`, `DegreeRigidity_Effective_EffectiveSplitConditions`, `DegreeRigidity_Effective_FiniteCodeBound`, `DegreeRigidity_Effective_FiniteExtensionCode`, `DegreeRigidity_Effective_FiniteInjuryLimits`, `DegreeRigidity_Effective_FiniteInjurySchedule`, `DegreeRigidity_Effective_FiniteJoinSections`, `DegreeRigidity_Effective_FiniteNaturalGraph`, `DegreeRigidity_Effective_FiniteOverwrite`, `DegreeRigidity_Effective_FiniteShuffle`, `DegreeRigidity_Effective_FiniteTranscript`, `DegreeRigidity_Effective_FiniteTuple`, `DegreeRigidity_Effective_GuardedComputability`, `DegreeRigidity_Effective_GuardedPair`, `DegreeRigidity_Effective_PartialComputability`, `DegreeRigidity_Effective_ProgramSelection`, `DegreeRigidity_Effective_StablePair`, `DegreeRigidity_Effective_TableIndices`, `DegreeRigidity_Effective_TupleFormula`, `DegreeRigidity_Effective_TupleRelation`, `DegreeRigidity_Effective_UniformAgreement`, `DegreeRigidity_Effective_UniformPair`, `DegreeRigidity_Effective_UniformProgram`, `DegreeRigidity_Effective_UniformRun`, `DegreeRigidity_Effective_UniformSplit`, `DegreeRigidity_OrdinalCodes_NaturalAdditionTrace`, `DegreeRigidity_OrdinalCodes_NaturalDefinitions`, `DegreeRigidity_OrdinalCodes_NaturalIterationFormula`, `DegreeRigidity_OrdinalCodes_NaturalIterationTrace`, `DegreeRigidity_OrdinalCodes_NaturalMultiplicationFormula`, `DegreeRigidity_OrdinalCodes_NaturalPairingFormula`, `DegreeRigidity_OrdinalCodes_NaturalPrimitiveRecursion`, `DegreeRigidity_OrdinalCodes_NaturalProjectionFormula`, `DegreeRigidity_OrdinalCodes_NaturalTermFormula`, `DegreeRigidity_OrdinalCodes_RankGraphConstruction`, `DegreeRigidity_OrdinalCodes_RankRecursion`, `DegreeRigidity_Representation_Assembly`, `DegreeRigidity_Representation_CategoryMachine`, `DegreeRigidity_Representation_CategoryReduction`, `DegreeRigidity_Representation_CommonIdeal`, `DegreeRigidity_Representation_CommonIdealSearch`, `DegreeRigidity_Representation_CommonIdealSelection`, `DegreeRigidity_Representation_GenericCoding`, `DegreeRigidity_Representation_GenericFilterName`, `DegreeRigidity_Representation_GenericIdentity`, `DegreeRigidity_Representation_GenericRepresentation`, `DegreeRigidity_Representation_GenericTotality`, `DegreeRigidity_Representation_GenericTruth`, `DegreeRigidity_Representation_GroundInclusion`, `DegreeRigidity_Representation_SourceIdentity`, `DegreeRigidity_SetModels_ChoiceFromOrdinalCover`, `DegreeRigidity_SetModels_ChoiceTrace`, `DegreeRigidity_SetModels_ChoiceTraceExtension`, `DegreeRigidity_SetModels_ChoiceTraceFormula`, `DegreeRigidity_SetModels_CollapseCoding`, `DegreeRigidity_SetModels_ConservativeExtension`, `DegreeRigidity_SetModels_CountableBound`, `DegreeRigidity_SetModels_CountedRegularBasis`, `DegreeRigidity_SetModels_DegreeSetFormula`, `DegreeRigidity_SetModels_EnumerationDecoding`, `DegreeRigidity_SetModels_ExtensionBasicAxioms`, `DegreeRigidity_SetModels_FiniteSkolem`, `DegreeRigidity_SetModels_FixedArithmetic`, `DegreeRigidity_SetModels_FragmentHull`, `DegreeRigidity_SetModels_GeneratedHull`, `DegreeRigidity_SetModels_IdealInterpretation`, `DegreeRigidity_SetModels_IdealSelection`, `DegreeRigidity_SetModels_InternalChoice`, `DegreeRigidity_SetModels_InternalCollapseConditions`, `DegreeRigidity_SetModels_InternalCollapseCounting`, `DegreeRigidity_SetModels_InternalCollapseDense`, `DegreeRigidity_SetModels_InternalFiniteSubsets`, `DegreeRigidity_SetModels_InternalFunctionOrbit`, `DegreeRigidity_SetModels_InternalHull`, `DegreeRigidity_SetModels_InternalMinimalSelector`, `DegreeRigidity_SetModels_InternalNameEvaluation`, `DegreeRigidity_SetModels_InternalNaturalRelationReal`, `DegreeRigidity_SetModels_InternalProjectedGeneric`, `DegreeRigidity_SetModels_InternalRelationCollapse`, `DegreeRigidity_SetModels_InternalSerialSelection`, `DegreeRigidity_SetModels_InternalUniformization`, `DegreeRigidity_SetModels_ModelArithmeticComprehension`, `DegreeRigidity_SetModels_ModelDegreeOrder`, `DegreeRigidity_SetModels_ModelDegreeUniverse`, `DegreeRigidity_SetModels_ModelIterationFormula`, `DegreeRigidity_SetModels_ModelIterationTrace`, `DegreeRigidity_SetModels_ModelReals`, `DegreeRigidity_SetModels_NameDifferenceDense`, `DegreeRigidity_SetModels_NameExtension`, `DegreeRigidity_SetModels_NameUnionCode`, `DegreeRigidity_SetModels_OrderedNameCode`, `DegreeRigidity_SetModels_RecursiveNames`, `DegreeRigidity_SetModels_RelationCollapse`, `DegreeRigidity_SetModels_RelationHull`, `DegreeRigidity_SetModels_ShuffleRequirements`, `DegreeRigidity_SetModels_SkolemOperations`, `DegreeRigidity_Syntax_BoundedTruthRecursion`, `DegreeRigidity_Syntax_CertificateMatrix`, `DegreeRigidity_Syntax_CheckGraphConstruction`, `DegreeRigidity_Syntax_CheckedCode`, `DegreeRigidity_Syntax_FiniteFragment`, `DegreeRigidity_Syntax_FiniteModelGraph`, `DegreeRigidity_Syntax_FormulaIsomorphism`, `DegreeRigidity_Syntax_PrimitivePredicateFormula`, `DegreeRigidity_Syntax_SigmaBoundedUniversal`, `DegreeRigidity_Syntax_SigmaHull`, `DegreeRigidity_Syntax_TermEvaluationGraph`, `DegreeRigidity_Syntax_TermFormula`.
--
--   **Imports.** It imports the published bundle `Def_DegreeRigidity`; the bundles `OAIQ064A000` and `OAIQ064A001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ064A005`, `OAIQ064A006` and `OAIQ064A007`; the statements `OAI.TuringRigidity.ArithmeticPersistence.persistent_iff`, `OAI.TuringRigidity.ArithmeticTree.native_nonidentity_absolute`, `OAI.TuringRigidity.ArithmeticTree.native_persistence_absolute`, `OAI.TuringRigidity.ArithmeticTree.setGenericallyPersistent_iff`, `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.real_collapse_reconstructs`, `OAI.TuringRigidity.CohenAbsorptionGeneric.product_generic_absorption`, `OAI.TuringRigidity.CohenManyAbsorption.same_generics_absorption`, `OAI.TuringRigidity.CohenRemainderTransport.transport_to_remainder`, `OAI.TuringRigidity.EnumerationConstruction.enumeration_exists`, `OAI.TuringRigidity.LocalUnary.localized_copy`, `OAI.TuringRigidity.RelativeConstructible.global_arithmetic_generic_program` and `OAI.TuringRigidity.SetModelPersistence.persistent_decoding`.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A000
import Definitions.Def_OAIQ064A001

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CountableForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CountableForcing
open Set

def GenericFor {P : Type*} [Preorder P] (D : ℕ → Set P) (G : GenericFilter P) : Prop :=
  ∀ n, ∃ p ∈ G.carrier, p ∈ D n

end TuringRigidity.CountableForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RecursiveNames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RecursiveNames
open Set CountableForcing
universe u
variable {P : Type u}

namespace Name

def checkPSet [Top P] : PSet.{u} → Name P
  | .mk ι child => .mk ι (fun i => checkPSet (child i)) (fun _ => ⊤)

noncomputable def check [Top P] (x : ZFSet.{u}) : Name P := checkPSet x.out

end Name
end TuringRigidity.RecursiveNames

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_NameExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RecursiveNames
open Set CountableForcing
universe u
variable {P : Type u}

namespace Name

def pair [Top P] (σ τ : Name P) : Name P :=
  .mk (ULift Bool) (fun i => if i.down then σ else τ) (fun _ => ⊤)

end Name

end TuringRigidity.RecursiveNames

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalHull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

noncomputable def hull (d q x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∀ c ∈ q, Transitive c → x ∈ c → z ∈ c) d

theorem mem_hull (d q x z : ZFSet.{u}) :
    z ∈ hull d q x ↔ z ∈ d ∧ ∀ c ∈ q, Transitive c → x ∈ c → z ∈ c :=
  ZFSet.mem_sep

theorem hull_subset (d q x : ZFSet.{u}) : hull d q x ⊆ d :=
  fun _ hz => (mem_hull _ _ _ _).mp hz |>.1

theorem self_mem_hull (d q : ZFSet.{u}) {x : ZFSet.{u}} (hx : x ∈ d) :
    x ∈ hull d q x := (mem_hull _ _ _ _).mpr ⟨hx,fun _ _ _ h => h⟩

theorem hull_transitive (d q x : ZFSet.{u}) (hd : Transitive d) :
    Transitive (hull d q x) := by
  intro y hy z hz
  obtain ⟨hyd,hyc⟩ := (mem_hull _ _ _ _).mp hy
  exact (mem_hull _ _ _ _).mpr
    ⟨hd y hyd z hz,fun c hc ht hx => ht y (hyc c hc ht hx) z hz⟩

theorem hull_least (d q x c : ZFSet.{u}) (hcq : c ∈ q)
    (hc : Transitive c) (hx : x ∈ c) : hull d q x ⊆ c :=
  fun _ hz => (mem_hull _ _ _ _).mp hz |>.2 c hcq hc hx

namespace Formula
def isHull (c x _d q : ℕ) : Formula :=
  .conj (.member c q) (.conj (transitive c) (.conj (.member x c)
    (allMem q (imp (.conj (transitive 0) (.member (x+1) 0)) (subset (c+1) 0)))))

theorem eval_isHull (c x d q : ℕ) (e : ℕ → ZFSet.{u}) :
    (isHull c x d q).Eval e ↔ e c ∈ e q ∧ Transitive (e c) ∧ e x ∈ e c ∧
      ∀ b ∈ e q, Transitive b → e x ∈ b → e c ⊆ b := by
  simp only [isHull, Eval, eval_transitive, eval_allMem, eval_imp,
    eval_subset, cons_zero, cons_succ]
  simp only [and_imp]
end Formula

end TuringRigidity.BoundedSetTheory

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

namespace Code
open Formula

def closed (d r b : ℕ) : Formula :=
  allMem b (allMem (d+1) (imp (pairMem 0 1 (r+2)) (.member 0 (b+2))))

theorem eval_closed (d r b : ℕ) (e : ℕ → ZFSet.{u}) :
    (closed d r b).Eval e ↔ Closed (e d) (e r) (e b) := by
  simp only [closed,Closed,eval_allMem,eval_imp,eval_pairMem,Formula.Eval,cons_zero,cons_succ]

def member : Formula := allMem 2
  (imp (.conj (closed 4 5 0) (.member 2 0)) (.member 1 0))

theorem eval_member (z x q d r : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    member.Eval (cons z (cons x (cons q (cons d (cons r e))))) ↔
      ∀ b ∈ q, Closed d r b → x ∈ b → z ∈ b := by
  simp only [member,eval_allMem,eval_imp,Formula.Eval,eval_closed,cons_zero,cons_succ]
  exact forall_congr' (fun b => forall_congr' (fun _ => and_imp))

def isHull (b x q d r : ℕ) : Formula :=
  .conj (.member b q) (.conj (closed d r b) (.conj (.member x b)
    (allMem q (imp (.conj (closed (d+1) (r+1) 0) (.member (x+1) 0)) (subset (b+1) 0)))))

theorem eval_isHull (b x q d r : ℕ) (e : ℕ → ZFSet.{u}) :
    (isHull b x q d r).Eval e ↔ e b ∈ e q ∧ Closed (e d) (e r) (e b) ∧ e x ∈ e b ∧
      ∀ a ∈ e q, Closed (e d) (e r) a → e x ∈ a → e b ⊆ a := by
  simp only [isHull,Formula.Eval,eval_closed,eval_allMem,eval_imp,eval_subset,cons_zero,cons_succ]
  simp only [and_imp]
end Code

end TuringRigidity.RelationHull

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
open Set RecursiveNames BoundedSetTheory
universe u

def unionFormula : Formula :=
  .existsMem 3 (.existsMem 5
    (.conj (.orderedPair 2 1 0)
      (.existsMem 4 (.existsMem 7 (.existsMem 8
        (.conj (.pairMem 2 1 6) (.conj (.pairMem 4 0 2)
          (.conj (.pairMem 3 1 10) (.pairMem 3 0 10)))))))))

theorem eval_unionFormula (t p r z : ZFSet.{u}) (env : ℕ → ZFSet.{u}) :
    unionFormula.Eval (cons z (cons t (cons (iterUnion 2 t)
      (cons (iterUnion 5 t) (cons p (cons r env)))))) ↔ unionPredicate t p r z := by
  simp only [unionFormula,Formula.Eval,cons_succ,cons_zero,
    Formula.eval_orderedPair,Formula.eval_pairMem,unionPredicate]

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
open RecursiveNames BoundedSetTheory
universe u

theorem encode_checkPSet {P : Type u} [Top P] (l : P → ZFSet.{u}) (x : PSet.{u}) :
    (Name.checkPSet x : Name P).encode l = checkedCode (l ⊤) (ZFSet.mk x) := by
  induction x with
  | mk ι child ih =>
    apply ZFSet.ext
    intro z
    change z ∈ ZFSet.range _ ↔ _
    rw [ZFSet.mem_range,mem_checkedCode]
    constructor
    · rintro ⟨i,hi⟩
      refine ⟨ZFSet.mk (child i),?_,by simpa only [ih] using hi.symm⟩
      change ∃ j, PSet.Equiv (child i) (child j)
      exact ⟨i,PSet.Equiv.refl _⟩
    · rintro ⟨y,hy,hz⟩
      induction y using Quotient.inductionOn with
      | h y =>
        change ∃ i, PSet.Equiv y (child i) at hy
        obtain ⟨i,hi⟩ := hy
        have he : ZFSet.mk y = ZFSet.mk (child i) := Quotient.sound hi
        change z = ZFSet.pair (checkedCode (l ⊤) (ZFSet.mk y)) (l ⊤) at hz
        rw [he] at hz
        exact ⟨i,by simpa only [ih] using hz.symm⟩

theorem encode_check {P : Type u} [Top P] (l : P → ZFSet.{u}) (x : ZFSet.{u}) :
    (Name.check x : Name P).encode l = checkedCode (l ⊤) x := by
  rw [Name.check,encode_checkPSet,ZFSet.mk_out]

def CheckGraph (d r f t : ZFSet.{u}) : Prop :=
  Transitive d ∧
  (∀ z ∈ f, ∃ x ∈ d, ∃ y ∈ r, z = ZFSet.pair x y) ∧
  (∀ x ∈ d, ∃ y ∈ r, ZFSet.pair x y ∈ f ∧
    ∀ z ∈ r, ZFSet.pair x z ∈ f → z = y) ∧
  (∀ x ∈ d, ∀ y ∈ r, ZFSet.pair x y ∈ f → RecursionStep f r t x y)

theorem CheckGraph.correct {d r f t : ZFSet.{u}} (h : CheckGraph d r f t)
    (x : ZFSet.{u}) (hx : x ∈ d) (v : ZFSet.{u}) (hv : v ∈ r)
    (hfv : ZFSet.pair x v ∈ f) : v = checkedCode t x := by
  induction x using ZFSet.inductionOn generalizing v with
  | h x ih =>
    have hs := h.2.2.2 x hx v hv hfv
    apply ZFSet.ext
    intro z
    rw [mem_checkedCode]
    constructor
    · intro hz
      obtain ⟨y,hy,w,hw,hfw,rfl⟩ := hs.1 z hz
      exact ⟨y,hy,by rw [ih y hy (h.1 x hx y hy) w hw hfw]⟩
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨w,hw,hfw,_⟩ := h.2.2.1 y (h.1 x hx y hy)
      rw [←ih y hy (h.1 x hx y hy) w hw hfw]
      exact hs.2 y hy w hw hfw

theorem CheckGraph.unique {d r s f g t : ZFSet.{u}}
    (hf : CheckGraph d r f t) (hg : CheckGraph d s g t) : f = g := by
  apply ZFSet.ext
  intro z
  have forward {r s f g : ZFSet.{u}} (hf : CheckGraph d r f t)
      (hg : CheckGraph d s g t) (hz : z ∈ f) : z ∈ g := by
    obtain ⟨x,hx,y,hy,rfl⟩ := hf.2.1 z hz
    obtain ⟨v,hv,hgv,_⟩ := hg.2.2.1 x hx
    have he := (hf.correct x hx y hy hz).trans (hg.correct x hx v hv hgv).symm
    exact he ▸ hgv
  exact ⟨forward hf hg,forward hg hf⟩

namespace CheckFormula
open BoundedSetTheory.Formula

def step (f r t x v : ℕ) : Formula :=
  .conj (allMem v (.existsMem (x+1) (.existsMem (r+2)
    (.conj (pairMem 1 0 (f+3)) (orderedPair 2 0 (t+3))))))
    (allMem x (allMem (r+1) (imp (pairMem 1 0 (f+2))
      (.existsMem (v+2) (orderedPair 0 1 (t+3))))))

theorem eval_step (f r t x v : ℕ) (e : ℕ → ZFSet.{u}) :
    (step f r t x v).Eval e ↔ RecursionStep (e f) (e r) (e t) (e x) (e v) := by
  simp only [step, Formula.Eval, eval_allMem, eval_pairMem, eval_orderedPair,
    eval_imp, cons_zero, cons_succ, RecursionStep]
  simp only [exists_eq_right]

def graph (d r f t : ℕ) : Formula :=
  .conj (transitive d) (.conj (functionGraph f d r)
    (allMem d (allMem (r+1) (imp (pairMem 1 0 (f+2)) (step (f+2) (r+2) (t+2) 1 0)))))

theorem eval_graph (d r f t : ℕ) (e : ℕ → ZFSet.{u}) :
    (graph d r f t).Eval e ↔ CheckGraph (e d) (e r) (e f) (e t) := by
  simp only [graph, Formula.Eval, eval_transitive, eval_functionGraph,
    eval_allMem, eval_imp, eval_pairMem, eval_step, cons_zero, cons_succ, CheckGraph]
  exact and_congr_right (fun _ => and_assoc)
end CheckFormula

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
open RecursiveNames BoundedSetTheory
universe u

def taggedImageFormula : Formula :=
  .existsMem 1 (.existsMem 4 (.conj (.pairMem 1 0 4) (.orderedPair 2 0 6)))

theorem eval_taggedImageFormula (z x f r t : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    taggedImageFormula.Eval (cons z (cons x (cons f (cons r (cons t e))))) ↔
      ∃ y ∈ x, ∃ w ∈ r, ZFSet.pair y w ∈ f ∧ z = ZFSet.pair w t := by
  simp only [taggedImageFormula,Formula.Eval,Formula.eval_pairMem,
    Formula.eval_orderedPair,cons_zero,cons_succ]

theorem CheckGraph.mem_iff {d r f t : ZFSet.{u}} (h : CheckGraph d r f t)
    (z : ZFSet.{u}) :
    z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (checkedCode t x) := by
  constructor
  · intro hz
    obtain ⟨x,hx,y,hy,rfl⟩ := h.2.1 z hz
    exact ⟨x,hx,by rw [h.correct x hx y hy hz]⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨y,hy,hfy,_⟩ := h.2.2.1 x hx
    rw [←h.correct x hx y hy hfy]
    exact hfy

theorem checkGraph_of_mem_iff (d f t : ZFSet.{u}) (hd : Transitive d)
    (hf : ∀ z, z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (checkedCode t x)) :
    CheckGraph d (iterUnion 2 f) f t := by
  have hpair (x v : ZFSet.{u}) : ZFSet.pair x v ∈ f ↔ x ∈ d ∧ v = checkedCode t x := by
    rw [hf]
    constructor
    · rintro ⟨y,hy,he⟩
      obtain ⟨rfl,hv⟩ := ZFSet.pair_inj.mp he
      exact ⟨hy,hv⟩
    · rintro ⟨hx,rfl⟩
      exact ⟨x,hx,rfl⟩
  refine ⟨hd,?_,?_,?_⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := (hf z).mp hz
    exact ⟨x,hx,checkedCode t x,second_mem_doubleUnion hz,rfl⟩
  · intro x hx
    have hp := (hpair x _).mpr ⟨hx,rfl⟩
    exact ⟨_,second_mem_doubleUnion hp,hp,fun v _ hv => (hpair x v).mp hv |>.2⟩
  · intro x hx v _ hv
    have he := (hpair x v).mp hv |>.2
    subst v
    constructor
    · intro z hz
      obtain ⟨y,hy,rfl⟩ := (mem_checkedCode t x z).mp hz
      have hp := (hpair y _).mpr ⟨hd x hx y hy,rfl⟩
      exact ⟨y,hy,_,second_mem_doubleUnion hp,hp,rfl⟩
    · intro y hy w _ hw
      rw [(hpair y w).mp hw |>.2]
      exact (mem_checkedCode t x _).mpr ⟨y,hy,rfl⟩

end TuringRigidity.TransitiveNameModel

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

namespace Code
open Formula

def step (d r b f x v : ℕ) : Formula :=
  .conj (allMem v (.existsMem (d+1)
    (.conj (pairMem 0 (x+2) (r+2)) (pairMem 0 1 (f+2)))))
    (allMem d (imp (pairMem 0 (x+1) (r+1))
      (allMem (b+1) (imp (pairMem 1 0 (f+2)) (.member 0 (v+2))))))

def graph (d r a b f : ℕ) : Formula :=
  .conj (subset a d) (.conj (RelationHull.Code.closed d r a)
    (.conj (functionGraph f a b)
      (allMem a (allMem (b+1) (imp (pairMem 1 0 (f+2))
        (step (d+2) (r+2) (b+2) (f+2) 1 0))))))

theorem eval_graph (d r a b f : ℕ) (e : ℕ → ZFSet.{u}) :
    (graph d r a b f).Eval e ↔ Graph (e d) (e r) (e a) (e b) (e f) := by
  simp only [graph,step,Graph,Formula.Eval,eval_subset,RelationHull.Code.eval_closed,
    eval_functionGraph,eval_allMem,eval_imp,eval_pairMem,cons_zero,cons_succ]
  exact and_congr_right (fun _ => and_congr_right (fun _ => and_assoc))
end Code

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

def nextFormula : Formula := .existsMem 1 (.conj (.pairMem 0 3 4) (.pairMem 0 1 5))

end TuringRigidity.RelationCollapse

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
open Set RecursiveNames BoundedSetTheory CountableForcing
universe u

namespace BasicAxioms

theorem extensionality (M : ZFSet.{u}) (hM : Transitive M) : Extensionality M := by
  intro a ha b hb h
  apply ZFSet.ext
  intro x
  exact ⟨fun hx => (h x (hM a ha x hx)).mp hx,
    fun hx => (h x (hM b hb x hx)).mpr hx⟩

theorem foundation (M : ZFSet.{u}) (hM : Transitive M) : Foundation M := by
  rintro a ha ⟨x,_,hxa⟩
  have hne : a ≠ ∅ := by intro h; exact ZFSet.notMem_empty x (h ▸ hxa)
  obtain ⟨y,hya,hy⟩ := ZFSet.regularity a hne
  refine ⟨y,hM a ha y hya,hya,fun z _ hz => ?_⟩
  have hz' : z ∈ a ∩ y := ZFSet.mem_inter.mpr ⟨hz.2,hz.1⟩
  exact ZFSet.notMem_empty z (hy ▸ hz')

end BasicAxioms

theorem encode_pair {P : Type u} [Top P] (l : P → ZFSet.{u}) (σ τ : Name P) :
    (Name.pair σ τ).encode l =
      ({ZFSet.pair (σ.encode l) (l ⊤),ZFSet.pair (τ.encode l) (l ⊤)} : ZFSet.{u}) := by
  apply ZFSet.ext
  intro x
  change x ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range,ZFSet.mem_pair]
  constructor
  · rintro ⟨⟨b⟩,hb⟩
    cases b
    · exact Or.inr hb.symm
    · exact Or.inl hb.symm
  · rintro (hx|hx)
    · exact ⟨⟨true⟩,hx.symm⟩
    · exact ⟨⟨false⟩,hx.symm⟩

end TuringRigidity.TransitiveNameModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GroundInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open RecursiveNames BoundedSetTheory CountableForcing
universe u

theorem infinity_of_omega (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) : Infinity M := by
  refine ⟨ZFSet.omega,hω,⟨∅,hM _ hω _ ZFSet.omega_zero,ZFSet.omega_zero,
    fun z _ => ZFSet.notMem_empty z⟩,?_⟩
  intro x _ hx
  have hs := ZFSet.omega_succ hx
  exact ⟨insert x x,hM _ hω _ hs,hs,fun z _ => ZFSet.mem_insert_iff⟩

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
open RecursiveNames BoundedSetTheory
universe u

noncomputable def genericFilterSet (p : ZFSet.{u}) (G : Set (Conditions p)) : ZFSet.{u} :=
  ZFSet.range (fun q : {q // q ∈ G} => label p q.val)

end TuringRigidity.TransitiveNameModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_OracleCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

namespace OracleCode

theorem eval_recursiveIn (g : ℕ →. ℕ) (c : OracleCode) :
    Nat.RecursiveIn {g} (eval g c) := by
  induction c with
  | zero => exact .zero
  | succ => exact .succ
  | left => exact .left
  | right => exact .right
  | query => exact .oracle g (Set.mem_singleton g)
  | pair c d hc hd => exact .pair hc hd
  | comp c d hc hd => exact .comp hc hd
  | prec c d hc hd => exact .prec hc hd
  | find c hc => exact .rfind hc

theorem turingReducible_iff_exists_code (f g : ℕ →. ℕ) :
    TuringReducible f g ↔ ∃ c : OracleCode, eval g c = f := by
  change RecursiveIn {g} f ↔ _
  rw [RecursiveIn.iff_nat]
  exact ⟨exists_code, fun ⟨c, hc⟩ => hc ▸ eval_recursiveIn g c⟩

end OracleCode

end TuringRigidity

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

theorem partrec_cond {α : Type*} [Primcodable α] {b : α → Bool} {f g : α →. ℕ}
    (hb : Computable b) (hf : Partrec f) (hg : Partrec g) :
    Partrec (fun a => if b a then f a else g a) := by
  obtain ⟨cf,hcf⟩ := partrec_code hf
  obtain ⟨cg,hcg⟩ := partrec_code hg
  have hs : Computable (fun a => cond (b a) cf cg) :=
    Computable.cond hb (Computable.const cf) (Computable.const cg)
  exact (Nat.Partrec.Code.eval_part.comp hs Computable.encode).of_eq (fun a => by
    cases he : b a <;> simp [hcf,hcg])

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

def step (p q : OracleCode) (j h : ℕ) (g old : ℕ →. ℕ) (k : ℕ) : Part ℕ :=
  old j >>= fun b =>
    OracleCode.eval
      (partialJoin (OracleCode.eval (partialJoin old (increment g h b)) p) (anchor g)) q k

def stage (p q : OracleCode) (j h : ℕ) (g : ℕ →. ℕ) : ℕ → ℕ →. ℕ
  | 0 => initial g
  | n+1 => step p q j h g (stage p q j h g n)

theorem partialJoin_approximates {f g : ℕ →. ℕ} {fs gs : ℕ → ℕ →. ℕ}
    (hf : ∀ k, Approximates (f k) (fun m => fs m k))
    (hg : ∀ k, Approximates (g k) (fun m => gs m k)) (k : ℕ) :
    Approximates (partialJoin f g k) (fun m => partialJoin (fs m) (gs m) k) := by
  simp only [partialJoin]
  split
  · exact hg _
  · exact hf _

variable {α : Type*} [Primcodable α]

theorem partialJoin_partrec {f g : α → ℕ →. ℕ} (hf : Partrec₂ f) (hg : Partrec₂ g) :
    Partrec₂ (fun a k => partialJoin (f a) (g a) k) := by
  apply partrec_cond (Computable.nat_bodd.comp snd)
  · exact hg.comp fst ((Primrec.nat_div.comp Primrec.id (Primrec.const 2)).to_comp.comp snd)
  · exact hf.comp fst ((Primrec.nat_div.comp Primrec.id (Primrec.const 2)).to_comp.comp snd)

end BranchMachine
end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteTranscript
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OracleCode

theorem eval_mono {g h : ℕ →. ℕ}
    (hgh : ∀ n a, a ∈ g n → a ∈ h n) (c : OracleCode) (n a : ℕ)
    (ha : a ∈ eval g c n) : a ∈ eval h c n := by
  have happrox : ∀ k, Approximates (h k) (fun m => if m = 0 then g k else h k) := by
    intro k
    constructor
    · intro m b hb
      dsimp only at hb
      split at hb
      · exact hgh k b hb
      · exact hb
    · intro b hb
      exact ⟨1, fun m hm => by simpa [show m ≠ 0 by omega] using hb⟩
  exact (eval_approximates happrox c n).1 0 a (by simpa using ha)

end TuringRigidity.OracleCode

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

def codeEnumeration (n : ℕ) : OracleCode :=
  (Encodable.decode (α := OracleCode) n).getD .zero

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_CommonIdeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CommonIdeal
open Set Encodable

def table (s : List Bool) : ℕ →. ℕ := BranchMachine.lookup (s.map bit)

def run (A : Oracle) (p : OracleCode) (s : List Bool) : ℕ →. ℕ :=
  OracleCode.eval (partialJoin (oracleFunction A) (table s)) p

def Extends (G : Oracle) (s : List Bool) : Prop :=
  ∀ i, i < s.length → G i = s.getD i false

theorem table_mono {s t : List Bool} (h : s <+: t) :
    ∀ k a, a ∈ table s k → a ∈ table t k := by
  obtain ⟨u,rfl⟩ := h
  intro k a ha
  change a ∈ (((s ++ u).map bit)[k]? : Part ℕ)
  change a ∈ ((s.map bit)[k]? : Part ℕ) at ha
  have hk : k < s.length := by
    by_contra hn
    simp [List.getElem?_eq_none (show (s.map bit).length ≤ k by simp; omega)] at ha
  simpa [List.map_append, List.getElem?_append, hk] using ha

def Disagree (A : Oracle) (p q : OracleCode) (s t : List Bool) : Prop :=
  ∃ n a b, a ≠ b ∧ a ∈ run A p s n ∧ b ∈ run A q t n

def Agree (A : Oracle) (p q : OracleCode) (s t : List Bool) : Prop :=
  ∀ u v n a b, s <+: u → t <+: v →
    a ∈ run A p u n → b ∈ run A q v n → a = b

def Requirement (A : Oracle) (p q : OracleCode) (s t : List Bool) : Prop :=
  Disagree A p q s t ∨ Agree A p q s t

end TuringRigidity.CommonIdeal

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_CommonIdealSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CommonIdeal
open Encodable Computable UniformOracle

theorem table_partrec : Partrec₂ table :=
  BranchMachine.lookup_partrec.comp
    ((Primrec.list_map Primrec.id (bit_primrec.comp Primrec.snd).to₂).to_comp.comp fst) snd

def finiteRun (p : OracleCode) (s : List Bool) (L : List ℕ) (w : ℕ) : Part ℕ :=
  OracleCode.eval (partialJoin (BranchMachine.lookup L)
    (table (s ++ BorelGeneric.word (Nat.unpair w).1))) p (Nat.unpair w).2

def searchTrial (A : Oracle) (d : Nat.Partrec.Code) (n z : ℕ) : Option ℕ :=
  d.evaln (Nat.unpair (Nat.unpair z).2).2
    (Nat.pair (encode (oraclePrefix (fun k => bit (A k)) (Nat.unpair z).1))
      (Nat.pair (Nat.unpair (Nat.unpair z).2).1 n))

end TuringRigidity.CommonIdeal

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_CommonIdealSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CommonIdeal
open Set Encodable

def even (G : Oracle) : Oracle := fun n => G (2*n)
def odd (G : Oracle) : Oracle := fun n => G (2*n+1)
def pad (s : List Bool) : Oracle := fun n => s.getD n false

def Embeds (r s t : List Bool) : Prop :=
  ∀ G : Oracle, Extends G r → Extends (even G) s ∧ Extends (odd G) t

def family (A : Oracle) (n c : ℕ) : Prop :=
  ∃ s t : List Bool, Embeds (BorelGeneric.word c) s t ∧
    Requirement A (codeEnumeration (Nat.unpair n).1) (codeEnumeration (Nat.unpair n).2) s t

end TuringRigidity.CommonIdeal

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_Assembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Topology
namespace TuringRigidity

noncomputable def fourTuple (F : ℝ → Oracle) (t u v : ℝ) (δ : ℚ) : Oracle :=
  join (join (join (F u) (F (u-v))) (F (v-u+(δ : ℝ)*t)))
    (F (v-u+(δ : ℝ)*(t-1)))

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

def InfiniteOdd (G : Oracle) : Prop := ∀ N, ∃ n, N ≤ n ∧ G (2*n+1) = true

end TuringRigidity.GenericCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteShuffle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.FiniteShuffle
open GenericCoding UniformOracle BinarySeries

theorem prefix_default (s : List Bool) : initial (fun i => s.getD i false) s.length = s := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [initial,List.getD,hj]

def OddBound (n : ℕ) (G : Oracle) : Prop := ∀ i, n ≤ i → G (2*i+1) = false

def freeze (n : ℕ) (G : Oracle) : Oracle :=
  join (fun i => G (2*i)) (fun i => if i < n then G (2*i+1) else false)

theorem initial_prefix {A B : Oracle} {n m : ℕ} (hnm : n ≤ m) (h : Agree n A B) :
    initial A n <+: initial B m := by
  apply List.prefix_iff_getElem.mpr
  refine ⟨by simpa using hnm,?_⟩
  intro i hi
  simpa [initial] using h i (by simpa using hi)

end TuringRigidity.FiniteShuffle

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
open FiniteShuffle GenericCoding Set

theorem realizes_initial (A G : Oracle) (n : ℕ) :
    Realizes (initial A n) G ↔ Agree n A G := by
  change (∀ i, i < (initial A n).length → (initial A n).getD i false = G i) ↔ _
  simp only [prefix_length]
  constructor
  · intro h i hi
    rw [←prefix_getD A n i hi]
    exact h i hi
  · intro h i hi
    rw [prefix_getD A n i hi]
    exact h i hi

theorem realizes_mono {s t : List Bool} {G : Oracle} (h : s <+: t) (hg : Realizes t G) :
    Realizes s G := fun i hi => (getD_of_prefix h i hi).trans (hg i (lt_of_lt_of_le hi h.length_le))

def OpenSet (D : List Bool → Prop) : Set Oracle := {G | ∃ s, D s ∧ Realizes s G}

def GenericFor (D : ℕ → List Bool → Prop) (G : Oracle) : Prop := ∀ n, G ∈ OpenSet (D n)

end TuringRigidity.ShuffleRequirements

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_IdealSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set
namespace TuringRigidity

noncomputable def programOutput (c : OracleCode) (A : Oracle) : Oracle :=
  fun n => by classical exact decide (1 ∈ OracleCode.eval (oracleFunction A) c n)

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GenericIdentity
open Set

def PrincipalIntersection (U L R : Oracle) : Prop :=
  ∀ b : Degree, b ≤ degree U ↔ b ≤ degree L ∧ b ≤ degree R

noncomputable def value (p : OracleCode) (P A : Oracle) : Oracle := programOutput p (join A P)

def Total (p : OracleCode) (P A : Oracle) : Prop :=
  ∃ B, OracleCode.eval (oracleFunction (join A P)) p = oracleFunction B

end TuringRigidity.GenericIdentity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericTruth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GenericTruth
open FiniteShuffle ShuffleRequirements Set Filter Encodable

def CylinderIn (U : Set Oracle) (s : List Bool) : Prop := ∀ G, Realizes s G → G ∈ U

end TuringRigidity.GenericTruth

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_CategoryMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CategorySearch
open Computable Encodable

noncomputable def Avalue (A : Oracle) (k : ℕ) : ℕ := if A k then 1 else 0

end TuringRigidity.CategorySearch

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

noncomputable def searchTrial (A : Oracle) (d : Nat.Partrec.Code) (n s : ℕ) : Option ℕ :=
  UniformOracle.trial (Avalue A) d
    (Nat.unpair (trialInput (Nat.pair n s))).1
    (Nat.unpair (trialInput (Nat.pair n s))).2

end TuringRigidity.CategorySearch

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
open FiniteShuffle ShuffleRequirements PairGenericSelection

def GenericProgramRepresentation (π : Degree ≃o Degree) : Prop :=
  ∃ D : ℕ → List Bool → Prop, (∀ n, DenseOpen (D n)) ∧
    ∃ P : Oracle, ∃ p : OracleCode, ∀ A, GenericFor D A →
      ∃ B, OracleCode.eval (oracleFunction (join A P)) p = oracleFunction B ∧ degree B = π (degree A)

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_SourceIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GenericIdentity

def RepresentsAt (π : Degree ≃o Degree) (p : OracleCode) (P A : Oracle) : Prop :=
  Total p P A ∧ degree (value p P A) = π (degree A)

end TuringRigidity.GenericIdentity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenBorelForcing
attribute [-instance] _root_.OAI.TuringRigidity.CohenRecursiveName.instOrderTopCondition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenBorelForcing
open Set FiniteShuffle ShuffleRequirements GenericTruth CountableForcing

def realFilter (A : Oracle) : GenericFilter Condition where
  carrier := {p | Realizes p.word A}
  nonempty := ⟨⟨[]⟩,by intro i hi; simp at hi⟩
  upper := fun hpq hp => realizes_mono hpq hp
  directed := by
    intro p q hp hq
    let n := max p.word.length q.word.length
    refine ⟨⟨initial A n⟩,(realizes_initial A A n).mpr (fun _ _ => rfl),?_,?_⟩
    · change p.word <+: initial A n
      rw [←prefix_default p.word]
      exact initial_prefix (n := p.word.length) (m := n) (le_max_left _ _) hp
    · change q.word <+: initial A n
      rw [←prefix_default q.word]
      exact initial_prefix (n := q.word.length) (m := n) (le_max_right _ _) hq

end TuringRigidity.CohenBorelForcing

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

def codedFormula : Formula :=
  .existsMem 1 (.existsMem 2 (.conj (.orderedPair 2 1 0)
    (.existsMem 4 (.existsMem 5 (.conj (.member 1 0)
      (.conj (.pairMem 1 3 7) (.pairMem 0 2 7)))))))

end TuringRigidity.RelationCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_FormulaIsomorphism
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u

theorem map_cons (j : ZFSet.{u} → ZFSet.{u}) (x : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (fun i => j (cons x e i)) = cons (j x) (fun i => j (e i)) := by
  funext i; cases i <;> rfl

theorem Formula.realize_isomorphism (A B : ZFSet.{u}) (j : ZFSet.{u} → ZFSet.{u})
    (hin : ∀ x ∈ A, j x ∈ B)
    (hout : ∀ y ∈ B, ∃ x ∈ A, j x = y)
    (hi : ∀ x ∈ A, ∀ y ∈ A, j x = j y → x = y)
    (hm : ∀ x ∈ A, ∀ y ∈ A, j x ∈ j y ↔ x ∈ y)
    (φ : Formula) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) :
    φ.Realize A e ↔ φ.Realize B (fun i => j (e i)) := by
  induction φ generalizing e with
  | equal i k =>
    exact ⟨congrArg j,hi _ (he i) _ (he k)⟩
  | member i k => exact (hm _ (he i) _ (he k)).symm
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ e he) (ihψ e he)
  | neg φ ih => exact not_congr (ih e he)
  | existsMem i φ ih =>
    have he' (x : ZFSet.{u}) (hx : x ∈ A) : ∀ n, cons x e n ∈ A := by
      intro n; cases n with
      | zero => exact hx
      | succ n => exact he n
    constructor
    · rintro ⟨x,hx,hxi,hφ⟩
      refine ⟨j x,hin x hx,(hm x hx (e i) (he i)).mpr hxi,?_⟩
      have h := (ih (cons x e) (he' x hx)).mp hφ
      rwa [map_cons] at h
    · rintro ⟨y,hy,hyi,hφ⟩
      obtain ⟨x,hx,rfl⟩ := hout y hy
      refine ⟨x,hx,(hm x hx (e i) (he i)).mp hyi,?_⟩
      apply (ih (cons x e) (he' x hx)).mpr
      rwa [map_cons]

end TuringRigidity.BoundedSetTheory

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

namespace ChoiceCode
open Formula

def graph (a f : ℕ) : Formula :=
  .conj (allMem f (.existsMem (a+1) (.existsMem 0 (orderedPair 2 1 0))))
    (allMem a (.existsMem 0 (.conj (pairMem 1 0 (f+2))
      (allMem 1 (imp (pairMem 2 0 (f+3)) (.equal 0 1))))))

end ChoiceCode

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

def Graph (d r f : ZFSet.{u}) : Prop :=
  Transitive d ∧
  (∀ z ∈ f, ∃ x ∈ d, ∃ y ∈ r, z = ZFSet.pair x y) ∧
  (∀ x ∈ d, ∃ y ∈ r, ZFSet.pair x y ∈ f ∧
    ∀ z ∈ r, ZFSet.pair x z ∈ f → z = y) ∧
  (∀ x ∈ d, ∀ y ∈ r, ZFSet.pair x y ∈ f → Step f r x y)

theorem Graph.correct {d r f : ZFSet.{u}} (h : Graph d r f)
    (x : ZFSet.{u}) (hx : x ∈ d) (v : ZFSet.{u}) (hv : v ∈ r)
    (hfv : ZFSet.pair x v ∈ f) : v = rankSet x := by
  induction x using ZFSet.inductionOn generalizing v with
  | h x ih =>
    have hs := h.2.2.2 x hx v hv hfv
    apply ZFSet.ext
    intro z
    rw [mem_rankSet]
    constructor
    · intro hz
      obtain ⟨y,hy,w,hw,hfw,hz⟩ := hs.1 z hz
      rw [ih y hy (h.1 x hx y hy) w hw hfw] at hz
      exact ⟨y,hy,hz⟩
    · rintro ⟨y,hy,hz⟩
      obtain ⟨w,hw,hfw,_⟩ := h.2.2.1 y (h.1 x hx y hy)
      rw [←ih y hy (h.1 x hx y hy) w hw hfw] at hz
      exact hz.elim (fun hzw => hzw ▸ (hs.2 y hy w hw hfw).1)
        (fun hz => (hs.2 y hy w hw hfw).2 hz)

theorem Graph.unique {d r s f g : ZFSet.{u}}
    (hf : Graph d r f) (hg : Graph d s g) : f = g := by
  apply ZFSet.ext
  intro z
  have forward {r s f g : ZFSet.{u}} (hf : Graph d r f)
      (hg : Graph d s g) (hz : z ∈ f) : z ∈ g := by
    obtain ⟨x,hx,y,hy,rfl⟩ := hf.2.1 z hz
    obtain ⟨v,hv,hgv,_⟩ := hg.2.2.1 x hx
    have he := (hf.correct x hx y hy hz).trans (hg.correct x hx v hv hgv).symm
    exact he ▸ hgv
  exact ⟨forward hf hg,forward hg hf⟩

namespace Code
open Formula

def step (f r x v : ℕ) : Formula :=
  .conj (allMem v (.existsMem (x+1) (.existsMem (r+2)
    (.conj (pairMem 1 0 (f+3)) (disj (.equal 2 0) (.member 2 0))))))
    (allMem x (allMem (r+1) (imp (pairMem 1 0 (f+2))
      (.conj (.member 0 (v+2)) (subset 0 (v+2))))))

theorem eval_step (f r x v : ℕ) (e : ℕ → ZFSet.{u}) :
    (step f r x v).Eval e ↔ Step (e f) (e r) (e x) (e v) := by
  simp only [step,Formula.Eval,eval_allMem,eval_pairMem,eval_disj,
    eval_imp,eval_subset,cons_zero,cons_succ,Step]

def graph (d r f : ℕ) : Formula :=
  .conj (transitive d) (.conj (functionGraph f d r)
    (allMem d (allMem (r+1) (imp (pairMem 1 0 (f+2)) (step (f+2) (r+2) 1 0)))))

theorem eval_graph (d r f : ℕ) (e : ℕ → ZFSet.{u}) :
    (graph d r f).Eval e ↔ Graph (e d) (e r) (e f) := by
  simp only [graph,Formula.Eval,eval_transitive,eval_functionGraph,
    eval_allMem,eval_imp,eval_pairMem,eval_step,cons_zero,cons_succ,Graph]
  exact and_congr_right (fun _ => and_assoc)
end Code

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

def imageFormula : Formula :=
  .existsMem 1 (.existsMem 4 (.conj (.pairMem 1 0 4)
    (.disj (.equal 2 0) (.member 2 0))))

theorem eval_imageFormula (z x f r : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    imageFormula.Eval (cons z (cons x (cons f (cons r e)))) ↔
      ∃ y ∈ x, ∃ w ∈ r, ZFSet.pair y w ∈ f ∧ (z = w ∨ z ∈ w) := by
  simp only [imageFormula,Formula.Eval,Formula.eval_pairMem,Formula.eval_disj,cons_zero,cons_succ]

theorem Graph.mem_iff {d r f : ZFSet.{u}} (h : Graph d r f) (z : ZFSet.{u}) :
    z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (rankSet x) := by
  constructor
  · intro hz
    obtain ⟨x,hx,y,hy,rfl⟩ := h.2.1 z hz
    exact ⟨x,hx,by rw [h.correct x hx y hy hz]⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨y,hy,hfy,_⟩ := h.2.2.1 x hx
    rw [←h.correct x hx y hy hfy]
    exact hfy

theorem graph_of_mem_iff (d f : ZFSet.{u}) (hd : Transitive d)
    (hf : ∀ z, z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (rankSet x)) :
    Graph d (iterUnion 2 f) f := by
  have hpair (x v : ZFSet.{u}) : ZFSet.pair x v ∈ f ↔ x ∈ d ∧ v = rankSet x := by
    rw [hf]
    constructor
    · rintro ⟨y,hy,he⟩
      obtain ⟨rfl,hv⟩ := ZFSet.pair_inj.mp he
      exact ⟨hy,hv⟩
    · rintro ⟨hx,rfl⟩; exact ⟨x,hx,rfl⟩
  refine ⟨hd,?_,?_,?_⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := (hf z).mp hz
    exact ⟨x,hx,rankSet x,second_mem_doubleUnion hz,rfl⟩
  · intro x hx
    have hp := (hpair x _).mpr ⟨hx,rfl⟩
    exact ⟨_,second_mem_doubleUnion hp,hp,fun v _ hv => (hpair x v).mp hv |>.2⟩
  · intro x hx v _ hv
    have he := (hpair x v).mp hv |>.2
    subst v
    constructor
    · intro z hz
      obtain ⟨y,hy,hz⟩ := (mem_rankSet x z).mp hz
      have hp := (hpair y _).mpr ⟨hd x hx y hy,rfl⟩
      exact ⟨y,hy,_,second_mem_doubleUnion hp,hp,hz⟩
    · intro y hy w _ hw
      rw [(hpair y w).mp hw |>.2]
      exact ⟨(mem_rankSet x _).mpr ⟨y,hy,Or.inl rfl⟩,
        fun z hz => (mem_rankSet x z).mpr ⟨y,hy,Or.inr hz⟩⟩

end TuringRigidity.InternalRank

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

theorem prepend_tail (xs : List ZFSet.{u}) (e : ℕ → ZFSet.{u}) (i : ℕ) :
    prepend xs e (xs.length+i) = e i := by
  induction xs with
  | nil => simp only [prepend_nil,List.length_nil,Nat.zero_add]
  | cons x xs ih => simpa only [List.length_cons,Nat.succ_add,prepend_cons,cons_succ] using ih

theorem prepend_congr (xs : List ZFSet.{u}) (e f : ℕ → ZFSet.{u})
    (i : ℕ) (hi : i < xs.length) : prepend xs e i = prepend xs f i := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih => cases i with
    | zero => rfl
    | succ i => exact ih i (Nat.lt_of_succ_lt_succ hi)

theorem prepend_rotate (xs : List ZFSet.{u}) (x t : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (fun i => prepend xs (cons t (cons x e)) (rotate xs.length i)) =
      cons x (prepend xs e) := by
  funext i
  cases i with
  | zero => exact prepend_tail xs (cons t (cons x e)) 1
  | succ i =>
    change prepend xs (cons t (cons x e)) (if i < xs.length then i else i+2) = prepend xs e i
    by_cases hi : i < xs.length
    · rw [ite_eq_left hi]; exact prepend_congr xs _ _ i hi
    · rw [ite_eq_right hi]
      obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi)
      rw [Nat.add_assoc,prepend_tail,prepend_tail]
      rfl

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_TupleFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace FiniteTuple

def unpack : ℕ → ℕ → ℕ → ℕ → Formula → Formula
  | 0,t,_c,z,φ => .conj (.equal t z) φ
  | n+1,t,c,z,φ => .existsMem c (.existsMem (c+1)
      (.conj (.orderedPair (t+2) 1 0)
        (unpack n 0 (c+2) (z+2) (φ.rename (rotate n)))))

theorem pair_components {c x y : ZFSet.{u}} (hc : Transitive c)
    (hp : ZFSet.pair x y ∈ c) : x ∈ c ∧ y ∈ c := by
  have hxy : ({x,y} : ZFSet.{u}) ∈ c :=
    hc _ hp _ (ZFSet.mem_pair.mpr (Or.inr rfl))
  exact ⟨hc _ hxy _ (ZFSet.mem_pair.mpr (Or.inl rfl)),
    hc _ hxy _ (ZFSet.mem_pair.mpr (Or.inr rfl))⟩

theorem eval_unpack (xs : List ZFSet.{u}) (t c z : ℕ) (φ : Formula)
    (e : ℕ → ZFSet.{u}) (ht : e t = code xs) (hc : Transitive (e c))
    (hcode : code xs ∈ e c) (hz : e z = ∅) :
    (unpack xs.length t c z φ).Eval e ↔ φ.Eval (prepend xs e) := by
  induction xs generalizing t c z φ e with
  | nil =>
    simp only [List.length_nil,unpack,Formula.Eval,ht,hz,code,prepend_nil,true_and]
  | cons x xs ih =>
    have hparts := pair_components hc hcode
    simp only [List.length_cons,unpack,Formula.Eval,Formula.eval_orderedPair,
      cons_zero,cons_succ,ht]
    constructor
    · rintro ⟨y,hy,s,hs,hpair,hφ⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hpair
      have h := (ih 0 (c+2) (z+2) (φ.rename (rotate xs.length))
        (cons (code xs) (cons x e)) rfl hc hparts.2 hz).mp hφ
      rw [Formula.eval_rename,prepend_rotate] at h
      exact h
    · intro h
      refine ⟨x,hparts.1,code xs,hparts.2,rfl,?_⟩
      apply (ih 0 (c+2) (z+2) (φ.rename (rotate xs.length))
        (cons (code xs) (cons x e)) rfl hc hparts.2 hz).mpr
      rw [Formula.eval_rename,prepend_rotate]
      exact h

def relativizeBounded (d : ℕ) : Formula → Formula
  | .equal i j => .equal i j
  | .member i j => .member i j
  | .conj φ ψ => .conj (relativizeBounded d φ) (relativizeBounded d ψ)
  | .neg φ => .neg (relativizeBounded d φ)
  | .existsMem i φ => .existsMem d (.conj (.member 0 (i+1)) (relativizeBounded (d+1) φ))

theorem eval_relativizeBounded (φ : Formula) (d : ℕ) (e : ℕ → ZFSet.{u}) :
    (relativizeBounded d φ).Eval e ↔ φ.Realize (e d) e := by
  induction φ generalizing d e with
  | equal => rfl
  | member => rfl
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ d e) (ihψ d e)
  | neg φ ih => exact not_congr (ih d e)
  | existsMem i φ ih =>
    simp only [relativizeBounded,Formula.Eval,Formula.Realize,cons_zero,cons_succ]
    apply exists_congr; intro x
    apply and_congr_right; intro _
    exact and_congr_right (fun _ => ih (d+1) (cons x e))

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

theorem prepend_outputFirst (xs junk : List ZFSet.{u}) (y : ZFSet.{u})
    (e : ℕ → ZFSet.{u}) :
    (fun i => prepend xs (cons y (prepend junk e)) (outputFirst xs.length junk.length i)) =
      cons y (prepend xs e) := by
  funext i
  cases i with
  | zero => exact prepend_tail xs (cons y (prepend junk e)) 0
  | succ i =>
    change prepend xs (cons y (prepend junk e))
      (if i < xs.length then i else i+junk.length+1) = prepend xs e i
    by_cases hi : i < xs.length
    · rw [ite_eq_left hi]; exact prepend_congr xs _ _ i hi
    · rw [ite_eq_right hi]
      obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi)
      have harith : xs.length+j+junk.length+1 = xs.length+(junk.length+j+1) := by omega
      rw [harith,prepend_tail,prepend_tail,cons_succ,prepend_tail]

noncomputable def relation (d : ZFSet.{u}) (n : ℕ) (φ : Formula)
    (e : ℕ → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ xs : List ZFSet.{u}, xs.length = n ∧
    (∀ x ∈ xs, x ∈ d) ∧ ∃ y ∈ d, z = ZFSet.pair (code xs) y ∧
      φ.Eval (cons y (prepend xs e))) (ZFSet.prod (space d n) d)

theorem relation_pair (d y : ZFSet.{u}) (xs : List ZFSet.{u}) (φ : Formula)
    (e : ℕ → ZFSet.{u}) : ZFSet.pair (code xs) y ∈ relation d xs.length φ e ↔
      (∀ x ∈ xs, x ∈ d) ∧ y ∈ d ∧ φ.Eval (cons y (prepend xs e)) := by
  rw [relation,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,ys,hlen,hys,z,hz,hpair,hφ⟩
    obtain ⟨hcode,rfl⟩ := ZFSet.pair_inj.mp hpair
    obtain rfl := code_injective_length xs ys hlen.symm hcode
    exact ⟨hys,hz,hφ⟩
  · rintro ⟨hxs,hy,hφ⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨_,code_mem_space d xs hxs,y,hy,rfl⟩,
      xs,rfl,hxs,y,hy,rfl,hφ⟩

def relationFormula (n : ℕ) (φ : Formula) : Formula :=
  .existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
    (unpack n 1 5 6 (φ.rename (outputFirst n 6)))))

theorem eval_relationFormula (d c z : ZFSet.{u}) (n : ℕ) (φ : Formula)
    (e : ℕ → ZFSet.{u}) (hc : Transitive c) (hspace : space d n ⊆ c) :
    (relationFormula n φ).Eval (cons z (cons (space d n) (cons d (cons c (cons ∅ e))))) ↔
      z ∈ relation d n φ e := by
  simp only [relationFormula,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ]
  constructor
  · rintro ⟨t,ht,y,hy,rfl,hφ⟩
    obtain ⟨xs,rfl,hxs,rfl⟩ := (mem_space d t n).mp ht
    apply (relation_pair d y xs φ e).mpr
    refine ⟨hxs,hy,?_⟩
    have h := (eval_unpack xs 1 5 6 (φ.rename (outputFirst xs.length 6))
      (cons y (cons (code xs) (cons (ZFSet.pair (code xs) y)
        (cons (space d xs.length) (cons d (cons c (cons ∅ e)))))))
      rfl hc (hspace ht) rfl).mp hφ
    rw [Formula.eval_rename] at h
    have he := prepend_outputFirst xs [code xs,ZFSet.pair (code xs) y,space d xs.length,d,c,∅] y e
    exact he ▸ h
  · intro hz
    obtain ⟨_,xs,hlen,hxs,y,hy,rfl,hφ⟩ := ZFSet.mem_sep.mp hz
    subst n
    have ht := code_mem_space d xs hxs
    refine ⟨code xs,ht,y,hy,rfl,?_⟩
    apply (eval_unpack xs 1 5 6 (φ.rename (outputFirst xs.length 6))
      (cons y (cons (code xs) (cons (ZFSet.pair (code xs) y)
        (cons (space d xs.length) (cons d (cons c (cons ∅ e)))))))
      rfl hc (hspace ht) rfl).mpr
    rw [Formula.eval_rename]
    have he := prepend_outputFirst xs [code xs,ZFSet.pair (code xs) y,space d xs.length,d,c,∅] y e
    exact he.symm ▸ hφ

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

def selectionFormula : Formula :=
  .existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
    (.existsMem 5 (.conj
      (.allMem 5 (.iff (.member 0 1) (.pairMem 3 0 9))) (.pairMem 0 1 7)))))

theorem eval_selectionFormula (z a b q f r : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    selectionFormula.Eval (cons z (cons a (cons b (cons q (cons f (cons r e)))))) ↔
      ∃ x ∈ a, ∃ y ∈ b, z = ZFSet.pair x y ∧ ∃ s ∈ q,
        (∀ w ∈ b, w ∈ s ↔ ZFSet.pair x w ∈ r) ∧ ZFSet.pair s y ∈ f := by
  simp only [selectionFormula,Formula.Eval,Formula.eval_orderedPair,Formula.eval_allMem,
    Formula.eval_iff,Formula.eval_pairMem,cons_zero,cons_succ]

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

def SkolemGraph (d : ZFSet.{u}) (n : ℕ) (φ : Formula)
    (e : ℕ → ZFSet.{u}) (g : ZFSet.{u}) : Prop :=
  g ⊆ relation d n φ e ∧
  ∀ xs : List ZFSet.{u}, xs.length = n → (∀ x ∈ xs, x ∈ d) →
    (∃ y ∈ d, φ.Eval (cons y (prepend xs e))) →
      ∃ y ∈ d, ZFSet.pair (code xs) y ∈ g ∧
        ∀ z ∈ d, ZFSet.pair (code xs) z ∈ g → z = y

theorem SkolemGraph.correct {d g : ZFSet.{u}} {n : ℕ} {φ : Formula}
    {e : ℕ → ZFSet.{u}} (hg : SkolemGraph d n φ e g)
    (xs : List ZFSet.{u}) (hlen : xs.length = n) {y : ZFSet.{u}}
    (hy : ZFSet.pair (code xs) y ∈ g) :
    (∀ x ∈ xs, x ∈ d) ∧ y ∈ d ∧ φ.Eval (cons y (prepend xs e)) := by
  subst n
  exact (relation_pair d y xs φ e).mp (hg.1 hy)

theorem SkolemGraph.functional {d g : ZFSet.{u}} {n : ℕ} {φ : Formula}
    {e : ℕ → ZFSet.{u}} (hg : SkolemGraph d n φ e g)
    (xs : List ZFSet.{u}) (hlen : xs.length = n) {y z : ZFSet.{u}}
    (hy : ZFSet.pair (code xs) y ∈ g) (hz : ZFSet.pair (code xs) z ∈ g) : y = z := by
  have hy' := hg.correct xs hlen hy
  have hz' := hg.correct xs hlen hz
  obtain ⟨w,_,_,hu⟩ := hg.2 xs hlen hy'.1 ⟨y,hy'.2⟩
  exact (hu y hy'.2.1 hy).trans (hu z hz'.2.1 hz).symm

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
namespace Formula

def scope : Formula → ℕ
  | .equal i j | .member i j => max (i+1) (j+1)
  | .conj φ ψ => max φ.scope ψ.scope
  | .neg φ => φ.scope
  | .existsMem i φ => max (i+1) (φ.scope-1)

theorem realize_congr (φ : Formula) (d : ZFSet.{u}) (e f : ℕ → ZFSet.{u})
    (h : ∀ i, i < φ.scope → e i = f i) : φ.Realize d e ↔ φ.Realize d f := by
  induction φ generalizing e f with
  | equal i j => simp only [Realize,h i (by simp [scope]),h j (by simp [scope])]
  | member i j => simp only [Realize,h i (by simp [scope]),h j (by simp [scope])]
  | conj φ ψ ihφ ihψ =>
    exact and_congr (ihφ e f (fun i hi => h i (by simp only [scope]; omega)))
      (ihψ e f (fun i hi => h i (by simp only [scope]; omega)))
  | neg φ ih => exact not_congr (ih e f h)
  | existsMem i φ ih =>
    simp only [Realize,h i (by simp only [scope]; omega)]
    apply exists_congr; intro x
    apply and_congr_right; intro _
    apply and_congr_right; intro _
    apply ih; intro j hj
    cases j with
    | zero => rfl
    | succ j => exact h j (by simp only [scope]; omega)

def width : Formula → ℕ
  | .equal i j | .member i j => max (i+1) (j+1)
  | .conj φ ψ => max φ.width ψ.width
  | .neg φ => φ.width
  | .existsMem i φ => max (i+1) φ.width

theorem scope_le_width (φ : Formula) : φ.scope ≤ φ.width := by
  induction φ <;> simp only [scope,width] at * <;> omega
end Formula
namespace FiniteTuple

theorem takeEnv_agree (n : ℕ) (e f : ℕ → ZFSet.{u}) (i : ℕ) (hi : i < n) :
    prepend (takeEnv n e) f i = e i := by
  induction n generalizing e i with
  | zero => omega
  | succ n ih => cases i with
    | zero => rfl
    | succ i => exact ih (fun j => e (j+1)) i (Nat.lt_of_succ_lt_succ hi)

def witnessBody (n i : ℕ) (φ : Formula) : Formula :=
  .conj (.member 0 (i+1)) (relativizeBounded (n+1) φ)

theorem eval_witnessBody (n i : ℕ) (φ : Formula) (hn : i < n) (hφ : φ.scope ≤ n+1)
    (d x : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (witnessBody n i φ).Eval (cons x (prepend (takeEnv n e) (fun _ => d))) ↔
      x ∈ e i ∧ φ.Realize d (cons x e) := by
  simp only [witnessBody,Formula.Eval,cons_zero,cons_succ,eval_relativizeBounded]
  rw [takeEnv_agree n e _ i hn]
  have hd : prepend (takeEnv n e) (fun _ => d) n = d := by
    simpa only [length_takeEnv,Nat.add_zero] using prepend_tail (takeEnv n e) (fun _ => d) 0
  rw [hd]
  apply and_congr_right; intro _
  apply φ.realize_congr; intro j hj
  cases j with
  | zero => rfl
  | succ j => exact takeEnv_agree n e _ j (by omega)

def occurrences : Formula → List (ℕ × Formula)
  | .equal _ _ | .member _ _ => []
  | .conj φ ψ => occurrences φ ++ occurrences ψ
  | .neg φ => occurrences φ
  | .existsMem i φ => (i,φ) :: occurrences φ

def fragment (n : ℕ) (φ : Formula) : List Formula :=
  (occurrences φ).map (fun p => witnessBody n p.1 p.2)

theorem occurrence_width (φ : Formula) (i : ℕ) (ψ : Formula)
    (hm : (i,ψ) ∈ occurrences φ) : i < φ.width ∧ ψ.scope ≤ φ.width+1 := by
  induction φ with
  | equal => simp [occurrences] at hm
  | member => simp [occurrences] at hm
  | conj φ θ ihφ ihθ =>
    rcases List.mem_append.mp hm with hm|hm
    · have hh := ihφ hm; simp only [Formula.width]; omega
    · have hh := ihθ hm; simp only [Formula.width]; omega
  | neg φ ih => exact ih hm
  | existsMem j φ ih =>
    rcases List.mem_cons.mp hm with hp|hm
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj hp
      have hh := Formula.scope_le_width ψ
      simp only [Formula.width]; omega
    · have hh := ih hm; simp only [Formula.width]; omega

def Witnesses (d h : ZFSet.{u}) (φ : Formula) : Prop :=
  ∀ i ψ, (i,ψ) ∈ occurrences φ →
    ∀ e : ℕ → ZFSet.{u}, (∀ j, e j ∈ h) →
      (∃ x ∈ d, x ∈ e i ∧ ψ.Realize d (cons x e)) →
        ∃ x ∈ h, x ∈ e i ∧ ψ.Realize d (cons x e)

theorem realize_of_witnesses (d h : ZFSet.{u}) (hhd : h ⊆ d) (φ : Formula)
    (hw : Witnesses d h φ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ h) :
    φ.Realize h e ↔ φ.Realize d e := by
  induction φ generalizing e with
  | equal => rfl
  | member => rfl
  | conj φ ψ ihφ ihψ =>
    have hwφ : Witnesses d h φ := fun i θ hi => hw i θ (List.mem_append_left _ hi)
    have hwψ : Witnesses d h ψ := fun i θ hi => hw i θ (List.mem_append_right _ hi)
    exact and_congr (ihφ hwφ e he) (ihψ hwψ e he)
  | neg φ ih => exact not_congr (ih hw e he)
  | existsMem i φ ih =>
    have hwφ : Witnesses d h φ := fun j θ hj => hw j θ (List.mem_cons_of_mem _ hj)
    have env (x : ZFSet.{u}) (hx : x ∈ h) : ∀ j, cons x e j ∈ h := by
      intro j; cases j with
      | zero => exact hx
      | succ j => exact he j
    constructor
    · rintro ⟨x,hx,hxi,hφ⟩
      exact ⟨x,hhd hx,hxi,(ih hwφ (cons x e) (env x hx)).mp hφ⟩
    · intro hφ
      obtain ⟨x,hx,hxi,hψ⟩ := hw i φ (List.mem_cons_self) e he hφ
      exact ⟨x,hx,hxi,(ih hwφ (cons x e) (env x hx)).mpr hψ⟩

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_FragmentHull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace FiniteTuple

def differenceBody : Formula := .neg (.iff (.member 0 1) (.member 0 2))

theorem closed_extensional (d h g : ZFSet.{u}) (n : ℕ) (hn : 2 ≤ n)
    (hd : Transitive d) (hhd : h ⊆ d) (hcl : Closed n g h)
    (hgs : ∃ f, f ⊆ g ∧ SkolemGraph d n differenceBody (fun _ => d) f) :
    RelationCollapse.StructureExtensional h := by
  classical
  intro x hx y hy hext
  by_contra hne
  have hdiff : ∃ z, ¬ (z ∈ x ↔ z ∈ y) := by
    by_contra hnz
    apply hne
    apply ZFSet.ext; intro z
    exact Classical.byContradiction (fun hz => hnz ⟨z,hz⟩)
  obtain ⟨z,hz⟩ := hdiff
  have hzd : z ∈ d := by
    by_cases hzx : z ∈ x
    · exact hd x (hhd hx) z hzx
    · have hzy : z ∈ y := by
        by_contra hzy
        exact hz ⟨fun h => False.elim (hzx h),fun h => False.elim (hzy h)⟩
      exact hd y (hhd hy) z hzy
  let e := cons x (cons y (fun _ => x))
  let xs := takeEnv n e
  have heh : ∀ i, e i ∈ h := by
    intro i; rcases i with _|i; exact hx
    rcases i with _|i; exact hy
    exact hx
  have hxs : ∀ v ∈ xs, v ∈ h := takeEnv_mem n e h heh
  have hlen : xs.length = n := length_takeEnv n e
  have eval (v : ZFSet.{u}) : differenceBody.Eval (cons v (prepend xs (fun _ => d))) ↔
      ¬ (v ∈ x ↔ v ∈ y) := by
    simp only [differenceBody,Formula.Eval,Formula.eval_iff,cons_zero,cons_succ]
    rw [takeEnv_agree n e _ 0 (by omega),takeEnv_agree n e _ 1 (by omega)]
    rfl
  obtain ⟨f,hfg,hf⟩ := hgs
  obtain ⟨v,_,hv,_⟩ := hf.2 xs hlen (fun v hv => hhd (hxs v hv)) ⟨z,hzd,(eval z).mpr hz⟩
  have hvh := hcl xs hlen hxs v (hfg hv)
  exact (eval v).mp (hf.correct xs hlen hv).2.2 (hext v hvh)

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
namespace SigmaFormula

def feed : List ZFSet.{u} → (ℕ → ZFSet.{u}) → (ℕ → ZFSet.{u})
  | [],e => e
  | x::xs,e => feed xs (cons x e)

theorem feed_mem (xs : List ZFSet.{u}) (e : ℕ → ZFSet.{u}) (d : ZFSet.{u})
    (hxs : ∀ x ∈ xs, x ∈ d) (he : ∀ i, e i ∈ d) : ∀ i, feed xs e i ∈ d := by
  induction xs generalizing e with
  | nil => exact he
  | cons x xs ih =>
    have he' : ∀ i, cons x e i ∈ d := by
      intro i; cases i with
      | zero => exact hxs x List.mem_cons_self
      | succ i => exact he i
    exact ih (cons x e) (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) he'

end SigmaFormula
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteExtensionCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse
universe u
namespace FiniteTuple

noncomputable def indexSpace (t : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod {natSet 0} t ∪ ZFSet.prod {natSet 1} ZFSet.omega

noncomputable def finiteIndex (t : ZFSet.{u}) (xs : List ZFSet.{u}) (x : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if x ∈ t then ZFSet.pair (natSet 0) x else ZFSet.pair (natSet 1) (natSet (xs.idxOf x))

theorem finiteIndex_mem (t : ZFSet.{u}) (xs : List ZFSet.{u}) (x : ZFSet.{u}) :
    finiteIndex t xs x ∈ indexSpace t := by
  classical
  unfold finiteIndex
  by_cases hx : x ∈ t
  · rw [ite_eq_left hx]
    exact ZFSet.mem_union.mpr (Or.inl (ZFSet.mem_prod.mpr
      ⟨_,ZFSet.mem_singleton.mpr rfl,x,hx,rfl⟩))
  · rw [ite_eq_right hx]
    exact ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_prod.mpr
      ⟨_,ZFSet.mem_singleton.mpr rfl,_,(mem_omega _).mpr ⟨xs.idxOf x,rfl⟩,rfl⟩))

theorem finiteIndex_injective (t : ZFSet.{u}) (xs : List ZFSet.{u})
    (x : ZFSet.{u}) (hx : x ∈ t ∪ elements xs) (y : ZFSet.{u}) (_hy : y ∈ t ∪ elements xs)
    (he : finiteIndex t xs x = finiteIndex t xs y) : x = y := by
  classical
  unfold finiteIndex at he
  by_cases hxt : x ∈ t <;> by_cases hyt : y ∈ t
  · rw [ite_eq_left hxt,ite_eq_left hyt] at he
    exact (ZFSet.pair_inj.mp he).2
  · rw [ite_eq_left hxt,ite_eq_right hyt] at he
    have hf := natSet_injective (ZFSet.pair_inj.mp he).1
    omega
  · rw [ite_eq_right hxt,ite_eq_left hyt] at he
    have hf := natSet_injective (ZFSet.pair_inj.mp he).1
    omega
  · rw [ite_eq_right hxt,ite_eq_right hyt] at he
    have hidx := natSet_injective (ZFSet.pair_inj.mp he).2
    have hxl : x ∈ xs := (mem_elements x xs).mp ((ZFSet.mem_union.mp hx).resolve_left hxt)
    exact (List.idxOf_inj hxl).mp hidx

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

theorem transitive_union {a b : ZFSet.{u}} (ha : Transitive a) (hb : Transitive b) :
    Transitive (a ∪ b) := by
  intro x hx y hy
  rcases ZFSet.mem_union.mp hx with hx|hx
  · exact ZFSet.mem_union.mpr (Or.inl (ha x hx y hy))
  · exact ZFSet.mem_union.mpr (Or.inr (hb x hx y hy))

theorem transitive_adjoin {a z : ZFSet.{u}} (ha : Transitive a) (hz : z ⊆ a) :
    Transitive (a ∪ ({z} : ZFSet.{u})) := by
  intro x hx y hy
  rcases ZFSet.mem_union.mp hx with hx|hx
  · exact ZFSet.mem_union.mpr (Or.inl (ha x hx y hy))
  · obtain rfl := ZFSet.mem_singleton.mp hx
    exact ZFSet.mem_union.mpr (Or.inl (hz hy))

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_TermFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace Formula

def rightPair (s a b c : ℕ) : Formula := .existsMem s (.existsMem 0
  (.conj (.orderedPair (s+2) (a+2) 0) (.orderedPair 0 (b+2) (c+2))))

def leftPair (s a b c : ℕ) : Formula := .existsMem s (.existsMem 0
  (.conj (.orderedPair (s+2) 0 (c+2)) (.orderedPair 0 (a+2) (b+2))))

theorem eval_rightPair (s a b c : ℕ) (e : ℕ → ZFSet.{u}) :
    (rightPair s a b c).Eval e ↔ e s = ZFSet.pair (e a) (ZFSet.pair (e b) (e c)) := by
  simp only [rightPair,Eval,eval_orderedPair,cons_zero,cons_succ]
  constructor
  · rintro ⟨p,_,q,_,h,rfl⟩; exact h
  · intro h
    refine ⟨{e a,ZFSet.pair (e b) (e c)},?_,ZFSet.pair (e b) (e c),?_,h,rfl⟩
    · rw [h]; exact ZFSet.mem_pair.mpr (Or.inr rfl)
    · exact ZFSet.mem_pair.mpr (Or.inr rfl)

theorem eval_leftPair (s a b c : ℕ) (e : ℕ → ZFSet.{u}) :
    (leftPair s a b c).Eval e ↔ e s = ZFSet.pair (ZFSet.pair (e a) (e b)) (e c) := by
  simp only [leftPair,Eval,eval_orderedPair,cons_zero,cons_succ]
  constructor
  · rintro ⟨p,_,q,_,h,rfl⟩; exact h
  · intro h
    refine ⟨{ZFSet.pair (e a) (e b),e c},?_,ZFSet.pair (e a) (e b),?_,h,rfl⟩
    · rw [h]; exact ZFSet.mem_pair.mpr (Or.inr rfl)
    · exact ZFSet.mem_pair.mpr (Or.inl rfl)

def appMem (a b c f : ℕ) : Formula := .existsMem f (leftPair 0 (a+1) (b+1) (c+1))

theorem eval_appMem (a b c f : ℕ) (e : ℕ → ZFSet.{u}) :
    (appMem a b c f).Eval e ↔ ZFSet.pair (ZFSet.pair (e a) (e b)) (e c) ∈ e f := by
  simp only [appMem,Eval,eval_leftPair,cons_zero,cons_succ]
  exact ⟨fun ⟨x,hx,he⟩ => he ▸ hx,fun h => ⟨_,h,rfl⟩⟩
end Formula
namespace FiniteTerm
open Formula

def stepFormula (c v A B L O K D f z o t : ℕ) : Formula :=
  .disj (.existsMem A (.conj (.orderedPair (c+1) (z+1) 0) (.pairMem 0 (v+1) (L+1))))
    (.disj
      (.existsMem B (.existsMem (K+1) (.existsMem (D+2)
        (.conj (.rightPair (c+3) (o+3) 2 1)
          (.conj (.pairMem 1 0 (f+3)) (.appMem 2 0 (v+3) (O+3)))))))
      (.existsMem K (.existsMem (K+1) (.existsMem (D+2) (.existsMem (D+3)
        (.conj (.rightPair (c+4) (t+4) 3 2)
          (.conj (.pairMem 3 1 (f+4))
            (.conj (.pairMem 2 0 (f+4)) (.orderedPair (v+4) 1 0)))))))))

def certificateFormula (A B L O K D f z o t : ℕ) : Formula :=
  .allMem f (.existsMem (K+1) (.existsMem (D+2) (.conj (.orderedPair 2 1 0)
    (stepFormula 1 0 (A+3) (B+3) (L+3) (O+3) (K+3) (D+3) (f+3) (z+3) (o+3) (t+3)))))

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

def graphFormula : Formula :=
  .existsMem 6 (.existsMem 8 (.conj (.orderedPair 2 1 0)
    (.existsMem 3 (.conj (certificateFormula 5 6 7 8 9 10 0 11 12 13) (.pairMem 2 1 0)))))

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

theorem Trace.compatible {α a q s f g : ZFSet.{u}} (_hα : Transitive α)
    (hs : ChoiceGraph q s) (hf : Trace α a q s f) (hg : Trace α a q s g)
    (i x y : ZFSet.{u}) (hix : ZFSet.pair i x ∈ f) (hiy : ZFSet.pair i y ∈ g) : x = y := by
  induction i using ZFSet.inductionOn generalizing x y with
  | h i ih =>
    have hi := (hf.pair_mem hix).1
    have hx := (hf.pair_mem hix).2
    have hy := (hg.pair_mem hiy).2
    obtain ⟨r,_,hr,hrx⟩ := hf.choice i hi x hx hix
    obtain ⟨t,_,ht,hty⟩ := hg.choice i hi y hy hiy
    have heq : r = t := hr.eq ht (by
      intro j hji z _
      constructor
      · intro hjz
        obtain ⟨w,_,hjw⟩ := hg.initial i hi y hy hiy j hji
        have hzw := ih j hji z w hjz hjw
        exact hzw.symm ▸ hjw
      · intro hjz
        obtain ⟨w,_,hjw⟩ := hf.initial i hi x hx hix j hji
        have hwz := ih j hji w z hjw hjz
        exact hwz ▸ hjw)
    rw [heq] at hrx
    exact hs.functional hrx hty

theorem Trace.functional {α a q s f : ZFSet.{u}} (hα : Transitive α)
    (hs : ChoiceGraph q s) (hf : Trace α a q s f) : FiniteTerm.Functional f :=
  fun i x y hx hy => hf.compatible hα hs hf i x y hx hy

theorem Trace.sUnion {α a q s C : ZFSet.{u}} (hα : Transitive α)
    (hs : ChoiceGraph q s) (hC : ∀ f ∈ C, Trace α a q s f) :
    Trace α a q s (ZFSet.sUnion C) := by
  have from_pair (i x : ZFSet.{u}) (hix : ZFSet.pair i x ∈ ZFSet.sUnion C) :
      ∃ f ∈ C, ZFSet.pair i x ∈ f := ZFSet.mem_sUnion.mp hix
  refine ⟨?_,?_,?_⟩
  · intro z hz
    obtain ⟨f,hf,hzf⟩ := ZFSet.mem_sUnion.mp hz
    exact (hC f hf).shape z hzf
  · intro i hi x hx hix j hji
    obtain ⟨f,hf,hif⟩ := from_pair i x hix
    obtain ⟨y,hy,hjy⟩ := (hC f hf).initial i hi x hx hif j hji
    exact ⟨y,hy,ZFSet.mem_sUnion.mpr ⟨f,hf,hjy⟩⟩
  · intro i hi x hx hix
    obtain ⟨f,hf,hif⟩ := from_pair i x hix
    obtain ⟨r,hr,hrdef,hrx⟩ := (hC f hf).choice i hi x hx hif
    refine ⟨r,hr,⟨hrdef.1,?_⟩,hrx⟩
    intro y hy
    rw [hrdef.2 y hy]
    apply not_congr
    constructor
    · rintro ⟨j,hji,hjy⟩
      exact ⟨j,hji,ZFSet.mem_sUnion.mpr ⟨f,hf,hjy⟩⟩
    · rintro ⟨j,hji,hjy⟩
      obtain ⟨g,hg,hjg⟩ := from_pair j y hjy
      obtain ⟨z,_,hjz⟩ := (hC f hf).initial i hi x hx hif j hji
      have hzy := (hC f hf).compatible hα hs (hC g hg) j z y hjz hjg
      exact ⟨j,hji,hzy ▸ hjz⟩

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
open Formula

def remainingFormula (a f i r : ℕ) : Formula :=
  .conj (.subset r a) (.allMem a (.iff (.member 0 (r+1))
    (.neg (.existsMem (i+1) (.pairMem 0 1 (f+2))))))

theorem eval_remainingFormula (a f i r : ℕ) (e : ℕ → ZFSet.{u}) :
    (remainingFormula a f i r).Eval e ↔ Remaining (e a) (e f) (e i) (e r) := by
  simp only [remainingFormula,Remaining,Formula.Eval,eval_subset,eval_allMem,eval_iff,
    eval_pairMem,cons_zero,cons_succ]

def traceFormula (α a q s f : ℕ) : Formula := .conj
  (.allMem f (.existsMem (α+1) (.existsMem (a+2) (.orderedPair 2 1 0))))
  (.conj
    (.allMem α (.allMem (a+1) (.imp (.pairMem 1 0 (f+2))
      (.allMem 1 (.existsMem (a+3) (.pairMem 1 0 (f+4)))))))
    (.allMem α (.allMem (a+1) (.imp (.pairMem 1 0 (f+2))
      (.existsMem (q+2) (.conj (remainingFormula (a+3) (f+3) 2 0) (.pairMem 0 1 (s+3))))))))

theorem eval_traceFormula (α a q s f : ℕ) (e : ℕ → ZFSet.{u}) :
    (traceFormula α a q s f).Eval e ↔ Trace (e α) (e a) (e q) (e s) (e f) := by
  simp only [traceFormula,Formula.Eval,eval_allMem,eval_imp,eval_orderedPair,
    eval_pairMem,eval_remainingFormula,cons_zero,cons_succ]
  exact ⟨fun ⟨hshape,hinitial,hchoice⟩ => ⟨hshape,hinitial,hchoice⟩,
    fun h => ⟨h.shape,h.initial,h.choice⟩⟩

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

theorem Trace.adjoin {α a q s f i x r : ZFSet.{u}} (hf : Trace α a q s f)
    (hi : i ∈ α) (hit : Transitive i) (hx : x ∈ a) (hr : r ∈ q)
    (hrem : Remaining a f i r) (hrx : ZFSet.pair r x ∈ s)
    (hprev : ∀ j ∈ i, ∃ y ∈ a, ZFSet.pair j y ∈ f)
    (hdom : ∀ j y, ZFSet.pair j y ∈ f → j ∈ i) :
    Trace α a q s (f ∪ ({ZFSet.pair i x} : ZFSet.{u})) := by
  refine ⟨?_,?_,?_⟩
  · intro z hz
    rcases ZFSet.mem_union.mp hz with hz|hz
    · exact hf.shape z hz
    · obtain rfl := ZFSet.mem_singleton.mp hz
      exact ⟨i,hi,x,hx,rfl⟩
  · intro j hj y hy hjy k hkj
    rcases ZFSet.mem_union.mp hjy with hjy|hjy
    · obtain ⟨z,hz,hkz⟩ := hf.initial j hj y hy hjy k hkj
      exact ⟨z,hz,ZFSet.mem_union.mpr (Or.inl hkz)⟩
    · have he := ZFSet.mem_singleton.mp hjy
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
      obtain ⟨z,hz,hkz⟩ := hprev k hkj
      exact ⟨z,hz,ZFSet.mem_union.mpr (Or.inl hkz)⟩
  · intro j hj y hy hjy
    rcases ZFSet.mem_union.mp hjy with hjy|hjy
    · obtain ⟨b,hb,hbrem,hby⟩ := hf.choice j hj y hy hjy
      refine ⟨b,hb,⟨hbrem.1,?_⟩,hby⟩
      intro z hz
      rw [hbrem.2 z hz]
      apply not_congr
      apply exists_congr; intro k
      apply and_congr_right; intro hkj
      exact (adjoin_prior f i x k z (hit j (hdom j y hjy) k hkj)).symm
    · have he := ZFSet.mem_singleton.mp hjy
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
      refine ⟨r,hr,⟨hrem.1,?_⟩,hrx⟩
      intro z hz
      rw [hrem.2 z hz]
      apply not_congr
      apply exists_congr; intro k
      apply and_congr_right; intro hki
      exact (adjoin_prior f j y k z hki).symm

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

open Formula
def leastValueFormula (δ V F H x y : ℕ) : Formula := .conj (.member y x)
  (.existsMem δ (.existsMem (V+1) (.conj (.pairMem 1 0 (F+2))
    (.conj (.pairMem 0 (y+2) (H+2))
      (allMem 1 (allMem (V+3) (allMem (x+4)
        (.neg (.conj (.pairMem 2 1 (F+5)) (.pairMem 1 0 (H+5)))))))))))

theorem eval_leastValueFormula (δ V F H x y : ℕ) (e : ℕ → ZFSet.{u}) :
    (leastValueFormula δ V F H x y).Eval e ↔
      LeastValue (e δ) (e V) (e F) (e H) (e x) (e y) := by
  simp only [leastValueFormula,LeastValue,Formula.Eval,eval_pairMem,eval_allMem,cons_zero,cons_succ]

def selectionFormula : Formula := .existsMem 1 (.existsMem 3
  (.conj (.orderedPair 2 1 0) (leastValueFormula 5 6 7 8 1 0)))

end InternalWellOrder
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

theorem skolem_functional {d g : ZFSet.{u}} {n : ℕ} {φ : Formula} {e : ℕ → ZFSet.{u}}
    (hg : FiniteTuple.SkolemGraph d n φ e g) : Functional g := by
  intro c x y hx hy
  have hp := (ZFSet.mem_sep.mp (hg.1 hx)).1
  obtain ⟨c',hc,x',_,he⟩ := ZFSet.mem_prod.mp hp
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  obtain ⟨xs,hlen,_,rfl⟩ := (FiniteTuple.mem_space d c n).mp hc
  exact hg.functional xs hlen hx hy

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
namespace FiniteTuple

theorem witnesses_of_closed_graphs (d h : ZFSet.{u}) (n : ℕ) (φ : Formula)
    (hn : φ.width ≤ n) (hhd : h ⊆ d)
    (hgs : ∀ ψ ∈ fragment n φ, ∃ g, SkolemGraph d n ψ (fun _ => d) g ∧ Closed n g h) :
    Witnesses d h φ := by
  intro i ψ hm e he hw
  have hbounds := occurrence_width φ i ψ hm
  have hin : i < n := lt_of_lt_of_le hbounds.1 hn
  have hψn : ψ.scope ≤ n+1 := by omega
  obtain ⟨g,hg,hcl⟩ := hgs _ (List.mem_map.mpr ⟨(i,ψ),hm,rfl⟩)
  let xs := takeEnv n e
  have hxs : ∀ x ∈ xs, x ∈ h := takeEnv_mem n e h he
  have hlen : xs.length = n := length_takeEnv n e
  obtain ⟨y,hy,hyi,hψ⟩ := hw
  have hsuccess := (eval_witnessBody n i ψ hin hψn d y e).mpr ⟨hyi,hψ⟩
  obtain ⟨z,_,hz,_⟩ := hg.2 xs hlen (fun x hx => hhd (hxs x hx)) ⟨y,hy,hsuccess⟩
  exact ⟨z,hcl xs hlen hxs z hz,
    (eval_witnessBody n i ψ hin hψn d z e).mp (hg.correct xs hlen hz).2.2⟩

end FiniteTuple
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
open RecursiveNames BoundedSetTheory
universe u

namespace NameCodeFormula
open _root_.OAI.TuringRigidity.BoundedSetTheory.Formula

def pairName (t x y z : ℕ) : Formula :=
  .conj (allMem z (disj (orderedPair 0 (x+1) (t+1)) (orderedPair 0 (y+1) (t+1))))
    (.conj (.existsMem z (orderedPair 0 (x+1) (t+1)))
      (.existsMem z (orderedPair 0 (y+1) (t+1))))

theorem eval_pairName (t x y z : ℕ) (e : ℕ → ZFSet.{u}) :
    (pairName t x y z).Eval e ↔ e z = pairNameCode (e t) (e x) (e y) := by
  simp only [pairName,Formula.Eval,eval_allMem,eval_disj,eval_orderedPair,cons_zero,cons_succ]
  constructor
  · rintro ⟨h,hx,hy⟩
    apply ZFSet.ext; intro w
    rw [pairNameCode,ZFSet.mem_pair]
    constructor
    · exact h w
    · rintro (rfl|rfl)
      · obtain ⟨v,hv,rfl⟩ := hx; exact hv
      · obtain ⟨v,hv,rfl⟩ := hy; exact hv
  · intro he
    rw [he]
    exact ⟨fun w hw => ZFSet.mem_pair.mp hw,
      ⟨_,ZFSet.mem_pair.mpr (Or.inl rfl),rfl⟩,
      ⟨_,ZFSet.mem_pair.mpr (Or.inr rfl),rfl⟩⟩

end NameCodeFormula

noncomputable def orderedPairName {P : Type u} [Top P] (a b : Name P) : Name P :=
  Name.pair (Name.pair a a) (Name.pair a b)

theorem encode_orderedPairName {P : Type u} [Top P] (l : P → ZFSet.{u}) (a b : Name P) :
    (orderedPairName a b).encode l = orderedNameCode (l ⊤) (a.encode l) (b.encode l) := by
  simp only [orderedPairName,encode_pair,orderedNameCode,pairNameCode]

end TuringRigidity.TransitiveNameModel

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
namespace Formula

def envBound : ℕ → Formula
  | 0 => .equal 0 0
  | n+1 => .conj (envBound n) (.member (n+1) 0)

theorem eval_envBound (n : ℕ) (e : ℕ → ZFSet.{u}) :
    (envBound n).Eval e ↔ ∀ i, i < n → e (i+1) ∈ e 0 := by
  induction n with
  | zero => simp [envBound,Eval]
  | succ n ih =>
    simp only [envBound,Eval,ih]
    constructor
    · rintro ⟨h,hn⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi|rfl
      · exact h i hi
      · exact hn
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi),h n (Nat.lt_succ_self n)⟩
end Formula
namespace SigmaFormula

def skipDomain : ℕ → ℕ
  | 0 => 0
  | i+1 => i+2

end SigmaFormula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelReals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

noncomputable def decodeReal (x : ZFSet.{u}) : Oracle := fun n => by
  classical
  exact decide (natSet n ∈ x)

theorem decodeReal_true (x : ZFSet.{u}) (n : ℕ) : decodeReal x n = true ↔ natSet n ∈ x := by
  classical
  simp only [decodeReal,decide_eq_true_eq]

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_TableIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TableIndices
open Encodable UniformOracle CommonIdeal

theorem reduces_represents {Y A : Oracle} (h : Reduces A Y) :
    ∃ d : Nat.Partrec.Code, Represents Y d A := by
  obtain ⟨e, he⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp h
  have hf : Partrec₂ (fun L : List ℕ => fun n => OracleCode.eval (BranchMachine.lookup L) e n) :=
    OracleCode.eval_partrec BranchMachine.lookup_partrec e
  obtain ⟨d, hd⟩ := partrec_code hf
  have hd' : ∀ L n, d.eval (Nat.pair (encode L) n) = OracleCode.eval (BranchMachine.lookup L) e n :=
    fun L n => hd (L, n)
  have ha (n : ℕ) : Approximates (oracleFunction A n)
      (fun m => d.eval (Nat.pair (encode (oraclePrefix (fun k => bit (Y k)) m)) n)) := by
    simp only [hd']
    rw [← he]
    exact OracleCode.eval_approximates (prefix_approximates (fun k => bit (Y k))) e n
  refine ⟨d, ?_, ?_⟩
  · intro n z a hz
    exact Part.mem_some_iff.mp ((ha n).1 (Nat.unpair z).1 a (Nat.Partrec.Code.evaln_sound hz))
  · intro n
    obtain ⟨m, hm⟩ := (ha n).2 (bit (A n)) (Part.mem_some _)
    obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp (hm m le_rfl)
    exact ⟨Nat.pair m t, bit (A n), by simpa [run, trial] using ht⟩

end TuringRigidity.TableIndices

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
open Encodable UniformOracle TableIndices IndexMatrix IndexedOrder BoundedRecursive

def entryCheck (Y : Oracle) (v : ℕ) : ℕ :=
  let e := (Nat.unpair (Nat.unpair v).1).1
  let c := (Nat.unpair (Nat.unpair v).1).2
  let j := (Nat.unpair v).2
  if TableIndices.run Y (machine e) j (entry c j).2 = some (entry c j).1 then 1 else 0

def readsCheck (Y : Oracle) (v : ℕ) : ℕ :=
  allBelow (entryCheck Y) v (table (Nat.unpair v).2).length

instance instDecidableReads (Y : Oracle) (e : Nat.Partrec.Code) (L : List (ℕ × ℕ)) : Decidable (Reads Y e L) := by
  unfold Reads
  infer_instance

instance instDecidableCertificate (Y : Oracle) (e d : Nat.Partrec.Code) (n a z : ℕ) : Decidable (Certificate Y e d n a z) := by
  unfold Certificate
  infer_instance

end TuringRigidity.CertificateMatrix

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_UniformArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.UniformArithmetic
open Encodable

theorem Arith.congr {P Q} (h : Arith P) (he : ∀ O v, P O v ↔ Q O v) : Arith Q := by
  have : P = Q := funext (fun O => funext (fun v => propext (he O v)))
  exact this ▸ h

theorem Arith.or {P Q} (hP : Arith P) (hQ : Arith Q) :
    Arith (fun O v => P O v ∨ Q O v) :=
  (hP.neg.and hQ.neg).neg.congr (fun _ _ => by
    classical
    tauto)

theorem Arith.imp {P Q} (hP : Arith P) (hQ : Arith Q) :
    Arith (fun O v => P O v → Q O v) :=
  (hP.neg.or hQ).congr (fun _ _ => by tauto)

theorem Arith.all {P} (h : Arith P) :
    Arith (fun O v => ∀ n, P O (Nat.pair v n)) :=
  h.neg.ex.neg.congr (fun _ _ => by simp)

theorem equal {f g : ℕ → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Arith (fun _ v => f v = g v) := .pure _ (Primrec.eq.comp hf hg)

theorem less {f g : ℕ → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Arith (fun _ v => f v < g v) := .pure _ (Primrec.nat_lt.comp hf hg)

end TuringRigidity.UniformArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingForcing
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CodingForcing

theorem extends_trans {A : ℕ → Oracle} {p q r : Condition}
    (hpq : Extends A p q) (hqr : Extends A q r) : Extends A p r := by
  refine ⟨hpq.1.trans hqr.1, hpq.2.1.trans hqr.2.1,
    hpq.2.2.1.trans hqr.2.2.1, ?_⟩
  intro m hm hmr
  by_cases hmq : m < q.left.length
  · rw [getD_of_prefix hqr.1 hmq,
      getD_of_prefix hqr.2.1 (by simpa [← q.sameLength] using hmq)]
    exact hpq.2.2.2 m hm hmq
  · exact hqr.2.2.2 m ⟨Nat.le_of_not_gt hmq, hm.2.1.trans_le hpq.2.2.1, hm.2.2⟩ hmr

def append (p : Condition) (s : List Bool) : Condition where
  left := p.left ++ s
  right := p.right ++ s
  sameLength := by simp [p.sameLength]
  active := p.active

theorem append_extends (A : ℕ → Oracle) (p : Condition) (s : List Bool) :
    Extends A p (append p s) := by
  refine ⟨List.prefix_append _ _, List.prefix_append _ _, le_rfl, ?_⟩
  intro m hm _
  simp only [append, List.getD_eq_getElem?_getD, List.getElem?_append]
  rw [ite_eq_right (Nat.not_lt.mpr hm.1),
    ite_eq_right (by simpa [← p.sameLength] using Nat.not_lt.mpr hm.1), p.sameLength]

end TuringRigidity.CodingForcing

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
open Encodable UniformOracle CommonIdeal IndexMatrix

abbrev OracleFamily := Oracles → ℕ → Oracle
abbrev ArithmeticOracle (B : OracleFamily) :=
  Arith (fun O v => B O (left v) (right v) = true)

theorem query_at {B : OracleFamily} (hB : ArithmeticOracle B)
    {c n : ℕ → ℕ} (hc : Primrec c) (hn : Primrec n) :
    Arith (fun O v => B O (c v) (n v) = true) :=
  (hB.comp _ (Primrec₂.natPair.comp hc hn)).congr
    (fun _ _ => by simp only [left,right,Nat.unpair_pair])

theorem bit_equal {B : OracleFamily} (hB : ArithmeticOracle B)
    {c n a : ℕ → ℕ} (hc : Primrec c) (hn : Primrec n) (ha : Primrec a) :
    Arith (fun O v => a v = bit (B O (c v) (n v))) := by
  have h := query_at hB hc hn
  exact ((h.and (equal ha (Primrec.const 1))).or
    (h.neg.and (equal ha (Primrec.const 0)))).congr (fun O v => by
      cases B O (c v) (n v) <;> simp [bit])

def Prefix (B : Oracle) (m c : ℕ) : Prop :=
  (table c).length = m ∧ ∀ k, k < m → item c k = bit (B k)

theorem prefix_iff (B : Oracle) (m c : ℕ) :
    Prefix B m c ↔ table c = oraclePrefix (fun k => bit (B k)) m := by
  constructor
  · rintro ⟨hlen,he⟩
    apply List.ext_getElem
    · simpa [oraclePrefix] using hlen
    · intro k hk hk'
      have hkm : k < m := by simpa [oraclePrefix] using hk'
      have hh := he k hkm
      simpa [item,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,
        oraclePrefix] using hh
  · intro he
    constructor
    · simp [he,oraclePrefix]
    · intro k hk
      simp [item,he,oraclePrefix,List.getD_eq_getElem?_getD,List.getElem?_range hk]

theorem prefix_arith {B : OracleFamily} (hB : ArithmeticOracle B)
    {c m l : ℕ → ℕ} (hc : Primrec c) (hm : Primrec m) (hl : Primrec l) :
    Arith (fun O v => Prefix (B O (c v)) (m v) (l v)) := by
  have hb := bit_equal hB (hc.comp left_primrec) right_primrec
    (item_primrec.comp (hl.comp left_primrec) right_primrec)
  have ht := ((less right_primrec (hm.comp left_primrec)).imp hb).all
  exact ((equal (Primrec.list_length.comp (table_primrec.comp hl)) hm).and ht).congr
    (fun _ _ => by simp only [Prefix,left,right,Nat.unpair_pair])

def trialTest (e n m t a : ℕ) : Prop :=
  (machine e).evaln t (Nat.pair (encode (table m)) n) = some a

theorem trialTest_arith {e n m t a : ℕ → ℕ}
    (he : Primrec e) (hn : Primrec n) (hm : Primrec m) (ht : Primrec t) (ha : Primrec a) :
    Arith (fun _ v => trialTest (e v) (n v) (m v) (t v) (a v)) := by
  apply Arith.pure
  exact Primrec.eq.comp
    (Nat.Partrec.Code.primrec_evaln.comp
      ((ht.pair (machine_primrec.comp he)).pair
        (Primrec₂.natPair.comp (Primrec.encode.comp (table_primrec.comp hm)) hn)))
    (Primrec.option_some.comp ha)

theorem run_arith {B : OracleFamily} (hB : ArithmeticOracle B)
    {c e n z a : ℕ → ℕ} (hc : Primrec c) (he : Primrec e) (hn : Primrec n)
    (hz : Primrec z) (ha : Primrec a) :
    Arith (fun O v => TableIndices.run (B O (c v)) (machine (e v)) (n v) (z v) = some (a v)) := by
  have hp := prefix_arith hB (hc.comp left_primrec)
    ((left_primrec.comp hz).comp left_primrec) right_primrec
  have ht := trialTest_arith (he.comp left_primrec) (hn.comp left_primrec)
    right_primrec ((right_primrec.comp hz).comp left_primrec) (ha.comp left_primrec)
  apply (hp.and ht).ex.congr
  intro O v
  simp only [left,right,Nat.unpair_pair]
  constructor
  · rintro ⟨l,hp,ht⟩
    rw [prefix_iff] at hp
    simpa [trialTest,TableIndices.run,trial,hp] using ht
  · intro ht
    let L := oraclePrefix (fun k => bit (B O (c v) k)) (Nat.unpair (z v)).1
    refine ⟨encode L,?_,?_⟩
    · rw [prefix_iff]
      simp [table,L]
    · simpa [trialTest,table,L,TableIndices.run,trial] using ht

end TuringRigidity.UniformArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_OracleJump
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OracleJump
open Encodable UniformOracle CommonIdeal TableIndices IndexMatrix ArithmeticHierarchy

theorem forall_recursive_jump {Y : Oracle} {P : ℕ → Prop} (hP : RecursivePred Y P) :
    RecursivePred (jump Y) (fun x => ∀ a, P (Nat.pair x a)) := by
  have h := recursive_not (exists_recursive_jump (recursive_not hP))
  simpa only [not_exists, not_not] using h

end TuringRigidity.OracleJump

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticOracles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.UniformArithmetic
open Encodable UniformOracle CommonIdeal IndexMatrix TableIndices OracleJump EncodedForcing
noncomputable section

theorem parameter_arith (i : ℕ) : ArithmeticOracle (fun O _ => O i) :=
  (Arith.query i).comp _ right_primrec

theorem tableGraph_arith {B : OracleFamily} (hB : ArithmeticOracle B)
    {c e n : ℕ → ℕ} (hc : Primrec c) (he : Primrec e) (hn : Primrec n) :
    Arith (fun O v => tableGraph (B O (c v)) (e v) (n v)) :=
  ((run_arith hB (hc.comp left_primrec) (he.comp left_primrec)
    (hn.comp left_primrec) right_primrec (Primrec.const 1)).ex).congr
      (fun _ _ => by simp only [tableGraph,left,right,Nat.unpair_pair])

theorem tableOracle_arith {B : OracleFamily} (hB : ArithmeticOracle B)
    {e : ℕ → ℕ} (he : Primrec e) :
    ArithmeticOracle (fun O v => tableOracle (B O v) (e v)) := by
  exact (tableGraph_arith hB left_primrec (he.comp left_primrec) right_primrec).congr
    (fun _ _ => by simp [tableOracle])

theorem tableOracle_eq {B A : Oracle} {e : ℕ}
    (h : Represents B (machine e) A) : tableOracle B e = A := by
  funext n
  have hg : tableGraph B e n ↔ A n = true := by
    constructor
    · rintro ⟨z,hz⟩
      have hh := h.1 n z 1 (Option.mem_def.mpr hz)
      cases ha : A n <;> simp [bit,ha] at hh ⊢
    · intro ha
      obtain ⟨z,a,hz⟩ := h.2 n
      refine ⟨z,?_⟩
      have hh := h.1 n z a hz
      simpa [hh,bit,ha] using Option.mem_def.mp hz
  simp [tableOracle,hg]

end
end TuringRigidity.UniformArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.UniformArithmetic
open Encodable CommonIdeal IndexMatrix TableIndices OracleJump
noncomputable section

theorem join_arith {A B : OracleFamily} (hA : ArithmeticOracle A)
    (hB : ArithmeticOracle B) : ArithmeticOracle (fun O v => join (A O v) (B O v)) := by
  have ht : Arith (fun (_ : Oracles) v => (right v).bodd = true) :=
    .pure _ (Primrec.eq.comp (Primrec.nat_bodd.comp right_primrec) (Primrec.const true))
  have hd : Primrec (fun v => right v / 2) := Primrec.nat_div.comp right_primrec (Primrec.const 2)
  exact ((ht.and (query_at hB left_primrec hd)).or
    (ht.neg.and (query_at hA left_primrec hd))).congr (fun O v => by
      cases h : (right v).bodd <;> simp [join,h])

end
end TuringRigidity.UniformArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_CountableBound
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CountableBound
open UniformOracle

def sum (A : ℕ → Oracle) : Oracle := fun n => A (Nat.unpair n).1 (Nat.unpair n).2

end TuringRigidity.CountableBound

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_OracleEnumeration
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OracleEnumeration
open PrefixComputability

theorem exists_ge {A : Oracle} (hA : {n | A n = true}.Infinite) (n : ℕ) :
    ∃ m, n ≤ m ∧ A m = true := by
  by_contra h
  apply hA
  apply (Set.finite_le_nat n).subset
  intro m hm
  exact Nat.le_of_lt (Nat.lt_of_not_ge (fun hnm => h ⟨m, hnm, hm⟩))

noncomputable def next (A : Oracle) (hA : {n | A n = true}.Infinite) (n : ℕ) : ℕ :=
  Nat.find (exists_ge hA n)

noncomputable def enumerate (A : Oracle) (hA : {n | A n = true}.Infinite) : ℕ → ℕ
  | 0 => next A hA 0
  | n+1 => next A hA (enumerate A hA n + 1)

end TuringRigidity.OracleEnumeration

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingColumns
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CodingColumns
open PrefixComputability OracleEnumeration

theorem column_infinite (A : Oracle) (hA : {a | A a = true}.Infinite) (k cutoff : ℕ) :
    {m | column A k cutoff m = true}.Infinite := by
  have hi : (Nat.pair k '' {a | A a = true}).Infinite :=
    hA.image (fun a _ b _ h => (Nat.pair_eq_pair.mp h).2)
  apply (hi.sdiff (Set.finite_le_nat cutoff)).mono
  rintro m ⟨⟨a, ha, rfl⟩, hm⟩
  have hc : cutoff ≤ Nat.pair k a := Nat.le_of_lt (Nat.lt_of_not_ge hm)
  change A a = true at ha
  simp [hc, ha]

noncomputable def location (A : Oracle) (hA : {a | A a = true}.Infinite)
    (k cutoff : ℕ) : ℕ → ℕ := enumerate (column A k cutoff) (column_infinite A hA k cutoff)

noncomputable def readColumn (A : Oracle) (hA : {a | A a = true}.Infinite)
    (k cutoff : ℕ) (G : Oracle) : Oracle := fun n => G (location A hA k cutoff n)

end TuringRigidity.CodingColumns

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingAgreement
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CodingAgreement
open CodingForcing

def UniqueValues (A : ℕ → Oracle) (Y : Oracle) (e : OracleCode) (p : Condition) : Prop :=
  ∀ q r, Extends A p q → Extends A p r → ∀ n a b,
    a ∈ CommonIdeal.run Y e q.left n → b ∈ CommonIdeal.run Y e r.left n → a = b

end TuringRigidity.CodingAgreement

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingOnePoint
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CodingOnePoint
open CodingForcing CodingAgreement

def changeLeft (q : Condition) (m : ℕ) (b : Bool) : Condition where
  left := q.left.set m b
  right := q.right
  sameLength := by simpa using q.sameLength
  active := q.active

theorem changeLeft_extends {A : ℕ → Oracle} {p q : Condition} (hpq : Extends A p q)
    (m : ℕ) (hm : p.left.length ≤ m) (hnc : ¬ CodingLocation A p m) (b : Bool) :
    Extends A p (changeLeft q m b) := by
  refine ⟨prefix_set_of_le hpq.1 m hm b, hpq.2.1, hpq.2.2.1, ?_⟩
  intro j hj hjlen
  have hne : m ≠ j := by
    intro h
    subst j
    exact hnc hj
  have heq := hpq.2.2.2 j hj (by simpa [changeLeft] using hjlen)
  simpa [changeLeft, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne] using heq

end TuringRigidity.CodingOnePoint

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingLocations
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CodingLocations
open CodingForcing CodingAgreement CodingOnePoint CodingSplitting

def SplittingLocation (Y : Oracle) (e : OracleCode) (base : List Bool) (m : ℕ) : Prop :=
  ∃ s b n v w, base <+: s ∧ base.length ≤ m ∧ m < s.length ∧ v ≠ w ∧
    v ∈ CommonIdeal.run Y e s n ∧ w ∈ CommonIdeal.run Y e (s.set m b) n

end TuringRigidity.CodingLocations

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingSplitSearch
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CodingSplitSearch
open Encodable PrefixComputability CodingLocations

def trial (Y : Oracle) (d : Nat.Partrec.Code) (base : List Bool) (z : ℕ) : Option ℕ :=
  finiteTrial d base (oraclePrefix (fun n => CommonIdeal.bit (Y n)) (Nat.unpair z).1)
    ((decode (α := Witness) (Nat.unpair z).2).getD default)

end TuringRigidity.CodingSplitSearch

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingExtraction
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CodingExtraction
open CodingForcing CodingAgreement CodingLocations CodingSplitSearch PrefixComputability

theorem column_projection_reduces (C : Oracle) (k : ℕ) :
    Reduces (fun a => C (Nat.pair k a)) C := by
  apply RecursiveIn.iff_nat.mpr
  have hq : Nat.RecursiveIn {oracleFunction C} (oracleFunction C) := .oracle _ (Set.mem_singleton _)
  exact _root_.OAI.TuringRigidity.PrefixComputability.total_comp hq (_root_.OAI.TuringRigidity.PrefixComputability.total_primrec (Primrec₂.natPair.comp (Primrec.const k) Primrec.id))

end TuringRigidity.CodingExtraction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_EffectiveCohen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.EffectiveCohen
open Encodable UniformOracle ArithmeticHierarchy OracleJump EffectiveWitness EncodedForcing

theorem word_decision (Y : Oracle) :
    ∃ step : ℕ → ℕ, Nat.RecursiveIn {oracleFunction (jump Y)} (fun x => Part.some (step x)) ∧
      ∀ e p, word p <+: word (step (Nat.pair e p)) ∧
        (Halts Y e (encode (word (step (Nat.pair e p)))) ∨
          ∀ q : List Bool, word (step (Nat.pair e p)) <+: q → ¬ Halts Y e (encode q)) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let P : ℕ → Prop := fun v =>
    word (Nat.unpair (Nat.unpair v).1).2 <+: word (Nat.unpair v).2 ∧
      Halts Y (Nat.unpair (Nat.unpair v).1).1 (encode (word (Nat.unpair v).2))
  have hp := EncodedForcing.prefix_recursive Y (word_primrec.comp (r.comp f)) (word_primrec.comp r)
  have hh := (halts_sigma Y).comp (Primrec₂.natPair.comp (f.comp f)
    (Primrec.encode.comp (word_primrec.comp r)))
  have hP : Sigma Y 1 P := by
    simpa only [P,Nat.unpair_pair] using (Form.raise (n := 0) (s := true) hp).and hh
  obtain ⟨g,hg,hs⟩ := sigma1_choice hP
  let a : ℕ → ℕ := fun v => if (Nat.unpair v).2 = 0 then (Nat.unpair v).1 else (Nat.unpair v).2-1
  have ha : Primrec a := Primrec.ite
    (Primrec.eq.comp r (Primrec.const 0)) f (Primrec.nat_sub.comp r (Primrec.const 1))
  let step : ℕ → ℕ := fun x => a (Nat.pair (Nat.unpair x).2 (g x))
  have hstep := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := {oracleFunction (jump Y)}) ha)
    (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec r) hg)
  refine ⟨step,hstep,fun e p => ?_⟩
  rcases hs (Nat.pair e p) with ⟨hz,hn⟩ | ⟨hp,hw⟩
  · have he : step (Nat.pair e p) = p := by simp [step,a,hz]
    rw [he]
    refine ⟨List.prefix_rfl,Or.inr (fun q hq hhalt => ?_)⟩
    exact hn ⟨encode q,by simpa [P,word] using And.intro hq hhalt⟩
  · have hz : g (Nat.pair e p) ≠ 0 := by omega
    have he : step (Nat.pair e p) = g (Nat.pair e p)-1 := by simp [step,a,hz]
    rw [he]
    have hh : word p <+: word (g (Nat.pair e p)-1) ∧
        Halts Y e (encode (word (g (Nat.pair e p)-1))) := by simpa [P] using hw
    exact ⟨hh.1,Or.inl hh.2⟩

noncomputable def decider (Y : Oracle) : ℕ → ℕ := Classical.choose (word_decision Y)

def grow (p : ℕ) : ℕ := encode (word p ++ [false])

noncomputable def stage (Y : Oracle) : ℕ → ℕ
  | 0 => encode ([] : List Bool)
  | s+1 => grow (decider Y (Nat.pair s (stage Y s)))

noncomputable def generic (Y : Oracle) : Oracle := fun n => (word (stage Y (n+1))).getD n false

def OneGeneric (Y G : Oracle) : Prop := ∀ e, ∃ p : List Bool,
  (∀ n < p.length, G n = p.getD n false) ∧
    (Halts Y e (encode p) ∨ ∀ q : List Bool, p <+: q → ¬ Halts Y e (encode q))

end TuringRigidity.EffectiveCohen

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
open Encodable UniformOracle CommonIdeal ArithmeticHierarchy OracleJump EncodedForcing IndexMatrix

def Agrees (Y : Oracle) (p : List Bool) (L : List ℕ) : Prop :=
  ∀ i < L.length, if i.bodd then i/2 < p.length ∧ L.getD i 0 = bit (p.getD (i/2) false)
    else L.getD i 0 = bit (Y (i/2))

def Certificate (Y : Oracle) (v : ℕ) : Prop :=
  Agrees Y (word (Nat.unpair (Nat.unpair v).1).2) (table (Nat.unpair (Nat.unpair v).2).1) ∧
    ((machine (Nat.unpair (Nat.unpair (Nat.unpair v).1).1).1).evaln
      (Nat.unpair (Nat.unpair v).2).2
      (Nat.pair (encode (table (Nat.unpair (Nat.unpair v).2).1))
        (Nat.unpair (Nat.unpair (Nat.unpair v).1).1).2)).isSome = true

def OpenHalts (Y : Oracle) (x p : ℕ) : Prop := ∃ z, Certificate Y (Nat.pair (Nat.pair x p) z)

def Prefix (G : Oracle) (p : List Bool) : Prop := ∀ i < p.length, G i = p.getD i false

end TuringRigidity.CohenHalting

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenLowness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenLowness
open Encodable UniformOracle CommonIdeal ArithmeticHierarchy OracleJump EncodedForcing
open CohenHalting EffectiveCohen EffectiveWitness

def Extension (Y : Oracle) (x p : ℕ) : Prop :=
  ∃ q, word p <+: word q ∧ OpenHalts Y x (encode (word q))

def Deciding (Y G : Oracle) (v : ℕ) : Prop :=
  Prefix G (word (Nat.unpair v).2) ∧
    (OpenHalts Y (Nat.unpair v).1 (encode (word (Nat.unpair v).2)) ∨
      ¬ Extension Y (Nat.unpair v).1 (Nat.unpair v).2)

end TuringRigidity.CohenLowness

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_EffectiveSplitConditions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.EffectiveSplitConditions
open Encodable UniformOracle ArithmeticHierarchy EncodedForcing OracleJump
open CodingForcing CodingAgreement CodingLocations

def update (p w : ℕ) : ℕ :=
  if (Nat.unpair w).1 = 2 then
    code (append (condition p) ((word (item (Nat.unpair w).2 1)).drop (left p).length))
  else code (condition p)

theorem update_primrec : Primrec₂ update := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hc : Primrec (fun p : ℕ => code (condition p)) := Primrec₂.natPair.comp
    (Primrec.encode.comp left_primrec)
    (Primrec₂.natPair.comp (Primrec.encode.comp right_primrec) active_primrec)
  let l : Primrec (fun z : ℕ × ℕ => left z.1) := left_primrec.comp Primrec.fst
  let rr : Primrec (fun z : ℕ × ℕ => right z.1) := right_primrec.comp Primrec.fst
  let tail := Primrec.list_drop.comp (Primrec.list_length.comp l)
    (word_primrec.comp (item_primrec.comp (r.comp Primrec.snd) (Primrec.const 1)))
  have ha := Primrec₂.natPair.comp (Primrec.encode.comp (Primrec.list_append.comp l tail))
    (Primrec₂.natPair.comp (Primrec.encode.comp (Primrec.list_append.comp rr tail))
      (active_primrec.comp Primrec.fst))
  exact Primrec.ite (Primrec.eq.comp (f.comp Primrec.snd) (Primrec.const 2)) ha (hc.comp Primrec.fst)

end TuringRigidity.EffectiveSplitConditions

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

attribute [local instance] OAI.TuringRigidity.UniformProgram.instDecidableEqCode
def meaning : Code → OracleCode
  | .zero => .zero
  | .succ => .succ
  | .left => .left
  | .right => .right
  | .pair c d => .pair (meaning c) (meaning d)
  | .comp c d => .comp (meaning c) (meaning d)
  | .prec c d => .prec (meaning c) (meaning d)
  | .rfind' c => if c = .zero then .query else .find (meaning c)

def tag : Code → ℕ
  | .zero => 0 | .succ => 1 | .left => 2 | .right => 3
  | .pair _ _ => 4 | .comp _ _ => 5 | .prec _ _ => 6 | .rfind' _ => 7

theorem tag_primrec : Primrec tag := by
  have h := Nat.Partrec.Code.primrec_recOn (α := Code) (σ := ℕ) Primrec.id
    (Primrec.const 0) (Primrec.const 1) (Primrec.const 2) (Primrec.const 3)
    (pr := fun _ _ _ _ _ => 4) (Primrec.const 4)
    (co := fun _ _ _ _ _ => 5) (Primrec.const 5)
    (pc := fun _ _ _ _ _ => 6) (Primrec.const 6)
    (rf := fun _ _ _ => 7) (Primrec.const 7)
  exact h.of_eq (fun e => by cases e <;> rfl)

variable {α : Type*} [Primcodable α] (g : α → ℕ →. ℕ)

def layer (self : Code) (z : Code × α × ℕ) : Part ℕ :=
  let e := z.1
  let a := z.2.1
  let n := z.2.2
  let c := fun k => self.eval (encode (first e,a,k))
  let d := fun k => self.eval (encode (second e,a,k))
  if tag e = 0 then Part.some 0 else
  if tag e = 1 then Part.some (n+1) else
  if tag e = 2 then Part.some (Nat.unpair n).1 else
  if tag e = 3 then Part.some (Nat.unpair n).2 else
  if tag e = 4 then Nat.pair <$> c n <*> d n else
  if tag e = 5 then d n >>= c else
  if tag e = 6 then
    if (Nat.unpair n).2 = 0 then c (Nat.unpair n).1 else
      self.eval (encode (e,a,Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2-1))) >>= fun b =>
        d (Nat.pair (Nat.unpair n).1 (Nat.pair ((Nat.unpair n).2-1) b)) else
  if first e = .zero then g a n else
    Nat.rfind (fun k => (fun b => b = 0) <$> c (Nat.pair n k))

theorem layer_partrec (hg : Partrec₂ g) : Partrec₂ (layer g) := by
  let e : Computable (fun z : Code × (Code × α × ℕ) => z.2.1) := fst.comp snd
  let a : Computable (fun z : Code × (Code × α × ℕ) => z.2.2.1) := fst.comp (snd.comp snd)
  let n : Computable (fun z : Code × (Code × α × ℕ) => z.2.2.2) := snd.comp (snd.comp snd)
  have hc : Partrec₂ (fun z : Code × (Code × α × ℕ) => fun (k : ℕ) =>
      z.1.eval (encode (first z.2.1,z.2.2.1,k))) :=
    Nat.Partrec.Code.eval_part.comp (fst.comp fst)
      (Computable.encode.comp (((first_primrec.to_comp.comp e).comp fst).pair
        ((a.comp fst).pair snd)))
  have hd : Partrec₂ (fun z : Code × (Code × α × ℕ) => fun (k : ℕ) =>
      z.1.eval (encode (second z.2.1,z.2.2.1,k))) :=
    Nat.Partrec.Code.eval_part.comp (fst.comp fst)
      (Computable.encode.comp (((second_primrec.to_comp.comp e).comp fst).pair
        ((a.comp fst).pair snd)))
  have ht (i : ℕ) : Computable (fun z : Code × (Code × α × ℕ) => tag z.2.1 == i) :=
    (Primrec.beq.comp (tag_primrec.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const i)).to_comp
  have hq : Computable (fun z : Code × (Code × α × ℕ) => first z.2.1 == Nat.Partrec.Code.zero) :=
    (Primrec.beq.comp (first_primrec.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const Nat.Partrec.Code.zero)).to_comp
  have hpair : Partrec (fun z : Code × (Code × α × ℕ) =>
      Nat.pair <$> z.1.eval (encode (first z.2.1,z.2.2.1,z.2.2.2)) <*>
        z.1.eval (encode (second z.2.1,z.2.2.1,z.2.2.2))) := by
    change Partrec (fun z : Code × (Code × α × ℕ) =>
      (z.1.eval (encode (first z.2.1,z.2.2.1,z.2.2.2))).bind
        (fun x => (z.1.eval (encode (second z.2.1,z.2.2.1,z.2.2.2))).map (Nat.pair x)))
    apply Partrec.bind (hc.comp Computable.id n)
    apply Partrec.map ((hd.comp Computable.id n).comp fst)
    exact Primrec₂.natPair.to_comp.comp (snd.comp fst) snd
  have hcomp : Partrec (fun z : Code × (Code × α × ℕ) =>
      (z.1.eval (encode (second z.2.1,z.2.2.1,z.2.2.2))).bind
        (fun k => z.1.eval (encode (first z.2.1,z.2.2.1,k)))) := (hd.comp Computable.id n).bind (hc.comp fst snd)
  have hprev : Partrec (fun z : Code × (Code × α × ℕ) =>
      z.1.eval (encode (z.2.1,z.2.2.1,Nat.pair (Nat.unpair z.2.2.2).1 ((Nat.unpair z.2.2.2).2-1)))) :=
    Nat.Partrec.Code.eval_part.comp fst (Computable.encode.comp (e.pair (a.pair
      (Primrec₂.natPair.to_comp.comp ((fst.comp Computable.unpair).comp n)
        (Computable.pred.comp ((snd.comp Computable.unpair).comp n))))))
  have hnext : Partrec (fun z : (Code × (Code × α × ℕ)) × ℕ =>
      z.1.1.eval (encode (second z.1.2.1,z.1.2.2.1,
        Nat.pair (Nat.unpair z.1.2.2.2).1 (Nat.pair ((Nat.unpair z.1.2.2.2).2-1) z.2)))) :=
    hd.comp fst (Primrec₂.natPair.to_comp.comp (((fst.comp Computable.unpair).comp n).comp fst)
      (Primrec₂.natPair.to_comp.comp ((Computable.pred.comp ((snd.comp Computable.unpair).comp n)).comp fst) snd))
  have hzero : Computable (fun z : Code × (Code × α × ℕ) => (Nat.unpair z.2.2.2).2 == 0) :=
    (Primrec.beq.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.const 0)).to_comp
  have hbase : Partrec (fun z : Code × (Code × α × ℕ) =>
      z.1.eval (encode (first z.2.1,z.2.2.1,(Nat.unpair z.2.2.2).1))) :=
    hc.comp Computable.id ((fst.comp Computable.unpair).comp n)
  have hsucc : Partrec (fun z : Code × (Code × α × ℕ) =>
      (z.1.eval (encode (z.2.1,z.2.2.1,Nat.pair (Nat.unpair z.2.2.2).1 ((Nat.unpair z.2.2.2).2-1)))).bind
        (fun v => z.1.eval (encode (second z.2.1,z.2.2.1,
          Nat.pair (Nat.unpair z.2.2.2).1 (Nat.pair ((Nat.unpair z.2.2.2).2-1) v))))) := hprev.bind hnext
  have hprec := partrec_cond hzero hbase hsucc
  have hfind : Partrec (fun z : Code × (Code × α × ℕ) =>
      Nat.rfind (fun k => (fun b => b = 0) <$> z.1.eval (encode (first z.2.1,z.2.2.1,Nat.pair z.2.2.2 k)))) := Partrec.rfind ((hc.comp fst
    (Primrec₂.natPair.to_comp.comp (n.comp fst) snd)).map
      ((Primrec.beq.comp Primrec.snd (Primrec.const 0)).to_comp))
  have h := partrec_cond (ht 0) (Computable.const 0).partrec
    (partrec_cond (ht 1) (Computable.succ.comp n).partrec
    (partrec_cond (ht 2) ((fst.comp Computable.unpair).comp n).partrec
    (partrec_cond (ht 3) ((snd.comp Computable.unpair).comp n).partrec
    (partrec_cond (ht 4) hpair (partrec_cond (ht 5) hcomp
    (partrec_cond (ht 6) hprec (partrec_cond hq (hg.comp a n) hfind)))))))
  exact h.of_eq (fun z => by simp only [layer,beq_iff_eq]; rfl)

theorem eval_partrec (hg : Partrec₂ g) :
    Partrec (fun z : Code × α × ℕ => OracleCode.eval (g z.2.1) (meaning z.1) z.2.2) := by
  obtain ⟨c,hc⟩ := partrec_fixed_point (layer_partrec g hg)
  have he : ∀ e a n, c.eval (encode (e,a,n)) = OracleCode.eval (g a) (meaning e) n := by
    intro e
    induction e with
    | zero | succ | left | right => intros; rw [hc]; rfl
    | pair e f he hf | comp e f he hf =>
      intro a n
      rw [hc]
      simp only [layer,tag,first,second,meaning,OracleCode.eval,he,hf]
      simp <;> rfl
    | prec e f he hf =>
      intro a n
      have hn : ∃ u k, n = Nat.pair u k := ⟨_,_,(Nat.pair_unpair n).symm⟩
      obtain ⟨u,k,rfl⟩ := hn
      induction k with
      | zero =>
        rw [hc]
        simp only [layer,tag,first,second,meaning,Nat.unpair_pair]
        simp only [show (6 : ℕ) ≠ 0 from by decide,show (6 : ℕ) ≠ 1 from by decide,
          show (6 : ℕ) ≠ 2 from by decide,show (6 : ℕ) ≠ 3 from by decide,
          show (6 : ℕ) ≠ 4 from by decide,show (6 : ℕ) ≠ 5 from by decide,↓reduceIte]
        rw [he]
        simp only [OracleCode.eval,Nat.unpair_pair,Nat.rec_zero]
      | succ k ih =>
        rw [hc]
        simp only [layer,tag,first,second,meaning,he,hf,Nat.unpair_pair]
        simp only [show (6 : ℕ) ≠ 0 from by decide,show (6 : ℕ) ≠ 1 from by decide,
          show (6 : ℕ) ≠ 2 from by decide,show (6 : ℕ) ≠ 3 from by decide,
          show (6 : ℕ) ≠ 4 from by decide,show (6 : ℕ) ≠ 5 from by decide,
          ↓reduceIte,Nat.add_one_ne_zero,Nat.add_sub_cancel]
        rw [ih]
        simp only [meaning,OracleCode.eval,Nat.unpair_pair]
    | rfind' e he =>
      intro a n
      rw [hc]
      simp only [layer,tag,first,meaning,he]
      simp
      split <;> rfl
  exact (Nat.Partrec.Code.eval_part.comp (Computable.const c) Computable.encode).of_eq
    (fun z => he z.1 z.2.1 z.2.2)

end TuringRigidity.UniformProgram

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.UniformRun
open Encodable Computable UniformOracle CommonIdeal ArithmeticHierarchy OracleJump EncodedForcing IndexMatrix
open UniformProgram

def run (A : Oracle) (b e : Code) (p : List Bool) (n : ℕ) : Part ℕ :=
  OracleCode.eval (partialJoin (OracleCode.eval (oracleFunction A) (meaning b)) (table p)) (meaning e) n

def finiteRun (z : List ℕ × Code × Code × List Bool × ℕ) : Part ℕ :=
  OracleCode.eval (partialJoin (OracleCode.eval (BranchMachine.lookup z.1) (meaning z.2.1))
    (table z.2.2.2.1)) (meaning z.2.2.1) z.2.2.2.2

theorem eval_partialJoin_partrec {α : Type*} [Primcodable α]
    {L : α → List ℕ} {b e : α → Code} {p : α → List Bool} {n : α → ℕ}
    (hL : Computable L) (hb : Computable b) (he : Computable e)
    (hp : Computable p) (hn : Computable n) :
    Partrec (fun z => OracleCode.eval
      (partialJoin (OracleCode.eval (BranchMachine.lookup (L z)) (meaning (b z))) (table (p z)))
      (meaning (e z)) (n z)) := by
  have hbase : Partrec₂ (fun z : α => OracleCode.eval (BranchMachine.lookup (L z)) (meaning (b z))) :=
    (UniformProgram.eval_partrec BranchMachine.lookup BranchMachine.lookup_partrec).comp
      ((hb.comp fst).pair ((hL.comp fst).pair snd))
  have htable : Partrec₂ (fun z : α => table (p z)) := table_partrec.comp (hp.comp fst) snd
  exact (UniformProgram.eval_partrec _ (BranchMachine.partialJoin_partrec hbase htable)).comp
    (he.pair (Computable.id.pair hn))

theorem finiteRun_partrec : Partrec finiteRun := by
  exact eval_partialJoin_partrec
    (L := fun z : List ℕ × Code × Code × List Bool × ℕ => z.1)
    (b := fun z => z.2.1) (e := fun z => z.2.2.1)
    (p := fun z => z.2.2.2.1) (n := fun z => z.2.2.2.2)
    fst (fst.comp snd) (fst.comp (snd.comp snd))
    (fst.comp (snd.comp (snd.comp snd))) (snd.comp (snd.comp (snd.comp snd)))

theorem finiteRun_approximates (A : Oracle) (b e : Code) (p : List Bool) (n : ℕ) :
    Approximates (run A b e p n) (fun m => finiteRun
      (oraclePrefix (fun k => bit (A k)) m,b,e,p,n)) := by
  apply OracleCode.eval_approximates
  intro k
  apply BranchMachine.partialJoin_approximates
  · exact OracleCode.eval_approximates (prefix_approximates (fun k => bit (A k))) (meaning b)
  · intro k; exact Approximates.const _

theorem run_mono {A : Oracle} {b e : Code} {s t : List Bool}
    (h : s <+: t) (n a : ℕ) (ha : a ∈ run A b e s n) : a ∈ run A b e t n := by
  apply OracleCode.eval_mono (c := meaning e) (n := n) (a := a) ?_ ha
  intro k v hv
  cases hk : k.bodd with
  | false => simpa [partialJoin,hk] using hv
  | true =>
    exact table_mono h _ _ (by simpa [partialJoin,hk] using hv) |>
      (fun hh => by simpa [partialJoin,hk] using hh)

theorem run_table (A : Oracle) : ∃ d : Nat.Partrec.Code,
    ∀ b e p n a, a ∈ run A b e (word p) n ↔
      ∃ z, a ∈ TableIndices.run A d (encode (b,e,word p,n)) z := by
  obtain ⟨d,hd⟩ := partrec_code finiteRun_partrec
  have hd' (L : List ℕ) (b e : Code) (p : List Bool) (n : ℕ) :
      d.eval (Nat.pair (encode L) (encode (b,e,p,n))) = finiteRun (L,b,e,p,n) := hd (L,b,e,p,n)
  refine ⟨d,fun b e p n a => ?_⟩
  have ha := finiteRun_approximates A b e (word p) n
  constructor
  · intro h
    obtain ⟨m,hm⟩ := ha.2 a h
    have hh := hm m le_rfl
    dsimp only at hh
    rw [← hd'] at hh
    obtain ⟨t,ht⟩ := Nat.Partrec.Code.evaln_complete.mp hh
    exact ⟨Nat.pair m t,by simpa only [TableIndices.run,trial,Nat.unpair_pair] using ht⟩
  · rintro ⟨z,hz⟩
    have hh := Nat.Partrec.Code.evaln_sound hz
    rw [hd'] at hh
    exact ha.1 (Nat.unpair z).1 a hh

def Graph (A : Oracle) (v : ℕ) : Prop :=
  item v 4 ∈ run A (machine (item v 0)) (machine (item v 1)) (word (item v 2)) (item v 3)

theorem graph_sigma (A : Oracle) : Sigma A 1 (Graph A) := by
  obtain ⟨d,hd⟩ := run_table A
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let a (i : ℕ) := item_primrec.comp f (Primrec.const i)
  have hinput := Primrec.encode.comp ((machine_primrec.comp (a 0)).pair
    ((machine_primrec.comp (a 1)).pair ((word_primrec.comp (a 2)).pair (a 3))))
  have hr := _root_.OAI.TuringRigidity.UniformOracle.total_comp (run_uniform_recursive A) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec
    (Primrec₂.natPair.comp (Primrec.const (encode d)) (Primrec₂.natPair.comp hinput r)))
  have heq : Primrec (fun v : ℕ => if (decode (α := Option ℕ) (Nat.unpair v).1).getD none =
      some (Nat.unpair v).2 then 1 else 0) :=
    Primrec.ite (Primrec.eq.comp (Primrec.option_getD.comp (Primrec.decode.comp f) (Primrec.const none))
      (Primrec.option_some.comp r)) (Primrec.const 1) (Primrec.const 0)
  have hcert : RecursivePred A (fun v => item (Nat.unpair v).1 4 ∈
      TableIndices.run A d (encode (machine (item (Nat.unpair v).1 0),
        machine (item (Nat.unpair v).1 1),word (item (Nat.unpair v).1 2),
        item (Nat.unpair v).1 3)) (Nat.unpair v).2) := by
    exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec heq) (_root_.OAI.TuringRigidity.UniformOracle.total_pair hr (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (a 4)))).of_eq
      (fun v => by simp [Option.mem_def])
  apply Form.congr (exists_form (n := 0) hcert)
  intro v
  simp only [Graph,Nat.unpair_pair]
  exact (hd _ _ _ _ _).symm

theorem graph_sigma_of (A : Oracle) {b e p n a : ℕ → ℕ}
    (hb : Primrec b) (he : Primrec e) (hp : Primrec p) (hn : Primrec n) (ha : Primrec a) :
    Sigma A 1 (fun v => a v ∈ run A (machine (b v)) (machine (e v)) (word (p v)) (n v)) := by
  have h := (graph_sigma A).comp (Primrec.encode.comp
    (Primrec.list_cons.comp hb (Primrec.list_cons.comp he (Primrec.list_cons.comp hp
      (Primrec.list_cons.comp hn (Primrec.list_cons.comp ha (Primrec.const [])))))))
  simpa only [Graph,item,encodek,Option.getD_some,List.getD_cons_zero,List.getD_cons_succ] using h

end TuringRigidity.UniformRun

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformAgreement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.UniformAgreement
open Encodable UniformOracle ArithmeticHierarchy OracleJump EncodedForcing EffectiveWitness IndexMatrix
open CodingForcing UniformProgram

def Disagreement (A : Oracle) (x : ℕ) (p : Condition) : Prop :=
  ∃ n a b, a ≠ b ∧
    a ∈ UniformRun.run A (machine (item x 0)) (machine (item x 1)) p.left n ∧
    b ∈ UniformRun.run A (machine (item x 0)) (machine (item x 2)) p.right n

def NoDisagreement (A : Oracle) (x : ℕ) (p : Condition) : Prop :=
  ∀ q, Extends (columns A) p q → ¬ Disagreement A x q

end TuringRigidity.UniformAgreement

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.UniformSplit
open Encodable UniformOracle ArithmeticHierarchy OracleJump EncodedForcing EffectiveWitness IndexMatrix
open UniformProgram

def base (x : ℕ) := machine (item x 0)
def program (x : ℕ) := machine (item x 1)
def start (x : ℕ) := word (item x 2)

def SplitCert (A : Oracle) (v : ℕ) : Prop :=
  let x := (Nat.unpair v).1
  let w := (Nat.unpair v).2
  start x <+: word (item w 1) ∧ start x <+: word (item w 2) ∧ item w 3 ≠ item w 4 ∧
    item w 3 ∈ UniformRun.run A (base x) (program x) (word (item w 1)) (item w 0) ∧
    item w 4 ∈ UniformRun.run A (base x) (program x) (word (item w 2)) (item w 0)

def PointCert (A : Oracle) (v : ℕ) : Prop :=
  let x := (Nat.unpair v).1
  let w := (Nat.unpair v).2
  let q := word (item w 1)
  start x <+: q ∧ (start x).length ≤ item w 2 ∧ item w 2 < q.length ∧ item w 4 ≠ item w 5 ∧
    item w 4 ∈ UniformRun.run A (base x) (program x) q (item w 0) ∧
    item w 5 ∈ UniformRun.run A (base x) (program x) (q.set (item w 2) (item w 3).bodd) (item w 0)

theorem pointCert_sigma (A : Oracle) : Sigma A 1 (PointCert A) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let x (i : ℕ) := item_primrec.comp f (Primrec.const i)
  let w (i : ℕ) := item_primrec.comp r (Primrec.const i)
  let p := word_primrec.comp (x 2)
  let q := word_primrec.comp (w 1)
  have hp := EncodedForcing.prefix_recursive A p q
  have hlo := recursive_primrecPred A (Primrec.nat_le.comp (Primrec.list_length.comp p) (w 2))
  have hhi := recursive_primrecPred A (Primrec.nat_lt.comp (w 2) (Primrec.list_length.comp q))
  have hn := recursive_primrecPred A ((Primrec.eq.comp (w 4) (w 5)).not)
  have hl := UniformRun.graph_sigma_of A (x 0) (x 1) (w 1) (w 0) (w 4)
  have hr := UniformRun.graph_sigma_of A (x 0) (x 1)
    (Primrec.encode.comp (Primrec.list_set.comp q ((w 2).pair (Primrec.nat_bodd.comp (w 3)))))
    (w 0) (w 5)
  unfold PointCert
  simpa only [base,program,start,word,encodek,Option.getD_some] using
    (Form.raise (n := 0) (s := true) hp).and ((Form.raise (n := 0) (s := true) hlo).and
      ((Form.raise (n := 0) (s := true) hhi).and ((Form.raise (n := 0) (s := true) hn).and (hl.and hr))))

def ConvergesAbove (A : Oracle) (v : ℕ) : Prop :=
  let x := (Nat.unpair v).1
  let w := (Nat.unpair v).2
  ∃ q a, word (item w 1) <+: word q ∧
    a ∈ UniformRun.run A (base x) (program x) (word q) (item w 0)

def DivCert (A : Oracle) (v : ℕ) : Prop :=
  start (Nat.unpair v).1 <+: word (item (Nat.unpair v).2 1) ∧ ¬ ConvergesAbove A v

def Accept (A : Oracle) (v : ℕ) : Prop :=
  let x := (Nat.unpair v).1
  let tag := (Nat.unpair (Nat.unpair v).2).1
  let w := (Nat.unpair (Nat.unpair v).2).2
  (tag = 0 ∧ ¬ ∃ z, SplitCert A (Nat.pair x z)) ∨
    (tag = 1 ∧ PointCert A (Nat.pair x w)) ∨
    (tag = 2 ∧ DivCert A (Nat.pair x w))

theorem accept_total (A : Oracle) : ∀ x, ∃ w, Accept A (Nat.pair x w) := by
  intro x
  by_cases hs : ∃ z, SplitCert A (Nat.pair x z)
  · obtain ⟨z,hp,hq,hab,ha,hb⟩ := hs
    simp only [Nat.unpair_pair] at hp hq hab ha hb
    let f := fun w => UniformRun.run A (base x) (program x) w (item z 0)
    have hs : CodingSplitting.OnePoint (start x) f ∨
        ∃ w, start x <+: w ∧ ∀ u v, v ∉ f (w ++ u) := by
      by_cases hd : ∀ w, start x <+: w → ∃ u v, v ∈ f (w ++ u)
      · exact Or.inl (CodingSplitting.onePoint_of_dense
          (fun h v hv => UniformRun.run_mono h (item z 0) v hv) hd hp hq _ _ ha hb hab)
      · right; push Not at hd; exact hd
    rcases hs with hs | hd
    · obtain ⟨q,m,b,a,c,hpq,hlo,hhi,hac,ha,hc⟩ := hs
      refine ⟨Nat.pair 1 (encode [item z 0,encode q,m,CommonIdeal.bit b,a,c]),Or.inr (Or.inl ⟨by simp,?_⟩)⟩
      have hbit : (CommonIdeal.bit b).bodd = b := by cases b <;> rfl
      simpa [PointCert,item,word,hbit,f] using
        And.intro hpq (And.intro hlo (And.intro hhi (And.intro hac (And.intro ha hc))))
    · obtain ⟨q,hpq,hd⟩ := hd
      refine ⟨Nat.pair 2 (encode [item z 0,encode q]),Or.inr (Or.inr ⟨by simp,?_,?_⟩)⟩
      · simpa [item,word] using hpq
      · simp only [ConvergesAbove,Nat.unpair_pair,item,encodek,Option.getD_some,
          List.getD_cons_zero,List.getD_cons_succ,word]
        rintro ⟨r,a,hr,ha⟩
        obtain ⟨u,hu⟩ := hr
        exact hd u a (hu ▸ ha)
  · exact ⟨Nat.pair 0 0,Or.inl ⟨by simp,by simpa using hs⟩⟩

noncomputable def step (A : Oracle) : ℕ → ℕ := least (Accept A) (accept_total A)

theorem step_spec (A : Oracle) (x : ℕ) : Accept A (Nat.pair x (step A x)) :=
  least_spec (Accept A) (accept_total A) x

end TuringRigidity.UniformSplit

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
open Encodable UniformOracle ArithmeticHierarchy OracleJump EncodedForcing EffectiveWitness IndexMatrix
open CodingForcing UniformProgram

def request (v : ℕ) : ℕ := encode [item (Nat.unpair v).1 0,item (Nat.unpair v).1 1,encode (left (Nat.unpair v).2)]

theorem request_primrec : Primrec request := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  exact Primrec.encode.comp (Primrec.list_cons.comp (item_primrec.comp f (Primrec.const 0))
    (Primrec.list_cons.comp (item_primrec.comp f (Primrec.const 1))
      (Primrec.list_cons.comp (Primrec.encode.comp (left_primrec.comp r)) (Primrec.const []))))

def IsCoding (A : Oracle) (v : ℕ) : Prop :=
  CodingLocation (columns A) (condition (Nat.unpair v).1) (item (Nat.unpair (Nat.unpair v).2).2 2)

theorem coding_recursive (A : Oracle) : RecursivePred A (IsCoding A) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let m := item_primrec.comp (r.comp r) (Primrec.const 2)
  have hl := recursive_primrecPred A (Primrec.nat_le.comp (Primrec.list_length.comp (left_primrec.comp f)) m)
  have hk := recursive_primrecPred A (Primrec.nat_lt.comp (f.comp m) (active_primrec.comp f))
  have hq : Nat.RecursiveIn {oracleFunction A} (oracleFunction A) := .oracle _ (Set.mem_singleton _)
  have ha : RecursivePred A (fun v => A (item (Nat.unpair (Nat.unpair v).2).2 2) = true) := by
    exact (Nat.RecursiveIn.comp hq (_root_.OAI.TuringRigidity.UniformOracle.total_primrec m)).of_eq (fun v => by
      change (Part.some (item (Nat.unpair (Nat.unpair v).2).2 2)).bind (fun input => oracleFunction A input) = _
      rw [Part.bind_some]
      cases h : A (item (Nat.unpair (Nat.unpair v).2).2 2) <;> simp [oracleFunction,h])
  unfold IsCoding
  simpa only [CodingLocation,columns,condition,Nat.pair_unpair] using recursive_and hl (recursive_and hk ha)

noncomputable def outcome (A : Oracle) (v : ℕ) : ℕ := by
  classical
  let w := UniformSplit.step A (request v)
  exact if (Nat.unpair w).1 = 1 ∧ ¬ IsCoding A (Nat.pair (Nat.unpair v).2 w)
    then Nat.pair 3 (Nat.unpair w).2 else w

def update (p w : ℕ) : ℕ := EffectiveSplitConditions.update p (retag w)

noncomputable def next (A : Oracle) (v : ℕ) : ℕ := update (Nat.unpair v).2 (outcome A v)

theorem next_extends (A : Oracle) (v : ℕ) :
    Extends (columns A) (condition (Nat.unpair v).2) (condition (next A v)) ∧
    (condition (next A v)).active = (condition (Nat.unpair v).2).active := by
  unfold next update EffectiveSplitConditions.update
  split <;> rw [condition_code]
  · exact ⟨append_extends _ _ _,rfl⟩
  · exact ⟨extends_refl _ _,rfl⟩

theorem split_coding_or_divergence {A : Oracle} {x : ℕ} {p r : Condition}
    (hn : UniformAgreement.NoDisagreement A x p) (hpr : Extends (columns A) p r)
    (m : ℕ) (hm : p.left.length ≤ m) (hmr : m < r.left.length) (b : Bool)
    (n v w : ℕ) (hvw : v ≠ w)
    (hv : v ∈ UniformRun.run A (machine (item x 0)) (machine (item x 1)) r.left n)
    (hw : w ∈ UniformRun.run A (machine (item x 0)) (machine (item x 1)) (r.left.set m b) n) :
    CodingLocation (columns A) p m ∨
      ∀ q, Extends (columns A) r q → ∀ c,
        c ∉ UniformRun.run A (machine (item x 0)) (machine (item x 2)) q.right n := by
  by_cases hc : CodingLocation (columns A) p m
  · exact Or.inl hc
  · right
    intro q hrq c hvc
    have hpq := extends_trans hpr hrq
    have hpc := CodingOnePoint.changeLeft_extends hpq m hm hc b
    have hvq := UniformRun.run_mono hrq.1 n v hv
    have hwq := UniformRun.run_mono (CodingOnePoint.set_prefix_set hrq.1 m hmr b) n w hw
    have hveq : v = c := by
      by_contra hne
      exact hn q hpq ⟨n,v,c,hne,hvq,hvc⟩
    have hweq : w = c := by
      by_contra hne
      exact hn (CodingOnePoint.changeLeft q m b) hpc ⟨n,w,c,hne,hwq,hvc⟩
    exact hvw (hveq.trans hweq.symm)

end TuringRigidity.UniformPair

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_StablePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.StablePair
open Encodable UniformOracle ArithmeticHierarchy OracleJump EncodedForcing EffectiveWitness IndexMatrix
open CodingForcing UniformProgram UniformAgreement UniformPair

def Decisive (A : Oracle) (x : ℕ) (p : Condition) : Prop :=
  Disagreement A x p ∨ ∃ i n, (i = 1 ∨ i = 2) ∧ ∀ q, Extends (columns A) p q →
    ∀ a, a ∉ UniformRun.run A (machine (item x 0)) (machine (item x i))
      (if i = 1 then q.left else q.right) n

end TuringRigidity.StablePair

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_GuardedPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GuardedPair
open Encodable UniformOracle ArithmeticHierarchy OracleJump EncodedForcing EffectiveWitness IndexMatrix
open CodingForcing UniformProgram UniformPair
noncomputable section
attribute [local instance] Classical.propDecidable

def BadCert (A : Oracle) (v : ℕ) : Prop :=
  UniformSplit.PointCert A (Nat.pair (request (Nat.unpair v).1) (Nat.unpair v).2) ∧
    ¬ IsCoding A (Nat.pair (Nat.unpair (Nat.unpair v).1).2 (Nat.pair 1 (Nat.unpair v).2))

theorem badCert_sigma (A : Oracle) : Sigma A 1 (BadCert A) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hp := (UniformSplit.pointCert_sigma A).comp
    (Primrec₂.natPair.comp (request_primrec.comp f) r)
  have hc := recursive_comp (recursive_not (coding_recursive A))
    (Primrec₂.natPair.comp (r.comp f) (Primrec₂.natPair.comp (Primrec.const 1) r))
  exact hp.and (Form.raise (n := 0) (s := true) hc)

theorem bad_decisive (A : Oracle) (x p w : ℕ)
    (hn : UniformAgreement.NoDisagreement A x (condition p))
    (hb : BadCert A (Nat.pair (Nat.pair x p) w)) :
    StablePair.Decisive A x (condition (EffectiveSplitConditions.update p (Nat.pair 2 w))) := by
  obtain ⟨hp,hnc⟩ := hb
  have hpq : left p <+: word (item w 1) := by
    simpa [UniformSplit.PointCert,UniformSplit.start,request,item,word] using hp.1
  let q := append (condition p) ((word (item w 1)).drop (left p).length)
  have hl : q.left = word (item w 1) := by
    change left p ++ (word (item w 1)).drop (left p).length = _
    rw [List.prefix_iff_eq_take] at hpq
    conv_lhs => lhs; rw [hpq]
    exact List.take_append_drop _ _
  have hpoint : (left p).length ≤ item w 2 ∧ item w 2 < (word (item w 1)).length ∧
      item w 4 ≠ item w 5 ∧
      item w 4 ∈ UniformRun.run A (machine (item x 0)) (machine (item x 1)) (word (item w 1)) (item w 0) ∧
      item w 5 ∈ UniformRun.run A (machine (item x 0)) (machine (item x 1))
        ((word (item w 1)).set (item w 2) (item w 3).bodd) (item w 0) := by
    simpa [UniformSplit.PointCert,UniformSplit.start,UniformSplit.base,UniformSplit.program,
      request,item,word] using hp.2
  have hd := split_coding_or_divergence (r := q) hn (append_extends (columns A) (condition p)
    ((word (item w 1)).drop (left p).length)) (item w 2) hpoint.1
    (by simpa [hl] using hpoint.2.1) (item w 3).bodd (item w 0) (item w 4) (item w 5)
    hpoint.2.2.1 (by simpa [hl] using hpoint.2.2.2.1) (by simpa [hl] using hpoint.2.2.2.2)
  have hnc' : ¬ CodingLocation (columns A) (condition p) (item w 2) := by
    simpa only [IsCoding,Nat.unpair_pair] using hnc
  have he : condition (EffectiveSplitConditions.update p (Nat.pair 2 w)) = q := by
    simp [EffectiveSplitConditions.update,Nat.unpair_pair,condition_code,q]
  rw [he]
  exact Or.inr ⟨2,item w 0,Or.inr rfl,by simpa using hd.resolve_left hnc'⟩

def Outcome (A : Oracle) (x p : ℕ) : Prop :=
  (¬ ∃ z, UniformSplit.SplitCert A (Nat.pair (request (Nat.pair x p)) z)) ∨
    ∃ w, UniformSplit.PointCert A (Nat.pair (request (Nat.pair x p)) w) ∧
      CodingLocation (columns A) (condition p) (item w 2)

end
end TuringRigidity.GuardedPair

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteInjuryLimits
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.FiniteInjury
open CodingForcing

def leftLimit (p : ℕ → Condition) : Oracle := fun n => (p (n+1)).left.getD n false

def rightLimit (p : ℕ → Condition) : Oracle := fun n => (p (n+1)).right.getD n false

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

noncomputable def seen (proposal : ℕ → Finset ℕ → Option ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | s+1 => reset (insert (visit (seen proposal s)) (seen proposal s)) (action proposal s)

noncomputable def scheduled (proposal : ℕ → Finset ℕ → Option ℕ) (s : ℕ) : ℕ :=
  visit (seen proposal s)

end TuringRigidity.FiniteInjurySchedule

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ConservativeExtension
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ConservativeExtension
open CommonIdeal

def Decide (A Y : Oracle) (e : OracleCode) (s : List Bool) : Prop :=
  (∃ n a, a ∈ run A e s n ∧ a ≠ bit (Y n)) ∨
  ∀ t, s <+: t → ∀ n a, a ∈ run A e t n → a = bit (Y n)

end TuringRigidity.ConservativeExtension

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
open Encodable UniformOracle ArithmeticHierarchy EncodedForcing CohenHalting EffectiveCohen

def erase (i : ℕ) (G : Oracle) : Oracle := fun m => if (Nat.unpair m).1 = i then false else G m

def Disagrees (B : Oracle) (i : ℕ) (e : OracleCode) (p : ℕ) : Prop :=
  ∃ n a, Nat.pair i n < (word p).length ∧
    a ∈ CommonIdeal.run B e (eraseWord i (word p)) n ∧
    a ≠ CommonIdeal.bit ((word p).getD (Nat.pair i n) false)

end TuringRigidity.CohenColumns

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_GuardedComputability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GuardedComputability
open Encodable UniformOracle EncodedForcing CodingForcing FiniteInjury StageRecords
noncomputable section
attribute [local instance] Classical.propDecidable

def grow (p s : ℕ) : ℕ := Nat.pair (encode (left p ++ [false]))
  (Nat.pair (encode (right p ++ [false])) (s+1))

@[simp] theorem condition_grow (p s : ℕ) :
    condition (grow p s) = atLevel (append (condition p) [false]) (s+1) := condition_code (atLevel (append (condition p) [false]) (s+1))

end
end TuringRigidity.GuardedComputability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_EffectiveFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.EffectiveFamilies
open Encodable EncodedForcing UniformOracle SetCoding

def tuples (G : Oracle) : ℕ → Oracle
  | 0 => fun _ => false
  | n+1 => mix (tuples G n) (slice G n)

end TuringRigidity.EffectiveFamilies

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_EffectivePresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.EffectivePresentation
open EncodedForcing UniformOracle ArithmeticHierarchy EffectiveFamilies
open SetCoding RelationCoding AntichainParameters
noncomputable section
attribute [local instance] Classical.propDecidable

def emptyAntichain : AntichainCode := ⟨⊥,⊥,⊥⟩

def emptyRelation (n : ℕ) : RelationCode n :=
  ⟨fun _ => ⟨⊥,emptyAntichain,emptyAntichain⟩,emptyAntichain⟩

end
end TuringRigidity.EffectivePresentation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_FixedArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.FixedArithmetic
open Encodable EncodedForcing ArithmeticHierarchy UniformOracle OracleJump
open ArithmeticModelDecoding SetCoding RelationCoding

def zero : Oracle := fun _ => false

end TuringRigidity.FixedArithmetic

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
open AntichainParameters SetCoding RelationCoding

structure ACode (I : DegreeIdeal) where
  bound : I
  left : I
  right : I

end TuringRigidity.IdealInterpretation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_EnumerationDecoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.EnumerationDecoding
open IndexPresentation IndexTuples ArithmeticHierarchy DecodingTheorem
open SetCoding RelationCoding OracleJump ArithmeticModelDecoding

structure Enumeration where
  node : ℕ → Degree
  injective : Function.Injective node
  output : ℕ → Degree
  successor : RelationCode 2
  payload : RelationCode 2
  successor_spec : ∀ a b, successor.Holds (two a b) ↔ ∃ k, a = node k ∧ b = node (k+1)
  payload_spec : ∀ a b, payload.Holds (two a b) ↔ ∃ k, a = node k ∧ b = output k

def Defined (Y : Oracle) (S P : RelationCode 2) (z n j : ℕ) : Prop :=
  ∃ t, Path Y S z n t ∧ Presented Y P (twoIndex (item t n) j)

end TuringRigidity.EnumerationDecoding

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

open Formula

def minimalInFormula (r a x : ℕ) : Formula :=
  .conj (.member x a) (allMem a (.neg (pairMem 0 (x+1) (r+1))))

def leastMinimalFormula (δ F r a x : ℕ) : Formula := .conj (minimalInFormula r a x)
  (.existsMem δ (.conj (pairMem 0 (x+1) (F+1))
    (allMem 0 (allMem (a+2) (imp (pairMem 1 0 (F+3))
      (.neg (minimalInFormula (r+3) (a+3) 0)))))))

def minimalSelectorFormula : Formula := .existsMem 1 (.existsMem 3
  (.conj (.orderedPair 2 1 0) (leastMinimalFormula 5 6 7 1 0)))

end InternalWellOrder
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_FiniteModelGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

noncomputable def finiteModelGraph (f : ℕ → ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => {ZFSet.pair (natSet 0) (f 0)}
  | n+1 => finiteModelGraph f n ∪ ({ZFSet.pair (natSet (n+1)) (f (n+1))} : ZFSet.{u})

theorem mem_finiteModelGraph (f : ℕ → ZFSet.{u}) (n : ℕ) (z : ZFSet.{u}) :
    z ∈ finiteModelGraph f n ↔ ∃ i, i ≤ n ∧ z = ZFSet.pair (natSet i) (f i) := by
  induction n with
  | zero =>
    rw [finiteModelGraph,ZFSet.mem_singleton]
    constructor
    · intro h; exact ⟨0,le_rfl,h⟩
    · rintro ⟨i,hi,h⟩
      have he : i = 0 := Nat.eq_zero_of_le_zero hi
      simpa only [he] using h
  | succ n ih =>
    rw [finiteModelGraph,ZFSet.mem_union,ZFSet.mem_singleton,ih]
    constructor
    · rintro (⟨i,hi,hz⟩|hz)
      · exact ⟨i,Nat.le_succ_of_le hi,hz⟩
      · exact ⟨n+1,le_rfl,hz⟩
    · rintro ⟨i,hi,hz⟩
      by_cases hin : i ≤ n
      · exact Or.inl ⟨i,hin,hz⟩
      · have he : i = n+1 := by omega
        exact Or.inr (he ▸ hz)

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

namespace Formula

def modelIterationTrace (o R z k n b f : ℕ) (θ : Formula) : Formula :=
  .conj (.functionGraph f k R) (.conj (.successor k n) (.conj (.empty z)
    (.conj (.pairMem z b f)
      (allMem n (allMem (o+1) (imp (.successor 0 1)
        (allMem (R+2) (allMem (R+3) (imp (.pairMem 3 1 (f+4))
          (imp (.pairMem 2 0 (f+4)) (θ.rename modelIterationVars)))))))))))

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

def modelIteration (o R Q n b y : ℕ) (θ : Formula) : Formula :=
  .existsMem o (.existsMem (o+1) (.existsMem (Q+2)
    (.conj (modelIterationTrace (o+3) (R+3) 1 2 (n+3) (b+3) 0 (θ.rename modelIterationOuterVars))
      (.pairMem (n+3) (y+3) 0))))

end Formula
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalFunctionOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

noncomputable def orbitGraph (a : ℕ → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun n => ZFSet.pair (natSet n) (a n))

namespace Formula

def orbitMember (o d Q b F z : ℕ) : Formula := .existsMem o (.existsMem (d+1)
  (.conj (.orderedPair (z+2) 1 0)
    (modelIteration (o+2) (d+2) (Q+2) 1 (b+2) 0 (.pairMem 1 0 (F+5)))))

end Formula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalSerialSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationHull
universe u
namespace Formula

def predecessorSet (d r x a : ℕ) : Formula := .conj (.subset a d)
  (allMem d (iff (.member 0 (a+1)) (.pairMem 0 (x+1) (r+1))))

def serialSelector (d r q s z : ℕ) : Formula := .existsMem d (.existsMem (d+1)
  (.conj (.orderedPair (z+2) 1 0) (.existsMem (q+2)
    (.conj (predecessorSet (d+3) (r+3) 2 0) (.pairMem 0 1 (s+3))))))
end Formula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteNaturalGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

noncomputable def finiteNaturalGraph (f : ℕ → ℕ) : ℕ → ZFSet.{u}
  | 0 => {ZFSet.pair (natSet 0) (natSet (f 0))}
  | n+1 => finiteNaturalGraph f n ∪ ({ZFSet.pair (natSet (n+1)) (natSet (f (n+1)))} : ZFSet.{u})

theorem mem_finiteNaturalGraph (f : ℕ → ℕ) (n : ℕ) (z : ZFSet.{u}) :
    z ∈ finiteNaturalGraph f n ↔ ∃ i, i ≤ n ∧ z = ZFSet.pair (natSet i) (natSet (f i)) := by
  induction n with
  | zero =>
    rw [finiteNaturalGraph,ZFSet.mem_singleton]
    constructor
    · intro h; exact ⟨0,le_rfl,h⟩
    · rintro ⟨i,hi,h⟩
      have he : i = 0 := Nat.eq_zero_of_le_zero hi
      simpa only [he] using h
  | succ n ih =>
    rw [finiteNaturalGraph,ZFSet.mem_union,ZFSet.mem_singleton,ih]
    constructor
    · rintro (⟨i,hi,hz⟩|hz)
      · exact ⟨i,Nat.le_succ_of_le hi,hz⟩
      · exact ⟨n+1,le_rfl,hz⟩
    · rintro ⟨i,hi,hz⟩
      by_cases hin : i ≤ n
      · exact Or.inl ⟨i,hin,hz⟩
      · have he : i = n+1 := by omega
        exact Or.inr (he ▸ hz)

theorem finiteNaturalGraph_pair (f : ℕ → ℕ) (n i : ℕ) (y : ZFSet.{u}) :
    ZFSet.pair (natSet i) y ∈ finiteNaturalGraph f n ↔ i ≤ n ∧ y = natSet (f i) := by
  rw [mem_finiteNaturalGraph]
  constructor
  · rintro ⟨j,hj,he⟩
    obtain ⟨hij,hy⟩ := ZFSet.pair_inj.mp he
    have heq := natSet_injective hij
    subst j
    exact ⟨hj,hy⟩
  · rintro ⟨hi,rfl⟩
    exact ⟨i,hi,rfl⟩

end TuringRigidity.BoundedSetTheory

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

namespace Formula
def additionTrace (o z k n x f : ℕ) : Formula :=
  .conj (.functionGraph f k o) (.conj (.successor k n) (.conj (.empty z)
    (.conj (.pairMem z x f)
      (allMem n (allMem (o+1) (imp (.successor 0 1)
        (allMem (o+2) (allMem (o+3) (imp (.pairMem 3 1 (f+4))
          (imp (.pairMem 2 0 (f+4)) (.successor 0 1)))))))))))

theorem eval_additionTrace (o z k n x f : ℕ) (e : ℕ → ZFSet.{u}) :
    (additionTrace o z k n x f).Eval e ↔ AdditionTrace (e o) (e z) (e k) (e n) (e x) (e f) := by
  simp only [additionTrace,AdditionTrace,TransitiveNameModel.FunctionGraph,Formula.Eval,eval_functionGraph,eval_successor,
    eval_empty,eval_pairMem,eval_allMem,eval_imp,cons_zero,cons_succ]

def addition (o Q x n y : ℕ) : Formula := .existsMem o (.existsMem (o+1) (.existsMem (Q+2)
  (.conj (additionTrace (o+3) 1 2 (n+3) (x+3) 0) (.pairMem (n+3) (y+3) 0))))

theorem eval_addition (o Q x n y : ℕ) (e : ℕ → ZFSet.{u}) :
    (addition o Q x n y).Eval e ↔ ∃ k ∈ e o, ∃ z ∈ e o, ∃ f ∈ e Q,
      AdditionTrace (e o) z k (e n) (e x) f ∧ ZFSet.pair (e n) (e y) ∈ f := by
  simp only [addition,Formula.Eval,eval_additionTrace,eval_pairMem,cons_zero,cons_succ]
end Formula

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

namespace Formula

def iterationTrace (o z k n b f : ℕ) (θ : Formula) : Formula :=
  .conj (.functionGraph f k o) (.conj (.successor k n) (.conj (.empty z)
    (.conj (.pairMem z b f)
      (allMem n (allMem (o+1) (imp (.successor 0 1)
        (allMem (o+2) (allMem (o+3) (imp (.pairMem 3 1 (f+4))
          (imp (.pairMem 2 0 (f+4)) (θ.rename iterationVars)))))))))))

theorem eval_iterationTrace (o z k n b f : ℕ) (θ : Formula) (e : ℕ → ZFSet.{u}) :
    (iterationTrace o z k n b f θ).Eval e ↔ IterationTrace (e o) (e z) (e k) (e n) (e b) (e f)
      (fun i v w => θ.Eval (cons w (cons v (cons i e)))) := by
  simp only [iterationTrace,IterationTrace,TransitiveNameModel.FunctionGraph,Formula.Eval,
    eval_functionGraph,eval_successor,eval_empty,eval_pairMem,eval_allMem,eval_imp,eval_rename,cons_zero,cons_succ]
  have eq (i j v w : ZFSet.{u}) :
      (fun n => cons w (cons v (cons j (cons i e))) (iterationVars n)) = cons w (cons v (cons i e)) := by
    funext n
    rcases n with _|n; rfl
    rcases n with _|n; rfl
    rcases n with _|n <;> rfl
  simp only [eq]
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

def iteration (o Q n b y : ℕ) (θ : Formula) : Formula :=
  .existsMem o (.existsMem (o+1) (.existsMem (Q+2)
    (.conj (iterationTrace (o+3) 1 2 (n+3) (b+3) 0 (θ.rename iterationOuterVars))
      (.pairMem (n+3) (y+3) 0))))

theorem eval_iteration (o Q n b y : ℕ) (θ : Formula) (e : ℕ → ZFSet.{u}) :
    (iteration o Q n b y θ).Eval e ↔ ∃ k ∈ e o, ∃ z ∈ e o, ∃ f ∈ e Q,
      IterationTrace (e o) z k (e n) (e b) f
        (fun i v w => θ.Eval (cons w (cons v (cons i e)))) ∧ ZFSet.pair (e n) (e y) ∈ f := by
  simp only [iteration,Formula.Eval,eval_iterationTrace,eval_pairMem,eval_rename,cons_zero,cons_succ]
  have eq (k z f i v w : ZFSet.{u}) :
      (fun n => cons w (cons v (cons i (cons f (cons z (cons k e))))) (iterationOuterVars n)) =
        cons w (cons v (cons i e)) := by
    funext n
    rcases n with _|n; rfl
    rcases n with _|n; rfl
    rcases n with _|n <;> rfl
  simp only [eq]

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

namespace Formula
def multiplication (o Q x n y : ℕ) : Formula := .existsMem o
  (.conj (.empty 0) (iteration (o+1) (Q+1) (n+1) 0 (y+1)
    (addition (o+4) (Q+4) 1 (x+4) 0)))

end Formula
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

namespace NaturalTerm

def operation (m : Bool) (o Q a b y : ℕ) : Formula :=
  if m then .multiplication o Q a b y else .addition o Q a b y

def graph (o Q y : ℕ) (v : ℕ → ℕ) : NaturalTerm → Formula
  | .var i => .equal y (v i)
  | .binary m a b => .existsMem o (.existsMem (o+1)
      (.conj (graph (o+2) (Q+2) 1 (fun i => v i+2) a)
        (.conj (graph (o+2) (Q+2) 0 (fun i => v i+2) b) (operation m (o+2) (Q+2) 1 0 (y+2)))))

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

def naturalPair (o Q x n y : ℕ) : Formula := .disj
  (.conj (.member x n) (pairLeftTerm.graph o Q y (pairVars x n)))
  (.conj (.neg (.member x n)) (pairRightTerm.graph o Q y (pairVars x n)))

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

def DefinesNatural (φ : Formula) (f : ℕ → ℕ) : Prop :=
  ∀ e : ℕ → ZFSet.{u}, e 2 = ZFSet.omega →
    (∀ g : ℕ → ℕ, ∀ k, finiteNaturalGraph g k ∈ e 3) → ∀ n, e 1 = natSet n →
      (φ.Eval e ↔ e 0 = natSet (f n))

namespace Formula

def unary (φ : Formula) (o Q x y : ℕ) : Formula := φ.rename (unaryVars o Q x y)

theorem unary_spec {φ : Formula} {f : ℕ → ℕ} (hφ : DefinesNatural.{u} φ f)
    (o Q x y : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ g : ℕ → ℕ, ∀ k, finiteNaturalGraph g k ∈ e Q) (n : ℕ) (hx : e x = natSet n) :
    (unary φ o Q x y).Eval e ↔ e y = natSet (f n) := by
  rw [unary,eval_rename]
  exact hφ (fun i => e (unaryVars o Q x y i)) ho hQ n hx

def numericComposition (φ ψ : Formula) : Formula := .existsMem 2
  (.conj (unary ψ 3 4 2 0) (unary φ 3 4 0 1))

def numericPair (φ ψ : Formula) : Formula := .existsMem 2 (.existsMem 3
  (.conj (unary φ 4 5 3 1) (.conj (unary ψ 4 5 3 0) (naturalPair 4 5 1 0 2))))

def pairedUnary (φ : Formula) (o Q a b y : ℕ) : Formula := .existsMem o
  (.conj (naturalPair (o+1) (Q+1) (a+1) (b+1) 0) (unary φ (o+1) (Q+1) 0 (y+1)))

end Formula

theorem definesNatural_zero : DefinesNatural.{u} (.empty 0) (fun _ => 0) := by
  intro e _ _ n _
  exact Formula.eval_empty 0 e

theorem definesNatural_succ : DefinesNatural.{u} (.successor 0 1) Nat.succ := by
  intro e _ _ n hn
  rw [Formula.eval_successor,hn]
  rfl

theorem DefinesNatural.comp {φ ψ : Formula} {f g : ℕ → ℕ}
    (hf : DefinesNatural.{u} φ f) (hg : DefinesNatural.{u} ψ g) :
    DefinesNatural.{u} (Formula.numericComposition φ ψ) (fun n => f (g n)) := by
  intro e ho hQ n hn
  have hv (w : ZFSet.{u}) := Formula.unary_spec hg 3 4 2 0 (cons w e) ho hQ n hn
  have hu := Formula.unary_spec hf 3 4 0 1 (cons (natSet (g n)) e) ho hQ (g n) rfl
  simp only [Formula.numericComposition,Formula.Eval]
  constructor
  · rintro ⟨w,_,hw,h⟩
    obtain rfl := (hv w).mp hw
    exact hu.mp h
  · intro h
    refine ⟨natSet (g n),?_,(hv _).mpr rfl,hu.mpr h⟩
    rw [ho]; exact (mem_omega _).mpr ⟨g n,rfl⟩

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NaturalProjectionFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u
namespace Formula

def naturalProjection (right : Bool) : Formula := .existsMem 2 (.existsMem 3
  (.conj (naturalPair 4 5 1 0 3) (.equal 2 (if right then 0 else 1))))

end Formula
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NaturalPrimitiveRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u
namespace Formula

def primitiveStep (ψ : Formula) : Formula := .existsMem 8
  (.conj (naturalPair 9 10 3 2 0) (pairedUnary ψ 9 10 6 0 1))

def primitiveRecursion (φ ψ : Formula) : Formula := .existsMem 2 (.existsMem 3 (.existsMem 4
  (.conj (naturalPair 5 6 2 1 4) (.conj (unary φ 5 6 2 0)
    (iteration 5 6 1 0 3 (primitiveStep ψ))))))

end Formula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_PrimitivePredicateFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u

def DefinesPredicate (φ : Formula) (P : ℕ → Prop) : Prop :=
  ∀ e : ℕ → ZFSet.{u}, e 1 = ZFSet.omega →
    (∀ g : ℕ → ℕ, ∀ k, finiteNaturalGraph g k ∈ e 2) → ∀ n, e 0 = natSet n →
      (φ.Eval e ↔ P n)

def Formula.numericalPredicate (φ : Formula) : Formula := .existsMem 1
  (.conj (unary φ 2 3 1 0) (.neg (.empty 0)))

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

def arithmeticExists (φ : Formula) : Formula := .existsMem 1 (.existsMem 2
  (.conj (naturalPair 3 4 2 1 0) (φ.rename (arithmeticVars 2))))

def arithmeticComp (φ ψ : Formula) : Formula := .existsMem 1
  (.conj (unary ψ 2 3 1 0) (φ.rename (arithmeticVars 1)))
end Formula

end TuringRigidity.BoundedSetTheory

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

noncomputable def arithmeticReal (P : Predicate) (O : Oracles) : Oracle := fun n => by
  classical
  exact decide (P O n)

theorem arithmeticReal_true (P : Predicate) (O : Oracles) (n : ℕ) :
    arithmeticReal P O n = true ↔ P O n := by
  classical
  simp only [arithmeticReal,decide_eq_true_eq]

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

def oracleParameters (φ : Formula) (o Q n : ℕ) (r : ℕ → ℕ) : Formula :=
  φ.rename (oracleParameterVars o Q n r)

def twoOracles (φ : Formula) (o Q n x y : ℕ) : Formula :=
  oracleParameters φ o Q n (fun i => if i = 0 then x else y)

end Formula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_DegreeSetFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u

namespace Formula
def degreeSet (φ : Formula) (o Q z R A D : ℕ) : Formula :=
  .conj (.subset D R) (allMem R (iff (.member 0 (D+1)) (twoOracles φ (o+1) (Q+1) (z+1) 0 (A+1))))

end Formula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalNaturalRelationReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse
universe u

noncomputable def naturalRelationReal (G : ZFSet.{u}) : Oracle := fun v => by
  classical
  exact decide (ZFSet.pair (natSet (Nat.unpair v).1) (natSet (Nat.unpair v).2) ∈ G)

namespace Formula
def naturalRelationBit (o Q G v : ℕ) : Formula := .existsMem o (.existsMem (o+1)
  (.conj (naturalPair (o+2) (Q+2) 1 0 (v+2)) (.pairMem 1 0 (G+2))))

end Formula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelDegreeUniverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

namespace Formula
def degreeUniverseMember (φ : Formula) (o Q z R D : ℕ) : Formula :=
  .existsMem R (degreeSet φ (o+1) (Q+1) (z+1) (R+1) 0 (D+1))

end Formula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelDegreeOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel UniformArithmetic
universe u

namespace Formula
def degreeLE (φ : Formula) (o Q z D E : ℕ) : Formula :=
  .existsMem D (.existsMem (E+1) (twoOracles φ (o+2) (Q+2) (z+2) 1 0))

def degreeOrderMember (φ : Formula) (o Q z U p : ℕ) : Formula :=
  .existsMem U (.existsMem (U+1) (.conj (.orderedPair (p+2) 1 0)
    (degreeLE φ (o+2) (Q+2) (z+2) 1 0)))

end Formula

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

def Prefix (A p : ZFSet.{u}) : Prop :=
  ∃ n : ℕ, TransitiveNameModel.FunctionGraph (natSet n) A p

theorem prefix_subset {A p : ZFSet.{u}} (hp : Prefix A p) : p ⊆ ZFSet.prod ZFSet.omega A := by
  obtain ⟨n,hp⟩ := hp
  intro z hz
  obtain ⟨i,hi,x,hx,rfl⟩ := hp.1 z hz
  obtain ⟨k,_,rfl⟩ := (mem_natSet n i).mp hi
  exact ZFSet.mem_prod.mpr ⟨natSet k,(mem_omega _).mpr ⟨k,rfl⟩,x,hx,rfl⟩

theorem prefix_empty (A : ZFSet.{u}) : Prefix A ∅ :=
  ⟨0,fun _ h => False.elim (ZFSet.notMem_empty _ h),fun _ h => False.elim (ZFSet.notMem_empty _ h)⟩

noncomputable def append (p : ZFSet.{u}) (n : ℕ) (x : ZFSet.{u}) : ZFSet.{u} :=
  p ∪ ({ZFSet.pair (natSet n) x} : ZFSet.{u})

def prefixFormula (o A p : ℕ) : Formula := .existsMem o (.functionGraph (p+1) 0 (A+1))

theorem eval_prefixFormula (o A p : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega) :
    (prefixFormula o A p).Eval e ↔ Prefix (e A) (e p) := by
  simp only [prefixFormula,Formula.Eval,Formula.eval_functionGraph,cons_zero,cons_succ]
  rw [ho]
  exact ⟨fun ⟨n,hn,h⟩ => by obtain ⟨k,rfl⟩ := (mem_omega n).mp hn; exact ⟨k,h⟩,
    fun ⟨n,h⟩ => ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,h⟩⟩

attribute [local instance] order

attribute [local instance] collapsePreorder

end TuringRigidity.BoundedSetTheory.InternalCollapse

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
open TransitiveNameModel CountableForcing
universe u
attribute [local instance] order collapsePreorder

noncomputable def definedAt (c A : ZFSet.{u}) (n : ℕ) : ZFSet.{u} :=
  ZFSet.sep (fun p => ∃ x ∈ A, ZFSet.pair (natSet n) x ∈ p) c

end TuringRigidity.BoundedSetTheory.InternalCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCollapseCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalCollapse
open TransitiveNameModel CountableForcing
universe u
attribute [local instance] order collapsePreorder

noncomputable def unionGraph {c : ZFSet.{u}} (G : GenericFilter (Conditions c)) : ZFSet.{u} :=
  ZFSet.sUnion (genericFilterSet c G.carrier)

end TuringRigidity.BoundedSetTheory.InternalCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CheckedForcingRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CheckedForcingRelation
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AtomicForcing
variable {c : ZFSet.{0}} [Preorder (Conditions c)] [Top (Conditions c)]

noncomputable def relation (a : ZFSet.{0}) (τ : Name (Conditions c)) : ZFSet.{0} :=
  (ZFSet.prod a c).sep (fun z => ∃ x ∈ a, ∃ p : Conditions c,
    z = ZFSet.pair x (label c p) ∧ MemForces (Name.check x) τ p)

end TuringRigidity.CheckedForcingRelation

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

noncomputable def bitSet (b : Bool) : ZFSet.{0} := natSet (if b then 1 else 0)

noncomputable def alphabet : ZFSet.{0} := {bitSet false, bitSet true}

theorem bitSet_injective : Function.Injective bitSet := by
  intro a b h
  have h' := natSet_injective h
  cases a <;> cases b <;> simp_all [bitSet]

theorem mem_alphabet (x : ZFSet.{0}) : x ∈ alphabet ↔ ∃ b : Bool, x = bitSet b := by
  simp only [alphabet,ZFSet.mem_insert_iff,ZFSet.mem_singleton]
  constructor
  · rintro (h|h)
    exact ⟨false,h⟩
    exact ⟨true,h⟩
  · rintro ⟨b,rfl⟩; cases b <;> simp

noncomputable def wordCode (s : List Bool) : ZFSet.{0} :=
  ZFSet.range (fun i : Fin s.length => ZFSet.pair (natSet i.val) (bitSet s[i.val]))

theorem mem_wordCode (s : List Bool) (z : ZFSet.{0}) :
    z ∈ wordCode s ↔ ∃ i : Fin s.length, z = ZFSet.pair (natSet i.val) (bitSet s[i.val]) := by
  simp only [wordCode,ZFSet.mem_range,eq_comm]

theorem pair_mem_wordCode (s : List Bool) (n : ℕ) (b : Bool) :
    ZFSet.pair (natSet n) (bitSet b) ∈ wordCode s ↔
      ∃ h : n < s.length, b = s[n] := by
  rw [mem_wordCode]
  constructor
  · rintro ⟨i,he⟩
    obtain ⟨hn,hb⟩ := ZFSet.pair_inj.mp he
    have hn' := natSet_injective hn
    exact ⟨hn' ▸ i.isLt,by simpa only [←hn'] using bitSet_injective hb⟩
  · rintro ⟨hn,rfl⟩; exact ⟨⟨n,hn⟩,rfl⟩

noncomputable def conditions : ZFSet.{0} :=
  ZFSet.sep (Prefix alphabet) (ZFSet.powerset (ZFSet.prod ZFSet.omega alphabet))

theorem mem_conditions (p : ZFSet.{0}) : p ∈ conditions ↔ Prefix alphabet p := by
  rw [conditions,ZFSet.mem_sep]
  exact ⟨And.right,fun h => ⟨ZFSet.mem_powerset.mpr (prefix_subset h),h⟩⟩

attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleTupleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

noncomputable def tupleGraph {n : ℕ} (v : Fin n → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun i : Fin n => ZFSet.pair (natSet i.val) (v i))

theorem tupleGraph_pair {n : ℕ} (v : Fin n → ZFSet.{u}) (i : Fin n) (x : ZFSet.{u}) :
    ZFSet.pair (natSet i.val) x ∈ tupleGraph v ↔ x = v i := by
  rw [tupleGraph,ZFSet.mem_range]
  constructor
  · rintro ⟨j,hj⟩
    obtain ⟨hji,hx⟩ := ZFSet.pair_inj.mp hj
    have he : j = i := Fin.ext (natSet_injective hji)
    subst j; exact hx.symm
  · rintro rfl; exact ⟨i,rfl⟩

end TuringRigidity.RelativeConstructible

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

noncomputable def finiteSubsets (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun t : Σ n : ℕ, Fin n → Conditions A =>
    ZFSet.range (fun i => label A (t.2 i)))

def rangeFormula (o A x g : ℕ) : Formula :=
  .conj (.subset x A) (.allMem A
    (.iff (.member 0 (x+1)) (.existsMem (o+1) (.pairMem 0 1 (g+2)))))

end TuringRigidity.InternalFiniteSubsets

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenConditionCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenConditionCode
open Set TransitiveNameModel BoundedSetTheory InternalFiniteSubsets
open CohenSymmetry CohenCoordinates
open InternalCohen (bitSet alphabet bitSet_injective mem_alphabet)

noncomputable def graph (A : ZFSet.{0}) (p : Condition (Conditions A)) : ZFSet.{0} :=
  ZFSet.range (fun i : ↥(support p) =>
    ZFSet.pair (label A i.val) (bitSet ((p.val i.val).getD false)))

theorem pair_mem_graph (A : ZFSet.{0}) (p : Condition (Conditions A))
    (i : Conditions A) (b : Bool) :
    ZFSet.pair (label A i) (bitSet b) ∈ graph A p ↔ p.val i = some b := by
  classical
  rw [graph,ZFSet.mem_range]
  constructor
  · rintro ⟨j,hj⟩
    obtain ⟨he,hb⟩ := ZFSet.pair_inj.mp hj
    have hji := label_injective A he
    have hn := (mem_support p j.val).mp j.property
    have hv : p.val j.val = some ((p.val j.val).getD false) := by
      cases h : p.val j.val with
      | none => exact False.elim (hn h)
      | some c => rfl
    rw [bitSet_injective hb,hji] at hv
    exact hv
  · intro hi
    refine ⟨⟨i,(mem_support p i).mpr (by simp [hi])⟩,?_⟩
    simp [hi]

theorem mem_graph (A : ZFSet.{0}) (p : Condition (Conditions A)) (z : ZFSet.{0}) :
    z ∈ graph A p ↔ ∃ i b, p.val i = some b ∧ z = ZFSet.pair (label A i) (bitSet b) := by
  constructor
  · intro hz
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz
    exact ⟨i.val,_,(pair_mem_graph A p _ _).mp (ZFSet.mem_range_self i),rfl⟩
  · rintro ⟨i,b,hi,rfl⟩; exact (pair_mem_graph A p i b).mpr hi

theorem graph_subset_iff (A : ZFSet.{0}) (p q : Condition (Conditions A)) :
    graph A q ⊆ graph A p ↔ p ≤ q := by
  constructor
  · intro h i b hb; exact (pair_mem_graph A p i b).mp (h ((pair_mem_graph A q i b).mpr hb))
  · intro h z hz
    obtain ⟨i,b,hi,rfl⟩ := (mem_graph A q z).mp hz
    exact (pair_mem_graph A p i b).mpr (h i b hi)

theorem graph_injective (A : ZFSet.{0}) : Function.Injective (graph A) := by
  intro p q h
  apply le_antisymm
  · exact (graph_subset_iff A p q).mp (by rw [h])
  · exact (graph_subset_iff A q p).mp (by rw [h])

def SingleValued (A p : ZFSet.{0}) : Prop :=
  ∀ x ∈ A, ∀ b ∈ alphabet, ∀ c ∈ alphabet,
    ZFSet.pair x b ∈ p → ZFSet.pair x c ∈ p → b = c

def IsCondition (A p : ZFSet.{0}) : Prop :=
  p ∈ finiteSubsets (ZFSet.prod A alphabet) ∧ SingleValued A p

end TuringRigidity.CohenConditionCode

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

def singleValuedFormula (A B p : ℕ) : Formula :=
  .allMem A (.allMem (B+1) (.allMem (B+2)
    (.imp (.pairMem 2 1 (p+3)) (.imp (.pairMem 2 0 (p+3)) (.equal 1 0)))))

noncomputable def conditions (A : ZFSet.{0}) : ZFSet.{0} :=
  (finiteSubsets (ZFSet.prod A alphabet)).sep (SingleValued A)

theorem mem_conditions (A p : ZFSet.{0}) : p ∈ conditions A ↔ IsCondition A p :=
  ZFSet.mem_sep

end TuringRigidity.CohenGroundPoset

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenGroundGeneric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenGroundGeneric
open Set TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open CohenSymmetry CohenConditionCode CohenGroundPoset
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def codeSet (A : ZFSet.{0}) (E : Set (Condition (Conditions A))) : ZFSet.{0} :=
  ZFSet.range (fun p : E => graph A p.val)

end TuringRigidity.CohenGroundGeneric

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
open Set TransitiveNameModel BoundedSetTheory InternalFiniteSubsets
open RelativeConstructible CohenSymmetry CohenCoordinates CohenConditionCode

def smallFormula (ω B C n p : ℕ) : Formula :=
  .existsMem n (.existsMem (C+1) (.conj (.functionGraph 0 1 (B+2))
    (rangeFormula (ω+2) (B+2) (p+2) 0)))

noncomputable def levels (A : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod ZFSet.omega (CohenGroundPoset.conditions A)).sep
    (fun z => ∃ n p, z = ZFSet.pair (natSet n) p ∧ Small n p)

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
open Set TransitiveNameModel BoundedSetTheory InternalFiniteSubsets
open CohenSymmetry CohenCoordinates CohenConditionCode CohenGroundPoset
open CohenGroundGeneric CohenChainCondition

def compFormula (c p q : ℕ) : Formula :=
  .existsMem c (.conj (.subset (p+1) 0) (.subset (q+1) 0))

def antiFormula (c E : ℕ) : Formula := .allMem E (.allMem (E+1)
  (.imp (.neg (.equal 1 0)) (.neg (compFormula (c+2) 1 0))))

noncomputable def stages (c U : ZFSet.{0}) : ZFSet.{0} :=
  (finiteSubsets U).sep (Anti c)

end TuringRigidity.CohenAntichainStages

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
open CohenGroundPoset CohenConditionCode CohenSizeLevels

def stepFormula (ω s c U L x y : ℕ) : Formula :=
  .existsMem ω (.existsMem (s+1) (.existsMem (ω+2) (.existsMem (s+3)
    (.conj (.orderedPair (x+4) 3 2) (.conj (.orderedPair (y+4) 1 0)
      (.conj (.successor 1 3) (.conj (.subset 2 0)
        (.allMem (U+4) (.imp (.pairMem 4 0 (L+5))
          (.existsMem 1 (compFormula (c+6) 1 0)))))))))))

end TuringRigidity.CohenAntichainSequence

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
open TransitiveNameModel BoundedSetTheory CohenAntichainStages CohenGroundPoset
open InternalRelationSelection

def selectedFormula (c U E : ℕ) : Formula := .conj (.subset E U)
  (.conj (antiFormula c E)
    (.allMem U (.existsMem (E+1) (compFormula (c+2) 1 0))))

end TuringRigidity.CohenAntichainSelector

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenGenericUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenGenericUnion
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open CohenSymmetry CohenConditionCode CohenGroundPoset CohenGroundGeneric
open InternalCohen (alphabet mem_alphabet bitSet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def definedAt (A x : ZFSet.{0}) : ZFSet.{0} :=
  (conditions A).sep (fun p => ∃ b ∈ alphabet, ZFSet.pair x b ∈ p)

end TuringRigidity.CohenGenericUnion

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenInternalSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenInternalSupport
open Set TransitiveNameModel BoundedSetTheory InternalFiniteSubsets
open CohenGroundPoset CohenConditionCode CohenSymmetry CohenCoordinates InternalCohen

noncomputable def supportSet (A p : ZFSet.{0}) : ZFSet.{0} :=
  A.sep (fun x => ∃ b ∈ alphabet, ZFSet.pair x b ∈ p)

def supportFormula (A B p S : ℕ) : Formula := .conj (.subset S A)
  (.allMem A (.iff (.member 0 (S+1)) (.existsMem (B+1) (.pairMem 1 0 (p+2)))))

noncomputable def used (A E : ZFSet.{0}) : ZFSet.{0} :=
  A.sep (fun x => ∃ p ∈ E, x ∈ supportSet A p)

end TuringRigidity.CohenInternalSupport

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenColumnRealName
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenColumnRealName
open TransitiveNameModel BoundedSetTheory InternalCollapse CountableForcing RecursiveNames
attribute [local instance] InternalCollapse.order 
open InternalCohen (bitSet)

def realNameFormula : BoundedSetTheory.Formula :=
  .existsMem 1 (.existsMem 3 (.existsMem 6 (.existsMem 9
    (.conj (.pairMem 2 1 7) (.conj (.orderedPair 0 11 2)
      (.conj (.pairMem 0 9 3) (.orderedPair 4 1 3)))))))

end TuringRigidity.CohenColumnRealName

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenProductFilters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenProductFilters
open Set CountableForcing CohenSymmetry CohenCoordinates
universe u v
variable {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]

def first (K : GenericFilter (P × Q)) : GenericFilter P where
  carrier := {p | ∃ q, (p,q) ∈ K.carrier}
  nonempty := by obtain ⟨p,hp⟩ := K.nonempty; exact ⟨p.1,p.2,hp⟩
  upper := by rintro p q hpq ⟨r,hr⟩; exact ⟨r,K.upper (p := (p,r)) (q := (q,r)) ⟨hpq,le_rfl⟩ hr⟩
  directed := by
    rintro p q ⟨r,hr⟩ ⟨s,hs⟩
    obtain ⟨t,ht,htp,htq⟩ := K.directed hr hs
    exact ⟨t.1,⟨t.2,ht⟩,htp.1,htq.1⟩

end TuringRigidity.CohenProductFilters

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenRestriction
open TransitiveNameModel BoundedSetTheory InternalFiniteSubsets CohenConditionCode CohenGroundPoset
open InternalCohen (alphabet)

noncomputable def restrict (B p : ZFSet.{0}) : ZFSet.{0} :=
  p.sep (fun z => ∃ x ∈ B, ∃ b ∈ alphabet, z = ZFSet.pair x b)

noncomputable def restrictionGraph (A B : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod (conditions A) (conditions B)).sep (fun z =>
    ∃ p ∈ conditions A, ∃ q ∈ conditions B, z = ZFSet.pair p q ∧ q = restrict B p)

end TuringRigidity.InternalCohenRestriction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenFactorRequirement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenFactorRequirement
open TransitiveNameModel BoundedSetTheory CohenGroundPoset
open InternalCohenRestriction
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def requirement (A B R : ZFSet.{0}) : ZFSet.{0} :=
  (conditions A).sep (fun p =>
    ∃ b ∈ conditions B, ZFSet.pair p b ∈ restrictionGraph A B ∧
    ∃ d ∈ conditions (A \ B), ZFSet.pair p d ∈ restrictionGraph A (A \ B) ∧
    ∃ r ∈ conditions (A \ B), r ⊆ d ∧
    ∃ a ∈ conditions B, a ⊆ b ∧ ZFSet.pair r a ∈ R)

end TuringRigidity.CohenFactorRequirement

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenBitFlip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenBitFlip
open TransitiveNameModel BoundedSetTheory CohenGroundPoset CohenConditionCode CohenSymmetry
open InternalCohen (alphabet bitSet mem_alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def mask (A B : ZFSet.{0}) (i : Conditions A) : Bool :=
  @decide (label A i ∈ B) (Classical.propDecidable _)

end TuringRigidity.InternalCohenBitFlip

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
open TransitiveNameModel RecursiveNames RelationCollapse
universe u

def activeFormula : Formula := .existsMem 1 (.existsMem 2
  (.conj (.orderedPair 2 1 0) (.existsMem 4 (.pairMem 2 0 1))))

end TuringRigidity.BoundedSetTheory.InternalNameEvaluation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_TaggedProductConditions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TaggedProductConditions
open TransitiveNameModel BoundedSetTheory
attribute [local instance] InternalCollapse.order

noncomputable def code (p s : ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.prod {natSet 0} p ∪ ZFSet.prod {natSet 1} s

theorem mem_code (p s z : ZFSet.{0}) : z ∈ code p s ↔
    (∃ x ∈ p, z = ZFSet.pair (natSet 0) x) ∨
    (∃ x ∈ s, z = ZFSet.pair (natSet 1) x) := by
  simp only [code,ZFSet.mem_union,ZFSet.mem_prod,ZFSet.mem_singleton]
  aesop

theorem left_mem (p s x : ZFSet.{0}) :
    ZFSet.pair (natSet 0) x ∈ code p s ↔ x ∈ p := by
  rw [mem_code]
  simp only [ZFSet.pair_inj,natSet_injective.eq_iff]
  simp

theorem right_mem (p s x : ZFSet.{0}) :
    ZFSet.pair (natSet 1) x ∈ code p s ↔ x ∈ s := by
  rw [mem_code]
  simp only [ZFSet.pair_inj,natSet_injective.eq_iff]
  simp

theorem code_subset (p s p' s' : ZFSet.{0}) :
    code p s ⊆ code p' s' ↔ p ⊆ p' ∧ s ⊆ s' := by
  constructor
  · intro h
    exact ⟨fun x hx => (left_mem p' s' x).mp (h ((left_mem p s x).mpr hx)),
      fun x hx => (right_mem p' s' x).mp (h ((right_mem p s x).mpr hx))⟩
  · rintro ⟨hp,hs⟩ z hz
    rcases (mem_code p s z).mp hz with ⟨x,hx,rfl⟩|⟨x,hx,rfl⟩
    · exact (left_mem p' s' x).mpr (hp hx)
    · exact (right_mem p' s' x).mpr (hs hx)

theorem code_injective (p s p' s' : ZFSet.{0}) :
    code p s = code p' s' ↔ p = p' ∧ s = s' := by
  constructor
  · intro h
    have h₁ := (code_subset p s p' s').mp (fun _ hx => h ▸ hx)
    have h₂ := (code_subset p' s' p s).mp (fun _ hx => h.symm ▸ hx)
    exact ⟨ZFSet.ext (fun x => ⟨fun hx => h₁.1 hx,fun hx => h₂.1 hx⟩),
      ZFSet.ext (fun x => ⟨fun hx => h₁.2 hx,fun hx => h₂.2 hx⟩)⟩
  · rintro ⟨rfl,rfl⟩; rfl

end TuringRigidity.TaggedProductConditions

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
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalGeneratedAlgebra InternalBooleanProjection InternalBooleanGeneric InternalBooleanDense
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

@[instance_reducible]
noncomputable def codeOrder (A : ZFSet.{0}) : PartialOrder (Conditions (positive A)) where
  le p q := label (positive A) p ⊆ label (positive A) q
  lt p q := label (positive A) p ⊆ label (positive A) q ∧ ¬ label (positive A) q ⊆ label (positive A) p
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_refl _ := fun _ h => h
  le_trans _ _ _ hpq hqr := fun _ h => hqr (hpq h)
  le_antisymm _ _ hpq hqp := label_injective _ (ZFSet.ext (fun _ => ⟨fun h => hpq h,fun h => hqp h⟩))

@[instance_reducible]
noncomputable def codePreorder (algebraSet : ZFSet.{0}) :
    Preorder (Conditions (positive algebraSet)) :=
  (codeOrder algebraSet).toPreorder

attribute [local instance] codeOrder codePreorder

end TuringRigidity.InternalProjectedGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_CountedRegularBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CountedRegularBasis
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalBooleanDense

def basicFormula (B p U : ℕ) : Formula :=
  .conj (.member U B) (.conj (.member p U)
    (.allMem B (.imp (.member (p+1) 0) (.subset (U+1) 0))))

end TuringRigidity.CountedRegularBasis

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenFiniteFlip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.CohenFiniteFlip
open TransitiveNameModel BoundedSetTheory CountableForcing InternalCollapse
open CohenGroundPoset InternalCohenBitFlip
open InternalCohen (bitSet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def prefixMask (a : ZFSet.{0}) (s : List Bool) (A : Oracle) : ZFSet.{0} :=
  ZFSet.range (fun i : {n : Fin s.length // A n.val ≠ s[n.val]} =>
    ZFSet.pair a (natSet i.val.val))

end TuringRigidity.CohenFiniteFlip

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteJoinSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.FiniteJoinSections
open FiniteShuffle ShuffleRequirements ArithmeticPrefixForcing

def Cover (s t u : List Bool) : Prop :=
  u.length ≤ 2 * s.length ∧ u.length ≤ 2 * t.length ∧
    Realizes u (join (fun i => s.getD i false) (fun i => t.getD i false))

def Product (D : List Bool → Prop) (s t : List Bool) : Prop :=
  ∃ u, D u ∧ Cover s t u

def Section (D : List Bool → Prop) (t s : List Bool) : Prop :=
  ∃ t', t <+: t' ∧ Product D s t'

def Fiber (D : List Bool → Prop) (A : Oracle) (t : List Bool) : Prop :=
  ∃ s, Realizes s A ∧ Product D s t

end TuringRigidity.FiniteJoinSections

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteOverwrite
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.FiniteOverwrite
open UniformPrograms

def overwrite (s : List Bool) (A : Oracle) (n : ℕ) : Bool :=
  if n < s.length then s.getD n false else A n

end TuringRigidity.FiniteOverwrite

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericTotality
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GenericIdentity
open Set FiniteShuffle ShuffleRequirements GenericTruth

def BinaryHalts (p : OracleCode) (P A : Oracle) (n : ℕ) : Prop :=
  0 ∈ OracleCode.eval (oracleFunction (join A P)) p n ∨
  1 ∈ OracleCode.eval (oracleFunction (join A P)) p n

end TuringRigidity.GenericIdentity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_NameDifferenceDense
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.FullSetForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)] [OrderTop (Conditions c)]

def NameDifference (a S : ZFSet.{u}) (t : Name (Conditions c)) : Set (Conditions c) :=
  {p | ∃ x ∈ a, (x ∈ S ∧ ∀ q, q ≤ p → ¬ MemForces (Name.check x) t q) ∨
    (x ∉ S ∧ MemForces (Name.check x) t p)}

end TuringRigidity.FullSetForcing

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

def Local (φ : Formula) (e : ℕ → ZFSet.{0}) : Prop :=
  ∀ D : ZFSet.{0}, Transitive D → ∀ t ∈ D, ∀ Y Z : ZFSet.{0},
    (∀ s ∈ D, ZFSet.rank s < ZFSet.rank t → (s ∈ Y ↔ s ∈ Z)) →
      (φ.Eval (cons t (cons Y e)) ↔ φ.Eval (cons t (cons Z e)))

def Partial (φ : Formula) (e : ℕ → ZFSet.{0}) (K D Y : ZFSet.{0}) : Prop :=
  Transitive D ∧ D ⊆ K ∧ Y ⊆ D ∧
    ∀ t ∈ D, t ∈ Y ↔ φ.Eval (cons t (cons Y e))

def partialFormula (φ : Formula) : Formula :=
  .conj (.transitive 1) (.conj (.subset 1 2) (.conj (.subset 0 1)
    (.allMem 1 (.iff (.member 0 1) (φ.rename dropSlots)))))

noncomputable def domain (φ : Formula) (e : ℕ → ZFSet.{0}) (K Q : ZFSet.{0}) : ZFSet.{0} :=
  K.sep (fun t => ∃ D ∈ Q, ∃ Y ∈ Q, Partial φ e K D Y ∧ t ∈ D)

noncomputable def truth (φ : Formula) (e : ℕ → ZFSet.{0}) (K Q : ZFSet.{0}) : ZFSet.{0} :=
  K.sep (fun t => ∃ D ∈ Q, ∃ Y ∈ Q, Partial φ e K D Y ∧ t ∈ Y)

def unionFormula (φ : Formula) (which : ℕ) : Formula :=
  .existsMem 1 (.existsMem 2 (.conj ((partialFormula φ).rename candidateSlots) (.member 2 which)))

end TuringRigidity.BoundedTruthRecursion

end OAI
end


