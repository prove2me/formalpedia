-- Prove2me | Definitions.Def_OAIQ064A006
-- name    : OAIQ064A006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T00:33:24.597133+00:00
-- url     : https://prove2.me/theorems/d0a4d7a5-252a-4b02-ad18-d99c583beb06
-- title:
--   Definitions bundle OAIQ064A006 of the split of OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 274 declarations of OpenAI's Lean: 149 definitions, 4 inductive types or structures, 4 instances and 117 theorems. The definitions and types are `OAI.TuringRigidity.BoundedSetTheory.DefinesArithmetic`, `OAI.TuringRigidity.BoundedSetTheory.DegreeEqualityFormula`, `OAI.TuringRigidity.BoundedSetTheory.DegreeOrderFormula`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTuple.relativizeSigma`, `OAI.TuringRigidity.BoundedSetTheory.SigmaCollection`, `OAI.TuringRigidity.BoundedSetTheory.SigmaFormula.boundedDisj`, `OAI.TuringRigidity.BoundedSetTheory.SigmaFormula.disj`, `OAI.TuringRigidity.BoundedSetTheory.SigmaFormula.domainRequest`, `OAI.TuringRigidity.BoundedSetTheory.SigmaFormula.existsMem`, `OAI.TuringRigidity.BoundedSetTheory.SigmaFormula.image`, `OAI.TuringRigidity.BoundedSetTheory.SigmaFormula.toLevy`, `OAI.TuringRigidity.BoundedSetTheory.arithmeticEnv`, `OAI.TuringRigidity.BoundedSetTheory.modelReals`, `OAI.TuringRigidity.CategoryAvoidance`, `OAI.TuringRigidity.CategorySearch.finiteOracle`, `OAI.TuringRigidity.CategorySearch.finiteRun`, `OAI.TuringRigidity.CategorySearch.inside`, `OAI.TuringRigidity.CategorySearch.rationalBit`, `OAI.TuringRigidity.CategorySearch.sample`, `OAI.TuringRigidity.CohenColumnRealName.poset`, `OAI.TuringRigidity.CohenColumnRealName.realName`, `OAI.TuringRigidity.CohenColumnRealName.realNameCode`, `OAI.TuringRigidity.CohenFactorReconstruction.reconstruct`, `OAI.TuringRigidity.CohenFiniteFlip.prefixFilter`, `OAI.TuringRigidity.CohenGroundPoset.conditionEquiv`, `OAI.TuringRigidity.CohenGroundPoset.encode`, `OAI.TuringRigidity.CohenNiceNameConstruction.cohenTop`, `OAI.TuringRigidity.CohenProductSplitting.productIso`, `OAI.TuringRigidity.CohenProductSplitting.productMap`, `OAI.TuringRigidity.CutAddition.decision`, `OAI.TuringRigidity.CutAddition.trial`, `OAI.TuringRigidity.CutArithmetic`, `OAI.TuringRigidity.ElementaryModel.Elementary`, `OAI.TuringRigidity.ElementaryModel.SentenceForm.rename`, `OAI.TuringRigidity.ElementaryModel.Valid`, `OAI.TuringRigidity.ElementaryModel.checkedValueFormula`, `OAI.TuringRigidity.ElementaryModel.fromBounded`, `OAI.TuringRigidity.ElementaryModel.fromSigma`, `OAI.TuringRigidity.ElementaryModel.hull`, `OAI.TuringRigidity.ElementaryModel.hullSet` and 113 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DegreeRigidity_CohenForcing_CohenColumnRealName`, `DegreeRigidity_CohenForcing_CohenConditionCode`, `DegreeRigidity_CohenForcing_CohenEffectiveGeneric`, `DegreeRigidity_CohenForcing_CohenFactorReconstruction`, `DegreeRigidity_CohenForcing_CohenGroundGeneric`, `DegreeRigidity_CohenForcing_CohenGroundPoset`, `DegreeRigidity_CohenForcing_CohenNiceNameConstruction`, `DegreeRigidity_CohenForcing_CohenPrefixDensity`, `DegreeRigidity_CohenForcing_CohenPrefixOverwrite`, `DegreeRigidity_CohenForcing_CohenPrefixReconstruction`, `DegreeRigidity_CohenForcing_CohenProductSplitting`, `DegreeRigidity_CohenForcing_CohenWordCodeGraph`, `DegreeRigidity_CohenForcing_FullSetForcing`, `DegreeRigidity_CohenForcing_InternalCohenBitFlip`, `DegreeRigidity_CohenForcing_InternalCohenConditions`, `DegreeRigidity_CohenForcing_InternalCohenFactor`, `DegreeRigidity_CohenForcing_InternalCohenFilters`, `DegreeRigidity_CohenForcing_InternalCohenHomogeneity`, `DegreeRigidity_CohenForcing_InternalCohenName`, `DegreeRigidity_CohenForcing_InternalCohenOddHits`, `DegreeRigidity_CohenForcing_InternalCohenPartition`, `DegreeRigidity_CohenForcing_InternalCohenProjectedGeneric`, `DegreeRigidity_CohenForcing_InternalCohenReindex`, `DegreeRigidity_CohenForcing_InternalCohenRequirements`, `DegreeRigidity_CohenForcing_InternalCohenRestriction`, `DegreeRigidity_CohenForcing_InternalCohenTailHomogeneity`, `DegreeRigidity_Computability_ArithmeticSetSyntax`, `DegreeRigidity_Computability_CutAddition`, `DegreeRigidity_Computability_Cuts`, `DegreeRigidity_Computability_OracleJump`, `DegreeRigidity_Computability_RationalCut`, `DegreeRigidity_Constructibility_ConstructibleTupleSpace`, `DegreeRigidity_Effective_FiniteNaturalGraph`, `DegreeRigidity_Effective_FiniteShuffle`, `DegreeRigidity_Effective_FiniteShuffleCertificate`, `DegreeRigidity_Effective_FiniteShuffleComputation`, `DegreeRigidity_Effective_GuardedComputability`, `DegreeRigidity_Effective_GuardedLimits`, `DegreeRigidity_Effective_GuardedPair`, `DegreeRigidity_Effective_GuardedScan`, `DegreeRigidity_Effective_GuardedStage`, `DegreeRigidity_Effective_LocalPair`, `DegreeRigidity_Effective_StablePair`, `DegreeRigidity_Effective_TupleFormula`, `DegreeRigidity_Effective_UniformAgreement`, `DegreeRigidity_Effective_UniformPair`, `DegreeRigidity_Effective_UniformSplit`, `DegreeRigidity_OrdinalCodes_IndexPresentation`, `DegreeRigidity_OrdinalCodes_NaturalAdditionTrace`, `DegreeRigidity_OrdinalCodes_NaturalDefinitions`, `DegreeRigidity_OrdinalCodes_NaturalIterationFormula`, `DegreeRigidity_OrdinalCodes_NaturalIterationTrace`, `DegreeRigidity_OrdinalCodes_NaturalMultiplicationFormula`, `DegreeRigidity_OrdinalCodes_NaturalPairingFormula`, `DegreeRigidity_OrdinalCodes_NaturalPrimitiveRecursion`, `DegreeRigidity_OrdinalCodes_NaturalProjectionFormula`, `DegreeRigidity_OrdinalCodes_NaturalTermFormula`, `DegreeRigidity_OrdinalCodes_NumericalCohenSets`, `DegreeRigidity_OrdinalCodes_SumComparison`, `DegreeRigidity_Representation_AmbientDegreeSyntax`, `DegreeRigidity_Representation_Assembly`, `DegreeRigidity_Representation_CategoryMachine`, `DegreeRigidity_Representation_CommonGenericModels`, `DegreeRigidity_Representation_GenericCoding`, `DegreeRigidity_Representation_GenericIdentity`, `DegreeRigidity_Representation_GenericTopology`, `DegreeRigidity_Representation_ParameterCoveringModels`, `DegreeRigidity_Representation_SourceIdentity`, `DegreeRigidity_SetModels_CollapsePrefixAbsolute`, `DegreeRigidity_SetModels_CollapseWithoutChoice`, `DegreeRigidity_SetModels_CountableElementaryHull`, `DegreeRigidity_SetModels_DegreeSetFormula`, `DegreeRigidity_SetModels_ElementaryCheckedCode`, `DegreeRigidity_SetModels_ElementaryCollapse`, `DegreeRigidity_SetModels_ElementaryLanguage`, `DegreeRigidity_SetModels_ElementaryModelIdeal`, `DegreeRigidity_SetModels_ElementarySatisfaction`, `DegreeRigidity_SetModels_ExtensionSigmaReplacement`, `DegreeRigidity_SetModels_FixedArithmetic`, `DegreeRigidity_SetModels_IdealInterpretation`, `DegreeRigidity_SetModels_IdealLift`, `DegreeRigidity_SetModels_IdealLocality`, `DegreeRigidity_SetModels_IdealPresentation`, `DegreeRigidity_SetModels_InternalBooleanExtension`, `DegreeRigidity_SetModels_InternalBooleanName`, `DegreeRigidity_SetModels_InternalBooleanProjection`, `DegreeRigidity_SetModels_InternalBooleanSyntax`, `DegreeRigidity_SetModels_InternalBooleanTop`, `DegreeRigidity_SetModels_InternalCollapseConditions`, `DegreeRigidity_SetModels_InternalColumnExtension`, `DegreeRigidity_SetModels_InternalCommonRequirements`, `DegreeRigidity_SetModels_InternalCountableFiniteUnion`, `DegreeRigidity_SetModels_InternalDenseInclusion`, `DegreeRigidity_SetModels_InternalFiniteEnumeration`, `DegreeRigidity_SetModels_InternalFiniteSubsets`, `DegreeRigidity_SetModels_InternalNiceName`, `DegreeRigidity_SetModels_InternalProjectedGeneric`, `DegreeRigidity_SetModels_InternalRegularAlgebra`, `DegreeRigidity_SetModels_InternalRegularOperations`, `DegreeRigidity_SetModels_InternalRegularOrder`, `DegreeRigidity_SetModels_InternalShuffleSets`, `DegreeRigidity_SetModels_InternalStructureCollapse`, `DegreeRigidity_SetModels_ModelDegreeOrder`, `DegreeRigidity_SetModels_ModelReals`, `DegreeRigidity_SetModels_MostowskiCollapse`, `DegreeRigidity_SetModels_ShuffleRequirements`, `DegreeRigidity_SetModels_TransitiveNameModel`, `DegreeRigidity_Syntax_CheckedMembershipSeparation`, `DegreeRigidity_Syntax_FiniteModelGraph`, `DegreeRigidity_Syntax_FormulaIsomorphism`, `DegreeRigidity_Syntax_LevySigmaSchemas`, `DegreeRigidity_Syntax_PrimitivePredicateFormula`, `DegreeRigidity_Syntax_SigmaCollection`, `DegreeRigidity_Syntax_SigmaDisjunction`, `DegreeRigidity_Syntax_SigmaDomainCollection`, `DegreeRigidity_Syntax_SigmaInterpretation`, `DegreeRigidity_Syntax_SigmaTransitiveWitness`.
--
--   **Imports.** It imports the published bundle `Def_DegreeRigidity`; the bundles `OAIQ064A002`, `OAIQ064A003` and `OAIQ064A004` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ064A008`; the statements `OAI.TuringRigidity.ArithmeticFiniteTruthTransfer.source_equation_finite_family`, `OAI.TuringRigidity.BoundedForcing.projected_arithmetic_output_cone`, `OAI.TuringRigidity.CohenDisjointPrefixPair.exists_iterated_pair`, `OAI.TuringRigidity.CohenNiceNameConstruction.internal_nice_name`, `OAI.TuringRigidity.CohenProjectedNameLift.lift_projected_real_name`, `OAI.TuringRigidity.FixedArithmetic.frame_exists`, `OAI.TuringRigidity.GroundIteratedTriple.generic_triple_of_arithmetic`, `OAI.TuringRigidity.GroundPrefixOverwrite.overwrite_generic`, `OAI.TuringRigidity.InternalBooleanIntermediate.internal_boolean_intermediate`, `OAI.TuringRigidity.InternalCohen.groundGeneric_table_simulation`, `OAI.TuringRigidity.InternalCohen.prefix_extension_eq_hull`, `OAI.TuringRigidity.IteratedGenericCommonIdeal.ideal_of_iterated_generics`, `OAI.TuringRigidity.OriginalRealFullIteration.original_name_full_iteration`, `OAI.TuringRigidity.OriginalRealQuotientModel.original_name_quotient`, `OAI.TuringRigidity.ProjectedArithmeticOutputName.representative_in_model`, `OAI.TuringRigidity.RealHullGenericTriple.exists_generic_prefix_triple`, `OAI.TuringRigidity.RealHullGenericTriple.exists_prefix_real`, `OAI.TuringRigidity.RealHullIteration.exists_iterated_pair`, `OAI.TuringRigidity.RealHullIteration.exists_iterated_prefix_pair`, `OAI.TuringRigidity.RelativeConstructible.hierarchy_witness_collection`, `OAI.TuringRigidity.RelativeConstructible.internal_hierarchyGraph_collection`, `OAI.TuringRigidity.RelativeConstructible.real_hull_prescribed_transfer`, `OAI.TuringRigidity.RelativeConstructible.uniform_hierarchy_certificate_collection` and `OAI.TuringRigidity.TwoRealHull.joined_factorization`; the proofs of `OAI.TuringRigidity.ArithmeticFiniteTruthTransfer.source_equation_finite_family`, `OAI.TuringRigidity.ArithmeticTree.native_nonidentity_absolute`, `OAI.TuringRigidity.ArithmeticTree.native_persistence_absolute`, `OAI.TuringRigidity.EnumerationConstruction.enumeration_exists`, `OAI.TuringRigidity.FixedArithmetic.frame_exists`, `OAI.TuringRigidity.LocalUnary.localized_copy`, `OAI.TuringRigidity.RelativeConstructible.hierarchy_witness_collection`, `OAI.TuringRigidity.RelativeConstructible.internal_defSystem_of_context`, `OAI.TuringRigidity.RelativeConstructible.internal_hierarchyGraph_collection` and `OAI.TuringRigidity.RelativeConstructible.uniform_hierarchy_certificate`.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A002
import Definitions.Def_OAIQ064A003
import Definitions.Def_OAIQ064A004

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_Cuts
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier _root_.OAI.TuringRigidity.instOrderBotDegree _root_.OAI.TuringRigidity.instSemilatticeSupDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Topology
namespace TuringRigidity

noncomputable def realDegree (x : ℝ) : Degree := degree (cut x)

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_RationalCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
namespace RationalCoding

def ltCode (i j : ℕ) : Prop :=
  positiveNumerator i*denominator j + negativeNumerator j*denominator i <
    positiveNumerator j*denominator i + negativeNumerator i*denominator j

instance instDecidableLtCode (i j : ℕ) : Decidable (ltCode i j) := inferInstanceAs (Decidable (_ < _))

end RationalCoding

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_Assembly
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Topology
namespace TuringRigidity

structure CutArithmetic : Prop where
  add : ∀ x y : ℝ, realDegree (x+y) ≤ realDegree x ⊔ realDegree y
  sub : ∀ x y : ℝ, realDegree (x-y) ≤ realDegree x ⊔ realDegree y
  smul : ∀ (q : ℚ) (x : ℝ), realDegree ((q : ℝ)*x) ≤ realDegree x
  translate : ∀ (x : ℝ) (q : ℚ), realDegree (x+(q : ℝ)) ≤ realDegree x

def CategoryAvoidance : Prop := ∀ A Y : Oracle, ¬ Reduces Y A →
  IsMeagre {p : ℝ × ℝ | Reduces Y (join (join A (cut p.1)) (cut p.2))}

def FourValueRecovery : Prop := ∀ F : ℝ → Oracle,
  Measurable F → (∀ B, {x | F x = B}.Countable) →
  (∀ x y, Reduces (F (x+y)) (join (F x) (F y))) →
  ∀ t : ℝ, Irrational t → 0 < t → t < 1 →
  ∃ G : Set (ℝ × ℝ), G ∈ residual (ℝ × ℝ) ∧
    ∀ p ∈ G, ∃ δ : ℚ, 0 < δ ∧ δ < 1 ∧ Reduces (cut t) (fourTuple F t p.1 p.2 δ)

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericCoding
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GenericCoding
open UniformOracle BinarySeries Encodable

def count (G : Oracle) : ℕ → ℕ := runningSum (fun n => bit G (2*n+1))

def code (A G : Oracle) (n : ℕ) : Bool :=
  if G (2*n+1) then A (count G n) else G (2*(n-count G n))

def recoverTrial (A G : Oracle) (k n : ℕ) : Option ℕ :=
  recoverDecision (k,count G n,bit G (2*n+1),bit (code A G) n)

end TuringRigidity.GenericCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteShuffle
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.FiniteShuffle
open GenericCoding UniformOracle BinarySeries

def extendEven (n : ℕ) (G T : Oracle) : Oracle :=
  join (fun i => if i < n then G (2*i) else T (i + count G n)) (fun i => G (2*i+1))

end TuringRigidity.FiniteShuffle

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ShuffleRequirements
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ShuffleRequirements
open FiniteShuffle GenericCoding Set

def Transfer (D : List Bool → Prop) (s : List Bool) : Prop :=
  ∀ A, ∃ t, D t ∧ ∀ G, Realizes s G → Realizes t (code A G)

def Requirements (D : ℕ → List Bool → Prop) (n : ℕ) (s : List Bool) : Prop :=
  if (Nat.unpair n).2 = 0 then D (Nat.unpair n).1 s
  else if (Nat.unpair n).2 = 1 then Transfer (D (Nat.unpair n).1) s
  else OddHit (Nat.unpair n).1 s

end TuringRigidity.ShuffleRequirements

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GenericTopology
open FiniteShuffle ShuffleRequirements GenericCoding Set

def Combined {X : Type*} (D : ℕ → List Bool → Prop) (R : X → ℕ → ℕ → Prop)
    (x : X) (n t : ℕ) : Prop :=
  if n % 2 = 0 then Requirements D (n/2) (BorelGeneric.word t) else R x (n/2) t

end TuringRigidity.GenericTopology

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericIdentity
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GenericIdentity
open Set

def SourceEquation (p : OracleCode) (P : Oracle) (z : Oracle × Oracle × Oracle) : Prop :=
  Total p P z.1 ∧ Total p P z.2.1 ∧ Total p P z.2.2 ∧
  Total p P (GenericCoding.code z.1 z.2.1) ∧ Total p P (GenericCoding.code z.1 z.2.2) ∧
  PrincipalIntersection (value p P z.1)
    (join (value p P (GenericCoding.code z.1 z.2.1)) (value p P z.2.1))
    (join (value p P (GenericCoding.code z.1 z.2.2)) (value p P z.2.2))

end TuringRigidity.GenericIdentity

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

def rationalBit (i k : ℕ) : ℕ := if RationalCoding.ltCode k i then 1 else 0

def sample (i j : ℕ) : ℝ × ℝ := (rationalEnumeration i,rationalEnumeration j)

def finiteOracle (L : List ℕ) (i j : ℕ) : ℕ →. ℕ :=
  partialJoin (partialJoin (BranchMachine.lookup L) (fun k => Part.some (rationalBit i k)))
    (fun k => Part.some (rationalBit j k))

def inside (l r : ℚ × ℚ) (i j : ℕ) : Prop :=
  RationalCoding.ltCode (encode l.1) i ∧ RationalCoding.ltCode i (encode r.1) ∧
  RationalCoding.ltCode (encode l.2) j ∧ RationalCoding.ltCode j (encode r.2)
instance instDecidableInside (l r : ℚ × ℚ) (i j : ℕ) : Decidable (inside l r i j) := inferInstanceAs (Decidable (_ ∧ _))

def finiteRun (c : OracleCode) (l r : ℚ × ℚ) (L : List ℕ) (w : ℕ) : Part ℕ :=
  let i := (Nat.unpair w).1
  let j := (Nat.unpair (Nat.unpair w).2).1
  let n := (Nat.unpair (Nat.unpair w).2).2
  if inside l r i j then OracleCode.eval (finiteOracle L i j) c n else Part.none

end TuringRigidity.CategorySearch

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_SumComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RationalCoding

def sumLeft (z : ℕ × ℕ × ℕ) : ℕ :=
  positiveNumerator z.1 * denominator z.2.1 * denominator z.2.2 +
    negativeNumerator z.2.1 * denominator z.1 * denominator z.2.2 +
    negativeNumerator z.2.2 * denominator z.1 * denominator z.2.1

def sumRight (z : ℕ × ℕ × ℕ) : ℕ :=
  negativeNumerator z.1 * denominator z.2.1 * denominator z.2.2 +
    positiveNumerator z.2.1 * denominator z.1 * denominator z.2.2 +
    positiveNumerator z.2.2 * denominator z.1 * denominator z.2.1

end TuringRigidity.RationalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_CutAddition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
namespace CutAddition
open RationalCoding UniformOracle

def decision (z : ℕ × (ℕ × ℕ) × (ℕ × ℕ)) : Option ℕ :=
  if z.2.2.1=1 ∧ z.2.2.2=1 ∧ sumLeft (z.1,z.2.1.1,z.2.1.2) < sumRight (z.1,z.2.1.1,z.2.1.2)
    then some 1 else
  if z.2.2.1=0 ∧ z.2.2.2=0 ∧ sumRight (z.1,z.2.1.1,z.2.1.2) < sumLeft (z.1,z.2.1.1,z.2.1.2)
    then some 0 else none

noncomputable def trial (x y : ℝ) (n m : ℕ) : Option ℕ :=
  decision (n,Nat.unpair m,
    (if cut x (Nat.unpair m).1 then 1 else 0,if cut y (Nat.unpair m).2 then 1 else 0))

end CutAddition

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_SourceIdentity
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GenericIdentity

noncomputable def ImageJoin (p : OracleCode) (P Y G : Oracle) : Oracle :=
  join (value p P (GenericCoding.code Y G)) (value p P G)

end TuringRigidity.GenericIdentity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_TransitiveNameModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open Set RecursiveNames
universe u

theorem genericExtension_countable (M p : ZFSet.{u})
    (hM : (M : Set ZFSet.{u}).Countable) (G : Set (Conditions p)) :
    (genericExtension M p G).Countable := by
  apply (hM.image (valueOnCode p G)).mono
  rintro x ⟨τ,hτ,rfl⟩
  exact ⟨Name.encode (label p) τ,hτ,valueOnCode_encode p G τ⟩

end TuringRigidity.TransitiveNameModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SigmaInterpretation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem SigmaFormula.upward (φ : SigmaFormula) (M N : ZFSet.{u})
    (hM : Transitive M) (hN : Transitive N) (hMN : M ⊆ N)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    φ.Realize M e → φ.Realize N e := by
  induction φ generalizing e with
  | bounded φ =>
    exact fun h => (φ.absolute N hN e (fun i => hMN (he i))).mpr
      ((φ.absolute M hM e he).mp h)
  | existsSet φ ih =>
    rintro ⟨x,hx,hφ⟩
    exact ⟨x,hMN hx,ih (cons x e) (fun i => by cases i <;> simp [cons,he,hx]) hφ⟩

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

def relativizeSigma (d : ℕ) : SigmaFormula → Formula
  | .bounded φ => relativizeBounded d φ
  | .existsSet φ => .existsMem d (relativizeSigma (d+1) φ)

theorem eval_relativizeSigma (φ : SigmaFormula) (d : ℕ) (e : ℕ → ZFSet.{u}) :
    (relativizeSigma d φ).Eval e ↔ φ.Realize (e d) e := by
  induction φ generalizing d e with
  | bounded φ => exact eval_relativizeBounded φ d e
  | existsSet φ ih =>
    simp only [relativizeSigma,Formula.Eval,SigmaFormula.Realize]
    apply exists_congr; intro x
    exact and_congr_right (fun _ => ih (d+1) (cons x e))

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

theorem graphRange_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hU : BoundedSetTheory.Union M) (hS : Separation M)
    {d f : ZFSet.{u}} (hd : d ∈ M) (hf : f ∈ M) : graphRange d f ∈ M := by
  simpa only [graphRange,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ] using
    sep_mem M hM hS (.existsMem 1 (.pairMem 0 1 3)) (cons d (fun _ => f))
      (by intro i; cases i <;> assumption) (iterUnion_mem M hM hU hf 2)

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

theorem SigmaFormula.realize_isomorphism (A B : ZFSet.{u}) (j : ZFSet.{u} → ZFSet.{u})
    (hin : ∀ x ∈ A, j x ∈ B)
    (hout : ∀ y ∈ B, ∃ x ∈ A, j x = y)
    (hi : ∀ x ∈ A, ∀ y ∈ A, j x = j y → x = y)
    (hm : ∀ x ∈ A, ∀ y ∈ A, j x ∈ j y ↔ x ∈ y)
    (φ : SigmaFormula) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) :
    φ.Realize A e ↔ φ.Realize B (fun i => j (e i)) := by
  induction φ generalizing e with
  | bounded φ => exact φ.realize_isomorphism A B j hin hout hi hm e he
  | existsSet φ ih =>
    have he' (x : ZFSet.{u}) (hx : x ∈ A) : ∀ n, cons x e n ∈ A := by
      intro n; cases n with
      | zero => exact hx
      | succ n => exact he n
    constructor
    · rintro ⟨x,hx,hφ⟩
      refine ⟨j x,hin x hx,?_⟩
      have h := (ih (cons x e) (he' x hx)).mp hφ
      rwa [map_cons] at h
    · rintro ⟨y,hy,hφ⟩
      obtain ⟨x,hx,rfl⟩ := hout y hy
      apply Exists.intro x
      refine ⟨hx,?_⟩
      apply (ih (cons x e) (he' x hx)).mpr
      rwa [map_cons]

end TuringRigidity.BoundedSetTheory

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

theorem membershipRelation_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    {d : ZFSet.{u}} (hd : d ∈ M) : membershipRelation d ∈ M := by
  simpa only [membershipRelation,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ] using
    sep_mem M hM hS (.existsMem 1 (.existsMem 2 (.conj (.orderedPair 2 1 0) (.member 1 0))))
      (fun _ => d) (fun _ => hd) (product_mem M hM hP hU hPow hS hd hd)

end TuringRigidity.RelationCollapse

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

def SigmaCollection (M : ZFSet.{u}) : Prop :=
  ∀ (φ : SigmaFormula) (e : ℕ → ZFSet.{u}), (∀ i, e i ∈ M) → ∀ a ∈ M,
    (∀ x ∈ a, ∃ y ∈ M, φ.Realize M (cons y (cons x e))) →
      ∃ W ∈ M, ∀ x ∈ a, ∃ y ∈ W, φ.Realize M (cons y (cons x e))

end TuringRigidity.BoundedSetTheory

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

def image (φ : SigmaFormula) : SigmaFormula :=
  .existsSet (andBounded (.member 0 2) (φ.rename imageVars))

theorem realize_image (φ : SigmaFormula) (M a y : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    φ.image.Realize M (cons y (cons a e)) ↔
      ∃ x ∈ M, x ∈ a ∧ φ.Realize M (cons y (cons x e)) := by
  simp only [image,Realize,realize_andBounded,realize_rename,Formula.Realize,cons_zero,cons_succ]
  apply exists_congr; intro x
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  have he : (fun i => cons x (cons y (cons a e)) (imageVars i)) = cons y (cons x e) := by
    funext i; rcases i with _|i; rfl
    rcases i with _|i <;> rfl
  rw [he]
end SigmaFormula
end TuringRigidity.BoundedSetTheory

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

theorem transitive_upward (φ : SigmaFormula) {d D : ZFSet.{u}} (hd : Transitive d) (hD : Transitive D)
    (hsub : d ⊆ D) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ d) :
    φ.Realize d e → φ.Realize D e := by
  induction φ generalizing e with
  | bounded φ =>
    intro h
    exact (φ.absolute D hD e (fun i => hsub (he i))).mpr ((φ.absolute d hd e he).mp h)
  | existsSet φ ih =>
    rintro ⟨x,hx,hφ⟩
    exact ⟨x,hsub hx,ih (cons x e) (by intro i; cases i <;> simp [cons,he,hx]) hφ⟩

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

def domainRequest (φ : SigmaFormula) : SigmaFormula := .bounded
  (.conj (.transitive 0) (.conj (.subset 2 0) (FiniteTuple.relativizeSigma 0 (φ.rename domainVars))))

theorem realize_domainRequest (φ : SigmaFormula) (M : ZFSet.{u}) (hM : Transitive M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) {d x t : ZFSet.{u}}
    (hd : d ∈ M) (hx : x ∈ M) (ht : t ∈ M) :
    φ.domainRequest.Realize M (cons d (cons x (cons t e))) ↔
      Transitive d ∧ t ⊆ d ∧ φ.Realize d (cons x e) := by
  have he' : ∀ i, cons d (cons x (cons t e)) i ∈ M := by
    intro i; rcases i with _|i; exact hd
    rcases i with _|i; exact hx
    rcases i with _|i; exact ht
    exact he i
  rw [domainRequest,Realize,Formula.absolute _ M hM _ he']
  simp only [Formula.Eval,Formula.eval_transitive,Formula.eval_subset,FiniteTuple.eval_relativizeSigma,
    realize_rename,cons_zero,cons_succ]
  have eq : (fun i => cons d (cons x (cons t e)) (domainVars i)) = cons x e := by
    funext i; cases i <;> rfl
  rw [eq]

end SigmaFormula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SigmaDisjunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u
namespace SigmaFormula

def boundedDisj (b : Formula) : SigmaFormula → SigmaFormula
  | .bounded c => .bounded (.disj b c)
  | .existsSet φ => .existsSet (boundedDisj (b.rename Nat.succ) φ)

def disj : SigmaFormula → SigmaFormula → SigmaFormula
  | .bounded b,ψ => boundedDisj b ψ
  | .existsSet φ,ψ => .existsSet (disj φ (ψ.rename Nat.succ))

theorem realize_boundedDisj (M : ZFSet.{u}) (h0 : (∅ : ZFSet.{u}) ∈ M)
    (b : Formula) (φ : SigmaFormula) (e : ℕ → ZFSet.{u}) :
    (boundedDisj b φ).Realize M e ↔ b.Realize M e ∨ φ.Realize M e := by
  induction φ generalizing b e with
  | bounded c => simp only [boundedDisj,Realize,Formula.disj,Formula.Realize]; tauto
  | existsSet φ ih =>
    change (∃ x ∈ M, (boundedDisj (b.rename Nat.succ) φ).Realize M (cons x e)) ↔ _
    simp_rw [ih,Formula.realize_rename]
    change (∃ x ∈ M, b.Realize M e ∨ φ.Realize M (cons x e)) ↔
      b.Realize M e ∨ ∃ x ∈ M, φ.Realize M (cons x e)
    constructor
    · rintro ⟨x,hx,h|h⟩
      · exact Or.inl h
      · exact Or.inr ⟨x,hx,h⟩
    · rintro (h|⟨x,hx,h⟩)
      · exact ⟨∅,h0,Or.inl h⟩
      · exact ⟨x,hx,Or.inr h⟩

theorem realize_disj (M : ZFSet.{u}) (h0 : (∅ : ZFSet.{u}) ∈ M)
    (φ ψ : SigmaFormula) (e : ℕ → ZFSet.{u}) :
    (disj φ ψ).Realize M e ↔ φ.Realize M e ∨ ψ.Realize M e := by
  induction φ generalizing ψ e with
  | bounded b => exact realize_boundedDisj M h0 b ψ e
  | existsSet φ ih =>
    change (∃ x ∈ M, (disj φ (ψ.rename Nat.succ)).Realize M (cons x e)) ↔ _
    simp_rw [ih,realize_rename]
    change (∃ x ∈ M, φ.Realize M (cons x e) ∨ ψ.Realize M e) ↔
      (∃ x ∈ M, φ.Realize M (cons x e)) ∨ ψ.Realize M e
    constructor
    · rintro ⟨x,hx,h|h⟩
      · exact Or.inl ⟨x,hx,h⟩
      · exact Or.inr h
    · rintro (⟨x,hx,h⟩|h)
      · exact ⟨x,hx,Or.inl h⟩
      · exact ⟨∅,h0,Or.inr h⟩

def existsMem (a : ℕ) (φ : SigmaFormula) : SigmaFormula :=
  .existsSet (.andBounded (.member 0 (a+1)) φ)

theorem realize_existsMem (M : ZFSet.{u}) (a : ℕ) (φ : SigmaFormula) (e : ℕ → ZFSet.{u}) :
    (existsMem a φ).Realize M e ↔ ∃ x ∈ M, x ∈ e a ∧ φ.Realize M (cons x e) := by
  simp only [existsMem,Realize,realize_andBounded,Formula.Realize,cons_zero,cons_succ]
end SigmaFormula

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

def SigmaFormula.toLevy : SigmaFormula → LevySigma
  | .bounded φ => .bounded φ
  | .existsSet φ => .existsSet φ.toLevy

theorem SigmaFormula.realize_toLevy (φ : SigmaFormula) (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    φ.toLevy.Realize M e ↔ φ.Realize M e := by
  induction φ generalizing e with
  | bounded φ => rfl
  | existsSet φ ih =>
    simp only [toLevy,LevySigma.Realize,Realize]
    apply exists_congr; intro x
    exact and_congr_right (fun _ => ih (cons x e))

theorem LevySigmaSeparation.finitePrefix {M : ZFSet.{u}} (hS : LevySigmaSeparation M) : SigmaSeparation M := by
  intro φ e he a ha
  obtain ⟨b,hb,hbdef⟩ := hS φ.toLevy e he a ha
  exact ⟨b,hb,fun x hx => (hbdef x hx).trans (and_congr_right (fun _ => φ.realize_toLevy M _))⟩

theorem LevySigmaReplacement.finitePrefix {M : ZFSet.{u}} (hR : LevySigmaReplacement M) : SigmaReplacement M := by
  intro φ e he a ha htotal
  obtain ⟨b,hb,hbdef⟩ := hR φ.toLevy e he a ha (by
    intro x hx
    obtain ⟨y,hy,hφ,hu⟩ := htotal x hx
    exact ⟨y,hy,(φ.realize_toLevy M _).mpr hφ,fun z hz h => hu z hz ((φ.realize_toLevy M _).mp h)⟩)
  refine ⟨b,hb,?_⟩
  intro y hy
  rw [hbdef y hy]
  apply exists_congr; intro x
  exact and_congr_right (fun _ => φ.realize_toLevy M _)

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelReals
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem realCode_subset (A : Oracle) : realCode.{u} A ⊆ ZFSet.omega :=
  fun _ hx => (ZFSet.mem_sep.mp hx).1

theorem natSet_mem_realCode (A : Oracle) (n : ℕ) : natSet.{u} n ∈ realCode A ↔ A n = true := by
  rw [realCode,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,m,he,hm⟩
    have hnm := natSet_injective he
    exact hnm.symm ▸ hm
  · intro hn
    exact ⟨(mem_omega _).mpr ⟨n,rfl⟩,n,rfl,hn⟩

theorem realCode_decodeReal {x : ZFSet.{u}} (hx : x ⊆ ZFSet.omega) : realCode (decodeReal x) = x := by
  apply ZFSet.ext; intro z
  by_cases hz : z ∈ ZFSet.omega.{u}
  · obtain ⟨n,rfl⟩ := (mem_omega z).mp hz
    rw [natSet_mem_realCode,decodeReal_true]
  · exact ⟨fun h => False.elim (hz (realCode_subset _ h)),fun h => False.elim (hz (hx h))⟩

theorem realCode_injective : Function.Injective (realCode.{u}) := by
  intro A B he
  funext n
  have h : A n = true ↔ B n = true := by
    rw [←natSet_mem_realCode.{u} A n,←natSet_mem_realCode.{u} B n,he]
  cases ha : A n <;> cases hb : B n <;> simp_all

theorem decodeReal_realCode (A : Oracle) : decodeReal (realCode.{u} A) = A :=
  realCode_injective (realCode_decodeReal (realCode_subset A))

def modelReals (M : ZFSet.{u}) : Set Oracle := {A | realCode A ∈ M}

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

theorem finiteModelGraph_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hω : ZFSet.omega.{u} ∈ M)
    (f : ℕ → ZFSet.{u}) (hf : ∀ i, f i ∈ M) (n : ℕ) : finiteModelGraph f n ∈ M := by
  have hn (i : ℕ) : natSet.{u} i ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨i,rfl⟩)
  induction n with
  | zero => exact singleton_mem M hM hP (orderedPair_mem M hM hP (hn 0) (hf 0))
  | succ n ih =>
    exact binary_union_mem M hM hP hU ih
      (singleton_mem M hM hP (orderedPair_mem M hM hP (hn (n+1)) (hf (n+1))))

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

theorem orderSet_pair (c : ZFSet.{u}) (p q : Conditions c) :
    ZFSet.pair (label c p) (label c q) ∈ orderSet c ↔ p ≤ q := by
  rw [orderSet,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,x,_,y,_,he,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact h
  · intro h
    exact ⟨ZFSet.mem_prod.mpr ⟨_,label_mem c p,_,label_mem c q,rfl⟩,
      _,label_mem c p,_,label_mem c q,rfl,h⟩

end TuringRigidity.BoundedSetTheory.InternalCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_CollapseWithoutChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalCollapse
open TransitiveNameModel CountableForcing
universe u
attribute [local instance] order

theorem conditions_exist_without_choice (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hω : ZFSet.omega.{u} ∈ M)
    {A : ZFSet.{u}} (hA : A ∈ M) :
    ∃ c ∈ M, ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix A p := by
  obtain ⟨Q,hQM,hQ⟩ := internal_power M hM hPow
    (product_mem M hM hP hU hPow hS hω hA)
  let e := cons ZFSet.omega (fun _ => A)
  have he : ∀ i, e i ∈ M := by intro i; cases i <;> assumption
  let c := ZFSet.sep (fun p => (prefixFormula 1 2 0).Eval (cons p e)) Q
  refine ⟨c,sep_mem M hM hS _ e he hQM,fun p => ?_⟩
  rw [ZFSet.mem_sep,eval_prefixFormula 1 2 0 (cons p e) rfl,hQ]
  exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,prefix_subset h.2⟩,h.2⟩⟩

end TuringRigidity.BoundedSetTheory.InternalCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_CollapsePrefixAbsolute
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalCollapse
open TransitiveNameModel
universe u

theorem prefix_mem_without_choice (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hω : ZFSet.omega.{u} ∈ M)
    {A p : ZFSet.{u}} (hA : A ∈ M) (hp : Prefix A p) : p ∈ M := by
  classical
  obtain ⟨n,hp⟩ := hp
  have h0 : (∅ : ZFSet.{u}) ∈ M := hM _ hω _ ZFSet.omega_zero
  cases n with
  | zero =>
    have eq : p = ∅ := by
      apply ZFSet.ext; intro z
      constructor
      · intro hz
        obtain ⟨i,hi,_,_,_⟩ := hp.1 z hz
        exact False.elim (ZFSet.notMem_empty i hi)
      · exact fun hz => False.elim (ZFSet.notMem_empty z hz)
    exact eq ▸ h0
  | succ n =>
    obtain ⟨v,hv,hva⟩ := InternalWellOrder.FunctionGraph.exists_presentation hp
    let f : ℕ → ZFSet.{u} := fun i => if i ≤ n then v (natSet i) else ∅
    have hf : ∀ i, f i ∈ M := by
      intro i
      dsimp only [f]
      split_ifs with hi
      · exact hM A hA _ (hva _ ((natSet_mem_natSet i (n+1)).mpr (by omega)))
      · exact h0
    have eq : p = finiteModelGraph f n := by
      apply ZFSet.ext; intro z
      rw [mem_finiteModelGraph]
      constructor
      · intro hz
        obtain ⟨j,hj,y,_,rfl⟩ := hp.1 z hz
        obtain ⟨i,hi,rfl⟩ := (mem_natSet (n+1) j).mp hj
        have hin : i ≤ n := by omega
        have hy := ((hv.pair_iff _ _).mp hz).2
        exact ⟨i,hin,by rw [hy]; simp only [f,ite_eq_left hin]⟩
      · rintro ⟨i,hi,rfl⟩
        apply (hv.pair_iff _ _).mpr
        exact ⟨(natSet_mem_natSet i (n+1)).mpr (by omega),by simp only [f,ite_eq_left hi]⟩
    rw [eq]
    exact finiteModelGraph_mem M hM hP hU hω f hf n

theorem conditions_exist_absolute_without_choice (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hω : ZFSet.omega.{u} ∈ M) {A : ZFSet.{u}} (hA : A ∈ M) :
    ∃ c ∈ M, ∀ p, p ∈ c ↔ Prefix A p := by
  obtain ⟨c,hc,hcdef⟩ := conditions_exist_without_choice M hM hP hU hPow hS hω hA
  exact ⟨c,hc,fun p => (hcdef p).trans
    ⟨And.right,fun hp => ⟨prefix_mem_without_choice M hM hP hU hω hA hp,hp⟩⟩⟩

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

theorem wordCode_function (s : List Bool) :
    TransitiveNameModel.FunctionGraph (natSet s.length) alphabet (wordCode s) := by
  constructor
  · intro z hz
    obtain ⟨i,rfl⟩ := (mem_wordCode s z).mp hz
    exact ⟨natSet i.val,(natSet_mem_natSet _ _).mpr i.isLt,
      bitSet s[i.val],(mem_alphabet _).mpr ⟨_,rfl⟩,rfl⟩
  · intro x hx
    obtain ⟨n,hn,rfl⟩ := (mem_natSet _ _).mp hx
    refine ⟨bitSet s[n],(mem_alphabet _).mpr ⟨_,rfl⟩,
      (pair_mem_wordCode _ _ _).mpr ⟨hn,rfl⟩,?_⟩
    intro y _ hy
    obtain ⟨i,he⟩ := (mem_wordCode _ _).mp hy
    obtain ⟨hi,hy⟩ := ZFSet.pair_inj.mp he
    have hi' := natSet_injective hi
    simpa only [←hi'] using hy

theorem wordCode_subset_iff (s t : List Bool) : wordCode s ⊆ wordCode t ↔ s <+: t := by
  constructor
  · intro h
    apply List.prefix_iff_getElem.mpr
    have hl : s.length ≤ t.length := by
      by_contra hn
      have hi : t.length < s.length := Nat.lt_of_not_ge hn
      have hh := (pair_mem_wordCode t t.length s[t.length]).mp
        (h ((pair_mem_wordCode s t.length s[t.length]).mpr ⟨hi,rfl⟩))
      exact (Nat.lt_irrefl _) hh.1
    exact ⟨hl,fun i hi => ((pair_mem_wordCode t i s[i]).mp
      (h ((pair_mem_wordCode s i s[i]).mpr ⟨hi,rfl⟩))).2⟩
  · intro h z hz
    obtain ⟨i,rfl⟩ := (mem_wordCode s z).mp hz
    exact (pair_mem_wordCode t _ _).mpr ⟨lt_of_lt_of_le i.isLt h.length_le,
      (List.prefix_iff_getElem.mp h).2 _ i.isLt⟩

theorem wordCode_injective : Function.Injective wordCode := by
  intro s t h
  exact List.Sublist.antisymm
    ((wordCode_subset_iff s t).mp (by rw [h])).sublist
    ((wordCode_subset_iff t s).mp (by rw [h])).sublist

theorem prefix_iff_wordCode (p : ZFSet.{0}) : Prefix alphabet p ↔ ∃ s, wordCode s = p := by
  classical
  constructor
  · rintro ⟨n,hp⟩
    have hv (i : Fin n) : ∃ b : Bool, ZFSet.pair (natSet i.val) (bitSet b) ∈ p := by
      obtain ⟨y,hy,hyf,_⟩ := hp.2 _ ((natSet_mem_natSet _ _).mpr i.isLt)
      obtain ⟨b,rfl⟩ := (mem_alphabet y).mp hy
      exact ⟨b,hyf⟩
    let s := List.ofFn (fun i : Fin n => (hv i).choose)
    have hs : s.length = n := List.length_ofFn
    refine ⟨s,ZFSet.ext (fun z => ?_)⟩
    constructor
    · intro hz
      obtain ⟨i,rfl⟩ := (mem_wordCode _ _).mp hz
      simpa only [s,List.getElem_ofFn] using (hv ⟨i.val,hs ▸ i.isLt⟩).choose_spec
    · intro hz
      obtain ⟨x,hx,y,_,rfl⟩ := hp.1 z hz
      obtain ⟨i,hi,rfl⟩ := (mem_natSet n x).mp hx
      have hv' := (hv ⟨i,hi⟩).choose_spec
      have he := hp.functional ((natSet_mem_natSet _ _).mpr hi) hz hv'
      rw [he]
      exact (mem_wordCode _ _).mpr ⟨⟨i,hs.symm ▸ hi⟩,by simp [s]⟩
  · rintro ⟨s,rfl⟩; exact ⟨s.length,wordCode_function s⟩

attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def encodeCondition (p : Condition) : Conditions conditions :=
  equivShrink conditions ⟨wordCode p.word,(mem_conditions _).mpr ⟨_,wordCode_function _⟩⟩

theorem label_encodeCondition (p : Condition) : label conditions (encodeCondition p) = wordCode p.word := by
  simp [encodeCondition,label]

noncomputable def conditionEquiv : Condition ≃o Conditions conditions := by
  have bijective : Function.Bijective encodeCondition := ⟨by
      intro p q h
      apply Condition.ext
      exact wordCode_injective (by simpa only [label_encodeCondition] using congrArg (label conditions) h),by
      intro q
      obtain ⟨s,hs⟩ := (prefix_iff_wordCode _).mp ((mem_conditions _).mp (label_mem conditions q))
      exact ⟨⟨s⟩,label_injective conditions (by rw [label_encodeCondition]; exact hs)⟩⟩
  refine { Equiv.ofBijective encodeCondition bijective with map_rel_iff' := ?_ }
  intro p q
  change label conditions (encodeCondition q) ⊆ label conditions (encodeCondition p) ↔ _
  rw [label_encodeCondition,label_encodeCondition,wordCode_subset_iff]
  rfl

end TuringRigidity.InternalCohen

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

namespace SentenceForm

def rename (v : ℕ → ℕ) : SentenceForm → SentenceForm
  | .equal i j => .equal (v i) (v j)
  | .member i j => .member (v i) (v j)
  | .conj p q => .conj (p.rename v) (q.rename v)
  | .neg p => .neg (p.rename v)
  | .ex p => .ex (p.rename (fun i => match i with | 0 => 0 | j+1 => v j+1))

end SentenceForm

def Elementary (D : Set ZFSet.{u}) : Prop :=
  ∀ p : SentenceForm, ∀ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ D) →
    (p.Sat D e ↔ p.Sat Set.univ e)

end TuringRigidity.ElementaryModel

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

theorem tupleGraph_function (A : ZFSet.{u}) {n : ℕ} (v : Fin n → ZFSet.{u})
    (hv : ∀ i, v i ∈ A) : FunctionGraph (natSet n) A (tupleGraph v) := by
  constructor
  · intro z hz
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz
    exact ⟨natSet i.val,(natSet_mem_natSet _ _).mpr i.isLt,v i,hv i,rfl⟩
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := (mem_natSet n x).mp hx
    exact ⟨v ⟨i,hi⟩,hv _,(tupleGraph_pair v ⟨i,hi⟩ _).mpr rfl,
      fun y _ hy => (tupleGraph_pair v ⟨i,hi⟩ y).mp hy⟩

theorem functionGraph_tuple (A g : ZFSet.{u}) (n : ℕ)
    (hg : FunctionGraph (natSet n) A g) :
    ∃ v : Fin n → ZFSet.{u}, (∀ i, v i ∈ A) ∧ g = tupleGraph v := by
  classical
  have hex (i : Fin n) := hg.2 (natSet i.val) ((natSet_mem_natSet _ _).mpr i.isLt)
  choose v hv hp hu using hex
  refine ⟨v,hv,?_⟩
  apply ZFSet.ext; intro z
  constructor
  · intro hz
    obtain ⟨x,hx,y,hy,rfl⟩ := hg.1 z hz
    obtain ⟨i,hi,rfl⟩ := (mem_natSet n x).mp hx
    exact (tupleGraph_pair v ⟨i,hi⟩ y).mpr (hu ⟨i,hi⟩ y hy hz)
  · intro hz
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz
    exact hp i

theorem finite_range_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (h0 : (∅ : ZFSet.{u}) ∈ M)
    (n : ℕ) (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ M) : ZFSet.range v ∈ M := by
  induction n with
  | zero =>
    have he : ZFSet.range v = ∅ := by
      apply ZFSet.ext; intro x
      simp only [ZFSet.mem_range,ZFSet.notMem_empty,iff_false]
      rintro ⟨i,_⟩; exact Fin.elim0 i
    rwa [he]
  | succ n ih =>
    have he : ZFSet.range v = ({v 0} : ZFSet.{u}) ∪ ZFSet.range (fun i : Fin n => v i.succ) := by
      apply ZFSet.ext; intro x
      simp only [ZFSet.mem_range,ZFSet.mem_union,ZFSet.mem_singleton,Fin.exists_fin_succ]
      exact or_congr eq_comm Iff.rfl
    rw [he]
    exact binary_union_mem M hM hP hU (singleton_mem M hM hP (hv 0))
      (ih _ (fun i => hv i.succ))

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

theorem mem_finiteSubsets (A x : ZFSet.{u}) :
    x ∈ finiteSubsets A ↔ ∃ (n : ℕ) (v : Fin n → ZFSet.{u}),
      (∀ i, v i ∈ A) ∧ x = ZFSet.range v := by
  rw [finiteSubsets,ZFSet.mem_range]
  constructor
  · rintro ⟨⟨n,v⟩,hx⟩
    exact ⟨n,fun i => label A (v i),fun i => label_mem A (v i),hx.symm⟩
  · rintro ⟨n,v,hv,rfl⟩
    refine ⟨⟨n,fun i => equivShrink A ⟨v i,hv i⟩⟩,?_⟩
    congr 1; funext i; simp [label]

theorem mem_finiteSubsets_iff (A x : ZFSet.{u}) :
    x ∈ finiteSubsets A ↔ x ⊆ A ∧ (x : Set ZFSet.{u}).Finite := by
  rw [mem_finiteSubsets]
  constructor
  · rintro ⟨n,v,hv,rfl⟩
    exact ⟨fun z hz => by obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz; exact hv i,
      by rw [ZFSet.coe_range]; exact Set.finite_range v⟩
  · rintro ⟨hx,hfin⟩
    let : Fintype x := hfin.fintype
    let v : Fin (Fintype.card x) → ZFSet.{u} := fun i => ((Fintype.equivFin x).symm i).val
    refine ⟨_,v,fun i => hx ((Fintype.equivFin x).symm i).property,?_⟩
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_range]
    exact ⟨fun hz => ⟨(Fintype.equivFin x) ⟨z,hz⟩,by simp [v]⟩,
      fun ⟨i,hi⟩ => hi ▸ ((Fintype.equivFin x).symm i).property⟩

theorem rangeFormula_spec (o A x g : ℕ) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega) {n : ℕ} {v : Fin n → ZFSet.{u}}
    (hv : ∀ i, v i ∈ e A) (hg : e g = tupleGraph v) :
    (rangeFormula o A x g).Eval e ↔ e x = ZFSet.range v := by
  simp only [rangeFormula,Formula.Eval,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,Formula.eval_pairMem,cons_zero,cons_succ]
  rw [ho,hg]
  have hr (z : ZFSet.{u}) : (∃ i ∈ ZFSet.omega, ZFSet.pair i z ∈ tupleGraph v) ↔
      z ∈ ZFSet.range v := by
    constructor
    · rintro ⟨i,_,hi⟩
      obtain ⟨j,hj⟩ := ZFSet.mem_range.mp hi
      exact ZFSet.mem_range.mpr ⟨j,(ZFSet.pair_inj.mp hj).2⟩
    · rintro hz
      obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz
      exact ⟨natSet i.val,(mem_omega _).mpr ⟨i.val,rfl⟩,(tupleGraph_pair v i _).mpr rfl⟩
  constructor
  · rintro ⟨hsub,h⟩
    apply ZFSet.ext; intro z
    constructor
    · intro hz; exact (hr z).mp ((h z (hsub hz)).mp hz)
    · intro hz
      have hzA : z ∈ e A := by obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz; exact hv i
      exact (h z hzA).mpr ((hr z).mpr hz)
  · intro he
    refine ⟨fun z hz => ?_,fun z _ => ?_⟩
    · rw [he] at hz; obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz; exact hv i
    · rw [he]; exact (hr z).symm

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

theorem graph_isCondition (A : ZFSet.{0}) (p : Condition (Conditions A)) :
    IsCondition A (graph A p) := by
  constructor
  · apply (mem_finiteSubsets_iff _ _).mpr
    constructor
    · intro z hz
      obtain ⟨i,b,_,rfl⟩ := (mem_graph A p z).mp hz
      exact ZFSet.mem_prod.mpr ⟨_,label_mem A i,_,(mem_alphabet _).mpr ⟨b,rfl⟩,rfl⟩
    · rw [graph,ZFSet.coe_range]; exact Set.finite_range _
  · intro x hx b hb c hc hpb hpc
    obtain ⟨b,rfl⟩ := (mem_alphabet _).mp hb
    obtain ⟨c,rfl⟩ := (mem_alphabet _).mp hc
    let i : Conditions A := equivShrink A ⟨x,hx⟩
    have hi : label A i = x := by simp [i,label]
    rw [←hi,pair_mem_graph] at hpb hpc
    exact congrArg bitSet (Option.some.inj (hpb.symm.trans hpc))

theorem isCondition_iff_graph (A x : ZFSet.{0}) :
    IsCondition A x ↔ ∃ p : Condition (Conditions A), graph A p = x := by
  classical
  constructor
  · intro hx
    have hsub := ((mem_finiteSubsets_iff _ _).mp hx.1).1
    have hfin := ((mem_finiteSubsets_iff _ _).mp hx.1).2
    let v (i : Conditions A) : Option Bool :=
      if h : ∃ b, ZFSet.pair (label A i) (bitSet b) ∈ x then some h.choose else none
    have hv (i : Conditions A) (b : Bool) :
        v i = some b ↔ ZFSet.pair (label A i) (bitSet b) ∈ x := by
      dsimp only [v]
      split_ifs with h
      · constructor
        · intro he; exact Option.some.inj he ▸ h.choose_spec
        · intro hb
          have he := hx.2 _ (label_mem A i) _ ((mem_alphabet _).mpr ⟨h.choose,rfl⟩)
            _ ((mem_alphabet _).mpr ⟨b,rfl⟩) h.choose_spec hb
          exact congrArg some (bitSet_injective he)
      · constructor
        · intro he; cases he
        · intro hb; exact False.elim (h ⟨b,hb⟩)
    have hfinite : {i | v i ≠ none}.Finite := by
      let f (i : Conditions A) := ZFSet.pair (label A i) (bitSet ((v i).getD false))
      have hf : Function.Injective f := by
        intro i j he; exact label_injective A (ZFSet.pair_inj.mp he).1
      apply (hfin.preimage hf.injOn).subset
      intro i hi
      change f i ∈ x
      apply (hv i _).mp
      cases he : v i with
      | none => exact False.elim (hi he)
      | some b => rfl
    let p : Condition (Conditions A) := ⟨v,hfinite⟩
    refine ⟨p,ZFSet.ext (fun z => ?_)⟩
    constructor
    · intro hz
      obtain ⟨i,b,hi,rfl⟩ := (mem_graph A p z).mp hz
      exact (hv i b).mp hi
    · intro hz
      obtain ⟨i,hi,b,hb,rfl⟩ := ZFSet.mem_prod.mp (hsub hz)
      obtain ⟨b,rfl⟩ := (mem_alphabet _).mp hb
      let j : Conditions A := equivShrink A ⟨i,hi⟩
      have hj : label A j = i := by simp [j,label]
      rw [←hj]
      exact (pair_mem_graph A p j b).mpr ((hv j b).mpr (hj ▸ hz))
  · rintro ⟨p,rfl⟩; exact graph_isCondition A p

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

theorem singleValuedFormula_spec (A B p : ℕ) (e : ℕ → ZFSet.{0}) (hB : e B = alphabet) :
    (singleValuedFormula A B p).Eval e ↔ SingleValued (e A) (e p) := by
  simp only [singleValuedFormula,Formula.eval_allMem,Formula.eval_imp,
    Formula.eval_pairMem,Formula.Eval,cons_zero,cons_succ,hB,SingleValued]

noncomputable def encode (A : ZFSet.{0}) (p : Condition (Conditions A)) : Conditions (conditions A) :=
  equivShrink (conditions A) ⟨graph A p,(mem_conditions A _).mpr (graph_isCondition A p)⟩

theorem label_encode (A : ZFSet.{0}) (p : Condition (Conditions A)) :
    label (conditions A) (encode A p) = graph A p := by simp [encode,label]

noncomputable def conditionEquiv (A : ZFSet.{0}) :
    Condition (Conditions A) ≃o Conditions (conditions A) :=
  { Equiv.ofBijective (encode A) ⟨by
      intro p q h
      exact graph_injective A (by simpa only [label_encode] using congrArg (label (conditions A)) h),by
      intro q
      obtain ⟨p,hp⟩ := (isCondition_iff_graph A _).mp ((mem_conditions A _).mp (label_mem _ q))
      exact ⟨p,label_injective _ (by rw [label_encode]; exact hp)⟩⟩ with
    map_rel_iff' := by
      intro p q
      change label _ (encode A q) ⊆ label _ (encode A p) ↔ _
      rw [label_encode,label_encode,graph_subset_iff] }

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
open Set TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AutomorphismName
open CohenSymmetry CohenConditionCode CohenGroundPoset
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem empty_mem_conditions (A : ZFSet.{0}) : (∅ : ZFSet.{0}) ∈ conditions A := by
  have he : graph A (⊤ : Condition (Conditions A)) = ∅ := by
    apply ZFSet.ext; intro z
    rw [mem_graph]
    constructor
    · rintro ⟨i,b,hi,_⟩; cases hi
    · intro hz; exact False.elim (ZFSet.notMem_empty _ hz)
  rw [←he]
  exact (mem_conditions A _).mpr (graph_isCondition A _)

end TuringRigidity.CohenGroundGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_IndexPresentation
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IndexPresentation
open Encodable TableIndices IndexMatrix OrderNormalForm

theorem value_surjective (Y : Oracle) (x : Degree) (hx : x ≤ degree Y) :
    ∃ e, Dom Y e ∧ value Y e = x := by
  obtain ⟨A, rfl⟩ := degree_surjective x
  obtain ⟨d, hd⟩ := reduces_represents hx
  have hr : Represents Y (machine (encode d)) A := by simpa using hd
  exact ⟨encode d, (valid_iff_represents _ _).mpr ⟨A, hr⟩, value_eq hr⟩

end TuringRigidity.IndexPresentation

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

theorem form_recursive {Y n s P} (h : Form Y n s P) : RecursivePred (iterate Y n) P := by
  induction n generalizing s P with
  | zero => exact h
  | succ n ih =>
    obtain ⟨Q,hQ,he⟩ := h
    have hr := ih hQ
    cases s with
    | false =>
      have hh := forall_recursive_jump hr
      have he' : (fun x => ∀ a, Q (Nat.pair x a)) = P := funext (fun x => propext (he x).symm)
      exact he' ▸ hh
    | true =>
      have hh := exists_recursive_jump hr
      have he' : (fun x => ∃ a, Q (Nat.pair x a)) = P := funext (fun x => propext (he x).symm)
      exact he' ▸ hh

end TuringRigidity.OracleJump

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

theorem finiteNaturalGraph_function (f : ℕ → ℕ) (n : ℕ) :
    TransitiveNameModel.FunctionGraph (natSet (n+1)) ZFSet.omega (finiteNaturalGraph.{u} f n) := by
  constructor
  · intro z hz
    obtain ⟨i,hi,rfl⟩ := (mem_finiteNaturalGraph f n z).mp hz
    exact ⟨natSet i,(natSet_mem_natSet i (n+1)).mpr (by omega),natSet (f i),
      (mem_omega _).mpr ⟨f i,rfl⟩,rfl⟩
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := (mem_natSet (n+1) x).mp hx
    have hin : i ≤ n := by omega
    refine ⟨natSet (f i),(mem_omega _).mpr ⟨f i,rfl⟩,
      (finiteNaturalGraph_pair f n i _).mpr ⟨hin,rfl⟩,?_⟩
    intro y _ hy
    exact ((finiteNaturalGraph_pair f n i y).mp hy).2

theorem finiteNaturalGraph_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hω : ZFSet.omega.{u} ∈ M)
    (f : ℕ → ℕ) (n : ℕ) : finiteNaturalGraph f n ∈ M := by
  have hn (i : ℕ) : natSet.{u} i ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨i,rfl⟩)
  induction n with
  | zero => exact singleton_mem M hM hP (orderedPair_mem M hM hP (hn 0) (hn (f 0)))
  | succ n ih =>
    exact binary_union_mem M hM hP hU ih
      (singleton_mem M hM hP (orderedPair_mem M hM hP (hn (n+1)) (hn (f (n+1)))))

theorem internal_finite_natural_graph_bound (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hω : ZFSet.omega.{u} ∈ M) :
    ∃ Q ∈ M, (∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ ZFSet.prod ZFSet.omega ZFSet.omega) ∧
      ∀ f : ℕ → ℕ, ∀ n, finiteNaturalGraph f n ∈ Q := by
  obtain ⟨Q,hQ,hQdef⟩ := internal_power M hM hPow (product_mem M hM hP hU hPow hS hω hω)
  refine ⟨Q,hQ,hQdef,?_⟩
  intro f n
  apply (hQdef _).mpr
  refine ⟨finiteNaturalGraph_mem M hM hP hU hω f n,?_⟩
  intro z hz
  obtain ⟨i,_,rfl⟩ := (mem_finiteNaturalGraph f n z).mp hz
  exact ZFSet.mem_prod.mpr ⟨_,(mem_omega _).mpr ⟨i,rfl⟩,_,(mem_omega _).mpr ⟨f i,rfl⟩,rfl⟩

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

theorem additionTrace_exists (a n : ℕ) :
    AdditionTrace ZFSet.omega (natSet 0) (natSet (n+1)) (natSet n) (natSet a)
      (finiteNaturalGraph.{u} (fun i => a+i) n) := by
  refine ⟨finiteNaturalGraph_function _ n,rfl,rfl,?_,?_⟩
  · exact (finiteNaturalGraph_pair _ n 0 _).mpr ⟨Nat.zero_le _,by simp⟩
  · intro i hi j _ hj v _ w _ hiv hjw
    obtain ⟨i,hi,rfl⟩ := (mem_natSet n i).mp hi
    have hj' : j = natSet (i+1) := hj
    subst j
    have hv := ((finiteNaturalGraph_pair _ n i v).mp hiv).2
    have hw := ((finiteNaturalGraph_pair _ n (i+1) w).mp hjw).2
    rw [hv,hw,Nat.add_succ]
    rfl

theorem AdditionTrace.correct {z k f : ZFSet.{u}} (a n : ℕ)
    (hf : AdditionTrace ZFSet.omega z k (natSet n) (natSet a) f)
    {y : ZFSet.{u}} (hy : ZFSet.pair (natSet n) y ∈ f) : y = natSet (a+n) := by
  obtain ⟨hfun,hk,rfl,hzero,hstep⟩ := hf
  have hk' : k = natSet (n+1) := hk
  subst k
  have computes (i : ℕ) (hi : i ≤ n) : ZFSet.pair (natSet i) (natSet (a+i)) ∈ f := by
    induction i with
    | zero => simpa only [Nat.add_zero,natSet] using hzero
    | succ i ih =>
      have hin : i ≤ n := by omega
      have hj : natSet.{u} (i+1) ∈ natSet (n+1) := (natSet_mem_natSet _ _).mpr (by omega)
      obtain ⟨w,hw,hjw,_⟩ := hfun.2 _ hj
      have he := hstep (natSet i) ((natSet_mem_natSet _ _).mpr (by omega)) (natSet (i+1))
        ((mem_omega _).mpr ⟨i+1,rfl⟩) rfl (natSet (a+i)) ((mem_omega _).mpr ⟨a+i,rfl⟩)
        w hw (ih hin) hjw
      have he' : w = natSet (a+(i+1)) := by
        rw [Nat.add_succ]
        exact he
      exact he' ▸ hjw
  exact hfun.functional ((natSet_mem_natSet n (n+1)).mpr (Nat.lt_succ_self n)) hy (computes n le_rfl)

theorem additionFormula_correct (Q : ZFSet.{u})
    (hQ : ∀ f : ℕ → ℕ, ∀ n, finiteNaturalGraph f n ∈ Q) (a n : ℕ) (y : ZFSet.{u}) :
    (Formula.addition 3 4 1 2 0).Eval (cons y (cons (natSet a) (cons (natSet n)
      (cons ZFSet.omega (fun _ => Q))))) ↔ y = natSet (a+n) := by
  rw [Formula.eval_addition]
  simp only [cons_zero,cons_succ]
  constructor
  · rintro ⟨k,_,z,_,f,_,hf,hy⟩
    exact hf.correct a n hy
  · intro hy
    refine ⟨natSet (n+1),(mem_omega _).mpr ⟨n+1,rfl⟩,natSet 0,
      (mem_omega _).mpr ⟨0,rfl⟩,finiteNaturalGraph (fun i => a+i) n,hQ _ _,additionTrace_exists a n,?_⟩
    exact (finiteNaturalGraph_pair _ n n y).mpr ⟨le_rfl,hy⟩

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

theorem iterationTrace_exists (b : ℕ) (g : ℕ → ℕ → ℕ)
    (S : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hS : ∀ i v, S (natSet i) (natSet v) (natSet (g i v))) (n : ℕ) :
    IterationTrace ZFSet.omega (natSet 0) (natSet (n+1)) (natSet n) (natSet b)
      (finiteNaturalGraph (fun i => Nat.rec b g i) n) S := by
  refine ⟨finiteNaturalGraph_function _ n,rfl,rfl,?_,?_⟩
  · exact (finiteNaturalGraph_pair _ n 0 _).mpr ⟨Nat.zero_le _,rfl⟩
  · intro i hi j _ hj v _ w _ hiv hjw
    obtain ⟨i,_,rfl⟩ := (mem_natSet n i).mp hi
    have hj' : j = natSet (i+1) := hj
    subst j
    rw [((finiteNaturalGraph_pair _ n i v).mp hiv).2,
      ((finiteNaturalGraph_pair _ n (i+1) w).mp hjw).2]
    exact hS i (Nat.rec b g i)

theorem IterationTrace.correct {z k f : ZFSet.{u}} (b n : ℕ) (g : ℕ → ℕ → ℕ)
    (S : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hS : ∀ i v w, S (natSet i) (natSet v) w → w = natSet (g i v))
    (hf : IterationTrace ZFSet.omega z k (natSet n) (natSet b) f S)
    {y : ZFSet.{u}} (hy : ZFSet.pair (natSet n) y ∈ f) : y = natSet (Nat.rec b g n) := by
  obtain ⟨hfun,hk,rfl,hzero,hstep⟩ := hf
  have hk' : k = natSet (n+1) := hk
  subst k
  have computes (i : ℕ) (hi : i ≤ n) : ZFSet.pair (natSet i) (natSet (Nat.rec b g i)) ∈ f := by
    induction i with
    | zero => exact hzero
    | succ i ih =>
      have hin : i ≤ n := by omega
      have hj : natSet.{u} (i+1) ∈ natSet (n+1) := (natSet_mem_natSet _ _).mpr (by omega)
      obtain ⟨w,hw,hjw,_⟩ := hfun.2 _ hj
      have hs := hstep (natSet i) ((natSet_mem_natSet _ _).mpr (by omega)) (natSet (i+1))
        ((mem_omega _).mpr ⟨i+1,rfl⟩) rfl (natSet (Nat.rec b g i))
        ((mem_omega _).mpr ⟨Nat.rec b g i,rfl⟩) w hw (ih hin) hjw
      have he : w = natSet (Nat.rec b g (i+1)) := hS i (Nat.rec b g i) w hs
      exact he ▸ hjw
  exact hfun.functional ((natSet_mem_natSet n (n+1)).mpr (Nat.lt_succ_self n)) hy (computes n le_rfl)

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

theorem addition_spec (o Q x n y : ℕ) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega) (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (a b : ℕ) (ha : e x = natSet a) (hb : e n = natSet b) :
    (addition o Q x n y).Eval e ↔ e y = natSet (a+b) := by
  have h := additionFormula_correct (e Q) hQ a b (e y)
  rw [eval_addition] at h
  simp only [cons_zero,cons_succ] at h
  rw [eval_addition,ho,ha,hb]
  exact h

theorem iteration_spec (o Q n b y : ℕ) (θ : Formula) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega) (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (N B : ℕ) (hn : e n = natSet N) (hb : e b = natSet B) (g : ℕ → ℕ → ℕ)
    (hθ : ∀ i v w, θ.Eval (cons w (cons (natSet v) (cons (natSet i) e))) ↔ w = natSet (g i v)) :
    (iteration o Q n b y θ).Eval e ↔ e y = natSet (Nat.rec B g N) := by
  rw [eval_iteration,ho,hn,hb]
  constructor
  · rintro ⟨k,_,z,_,f,_,hf,hy⟩
    exact hf.correct B N g _ (fun i v w h => (hθ i v w).mp h) hy
  · intro hy
    refine ⟨natSet (N+1),(mem_omega _).mpr ⟨N+1,rfl⟩,natSet 0,(mem_omega _).mpr ⟨0,rfl⟩,
      finiteNaturalGraph (fun i => Nat.rec B g i) N,hQ _ _,?_,?_⟩
    · exact iterationTrace_exists B g _ (fun i v => (hθ i v _).mpr rfl) N
    · exact (finiteNaturalGraph_pair _ N N _).mpr ⟨le_rfl,hy⟩

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

theorem multiplication_spec (o Q x n y : ℕ) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega) (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (a b : ℕ) (ha : e x = natSet a) (hb : e n = natSet b) :
    (multiplication o Q x n y).Eval e ↔ e y = natSet (a*b) := by
  have hθ (i v : ℕ) (w : ZFSet.{u}) :
      (addition (o+4) (Q+4) 1 (x+4) 0).Eval
        (cons w (cons (natSet v) (cons (natSet i) (cons ∅ e)))) ↔ w = natSet (v+a) := by
    apply addition_spec (o+4) (Q+4) 1 (x+4) 0
      (cons w (cons (natSet v) (cons (natSet i) (cons ∅ e))))
      (by simpa only [cons_succ] using ho)
      (by intro f k; simpa only [cons_succ] using hQ f k) v a rfl
    simpa only [cons_succ] using ha
  have hi := iteration_spec (o+1) (Q+1) (n+1) 0 (y+1)
    (addition (o+4) (Q+4) 1 (x+4) 0) (cons ∅ e)
    (by simpa only [cons_succ] using ho)
    (by intro f k; simpa only [cons_succ] using hQ f k) b 0
    (by simpa only [cons_succ] using hb) rfl (fun _ v => v+a) hθ
  simp only [cons_succ,nat_iteration_add] at hi
  simp only [multiplication,Formula.Eval,eval_empty,cons_zero]
  constructor
  · rintro ⟨z,_,rfl,h⟩
    exact hi.mp h
  · intro h
    exact ⟨∅,ho.symm ▸ ZFSet.omega_zero,rfl,hi.mpr h⟩

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

theorem operation_spec (m : Bool) (o Q x n y : ℕ) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega) (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (a b : ℕ) (ha : e x = natSet a) (hb : e n = natSet b) :
    (operation m o Q x n y).Eval e ↔ e y = natSet (if m then a*b else a+b) := by
  cases m with
  | false => exact Formula.addition_spec o Q x n y e ho hQ a b ha hb
  | true => exact Formula.multiplication_spec o Q x n y e ho hQ a b ha hb

theorem graph_spec (t : NaturalTerm) (o Q y : ℕ) (v : ℕ → ℕ) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega) (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (a : ℕ → ℕ) (ha : ∀ i, e (v i) = natSet (a i)) :
    (graph o Q y v t).Eval e ↔ e y = natSet (t.eval a) := by
  induction t generalizing o Q y v e with
  | var i => exact congrArg (fun z => e y = z) (ha i) |>.to_iff
  | binary m t s iht ihs =>
    have hωmem (k : ℕ) : natSet.{u} k ∈ e o := by
      rw [ho]; exact (mem_omega _).mpr ⟨k,rfl⟩
    have ht (w z : ZFSet.{u}) :
        (graph (o+2) (Q+2) 1 (fun i => v i+2) t).Eval (cons z (cons w e)) ↔ w = natSet (t.eval a) :=
      iht (o+2) (Q+2) 1 (fun i => v i+2) (cons z (cons w e)) ho hQ ha
    have hs (w z : ZFSet.{u}) :
        (graph (o+2) (Q+2) 0 (fun i => v i+2) s).Eval (cons z (cons w e)) ↔ z = natSet (s.eval a) :=
      ihs (o+2) (Q+2) 0 (fun i => v i+2) (cons z (cons w e)) ho hQ ha
    have hop := operation_spec m (o+2) (Q+2) 1 0 (y+2)
      (cons (natSet (s.eval a)) (cons (natSet (t.eval a)) e)) ho hQ (t.eval a) (s.eval a) rfl rfl
    simp only [graph,Formula.Eval]
    constructor
    · rintro ⟨w,_,z,_,hw,hz,h⟩
      obtain rfl := (ht w z).mp hw
      obtain rfl := (hs _ z).mp hz
      exact hop.mp h
    · intro h
      refine ⟨natSet (t.eval a),hωmem (t.eval a),
        natSet (s.eval a),hωmem (s.eval a),
        (ht _ _).mpr rfl,(hs _ _).mpr rfl,hop.mpr h⟩

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

theorem naturalPair_spec (o Q x n y : ℕ) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega) (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (a b : ℕ) (ha : e x = natSet a) (hb : e n = natSet b) :
    (naturalPair o Q x n y).Eval e ↔ e y = natSet (Nat.pair a b) := by
  have hv : ∀ i, e (pairVars x n i) = natSet (pairVars a b i) := by
    intro i; cases i <;> assumption
  have hl := NaturalTerm.graph_spec pairLeftTerm o Q y (pairVars x n) e ho hQ (pairVars a b) hv
  have hr := NaturalTerm.graph_spec pairRightTerm o Q y (pairVars x n) e ho hQ (pairVars a b) hv
  change (pairLeftTerm.graph o Q y (pairVars x n)).Eval e ↔ e y = natSet (b*b+a) at hl
  change (pairRightTerm.graph o Q y (pairVars x n)).Eval e ↔ e y = natSet (a*a+a+b) at hr
  simp only [naturalPair,eval_disj,Formula.Eval,hl,hr,ha,hb,natSet_mem_natSet,Nat.pair]
  by_cases h : a < b <;> simp [h]

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

theorem pairedUnary_spec {φ : Formula} {f : ℕ → ℕ} (hφ : DefinesNatural.{u} φ f)
    (o Q x n y : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ g : ℕ → ℕ, ∀ k, finiteNaturalGraph g k ∈ e Q)
    (a b : ℕ) (ha : e x = natSet a) (hb : e n = natSet b) :
    (pairedUnary φ o Q x n y).Eval e ↔ e y = natSet (f (Nat.pair a b)) := by
  have hp (w : ZFSet.{u}) := naturalPair_spec (o+1) (Q+1) (x+1) (n+1) 0 (cons w e) ho hQ a b ha hb
  have hu := unary_spec hφ (o+1) (Q+1) 0 (y+1) (cons (natSet (Nat.pair a b)) e) ho hQ (Nat.pair a b) rfl
  simp only [pairedUnary,Formula.Eval]
  constructor
  · rintro ⟨w,_,hw,h⟩
    obtain rfl := (hp w).mp hw
    exact hu.mp h
  · intro h
    refine ⟨natSet (Nat.pair a b),?_,(hp _).mpr rfl,hu.mpr h⟩
    rw [ho]; exact (mem_omega _).mpr ⟨Nat.pair a b,rfl⟩
end Formula

theorem DefinesNatural.pair {φ ψ : Formula} {f g : ℕ → ℕ}
    (hf : DefinesNatural.{u} φ f) (hg : DefinesNatural.{u} ψ g) :
    DefinesNatural.{u} (Formula.numericPair φ ψ) (fun n => Nat.pair (f n) (g n)) := by
  intro e ho hQ n hn
  have hv (w z : ZFSet.{u}) := Formula.unary_spec hf 4 5 3 1 (cons z (cons w e)) ho hQ n hn
  have hw (w z : ZFSet.{u}) := Formula.unary_spec hg 4 5 3 0 (cons z (cons w e)) ho hQ n hn
  have hp := Formula.naturalPair_spec 4 5 1 0 2 (cons (natSet (g n)) (cons (natSet (f n)) e))
    ho hQ (f n) (g n) rfl rfl
  have hmem (k : ℕ) : natSet.{u} k ∈ e 2 := by rw [ho]; exact (mem_omega _).mpr ⟨k,rfl⟩
  simp only [Formula.numericPair,Formula.Eval]
  constructor
  · rintro ⟨w,_,z,_,hvw,hwz,h⟩
    obtain rfl := (hv w z).mp hvw
    obtain rfl := (hw _ z).mp hwz
    exact hp.mp h
  · intro h
    exact ⟨natSet (f n),hmem _,natSet (g n),hmem _,(hv _ _).mpr rfl,(hw _ _).mpr rfl,hp.mpr h⟩

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

theorem naturalProjection_spec (right : Bool) : DefinesNatural.{u} (naturalProjection right)
    (fun n => if right then (Nat.unpair n).2 else (Nat.unpair n).1) := by
  intro e ho hQ n hn
  have select (a b : ZFSet.{u}) : cons b (cons a e) (if right then 0 else 1) =
      if right then b else a := by cases right <;> rfl
  have hmem (k : ℕ) : natSet.{u} k ∈ e 2 := by rw [ho]; exact (mem_omega _).mpr ⟨k,rfl⟩
  simp only [naturalProjection,Formula.Eval,cons_succ,select]
  constructor
  · rintro ⟨a,ha,b,hb,hpair,hy⟩
    rw [ho] at ha hb
    obtain ⟨a,rfl⟩ := (mem_omega a).mp ha
    obtain ⟨b,rfl⟩ := (mem_omega b).mp hb
    have hp := (naturalPair_spec 4 5 1 0 3 (cons (natSet b) (cons (natSet a) e))
      ho hQ a b rfl rfl).mp hpair
    have he : n = Nat.pair a b := natSet_injective (hn.symm.trans hp)
    subst n
    cases right <;> simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.unpair_pair] using hy
  · intro hy
    refine ⟨natSet (Nat.unpair n).1,hmem _,natSet (Nat.unpair n).2,hmem _,?_,?_⟩
    · apply (naturalPair_spec 4 5 1 0 3
        (cons (natSet (Nat.unpair n).2) (cons (natSet (Nat.unpair n).1) e))
        ho hQ _ _ rfl rfl).mpr
      simpa only [cons_succ,Nat.pair_unpair] using hn
    · cases right <;> simpa only [Bool.false_eq_true,ite_false,ite_true] using hy

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

theorem primitiveStep_spec {ψ : Formula} {g : ℕ → ℕ} (hg : DefinesNatural.{u} ψ g)
    (e : ℕ → ZFSet.{u}) (ho : e 5 = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e 6) (z : ℕ) (hz : e 2 = natSet z)
    (i v : ℕ) (w : ZFSet.{u}) :
    (primitiveStep ψ).Eval (cons w (cons (natSet v) (cons (natSet i) e))) ↔
      w = natSet (g (Nat.pair z (Nat.pair i v))) := by
  let E := cons w (cons (natSet v) (cons (natSet i) e))
  have hp (t : ZFSet.{u}) := naturalPair_spec 9 10 3 2 0 (cons t E) ho hQ i v rfl rfl
  have hu := pairedUnary_spec hg 9 10 6 0 1 (cons (natSet (Nat.pair i v)) E)
    ho hQ z (Nat.pair i v) hz rfl
  simp only [primitiveStep,Formula.Eval]
  constructor
  · rintro ⟨t,_,ht,h⟩
    obtain rfl := (hp t).mp ht
    exact hu.mp h
  · intro h
    refine ⟨natSet (Nat.pair i v),?_,(hp _).mpr rfl,hu.mpr h⟩
    change natSet (Nat.pair i v) ∈ e 5
    rw [ho]; exact (mem_omega _).mpr ⟨Nat.pair i v,rfl⟩
end Formula

theorem DefinesNatural.prec {φ ψ : Formula} {f g : ℕ → ℕ}
    (hf : DefinesNatural.{u} φ f) (hg : DefinesNatural.{u} ψ g) :
    DefinesNatural.{u} (Formula.primitiveRecursion φ ψ)
      (Nat.unpaired fun z n => Nat.rec (f z) (fun i v => g (Nat.pair z (Nat.pair i v))) n) := by
  intro e ho hQ N hn
  have hmem (k : ℕ) : natSet.{u} k ∈ e 2 := by rw [ho]; exact (mem_omega _).mpr ⟨k,rfl⟩
  have decode (x : ZFSet.{u}) (hx : x ∈ e 2) : ∃ n, x = natSet n := by
    rw [ho] at hx; exact (mem_omega x).mp hx
  have hp (z n : ℕ) (b : ZFSet.{u}) := Formula.naturalPair_spec 5 6 2 1 4
    (cons b (cons (natSet n) (cons (natSet z) e))) ho hQ z n rfl rfl
  have hb (z n : ℕ) (b : ZFSet.{u}) := Formula.unary_spec hf 5 6 2 0
    (cons b (cons (natSet n) (cons (natSet z) e))) ho hQ z rfl
  have hi (z n : ℕ) := Formula.iteration_spec 5 6 1 0 3 (Formula.primitiveStep ψ)
    (cons (natSet (f z)) (cons (natSet n) (cons (natSet z) e))) ho hQ n (f z) rfl rfl
    (fun i v => g (Nat.pair z (Nat.pair i v)))
    (Formula.primitiveStep_spec hg _ ho hQ z rfl)
  simp only [Formula.primitiveRecursion,Formula.Eval]
  constructor
  · rintro ⟨z,hz,n,hnum,b,_,hp',hb',hi'⟩
    obtain ⟨z,rfl⟩ := decode z hz
    obtain ⟨n,rfl⟩ := decode n hnum
    have hN : N = Nat.pair z n := natSet_injective (hn.symm.trans ((hp z n b).mp hp'))
    obtain rfl := (hb z n b).mp hb'
    have h := (hi z n).mp hi'
    simpa only [cons_succ,hN,Nat.unpaired,Nat.unpair_pair] using h
  · intro h
    let z := (Nat.unpair N).1
    let n := (Nat.unpair N).2
    refine ⟨natSet z,hmem _,natSet n,hmem _,natSet (f z),hmem _,?_,(hb z n _).mpr rfl,?_⟩
    · apply (hp z n _).mpr
      simpa only [cons_succ,z,n,Nat.pair_unpair] using hn
    · apply (hi z n).mpr
      exact h

theorem primitive_bounded_definition {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ∃ φ : Formula, DefinesNatural.{u} φ f := by
  induction hf with
  | zero => exact ⟨.empty 0,definesNatural_zero⟩
  | succ => exact ⟨.successor 0 1,definesNatural_succ⟩
  | left => exact ⟨.naturalProjection false,Formula.naturalProjection_spec false⟩
  | right => exact ⟨.naturalProjection true,Formula.naturalProjection_spec true⟩
  | pair _ _ ihf ihg =>
    obtain ⟨φ,hφ⟩ := ihf; obtain ⟨ψ,hψ⟩ := ihg
    exact ⟨.numericPair φ ψ,hφ.pair hψ⟩
  | comp _ _ ihf ihg =>
    obtain ⟨φ,hφ⟩ := ihf; obtain ⟨ψ,hψ⟩ := ihg
    exact ⟨.numericComposition φ ψ,hφ.comp hψ⟩
  | prec _ _ ihf ihg =>
    obtain ⟨φ,hφ⟩ := ihf; obtain ⟨ψ,hψ⟩ := ihg
    exact ⟨.primitiveRecursion φ ψ,hφ.prec hψ⟩

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

theorem primitive_predicate_bounded {P : ℕ → Prop} (hP : PrimrecPred P) :
    ∃ φ : Formula, DefinesPredicate.{u} φ P := by
  obtain ⟨inst,hP⟩ := hP
  let : DecidablePred P := inst
  let f := fun n => Encodable.encode (decide (P n))
  have hf : Nat.Primrec f := Primrec.nat_iff.mp (Primrec.encode.comp hP)
  obtain ⟨φ,hφ⟩ := primitive_bounded_definition.{u} hf
  refine ⟨φ.numericalPredicate,?_⟩
  intro e ho hQ n hn
  have hw (w : ZFSet.{u}) := Formula.unary_spec hφ 2 3 1 0 (cons w e) ho hQ n hn
  have htest : (natSet.{u} (f n) ≠ ∅) ↔ P n := by
    change (natSet.{u} (f n) ≠ natSet 0) ↔ P n
    rw [natSet_injective.ne_iff]
    dsimp [f]
    by_cases h : P n <;> simp [h]
  simp only [Formula.numericalPredicate,Formula.Eval,Formula.eval_empty,cons_zero]
  constructor
  · rintro ⟨w,_,hf',hne⟩
    obtain rfl := (hw w).mp hf'
    exact htest.mp hne
  · intro h
    refine ⟨natSet (f n),?_,(hw _).mpr rfl,htest.mpr h⟩
    rw [ho]; exact (mem_omega _).mpr ⟨f n,rfl⟩

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

noncomputable def arithmeticEnv (Q : ZFSet.{u}) (O : Oracles) (n : ℕ) : ℕ → ZFSet.{u} :=
  cons (natSet n) (cons ZFSet.omega (cons Q (fun i => realCode (O i))))

def DefinesArithmetic (φ : Formula) (P : Predicate) : Prop :=
  ∀ Q : ZFSet.{u}, (∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ Q) → ∀ O n,
    (φ.Eval (arithmeticEnv Q O n) ↔ P O n)

namespace Formula

theorem eval_arithmetic_shift_one (φ : Formula) (Q : ZFSet.{u}) (O : Oracles) (n m : ℕ) :
    (φ.rename (arithmeticVars 1)).Eval (cons (natSet m) (arithmeticEnv Q O n)) ↔
      φ.Eval (arithmeticEnv Q O m) := by
  rw [eval_rename]
  have he : (fun i => cons (natSet m) (arithmeticEnv Q O n) (arithmeticVars 1 i)) = arithmeticEnv Q O m := by
    funext i; cases i <;> rfl
  rw [he]

theorem eval_arithmetic_shift_two (φ : Formula) (Q : ZFSet.{u}) (O : Oracles) (n k m : ℕ) :
    (φ.rename (arithmeticVars 2)).Eval (cons (natSet m) (cons (natSet k) (arithmeticEnv Q O n))) ↔
      φ.Eval (arithmeticEnv Q O m) := by
  rw [eval_rename]
  have he : (fun i => cons (natSet m) (cons (natSet k) (arithmeticEnv Q O n)) (arithmeticVars 2 i)) =
      arithmeticEnv Q O m := by
    funext i; cases i <;> rfl
  rw [he]

end Formula

theorem DefinesArithmetic.existsNat {φ : Formula} {P : Predicate} (hφ : DefinesArithmetic.{u} φ P) :
    DefinesArithmetic.{u} φ.arithmeticExists (fun O n => ∃ k, P O (Nat.pair n k)) := by
  intro Q hQ O n
  have hp (k : ℕ) (w : ZFSet.{u}) := Formula.naturalPair_spec 3 4 2 1 0
    (cons w (cons (natSet k) (arithmeticEnv Q O n))) rfl hQ n k rfl rfl
  simp only [Formula.arithmeticExists,Formula.Eval,arithmeticEnv,cons_zero,cons_succ]
  constructor
  · rintro ⟨x,hx,w,_,hpair,h⟩
    obtain ⟨k,rfl⟩ := (mem_omega x).mp hx
    obtain rfl := (hp k w).mp hpair
    exact ⟨k,(hφ Q hQ O _).mp ((Formula.eval_arithmetic_shift_two φ Q O n k _).mp h)⟩
  · rintro ⟨k,h⟩
    exact ⟨natSet k,(mem_omega _).mpr ⟨k,rfl⟩,natSet (Nat.pair n k),
      (mem_omega _).mpr ⟨Nat.pair n k,rfl⟩,(hp k _).mpr rfl,
      (Formula.eval_arithmetic_shift_two φ Q O n k _).mpr ((hφ Q hQ O _).mpr h)⟩

theorem DefinesArithmetic.comp {φ ψ : Formula} {P : Predicate} {f : ℕ → ℕ}
    (hφ : DefinesArithmetic.{u} φ P) (hψ : DefinesNatural.{u} ψ f) :
    DefinesArithmetic.{u} (φ.arithmeticComp ψ) (fun O n => P O (f n)) := by
  intro Q hQ O n
  have hf (w : ZFSet.{u}) := Formula.unary_spec hψ 2 3 1 0
    (cons w (arithmeticEnv Q O n)) rfl hQ n rfl
  simp only [Formula.arithmeticComp,Formula.Eval,arithmeticEnv,cons_zero,cons_succ]
  constructor
  · rintro ⟨w,_,hw,h⟩
    obtain rfl := (hf w).mp hw
    exact (hφ Q hQ O _).mp ((Formula.eval_arithmetic_shift_one φ Q O n _).mp h)
  · intro h
    exact ⟨natSet (f n),(mem_omega _).mpr ⟨f n,rfl⟩,(hf _).mpr rfl,
      (Formula.eval_arithmetic_shift_one φ Q O n _).mpr ((hφ Q hQ O _).mpr h)⟩

theorem arithmetic_bounded_definition {P : Predicate} (hP : Arith P) :
    ∃ φ : Formula, DefinesArithmetic.{u} φ P := by
  induction hP with
  | pure P hP =>
    obtain ⟨φ,hφ⟩ := primitive_predicate_bounded.{u} hP
    exact ⟨φ,fun Q hQ O n => hφ (arithmeticEnv Q O n) rfl hQ n rfl⟩
  | query i =>
    exact ⟨.member 0 (i+3),fun Q _ O n => natSet_mem_realCode (O i) n⟩
  | neg h ih =>
    obtain ⟨φ,hφ⟩ := ih
    exact ⟨.neg φ,fun Q hQ O n => not_congr (hφ Q hQ O n)⟩
  | and h k ih ik =>
    obtain ⟨φ,hφ⟩ := ih; obtain ⟨ψ,hψ⟩ := ik
    exact ⟨.conj φ ψ,fun Q hQ O n => and_congr (hφ Q hQ O n) (hψ Q hQ O n)⟩
  | ex h ih =>
    obtain ⟨φ,hφ⟩ := ih
    exact ⟨φ.arithmeticExists,hφ.existsNat⟩
  | comp f h hf ih =>
    obtain ⟨φ,hφ⟩ := ih
    obtain ⟨ψ,hψ⟩ := primitive_bounded_definition.{u} (Primrec.nat_iff.mp hf)
    exact ⟨φ.arithmeticComp ψ,hφ.comp hψ⟩

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_DegreeSetFormula
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u

def DegreeEqualityFormula (φ : Formula) : Prop := ∀ o Q z x y : ℕ, ∀ e : ℕ → ZFSet.{u},
    e o = ZFSet.omega → (∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q) →
    e z = natSet 0 → ∀ A B : Oracle, e x = realCode A → e y = realCode B →
      ((Formula.twoOracles φ o Q z x y).Eval e ↔ degree A = degree B)

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
open Set TransitiveNameModel BoundedSetTheory InternalFiniteSubsets RelativeConstructible

def candidateFormula (ω U C E a : ℕ) : Formula := .conj (.subset a C)
  (.allMem C (.iff (.member 0 (a+1)) (rangeFormula (ω+1) (U+1) (E+1) 0)))

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
open Set TransitiveNameModel BoundedSetTheory InternalFiniteSubsets InternalFiniteEnumeration

def flattenFormula (ω Q S C B T U d k x : ℕ) : Formula :=
  .existsMem ω (.existsMem (ω+1) (.conj (Formula.naturalPair (ω+2) (Q+2) 1 0 (k+2))
    (.existsMem (S+2) (.conj (.pairMem 2 0 (B+3))
      (.existsMem (C+3) (.conj (.pairMem 1 0 (T+4))
        (entryFormula (U+4) 0 (d+4) 2 (x+4))))))))

end TuringRigidity.InternalCountableFiniteUnion

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalNiceName
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalNiceName
open TransitiveNameModel BoundedSetTheory RecursiveNames CountableForcing
variable {c : ZFSet.{0}} [Top (Conditions c)]

noncomputable def nice (E : ℕ → ZFSet.{0}) : Name (Conditions c) :=
  .mk (Σ n : ℕ, {p : Conditions c // label c p ∈ E n})
    (fun i => Name.check (natSet i.1)) (fun i => i.2.val)

end TuringRigidity.InternalNiceName

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenNiceNameConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenNiceNameConstruction
open TransitiveNameModel BoundedSetTheory RecursiveNames AtomicForcing CountableForcing
open CohenGroundPoset CohenAntichainSelector CohenInternalDecision
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

@[instance_reducible]
noncomputable def cohenTop (A : ZFSet.{0}) : OrderTop (Conditions (conditions A)) :=
  InternalCollapse.top (conditions A) (CohenGroundGeneric.empty_mem_conditions A)
attribute [local instance] cohenTop

end TuringRigidity.CohenNiceNameConstruction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenFilters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory InternalCollapse CohenBorelForcing CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable instance cohenTop : OrderTop (Conditions conditions) :=
  InternalCollapse.top conditions ((mem_conditions _).mpr (prefix_empty alphabet))

noncomputable def pullFilter (G : GenericFilter (Conditions conditions)) : GenericFilter Condition where
  carrier := {p | conditionEquiv p ∈ G.carrier}
  nonempty := by obtain ⟨q,hq⟩ := G.nonempty; exact ⟨conditionEquiv.symm q,by simpa using hq⟩
  upper := fun h hp => G.upper (conditionEquiv.monotone h) hp
  directed := by
    intro p q hp hq
    obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
    exact ⟨conditionEquiv.symm r,by simpa using hr,
      by simpa using conditionEquiv.symm.monotone hrp,
      by simpa using conditionEquiv.symm.monotone hrq⟩

noncomputable def pushFilter (G : GenericFilter Condition) : GenericFilter (Conditions conditions) where
  carrier := {p | conditionEquiv.symm p ∈ G.carrier}
  nonempty := by obtain ⟨q,hq⟩ := G.nonempty; exact ⟨conditionEquiv q,by simpa using hq⟩
  upper := fun h hp => G.upper (conditionEquiv.symm.monotone h) hp
  directed := by
    intro p q hp hq
    obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
    exact ⟨conditionEquiv r,by simpa using hr,
      by simpa using conditionEquiv.monotone hrp,
      by simpa using conditionEquiv.monotone hrq⟩

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenName
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory InternalCollapse CohenBorelForcing CountableForcing RecursiveNames
attribute [local instance] InternalCollapse.order

noncomputable def realName : Name (Conditions conditions) :=
  .mk {t : Conditions conditions × ℕ //
    ZFSet.pair (natSet t.2) (bitSet true) ∈ label conditions t.1}
    (fun t => Name.check (natSet t.val.2)) (fun t => t.val.1)

noncomputable def realNameCode (f : ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.sep (fun z => ∃ q ∈ conditions, ∃ n ∈ ZFSet.omega, ∃ v ∈ iterUnion 2 f,
    ZFSet.pair n v ∈ f ∧ ZFSet.pair n (bitSet true) ∈ q ∧ z = ZFSet.pair v q)
    (ZFSet.prod (iterUnion 2 f) conditions)

end TuringRigidity.InternalCohen

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
attribute [local instance] InternalCollapse.order CohenNiceNameConstruction.cohenTop
open InternalCohen (bitSet)

noncomputable abbrev poset (K : ZFSet.{0}) : ZFSet.{0} :=
  CohenGroundPoset.conditions (ZFSet.prod K ZFSet.omega)

noncomputable def realName (K a : ZFSet.{0}) : Name (Conditions (poset K)) :=
  .mk {t : Conditions (poset K) × ℕ //
    ZFSet.pair (ZFSet.pair a (natSet t.2)) (bitSet true) ∈ label (poset K) t.1}
    (fun t => Name.check (natSet t.val.2)) (fun t => t.val.1)

noncomputable def realNameCode (K a f : ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.sep (fun z => ∃ q ∈ poset K, ∃ n ∈ ZFSet.omega, ∃ v ∈ iterUnion 2 f,
    ∃ x ∈ ZFSet.prod K ZFSet.omega, ZFSet.pair n v ∈ f ∧ x = ZFSet.pair a n ∧ ZFSet.pair x (bitSet true) ∈ q ∧ z = ZFSet.pair v q)
    (ZFSet.prod (iterUnion 2 f) (poset K))

end TuringRigidity.CohenColumnRealName

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

def Cert (A : Oracle) (v : ℕ) : Prop :=
  let x := (Nat.unpair (Nat.unpair v).1).1
  let p := (Nat.unpair (Nat.unpair v).1).2
  let w := (Nat.unpair v).2
  Extends (columns A) (condition p) (condition (item w 0)) ∧ item w 2 ≠ item w 3 ∧
    item w 2 ∈ UniformRun.run A (machine (item x 0)) (machine (item x 1)) (left (item w 0)) (item w 1) ∧
    item w 3 ∈ UniformRun.run A (machine (item x 0)) (machine (item x 2)) (right (item w 0)) (item w 1)

theorem cert_sigma (A : Oracle) : Sigma A 1 (Cert A) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let x (i : ℕ) := item_primrec.comp (f.comp f) (Primrec.const i)
  let w (i : ℕ) := item_primrec.comp r (Primrec.const i)
  have he := recursive_comp (extends_recursive A) (Primrec₂.natPair.comp (r.comp f) (w 0))
  have hn := recursive_primrecPred A ((Primrec.eq.comp (w 2) (w 3)).not)
  have hl := UniformRun.graph_sigma_of A (x 0) (x 1) (Primrec.encode.comp (left_primrec.comp (w 0))) (w 1) (w 2)
  have hr := UniformRun.graph_sigma_of A (x 0) (x 2) (Primrec.encode.comp (right_primrec.comp (w 0))) (w 1) (w 3)
  unfold Cert
  simpa only [Nat.unpair_pair,word,encodek,Option.getD_some] using
    (Form.raise (n := 0) (s := true) he).and ((Form.raise (n := 0) (s := true) hn).and (hl.and hr))

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

theorem splitCert_sigma (A : Oracle) : Sigma A 1 (SplitCert A) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let x (i : ℕ) := item_primrec.comp f (Primrec.const i)
  let w (i : ℕ) := item_primrec.comp r (Primrec.const i)
  have hp := EncodedForcing.prefix_recursive A (word_primrec.comp (x 2)) (word_primrec.comp (w 1))
  have hq := EncodedForcing.prefix_recursive A (word_primrec.comp (x 2)) (word_primrec.comp (w 2))
  have hn := recursive_primrecPred A ((Primrec.eq.comp (w 3) (w 4)).not)
  have hl := UniformRun.graph_sigma_of A (x 0) (x 1) (w 1) (w 0) (w 3)
  have hr := UniformRun.graph_sigma_of A (x 0) (x 1) (w 2) (w 0) (w 4)
  exact (Form.raise (n := 0) (s := true) hp).and
    ((Form.raise (n := 0) (s := true) hq).and ((Form.raise (n := 0) (s := true) hn).and (hl.and hr)))

theorem convergesAbove_sigma (A : Oracle) : Sigma A 1 (ConvergesAbove A) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let x (i : ℕ) := item_primrec.comp (f.comp (f.comp f)) (Primrec.const i)
  let w (i : ℕ) := item_primrec.comp (r.comp (f.comp f)) (Primrec.const i)
  have hp := EncodedForcing.prefix_recursive A (word_primrec.comp (w 1)) (word_primrec.comp (r.comp f))
  have hh := UniformRun.graph_sigma_of A (x 0) (x 1) (r.comp f) (w 0) r
  have h := ((Form.raise (n := 0) (s := true) hp).and hh).ex.ex
  unfold ConvergesAbove
  simpa only [base,program,Nat.unpair_pair] using h

theorem divCert_recursive (A : Oracle) : RecursivePred (jump A) (DivCert A) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hp := EncodedForcing.prefix_recursive (jump A)
    (word_primrec.comp (item_primrec.comp f (Primrec.const 2)))
    (word_primrec.comp (item_primrec.comp r (Primrec.const 1)))
  exact recursive_and hp (recursive_not (form_recursive (convergesAbove_sigma A)))

theorem accept_recursive (A : Oracle) : RecursivePred (jump A) (Accept A) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have ht (i : ℕ) := recursive_primrecPred (jump A) (Primrec.eq.comp (f.comp r) (Primrec.const i))
  have hn := recursive_comp (recursive_not (form_recursive (splitCert_sigma A).ex)) f
  have hp := recursive_comp (form_recursive (pointCert_sigma A)) (Primrec₂.natPair.comp f (r.comp r))
  have hd := recursive_comp (divCert_recursive A) (Primrec₂.natPair.comp f (r.comp r))
  unfold Accept
  apply Form.congr (n := 0) (s := true) (Form.or (n := 0) (s := true) (recursive_and (ht 0) hn)
    (Form.or (n := 0) (s := true) (recursive_and (ht 1) hp) (recursive_and (ht 2) hd)))
  intro v
  rfl

theorem step_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (jump A)} (fun x => Part.some (step A x)) :=
  least_recursive (accept_recursive A) (accept_total A)

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

theorem outcome_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (jump A)} (fun v => Part.some (outcome A v)) := by
  classical
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hs := _root_.OAI.TuringRigidity.UniformOracle.total_comp (UniformSplit.step_recursive A) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec request_primrec)
  have hcode := _root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec r) hs
  have hc := _root_.OAI.TuringRigidity.UniformOracle.total_comp (recursive_lift (coding_recursive A)) hcode
  have hmap : Primrec (fun v : ℕ => if (Nat.unpair (Nat.unpair v).1).1 = 1 ∧ (Nat.unpair v).2 = 0
      then Nat.pair 3 (Nat.unpair (Nat.unpair v).1).2 else (Nat.unpair v).1) :=
    Primrec.ite ((Primrec.eq.comp (f.comp f) (Primrec.const 1)).and
      (Primrec.eq.comp r (Primrec.const 0))) (Primrec₂.natPair.comp (Primrec.const 3) (r.comp f)) f
  exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hmap) (_root_.OAI.TuringRigidity.UniformOracle.total_pair hs hc)).of_eq (fun v => by
    simp only [Nat.unpair_pair,outcome]
    by_cases h : IsCoding A (Nat.pair (Nat.unpair v).2 (UniformSplit.step A (request v))) <;> simp [h])

theorem next_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (jump A)} (fun v => Part.some (next A v)) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hu := EffectiveSplitConditions.update_primrec.comp f (retag_primrec.comp r)
  exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hu)
    (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec r) (outcome_recursive A))).of_eq
      (fun v => by simp only [Nat.unpair_pair]; rfl)

theorem disagreement_mono {A : Oracle} {x : ℕ} {p q : Condition}
    (hpq : Extends (columns A) p q) (h : UniformAgreement.Disagreement A x p) :
    UniformAgreement.Disagreement A x q := by
  obtain ⟨n,a,b,hab,ha,hb⟩ := h
  exact ⟨n,a,b,hab,UniformRun.run_mono hpq.1 n a ha,UniformRun.run_mono hpq.2.1 n b hb⟩

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

theorem decide_stable_exists (A : Oracle) : ∃ f : ℕ → ℕ,
    Nat.RecursiveIn {oracleFunction (jump A)} (fun v => Part.some (f v)) ∧
    ∀ x p, Extends (columns A) (condition p) (condition (f (Nat.pair x p))) ∧
      (Disagreement A x (condition (f (Nat.pair x p))) ∨ (f (Nat.pair x p) = p ∧ NoDisagreement A x (condition p))) := by
  obtain ⟨search,hs,hsearch⟩ := sigma1_choice (cert_sigma A)
  let out : ℕ → ℕ := fun v => if search v = 0 then (Nat.unpair v).2 else item (search v-1) 0
  have hmap : Primrec (fun v : ℕ => if (Nat.unpair v).2 = 0 then (Nat.unpair (Nat.unpair v).1).2
      else item ((Nat.unpair v).2-1) 0) := by
    let f := Primrec.fst.comp Primrec.unpair
    let r := Primrec.snd.comp Primrec.unpair
    exact Primrec.ite (Primrec.eq.comp r (Primrec.const 0)) (r.comp f)
      (item_primrec.comp (Primrec.nat_sub.comp r (Primrec.const 1)) (Primrec.const 0))
  refine ⟨out,?_,fun x p => ?_⟩
  · exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hmap) (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec Primrec.id) hs)).of_eq
      (fun v => by simp only [Nat.unpair_pair]; rfl)
  · rcases hsearch (Nat.pair x p) with ⟨hz,hn⟩ | ⟨hp,hc⟩
    · simp only [out,hz,↓reduceIte,Nat.unpair_pair]
      refine ⟨extends_refl _ _,Or.inr ⟨trivial,fun q hpq hd => ?_⟩⟩
      obtain ⟨n,a,b,hab,ha,hb⟩ := hd
      apply hn
      refine ⟨encode [code q,n,a,b],?_⟩
      simpa [Cert,item,word,← show left (code q) = q.left from congrArg Condition.left (condition_code q),
        ← show right (code q) = q.right from congrArg Condition.right (condition_code q),condition_code] using
        And.intro hpq (And.intro hab (And.intro ha hb))
    · have hz : search (Nat.pair x p) ≠ 0 := by omega
      simp only [out,ite_eq_right hz]
      simp only [Cert,Nat.unpair_pair] at hc
      exact ⟨hc.1,Or.inl ⟨_,_,_,hc.2⟩⟩

theorem next_precise (A : Oracle) (x p : ℕ)
    (hn : UniformAgreement.NoDisagreement A x (condition p)) :
    Extends (columns A) (condition p) (condition (next A (Nat.pair x p))) ∧
    (condition (next A (Nat.pair x p))).active = (condition p).active ∧
    ((condition (next A (Nat.pair x p)) = condition p ∧
      ((¬ ∃ z, UniformSplit.SplitCert A (Nat.pair (request (Nat.pair x p)) z)) ∨
      (∃ w, UniformSplit.PointCert A (Nat.pair (request (Nat.pair x p)) w) ∧
        CodingLocation (columns A) (condition p) (item w 2)))) ∨
      ∃ i n, (i = 1 ∨ i = 2) ∧ ∀ q, Extends (columns A) (condition (next A (Nat.pair x p))) q →
        ∀ a, a ∉ UniformRun.run A (machine (item x 0)) (machine (item x i))
          (if i = 1 then q.left else q.right) n) := by
  classical
  let v := Nat.pair x p
  let raw := UniformSplit.step A (request v)
  have hs := UniformSplit.step_spec A (request v)
  change UniformSplit.Accept A (Nat.pair (request v) raw) at hs
  simp only [UniformSplit.Accept,Nat.unpair_pair] at hs
  rcases hs with ⟨ht,hno⟩ | ⟨ht,hpoint⟩ | ⟨ht,hdiv⟩
  · have he : condition (next A v) = condition p := by
      simp [next,outcome,update,retag,EffectiveSplitConditions.update,← show raw = UniformSplit.step A (request v) from rfl,ht,v,condition_code]
    change Extends _ _ (condition (next A v)) ∧ _
    rw [he]
    exact ⟨extends_refl _ _,rfl,Or.inl ⟨rfl,Or.inl hno⟩⟩
  · let w := (Nat.unpair raw).2
    have hp := hpoint
    simp only [UniformSplit.PointCert,Nat.unpair_pair,UniformSplit.start,UniformSplit.base,
      UniformSplit.program,request,v,item,encodek,Option.getD_some,List.getD_cons_zero,List.getD_cons_succ,
      word] at hp
    have hpq : left p <+: word (item w 1) := hp.1
    let r := append (condition p) ((word (item w 1)).drop (left p).length)
    have hl : r.left = word (item w 1) := by
      change left p ++ (word (item w 1)).drop (left p).length = _
      rw [List.prefix_iff_eq_take] at hpq
      conv_lhs => lhs; rw [hpq]
      exact List.take_append_drop _ _
    by_cases hcoding : IsCoding A (Nat.pair p raw)
    · have he : condition (next A v) = condition p := by
        simp [next,outcome,update,retag,EffectiveSplitConditions.update,
          ← show raw = UniformSplit.step A (request v) from rfl,ht,v,hcoding,condition_code]
      change Extends _ _ (condition (next A v)) ∧ _
      rw [he]
      exact ⟨extends_refl _ _,rfl,Or.inl ⟨rfl,Or.inr ⟨w,hpoint,by simpa only [IsCoding,Nat.unpair_pair] using hcoding⟩⟩⟩
    · have he : condition (next A v) = r := by
        simp [next,outcome,update,retag,EffectiveSplitConditions.update,
          ← show raw = UniformSplit.step A (request v) from rfl,ht,v,hcoding,condition_code]
        rfl
      have hnc : ¬ CodingLocation (columns A) (condition p) (item w 2) := by simpa only [IsCoding,Nat.unpair_pair] using hcoding
      have hpr : Extends (columns A) (condition p) r := append_extends _ _ _
      have hd := split_coding_or_divergence (r := r) hn hpr
        (item w 2) hp.2.1 (by simpa [hl,item,word,w] using hp.2.2.1) (item w 3).bodd
        (item w 0) (item w 4) (item w 5) hp.2.2.2.1
        (by simpa [hl,item,word,w] using hp.2.2.2.2.1) (by simpa [hl,item,word,w] using hp.2.2.2.2.2)
      change Extends _ _ (condition (next A v)) ∧ _
      rw [he]
      refine ⟨append_extends _ _ _,rfl,Or.inr ⟨2,item w 0,Or.inr rfl,?_⟩⟩
      simpa using hd.resolve_left hnc
  · let w := (Nat.unpair raw).2
    have hpq : left p <+: word (item w 1) := by
      simpa [UniformSplit.DivCert,UniformSplit.start,request,v,item,word] using hdiv.1
    let r := append (condition p) ((word (item w 1)).drop (left p).length)
    have hl : r.left = word (item w 1) := by
      change left p ++ (word (item w 1)).drop (left p).length = _
      rw [List.prefix_iff_eq_take] at hpq
      conv_lhs => lhs; rw [hpq]
      exact List.take_append_drop _ _
    have he : condition (next A v) = r := by
      simp [next,outcome,update,retag,EffectiveSplitConditions.update,
        ← show raw = UniformSplit.step A (request v) from rfl,ht,v,condition_code]
      rfl
    change Extends _ _ (condition (next A v)) ∧ _
    rw [he]
    refine ⟨append_extends _ _ _,rfl,Or.inr ⟨1,item w 0,Or.inl rfl,?_⟩⟩
    intro q hrq a ha
    apply hdiv.2
    refine ⟨encode q.left,a,?_,?_⟩
    · simpa [word,w,hl] using hrq.1
    · simpa [UniformSplit.base,UniformSplit.program,request,v,item,word] using ha

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

def NoBad (A : Oracle) (x : ℕ) (p : Condition) : Prop :=
  ¬ ∃ w, BadCert A (Nat.pair (Nat.pair x (code p)) w)

theorem next_exists (A : Oracle) : ∃ g : ℕ → ℕ,
    Nat.RecursiveIn {oracleFunction (jump A)} (fun v => Part.some (g v)) ∧
    (∀ x p, Extends (columns A) (condition p) (condition (g (Nat.pair x p))) ∧
      (condition (g (Nat.pair x p))).active = (condition p).active) ∧
    ∀ x p, UniformAgreement.NoDisagreement A x (condition p) →
      StablePair.Decisive A x (condition (g (Nat.pair x p))) ∨
      (condition (g (Nat.pair x p)) = condition p ∧
        (¬ ∃ w, BadCert A (Nat.pair (Nat.pair x p) w)) ∧ Outcome A x p) := by
  obtain ⟨search,hs,hsearch⟩ := sigma1_choice (badCert_sigma A)
  let g := fun v => if search v = 0 then next A v else
    EffectiveSplitConditions.update (Nat.unpair v).2 (Nat.pair 2 (search v-1))
  have hrec : Nat.RecursiveIn {oracleFunction (jump A)} (fun v => Part.some (g v)) := by
    let f := Primrec.fst.comp Primrec.unpair
    let r := Primrec.snd.comp Primrec.unpair
    have hu := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (EffectiveSplitConditions.update_primrec.comp f r))
      (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec r) (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec
        (Primrec₂.natPair.comp (Primrec.const 2) (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))) hs))
    have hi := Primrec.ite (Primrec.eq.comp f (Primrec.const 0)) (f.comp r) (r.comp r)
    exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hi) (_root_.OAI.TuringRigidity.UniformOracle.total_pair hs (_root_.OAI.TuringRigidity.UniformOracle.total_pair (next_recursive A) hu))).of_eq
      (fun v => by simp only [Nat.unpair_pair]; rfl)
  refine ⟨g,hrec,fun x p => ?_,fun x p hn => ?_⟩
  · by_cases hz : search (Nat.pair x p) = 0
    · simpa only [g,ite_eq_left hz,Nat.unpair_pair] using next_extends A (Nat.pair x p)
    · simp only [g,ite_eq_right hz,Nat.unpair_pair,EffectiveSplitConditions.update,↓reduceIte,condition_code]
      exact ⟨append_extends _ _ _,rfl⟩
  · rcases hsearch (Nat.pair x p) with ⟨hz,hno⟩ | ⟨hpos,hbad⟩
    · simp only [g,ite_eq_left hz]
      rcases (StablePair.next_precise A x p hn).2.2 with ⟨he,ho⟩ | hd
      · exact Or.inr ⟨he,hno,ho⟩
      · exact Or.inl (Or.inr hd)
    · have hz : search (Nat.pair x p) ≠ 0 := by omega
      simp only [g,ite_eq_right hz,Nat.unpair_pair]
      exact Or.inl (bad_decisive A x p _ hn hbad)

theorem pair_exists (A : Oracle) : ∃ f : ℕ → ℕ,
    Nat.RecursiveIn {oracleFunction (jump A)} (fun v => Part.some (f v)) ∧
    ∀ x p, Extends (columns A) (condition p) (condition (f (Nat.pair x p))) ∧
      (UniformAgreement.Disagreement A x (condition (f (Nat.pair x p))) ∨
        ((condition (f (Nat.pair x p))).active = (condition p).active ∧
          UniformAgreement.NoDisagreement A x (condition p) ∧
          (StablePair.Decisive A x (condition (f (Nat.pair x p))) ∨
            (condition (f (Nat.pair x p)) = condition p ∧
              (¬ ∃ w, BadCert A (Nat.pair (Nat.pair x p) w)) ∧ Outcome A x p)))) := by
  obtain ⟨d,hd,hds⟩ := StablePair.decide_stable_exists A
  obtain ⟨g,hg,hge,hgs⟩ := next_exists A
  let f := fun v => g (Nat.pair (Nat.unpair v).1 (d v))
  refine ⟨f,?_,fun x p => ?_⟩
  · exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp hg (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.fst.comp Primrec.unpair)) hd)).of_eq (fun v => rfl)
  · obtain ⟨hp,hm⟩ := hds x p
    have hq := hge x (d (Nat.pair x p))
    refine ⟨by simpa only [f,Nat.unpair_pair] using extends_trans hp hq.1,?_⟩
    rcases hm with hm | ⟨he,hn⟩
    · exact Or.inl (by simpa only [f,Nat.unpair_pair] using disagreement_mono hq.1 hm)
    · simpa only [f,Nat.unpair_pair,he] using Or.inr ⟨(hge x p).2,hn,hgs x p hn⟩

noncomputable def procedure (A : Oracle) : ℕ → ℕ := Classical.choose (pair_exists A)

end
end TuringRigidity.GuardedPair

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

def NoBad (B : Oracle) (F : ℕ → Oracle) (x p : ℕ) : Prop :=
  ∀ w, UniformSplit.PointCert B (Nat.pair (request (Nat.pair x p)) w) →
    CodingLocation F (condition p) (item w 2)

end
end TuringRigidity.LocalPair

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_GuardedStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GuardedStage
open Encodable CodingForcing EncodedForcing FiniteInjury
noncomputable section
attribute [local instance] Classical.propDecidable

def pairProcedure (A : Oracle) : ℕ → ℕ := GuardedPair.procedure A

def candidate (A : Oracle) (t : ℕ) (p : Condition) : Condition :=
  atLevel (condition (pairProcedure A (Nat.pair t (code (atLevel p t))))) t

def Changes (A : Oracle) (t : ℕ) (p : Condition) : Prop :=
  (candidate A t p).left ≠ p.left ∨ (candidate A t p).right ≠ p.right

def scan (A : Oracle) (p : Condition) (done : Finset ℕ) (t : ℕ) : ℕ → Option ℕ
  | 0 => none
  | n+1 => if t ∉ done ∧ Changes A t p then some t else scan A p done (t+1) n

def stageAction (A : Oracle) (s : ℕ) (p : State) : Option ℕ := scan A (generic A p) p.done 0 s

def stageWord (A : Oracle) (s : ℕ) (p : State) : Condition :=
  match stageAction A s p with
  | none => generic A p
  | some t => candidate A t (generic A p)

def advance (A : Oracle) (s : ℕ) (p : State) : State where
  condition := atLevel (append (stageWord A s p) [false]) (s+1)
  done := FiniteInjury.update p.done (stageAction A s p)
  seen := FiniteInjurySchedule.reset (insert (FiniteInjurySchedule.visit p.seen) p.seen) (stageAction A s p)

def construction (A : Oracle) : ℕ → State
  | 0 => ⟨⟨[],[],rfl,0⟩,∅,∅⟩
  | s+1 => advance A s (construction A s)

def conditions (A : Oracle) (s : ℕ) := (construction A s).condition

def proposal (A : Oracle) (s : ℕ) (_ : Finset ℕ) : Option ℕ :=
  stageAction A s (construction A s)

end
end TuringRigidity.GuardedStage

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
open Encodable UniformOracle EncodedForcing CodingForcing FiniteInjury StageRecords
noncomputable section
attribute [local instance] Classical.propDecidable

def candidate (A : Oracle) (v : ℕ) : ℕ :=
  levelCode (GuardedStage.pairProcedure A (Nat.pair (Nat.unpair v).1
    (levelCode (Nat.unpair v).2 (Nat.unpair v).1))) (Nat.unpair v).1

def scanStep (A : Oracle) (v : ℕ) : ℕ :=
  let p := (Nat.unpair (Nat.unpair v).1).1
  let d := (Nat.unpair (Nat.unpair v).1).2
  let t := (Nat.unpair (Nat.unpair v).2).1
  let prev := (Nat.unpair (Nat.unpair v).2).2
  let c := candidate A (Nat.pair t p)
  if prev = 0 ∧ t ∉ record d ∧ (left c ≠ left p ∨ right c ≠ right p) then t+1 else prev

def scan (A : Oracle) (p d n : ℕ) : ℕ := recur (fun _ => 0) (scanStep A) (Nat.pair p d) n

end
end TuringRigidity.GuardedComputability

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

def stageAction (A : Oracle) (s v : ℕ) : ℕ :=
  scan A (genericCanonical A v) (Nat.unpair (Nat.unpair v).2).1 s

def stageWord (A : Oracle) (z : ℕ) : ℕ :=
  let s := (Nat.unpair z).1
  let v := (Nat.unpair z).2
  let a := stageAction A s v
  let g := genericCanonical A v
  if a = 0 then g else candidate A (Nat.pair (a-1) g)

def advance (A : Oracle) (z : ℕ) : ℕ :=
  let s := (Nat.unpair z).1
  let v := (Nat.unpair z).2
  let d := (Nat.unpair (Nat.unpair v).2).1
  let seen := (Nat.unpair (Nat.unpair v).2).2
  let a := stageAction A s v
  Nat.pair (grow (stageWord A z) s)
    (Nat.pair (doneUpdate d a) (seenReset (seenInsert seen (nextVisit seen)) a))

def initial : ℕ := Nat.pair (code ⟨[],[],rfl,0⟩) (Nat.pair (encode ([] : List ℕ)) (encode ([] : List ℕ)))

def construction (A : Oracle) : ℕ → ℕ :=
  recur (fun _ => initial) (fun v => advance A (Nat.unpair v).2) 0

end
end TuringRigidity.GuardedComputability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_GuardedLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GuardedLimits
open Encodable UniformOracle ArithmeticHierarchy EncodedForcing CodingForcing FiniteInjury
open GuardedStage
noncomputable section
attribute [local instance] Classical.propDecidable

def G₀ (A : Oracle) : Oracle := leftLimit (conditions A)
def G₁ (A : Oracle) : Oracle := rightLimit (conditions A)

end
end TuringRigidity.GuardedLimits

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_FixedArithmetic
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.FixedArithmetic
open Encodable EncodedForcing ArithmeticHierarchy UniformOracle OracleJump
open ArithmeticModelDecoding SetCoding RelationCoding BoundedDecoding

structure Frame where
  C : Oracle
  low : Reduces (jump C) (jump zero)
  injective : Function.Injective (fun k => degree (columns C k))
  successor : RelationCode 2
  below : RelationBelow successor (degree (jump zero))
  spec : ∀ a b, successor.Holds (two a b) ↔
    ∃ k, a = degree (columns C k) ∧ b = degree (columns C (k+1))

end TuringRigidity.FixedArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_IdealInterpretation
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IdealInterpretation
open AntichainParameters SetCoding RelationCoding

def ACode.external {I : DegreeIdeal} (p : ACode I) : AntichainCode := ⟨p.bound.val,p.left.val,p.right.val⟩
def ACode.map {I J : DegreeIdeal} (ρ : I ≃o J) (p : ACode I) : ACode J := ⟨ρ p.bound,ρ p.left,ρ p.right⟩

structure SCode (I : DegreeIdeal) where
  bound : I
  tags : ACode I
  decorated : ACode I

def SCode.external {I : DegreeIdeal} (p : SCode I) : SetCode := ⟨p.bound.val,p.tags.external,p.decorated.external⟩
def SCode.map {I J : DegreeIdeal} (ρ : I ≃o J) (p : SCode I) : SCode J :=
  ⟨ρ p.bound,p.tags.map ρ,p.decorated.map ρ⟩

structure RCode (I : DegreeIdeal) (n : ℕ) where
  coordinates : Fin n → SCode I
  tuples : ACode I

def RCode.external {I : DegreeIdeal} {n : ℕ} (p : RCode I n) : RelationCode n :=
  ⟨fun i => (p.coordinates i).external,p.tuples.external⟩
def RCode.map {I J : DegreeIdeal} {n : ℕ} (ρ : I ≃o J) (p : RCode I n) : RCode J n :=
  ⟨fun i => (p.coordinates i).map ρ,p.tuples.map ρ⟩

end TuringRigidity.IdealInterpretation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_IdealLift
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IdealInterpretation
open SetCoding RelationCoding BoundedDecoding ArithmeticModelDecoding

def ACode.ofBelow {I : DegreeIdeal} (p : AntichainCode) (b : I) (hp : AntichainBelow p b.val) : ACode I :=
  ⟨⟨p.bound,I.lower hp.1 b.property⟩,⟨p.left,I.lower hp.2.1 b.property⟩,
    ⟨p.right,I.lower hp.2.2 b.property⟩⟩

@[simp] theorem ACode.external_ofBelow {I : DegreeIdeal} (p : AntichainCode) (b : I)
    (hp : AntichainBelow p b.val) : (ACode.ofBelow p b hp).external = p := by cases p; rfl

def SCode.ofBelow {I : DegreeIdeal} (p : SetCode) (b : I) (hp : SetBelow p b.val) : SCode I :=
  ⟨⟨p.bound,I.lower hp.1 b.property⟩,ACode.ofBelow p.tags b hp.2.1,ACode.ofBelow p.decorated b hp.2.2⟩

@[simp] theorem SCode.external_ofBelow {I : DegreeIdeal} (p : SetCode) (b : I)
    (hp : SetBelow p b.val) : (SCode.ofBelow p b hp).external = p := by cases p; rfl

def RCode.ofBelow {I : DegreeIdeal} {n : ℕ} (p : RelationCode n) (b : I)
    (hp : RelationBelow p b.val) : RCode I n :=
  ⟨fun i => SCode.ofBelow (p.coordinates i) b (hp.1 i),ACode.ofBelow p.tuples b hp.2⟩

@[simp] theorem RCode.external_ofBelow {I : DegreeIdeal} {n : ℕ} (p : RelationCode n) (b : I)
    (hp : RelationBelow p b.val) : (RCode.ofBelow p b hp).external = p := by cases p; rfl

end TuringRigidity.IdealInterpretation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_IdealLocality
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IdealLocality
open OracleJump ArithmeticHierarchy ArithmeticModelDecoding BoundedDecoding IdealInterpretation
noncomputable section

def JumpClosed (J : DegreeIdeal) : Prop := ∀ x, x ∈ J.carrier → degreeJump x ∈ J.carrier

end
end TuringRigidity.IdealLocality

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_IdealPresentation
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IdealPresentation
open OracleJump ArithmeticHierarchy EncodedForcing BoundedDecoding IdealInterpretation IdealLocality
open EnumerationDecoding EnumerationConstruction
noncomputable section

def entry {J : DegreeIdeal} (H : Oracle) (hH : degree H ∈ J.carrier) (n : ℕ) : J :=
  ⟨degree (columns H n),J.lower (CodingExtraction.column_projection_reduces H n) hH⟩

def Graph {J : DegreeIdeal} (ρ : J ≃o J) (H : Oracle) (hH : degree H ∈ J.carrier) (v : ℕ) : Prop :=
  (ρ (entry H hH (Nat.unpair v).1)).val = degree (columns H (Nat.unpair v).2)

end
end TuringRigidity.IdealPresentation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenWordCodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory SetModelFunctions SetModelArithmetic SetModelReals
open Encodable EncodedForcing

noncomputable def wordGraphEnv (q n gl gb : ZFSet.{0}) : ℕ → ZFSet.{0} :=
  cons q (cons n (cons gl (cons gb (cons ZFSet.omega
    (cons alphabet (cons pairNumbers (fun _ => pairingSet)))))))

noncomputable def wordCodeGraph : ZFSet.{0} :=
  ZFSet.range (fun n : ℕ => ZFSet.pair (natSet n) (wordCode (word n)))

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenEffectiveGeneric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory Encodable OracleJump
open UniformArithmetic CohenBorelForcing CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def decisionCodes (Y : Oracle) (e : ℕ) : Oracle :=
  arithmeticReal (fun O n => WordDecision (O 0) e (EncodedForcing.word n)) (fun _ => Y)

noncomputable def decisionSet (Y : Oracle) (e : ℕ) : ZFSet.{0} :=
  ZFSet.sep (fun q => ∃ n ∈ realCode (decisionCodes Y e),
    ZFSet.pair n q ∈ wordCodeGraph) conditions

end TuringRigidity.InternalCohen

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

theorem mem_restrict (B p z : ZFSet.{0}) :
    z ∈ restrict B p ↔ z ∈ p ∧ z ∈ ZFSet.prod B alphabet := by
  rw [restrict,ZFSet.mem_sep,ZFSet.mem_prod]

theorem pair_restrict (B p x b : ZFSet.{0}) :
    ZFSet.pair x b ∈ restrict B p ↔ ZFSet.pair x b ∈ p ∧ x ∈ B ∧ b ∈ alphabet := by
  rw [mem_restrict,ZFSet.pair_mem_prod]

theorem restrict_condition (A B p : ZFSet.{0}) (hBA : B ⊆ A) (hp : p ∈ conditions A) :
    restrict B p ∈ conditions B := by
  obtain ⟨hfin,hsv⟩ := (mem_conditions A p).mp hp
  obtain ⟨_,hfinite⟩ := (mem_finiteSubsets_iff _ _).mp hfin
  apply (mem_conditions B _).mpr
  refine ⟨(mem_finiteSubsets_iff _ _).mpr ⟨fun z hz => (mem_restrict B p z).mp hz |>.2,
    hfinite.subset (fun z hz => (mem_restrict B p z).mp hz |>.1)⟩,?_⟩
  intro x hx b hb c hc hxb hxc
  exact hsv x (hBA hx) b hb c hc ((pair_restrict B p x b).mp hxb).1
    ((pair_restrict B p x c).mp hxc).1

theorem restrict_mono (B p q : ZFSet.{0}) (hpq : p ⊆ q) : restrict B p ⊆ restrict B q := by
  intro z hz
  obtain ⟨hz,hB⟩ := (mem_restrict B p z).mp hz
  exact (mem_restrict B q z).mpr ⟨hpq hz,hB⟩

end TuringRigidity.InternalCohenRestriction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenPartition
open TransitiveNameModel BoundedSetTheory InternalFiniteSubsets CohenConditionCode CohenGroundPoset
open InternalCohenRestriction
open InternalCohen (alphabet)

theorem condition_subset (A p : ZFSet.{0}) (hp : p ∈ conditions A) :
    p ⊆ ZFSet.prod A alphabet :=
  ((mem_finiteSubsets_iff _ _).mp ((mem_conditions A p).mp hp).1).1

theorem condition_mono (A B p : ZFSet.{0}) (hBA : B ⊆ A) (hp : p ∈ conditions B) :
    p ∈ conditions A := by
  obtain ⟨hf,hs⟩ := (mem_conditions B p).mp hp
  obtain ⟨hsub,hfin⟩ := (mem_finiteSubsets_iff _ _).mp hf
  apply (mem_conditions A p).mpr
  constructor
  · apply (mem_finiteSubsets_iff _ _).mpr
    exact ⟨fun z hz => by
      obtain ⟨x,hx,b,hb,rfl⟩ := ZFSet.mem_prod.mp (hsub hz)
      exact ZFSet.pair_mem_prod.mpr ⟨hBA hx,hb⟩,hfin⟩
  · intro x _ b hb c hc hxb hxc
    have hx := (ZFSet.pair_mem_prod.mp (hsub hxb)).1
    exact hs x hx b hb c hc hxb hxc

theorem union_condition (A B p q : ZFSet.{0}) (hBA : B ⊆ A)
    (hp : p ∈ conditions B) (hq : q ∈ conditions (A \ B)) :
    p ∪ q ∈ conditions A := by
  have hpA := condition_mono A B p hBA hp
  have hqA := condition_mono A (A \ B) q (fun _ h => (ZFSet.mem_sdiff.mp h).1) hq
  have hpf := ((mem_finiteSubsets_iff _ _).mp ((mem_conditions A p).mp hpA).1).2
  have hqf := ((mem_finiteSubsets_iff _ _).mp ((mem_conditions A q).mp hqA).1).2
  apply (mem_conditions A _).mpr
  constructor
  · apply (mem_finiteSubsets_iff _ _).mpr
    exact ⟨fun z hz => (ZFSet.mem_union.mp hz).elim (fun h => condition_subset A p hpA h) (fun h => condition_subset A q hqA h),
      by rw [ZFSet.coe_union]; exact hpf.union hqf⟩
  · intro x hx b hb c hc hxb hxc
    rcases ZFSet.mem_union.mp hxb with hxb|hxb <;>
      rcases ZFSet.mem_union.mp hxc with hxc|hxc
    · exact ((mem_conditions A p).mp hpA).2 x hx b hb c hc hxb hxc
    · exact False.elim ((ZFSet.mem_sdiff.mp (ZFSet.pair_mem_prod.mp (condition_subset (A \ B) q hq hxc)).1).2
        (ZFSet.pair_mem_prod.mp (condition_subset B p hp hxb)).1)
    · exact False.elim ((ZFSet.mem_sdiff.mp (ZFSet.pair_mem_prod.mp (condition_subset (A \ B) q hq hxb)).1).2
        (ZFSet.pair_mem_prod.mp (condition_subset B p hp hxc)).1)
    · exact ((mem_conditions A q).mp hqA).2 x hx b hb c hc hxb hxc

theorem union_restrict (A B p : ZFSet.{0}) (hp : p ∈ conditions A) :
    restrict B p ∪ restrict (A \ B) p = p := by
  classical
  apply ZFSet.ext; intro z
  rw [ZFSet.mem_union,mem_restrict,mem_restrict]
  constructor
  · exact fun h => h.elim And.left And.left
  · intro hz
    obtain ⟨x,hx,b,hb,rfl⟩ := ZFSet.mem_prod.mp (condition_subset A p hp hz)
    by_cases hxB : x ∈ B
    · exact Or.inl ⟨hz,ZFSet.pair_mem_prod.mpr ⟨hxB,hb⟩⟩
    · exact Or.inr ⟨hz,ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_sdiff.mpr ⟨hx,hxB⟩,hb⟩⟩

theorem restrict_union_left (A B p q : ZFSet.{0})
    (hp : p ∈ conditions B) (hq : q ∈ conditions (A \ B)) : restrict B (p ∪ q) = p := by
  apply ZFSet.ext; intro z
  rw [mem_restrict,ZFSet.mem_union]
  constructor
  · rintro ⟨hz,hzB⟩
    rcases hz with hz|hz
    · exact hz
    · obtain ⟨x,hx,b,hb,rfl⟩ := ZFSet.mem_prod.mp hzB
      exact False.elim ((ZFSet.mem_sdiff.mp (ZFSet.pair_mem_prod.mp (condition_subset (A \ B) q hq hz)).1).2 hx)
  · intro hz; exact ⟨Or.inl hz,condition_subset B p hp hz⟩

theorem restrict_union_right (A B p q : ZFSet.{0})
    (hp : p ∈ conditions B) (hq : q ∈ conditions (A \ B)) : restrict (A \ B) (p ∪ q) = q := by
  apply ZFSet.ext; intro z
  rw [mem_restrict,ZFSet.mem_union]
  constructor
  · rintro ⟨hz,hzB⟩
    rcases hz with hz|hz
    · obtain ⟨x,hx,b,hb,rfl⟩ := ZFSet.mem_prod.mp hzB
      exact False.elim ((ZFSet.mem_sdiff.mp hx).2 (ZFSet.pair_mem_prod.mp (condition_subset B p hp hz)).1)
    · exact hz
  · intro hz; exact ⟨Or.inr hz,condition_subset (A \ B) q hq hz⟩

theorem subset_iff_restrict (A B p q : ZFSet.{0})
    (hp : p ∈ conditions A) (hq : q ∈ conditions A) :
    p ⊆ q ↔ restrict B p ⊆ restrict B q ∧ restrict (A \ B) p ⊆ restrict (A \ B) q := by
  constructor
  · intro h; exact ⟨restrict_mono B p q h,restrict_mono (A \ B) p q h⟩
  · intro h z hz
    rw [←union_restrict A B p hp,ZFSet.mem_union] at hz
    rw [←union_restrict A B q hq,ZFSet.mem_union]
    exact hz.elim (fun hz => Or.inl (h.1 hz)) (fun hz => Or.inr (h.2 hz))

end TuringRigidity.InternalCohenPartition

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenFactor
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenFactor
open TransitiveNameModel BoundedSetTheory CohenGroundPoset InternalCohenRestriction InternalCohenPartition
open InternalCohen (alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def project (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (p : Conditions (conditions A)) : Conditions (conditions B) :=
  equivShrink _ ⟨restrict B (label _ p),restrict_condition A B _ hBA (label_mem _ p)⟩

theorem label_project (A B : ZFSet.{0}) (hBA : B ⊆ A) (p : Conditions (conditions A)) :
    label _ (project A B hBA p) = restrict B (label _ p) := by simp [project,label]

noncomputable def combine (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (p : Conditions (conditions B)) (q : Conditions (conditions (A \ B))) :
    Conditions (conditions A) :=
  equivShrink _ ⟨label _ p ∪ label _ q,union_condition A B _ _ hBA (label_mem _ p) (label_mem _ q)⟩

theorem label_combine (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (p : Conditions (conditions B)) (q : Conditions (conditions (A \ B))) :
    label _ (combine A B hBA p q) = label _ p ∪ label _ q := by simp [combine,label]

noncomputable def factorIso (A B : ZFSet.{0}) (hBA : B ⊆ A) :
    Conditions (conditions A) ≃o (Conditions (conditions B) × Conditions (conditions (A \ B))) where
  toFun p := (project A B hBA p,project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) p)
  invFun p := combine A B hBA p.1 p.2
  left_inv p := by
    apply label_injective
    rw [label_combine,label_project,label_project,union_restrict A B _ (label_mem _ p)]
  right_inv p := by
    apply Prod.ext <;> apply label_injective
    · rw [label_project,label_combine,restrict_union_left A B _ _ (label_mem _ p.1) (label_mem _ p.2)]
    · rw [label_project,label_combine,restrict_union_right A B _ _ (label_mem _ p.1) (label_mem _ p.2)]
  map_rel_iff' := by
    intro p q
    change (label _ (project A B hBA q) ⊆ label _ (project A B hBA p) ∧
      label _ (project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) q) ⊆ label _ (project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) p)) ↔ label _ q ⊆ label _ p
    rw [label_project,label_project,label_project,label_project]
    exact (subset_iff_restrict A B _ _ (label_mem _ q) (label_mem _ p)).symm

noncomputable def productCode (A B : ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.prod (conditions B) (conditions (A \ B))

noncomputable def factorGraph (A B : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod (conditions A) (productCode A B)).sep (fun z =>
    ∃ p ∈ conditions A, ∃ q ∈ conditions B, ∃ r ∈ conditions (A \ B),
      z = ZFSet.pair p (ZFSet.pair q r) ∧ q = restrict B p ∧ r = restrict (A \ B) p)

end TuringRigidity.InternalCohenFactor

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenProjectedGeneric
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenProjectedGeneric
open TransitiveNameModel BoundedSetTheory CountableForcing AutomorphismName
open CohenGroundPoset InternalCohenRestriction InternalCohenPartition InternalCohenFactor
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def projected (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) : GenericFilter (Conditions (conditions B)) :=
  CohenProductFilters.first (mapFilter (factorIso A B hBA) G)

noncomputable def densePreimage (A B D : ZFSet.{0}) : ZFSet.{0} :=
  (conditions A).sep (fun p => ∃ q ∈ conditions B,
    ZFSet.pair p q ∈ restrictionGraph A B ∧ q ∈ D)

end TuringRigidity.InternalCohenProjectedGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalColumnExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalColumnExtension
open TransitiveNameModel BoundedSetTheory CountableForcing
open CohenGroundPoset InternalCohenRestriction InternalCohenFactor InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] CohenNiceNameConstruction.cohenTop

noncomputable def filterImage (A B g : ZFSet.{0}) : ZFSet.{0} :=
  (conditions B).sep (fun q => ∃ p ∈ g, ZFSet.pair p q ∈ restrictionGraph A B)

end TuringRigidity.InternalColumnExtension

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenFactorReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenFactorReconstruction
open TransitiveNameModel BoundedSetTheory CountableForcing
open CohenGroundPoset InternalCohenFactor InternalCohenPartition InternalCohenRestriction
open InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def reconstruct (A B j l : ZFSet.{0}) : ZFSet.{0} :=
  (conditions A).sep (fun p => ∃ b ∈ j, ∃ d ∈ l,
    ZFSet.pair p b ∈ restrictionGraph A B ∧ ZFSet.pair p d ∈ restrictionGraph A (A \ B))

end TuringRigidity.CohenFactorReconstruction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenProductSplitting
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenProductSplitting
open TransitiveNameModel BoundedSetTheory TaggedProductConditions CohenGroundPoset
open CohenSymmetry
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def productMap (a b c : ZFSet.{0})
    (hc : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (x : Conditions a × Conditions b) : Conditions c :=
  equivShrink c ⟨code (label a x.1) (label b x.2),
    (hc _).mpr ⟨_,label_mem _ _,_,label_mem _ _,rfl⟩⟩

theorem label_productMap (a b c : ZFSet.{0})
    (hc : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (x : Conditions a × Conditions b) :
    label c (productMap a b c hc x) = code (label a x.1) (label b x.2) := by
  simp only [productMap,label,Equiv.symm_apply_apply]

noncomputable def productIso (a b c : ZFSet.{0})
    (hc : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s) :
    (Conditions a × Conditions b) ≃o Conditions c :=
  { Equiv.ofBijective (productMap a b c hc) ⟨by
      intro x y h
      have he := congrArg (label c) h
      rw [label_productMap,label_productMap,code_injective] at he
      exact Prod.ext (label_injective a he.1) (label_injective b he.2),by
      intro z
      obtain ⟨p,hp,s,hs,he⟩ := (hc _).mp (label_mem c z)
      obtain ⟨p,rfl⟩ := label_surjective a hp
      obtain ⟨s,rfl⟩ := label_surjective b hs
      exact ⟨(p,s),label_injective c ((label_productMap a b c hc (p,s)).trans he.symm)⟩⟩ with
    map_rel_iff' := by
      intro x y
      change label c (productMap a b c hc y) ⊆ label c (productMap a b c hc x) ↔ _
      rw [label_productMap,label_productMap,code_subset]
      rfl }

end TuringRigidity.CohenProductSplitting

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalRegularOperations
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalRegularOperations
open Set TransitiveNameModel BoundedSetTheory RegularCompletion
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

def decode (c U : ZFSet.{0}) (hU : Lower c U) : LowerSet (Conditions c) where
  carrier := {p | label c p ∈ U}
  lower' := by
    intro p q hpq hq
    exact hU _ hq _ (label_mem c q) hpq

theorem decode_injective (c U V : ZFSet.{0}) (hUc : U ⊆ c) (hVc : V ⊆ c)
    (hU : Lower c U) (hV : Lower c V) :
    decode c U hU = decode c V hV → U = V := by
  intro h
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨p,rfl⟩ := label_surjective c (hUc hz)
    exact (show label c p ∈ U ↔ label c p ∈ V from
      SetLike.ext_iff.mp h p).mp hz
  · intro hz
    obtain ⟨p,rfl⟩ := label_surjective c (hVc hz)
    exact (show label c p ∈ U ↔ label c p ∈ V from
      SetLike.ext_iff.mp h p).mpr hz

theorem decode_neg (c U : ZFSet.{0}) (hUc : U ⊆ c) (hU : Lower c U) :
    decode c (neg c U) (neg_lower c U) = (decode c U hU)ᶜ := by
  apply SetLike.ext
  intro p
  rw [RegularCompletion.mem_compl]
  change (label c p ∈ neg c U) ↔ _
  rw [neg,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,hp⟩ q hqp hq
    exact hp (label c q) hq hqp
  · intro hp
    refine ⟨label_mem c p,?_⟩
    intro q hq hpq
    obtain ⟨q,rfl⟩ := label_surjective c (hUc hq)
    exact hp q hpq hq

theorem regular_idempotent (c U : ZFSet.{0}) : regular c (regular c U) = regular c U := by
  apply decode_injective c _ _ (neg_subset c _) (neg_subset c _)
    (neg_lower c _) (neg_lower c _)
  simp only [regular,decode_neg c _ (neg_subset c _) (neg_lower c _),compl_compl_compl]

theorem neg_regular (c U : ZFSet.{0}) (hUc : U ⊆ c) (hU : Lower c U) : regular c (neg c U) = neg c U := by
  apply decode_injective c _ _ (neg_subset c _) (neg_subset c _) (neg_lower c _) (neg_lower c _)
  rw [decode_neg c _ (neg_subset c _) (neg_lower c _),
    decode_neg c _ (neg_subset c _) (neg_lower c _)]
  rw [decode_neg c U hUc hU]
  exact compl_compl_compl _

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
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem neg_isCode (c U : ZFSet.{0}) (hU : IsCode c U) : IsCode c (neg c U) :=
  ⟨neg_subset c U,neg_regular c U hU.1 (code_lower c U hU)⟩

theorem regular_isCode (c U : ZFSet.{0}) : IsCode c (regular c U) :=
  ⟨neg_subset c _,regular_idempotent c U⟩

theorem join_isCode (c F : ZFSet.{0}) : IsCode c (supCode c F) := regular_isCode c _

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

theorem negFormula_spec (c U V : ℕ) (e : ℕ → ZFSet.{0}) :
    (negFormula c U V).Eval e ↔ e V = neg (e c) (e U) := by
  simp only [negFormula,Formula.Eval,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,cons_zero,cons_succ]
  constructor
  · rintro ⟨hVc,hV⟩
    apply ZFSet.ext
    intro p
    rw [neg,ZFSet.mem_sep]
    exact ⟨fun h => ⟨hVc h,(hV p (hVc h)).mp h⟩,fun h => (hV p h.1).mpr h.2⟩
  · intro h
    rw [h]
    refine ⟨neg_subset _ _,fun p hp => ?_⟩
    exact (ZFSet.mem_sep).trans (and_iff_right hp)

def closedFormula (c B Q A : ℕ) : Formula :=
  .conj (.subset A B) (.conj
    (.allMem A (.existsMem (A+1) (negFormula (c+2) 1 0)))
    (.allMem Q (.imp (.subset 0 (A+1))
      (.existsMem (A+1) (supFormula (c+2) 1 0)))))

end TuringRigidity.InternalBooleanSyntax

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

theorem subset_supCode (c F : ZFSet.{0}) (hF : ∀ U ∈ F, IsCode c U)
    {U : ZFSet.{0}} (hU : U ∈ F) : U ⊆ supCode c F :=
  (supCode_le_iff c F _ hF (join_isCode c F)).mp (fun _ h => h) U hU

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

theorem inf_eq_neg_sup (c B F : ZFSet.{0})
    (hB : ∀ U ∈ B, IsCode c U) (hF : F ⊆ B)
    (hN : ∀ U ∈ F, neg c U ∈ B) :
    infCode c F = neg c (supCode c (complements c B F)) := by
  have hFc := fun U hU => hB U (hF hU)
  have hNc : ∀ V ∈ complements c B F, IsCode c V :=
    fun V hV => hB V (ZFSet.mem_sep.mp hV).1
  have hI := inf_isCode c F hFc
  have hni : supCode c (complements c B F) ⊆ neg c (infCode c F) := by
    apply (supCode_le_iff c _ _ hNc (neg_isCode c _ hI)).mpr
    intro V hV
    obtain ⟨_,U,hU,rfl⟩ := ZFSet.mem_sep.mp hV
    exact neg_antitone c _ U (inf_subset c F hU)
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    apply neg_antitone c _ _ hni
    change p ∈ regular c (infCode c F)
    rwa [hI.2]
  · intro hp
    refine ZFSet.mem_sep.mpr ⟨neg_subset c _ hp,fun U hU => ?_⟩
    have hnU : neg c U ∈ complements c B F :=
      ZFSet.mem_sep.mpr ⟨hN U hU,U,hU,rfl⟩
    have hx := neg_antitone c _ _ (subset_supCode c _ hNc hnU) hp
    change p ∈ regular c U at hx
    rwa [(hFc U hU).2] at hx

end TuringRigidity.InternalBooleanProjection

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalProjectedGeneric
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop
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

theorem label_info (A : ZFSet.{0}) (p : Conditions (positive A)) :
    label (positive A) p ∈ A ∧ label (positive A) p ≠ ∅ :=
  ZFSet.mem_sep.mp (label_mem (positive A) p)

end TuringRigidity.InternalProjectedGeneric

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
open TransitiveNameModel BoundedSetTheory CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def embed (a b : ZFSet.{0}) (hab : a ⊆ b) (p : Conditions a) : Conditions b :=
  equivShrink b ⟨label a p,hab (label_mem a p)⟩

theorem label_embed (a b : ZFSet.{0}) (hab : a ⊆ b) (p : Conditions a) :
    label b (embed a b hab p) = label a p := by simp [embed,label]

theorem embed_le_iff (a b : ZFSet.{0}) (hab : a ⊆ b) (p q : Conditions a) :
    embed a b hab p ≤ embed a b hab q ↔ p ≤ q := by
  change label b (embed a b hab q) ⊆ label b (embed a b hab p) ↔ _
  rw [label_embed,label_embed]; rfl

noncomputable def push (a b : ZFSet.{0}) (hab : a ⊆ b) (G : GenericFilter (Conditions a)) :
    GenericFilter (Conditions b) where
  carrier := {q | ∃ p ∈ G.carrier, embed a b hab p ≤ q}
  nonempty := by obtain ⟨p,hp⟩ := G.nonempty; exact ⟨embed a b hab p,p,hp,le_rfl⟩
  upper := by rintro p q hpq ⟨r,hr,hrp⟩; exact ⟨r,hr,hrp.trans hpq⟩
  directed := by
    rintro p q ⟨s,hs,hsp⟩ ⟨t,ht,htq⟩
    obtain ⟨r,hr,hrs,hrt⟩ := G.directed hs ht
    exact ⟨embed a b hab r,⟨r,hr,le_rfl⟩,
      ((embed_le_iff a b hab r s).mpr hrs).trans hsp,
      ((embed_le_iff a b hab r t).mpr hrt).trans htq⟩

end TuringRigidity.InternalDenseInclusion

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenPrefixDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenPrefixDensity
open TransitiveNameModel BoundedSetTheory InternalCohen CohenConditionCode InternalFiniteSubsets
attribute [local instance] InternalCollapse.order

theorem word_isCondition (s : List Bool) : IsCondition ZFSet.omega (wordCode s) := by
  refine ⟨(mem_finiteSubsets_iff _ _).mpr ⟨?_,?_⟩,?_⟩
  · intro z hz
    obtain ⟨i,rfl⟩ := (mem_wordCode s z).mp hz
    exact ZFSet.pair_mem_prod.mpr ⟨(mem_omega _).mpr ⟨i.val,rfl⟩,
      (mem_alphabet _).mpr ⟨_,rfl⟩⟩
  · rw [wordCode,ZFSet.coe_range]; exact Set.finite_range _
  · intro x _ b _ c _ hxb hxc
    obtain ⟨i,hi⟩ := (mem_wordCode s _).mp hxb
    have hxn := (ZFSet.pair_inj.mp hi).1
    exact (wordCode_function s).functional
      (hxn.symm ▸ (natSet_mem_natSet _ _).mpr i.isLt) hxb hxc

theorem conditions_subset : InternalCohen.conditions ⊆ CohenGroundPoset.conditions ZFSet.omega := by
  intro p hp
  obtain ⟨s,rfl⟩ := (prefix_iff_wordCode p).mp ((mem_conditions p).mp hp)
  exact (CohenGroundPoset.mem_conditions _ _).mpr (word_isCondition s)

end TuringRigidity.CohenPrefixDensity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenBitFlip
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenBitFlip
open TransitiveNameModel BoundedSetTheory CohenGroundPoset CohenConditionCode CohenSymmetry
open InternalCohen (alphabet bitSet mem_alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

def FlipMatches (A B p q : ZFSet.{0}) : Prop :=
  ∀ x ∈ A,
    (ZFSet.pair x (bitSet false) ∈ q ↔
      (x ∈ B ∧ ZFSet.pair x (bitSet true) ∈ p) ∨
      (x ∉ B ∧ ZFSet.pair x (bitSet false) ∈ p)) ∧
    (ZFSet.pair x (bitSet true) ∈ q ↔
      (x ∈ B ∧ ZFSet.pair x (bitSet false) ∈ p) ∨
      (x ∉ B ∧ ZFSet.pair x (bitSet true) ∈ p))

noncomputable def flipIso (A B : ZFSet.{0}) :
    Conditions (conditions A) ≃o Conditions (conditions A) :=
  (conditionEquiv A).symm.trans
    ((CohenSymmetry.flipIso (mask A B)).trans (conditionEquiv A))

noncomputable def flipGraph (A B : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod (conditions A) (conditions A)).sep (fun z =>
    ∃ p ∈ conditions A, ∃ q ∈ conditions A,
      z = ZFSet.pair p q ∧ FlipMatches A B p q)

end TuringRigidity.InternalCohenBitFlip

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenPrefixOverwrite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.CohenFiniteFlip
open TransitiveNameModel BoundedSetTheory CountableForcing InternalCollapse
open CohenGroundPoset InternalCohenBitFlip CohenColumnRealName FiniteOverwrite
open InternalCohen (bitSet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

noncomputable def prefixFilter (K a : ZFSet.{0}) (s : List Bool) (A : Oracle)
    (G : GenericFilter (Conditions (poset K))) : GenericFilter (Conditions (poset K)) :=
  AutomorphismName.mapFilter (flipIso (ZFSet.prod K ZFSet.omega) (prefixMask a s A)) G

end TuringRigidity.CohenFiniteFlip

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericalCohenSets
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory Encodable

noncomputable def wordPullback (D : ZFSet.{0}) : Oracle := fun n => by
  classical
  exact decide (wordCode (EncodedForcing.word n) ∈ D)

noncomputable def wordImage (A : Oracle) : ZFSet.{0} :=
  ZFSet.sep (fun q => ∃ n ∈ realCode A, ZFSet.pair n q ∈ wordCodeGraph) conditions

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenPrefixReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory UniformArithmetic Encodable
open CohenBorelForcing ShuffleRequirements
open EncodedForcing (word word_primrec)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def prefixCodes (A : Oracle) : Oracle :=
  arithmeticReal (fun O n => Realizes (word n) (O 0)) (fun _ => A)

end TuringRigidity.InternalCohen

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

noncomputable def witness (p : SentenceForm) (xs : List ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if h : ∃ x : ZFSet.{u}, p.Sat Set.univ (cons x (listEnv xs)) then Classical.choose h else ∅

noncomputable def stage (a : ℕ → ZFSet.{u}) : ℕ → Set ZFSet.{u}
  | 0 => Set.range a
  | n+1 => stage a n ∪ {x | ∃ p : SentenceForm, ∃ xs : List ZFSet.{u},
      (∀ y ∈ xs, y ∈ stage a n) ∧ x = witness p xs}

noncomputable def hull (a : ℕ → ZFSet.{u}) : Set ZFSet.{u} := ⋃ n, stage a n

theorem stage_countable (a : ℕ → ZFSet.{u}) (n : ℕ) : (stage a n).Countable := by
  induction n with
  | zero => exact Set.countable_range a
  | succ n ih =>
    apply ih.union
    let : Countable (stage a n) := ih.to_subtype
    have hc := Set.countable_range (fun z : SentenceForm × List (stage a n) =>
      witness z.1 (z.2.map Subtype.val))
    apply hc.mono
    rintro x ⟨p,xs,hxs,rfl⟩
    let ys : List (stage a n) := xs.attach.map (fun y => ⟨y.val,hxs y.val y.property⟩)
    have hy : ys.map Subtype.val = xs := by simp [ys,List.map_map]
    exact ⟨(p,ys),by simp only [hy]⟩

theorem hull_countable (a : ℕ → ZFSet.{u}) : (hull a).Countable :=
  Set.countable_iUnion (stage_countable a)

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ElementaryCollapse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse
universe u

noncomputable def hullSet (a : ℕ → ZFSet.{u}) : ZFSet.{u} := by
  letI : Countable (hull a) := (hull_countable a).to_subtype
  letI : Small.{u} (hull a) := Countable.toSmall _
  exact ZFSet.range (fun x : hull a => x.val)

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ElementarySatisfaction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse
universe u

def Valid (M : ZFSet.{u}) : Prop :=
  ∀ p : SentenceForm, (∀ e : ℕ → ZFSet.{u}, p.Sat Set.univ e) →
    ∀ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ M) → p.Sat (M : Set ZFSet) e

noncomputable def fromBounded : Formula → SentenceForm
  | .equal i j => .equal i j
  | .member i j => .member i j
  | .conj p q => .conj (fromBounded p) (fromBounded q)
  | .neg p => .neg (fromBounded p)
  | .existsMem i p => .ex (.conj (.member 0 (i+1)) (fromBounded p))

noncomputable def fromSigma : SigmaFormula → SentenceForm
  | .bounded p => fromBounded p
  | .existsSet p => .ex (fromSigma p)

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_FullSetForcing
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.FullSetForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
open ElementaryModel SentenceForm BoundedForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

def Forces (M : ZFSet.{u}) (e : ℕ → Name (Conditions c)) : SentenceForm → Conditions c → Prop
  | .equal i j, p => EqForces (e i) (e j) p
  | .member i j, p => MemForces (e i) (e j) p
  | .conj φ ψ, p => Forces M e φ p ∧ Forces M e ψ p
  | .neg φ, p => ∀ q, q ≤ p → ¬ Forces M e φ q
  | .ex φ, p => ∃ a : Name (Conditions c), a.encode (label c) ∈ M ∧ Forces M (push a e) φ p

noncomputable def code : SentenceForm → ℕ → ℕ → ℕ → (ℕ → ℕ) → SentenceForm
  | .equal i j, ci,oi,pi,v => fromSigma (SigmaCode.forcing (.bounded (.equal i j)) ci oi pi v)
  | .member i j, ci,oi,pi,v => fromSigma (SigmaCode.forcing (.bounded (.member i j)) ci oi pi v)
  | .conj φ ψ, ci,oi,pi,v => .conj (code φ ci oi pi v) (code ψ ci oi pi v)
  | .neg φ, ci,oi,pi,v => all (imp (.member 0 (ci+1))
      (imp (fromBounded (Formula.pairMem 0 (pi+1) (oi+1)))
        (.neg (code φ (ci+1) (oi+1) 0 (fun i => v i+1)))))
  | .ex φ, ci,oi,pi,v => .ex (.conj (fromSigma (NameValidity.Code.valid (ci+1) 0))
      (code φ (ci+1) (oi+1) (pi+1) (push 0 (fun i => v i+1))))

end TuringRigidity.FullSetForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenHomogeneity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenBitFlip
open TransitiveNameModel BoundedSetTheory CohenGroundPoset CohenConditionCode CohenSymmetry
open InternalCohen (alphabet bitSet mem_alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def matchingSet (A p q : ZFSet.{0}) : ZFSet.{0} :=
  A.sep (fun x =>
    (ZFSet.pair x (bitSet true) ∈ p ∧ ZFSet.pair x (bitSet true) ∉ q) ∨
    (ZFSet.pair x (bitSet true) ∉ p ∧ ZFSet.pair x (bitSet true) ∈ q))

end TuringRigidity.InternalCohenBitFlip

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenOddHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory UniformArithmetic Encodable
open ShuffleRequirements CohenBorelForcing CountableForcing
open EncodedForcing (word word_primrec)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def oddHitCodes (N : ℕ) : Oracle :=
  arithmeticReal (fun (_ : Oracles) v => OddHit N (word v)) (fun _ => decodeReal (∅ : ZFSet.{0}))

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenReindex
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenReindex
open TransitiveNameModel BoundedSetTheory CohenGroundPoset CohenConditionCode CohenSymmetry
open InternalCohen (alphabet bitSet mem_alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

def Matches (A B f p q : ZFSet.{0}) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, ZFSet.pair x y ∈ f → ∀ b ∈ alphabet,
    (ZFSet.pair x b ∈ p ↔ ZFSet.pair y b ∈ q)

noncomputable def reindexIso (A B : ZFSet.{0}) (e : Conditions A ≃ Conditions B) :
    Conditions (conditions A) ≃o Conditions (conditions B) :=
  (conditionEquiv A).symm.trans ((CohenCoordinates.reindex e).trans (conditionEquiv B))

noncomputable def reindexGraph (A B f : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod (conditions A) (conditions B)).sep (fun z =>
    ∃ p ∈ conditions A, ∃ q ∈ conditions B, z = ZFSet.pair p q ∧ Matches A B f p q)

end TuringRigidity.InternalCohenReindex

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenRequirements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory CohenBorelForcing CountableForcing
open FiniteShuffle ShuffleRequirements
attribute [local instance] BoundedSetTheory.InternalCollapse.order
  BoundedSetTheory.InternalCollapse.collapsePreorder

def openRequirement (E : ZFSet.{0}) (s : List Bool) : Prop :=
  ∃ t : Condition, t.word <+: s ∧ wordCode t.word ∈ E

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenTailHomogeneity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenTailHomogeneity
open TransitiveNameModel BoundedSetTheory CohenGroundPoset CohenConditionCode CohenSymmetry
open InternalCohenBitFlip InternalCohenRestriction
open InternalCohen (alphabet bitSet mem_alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder Classical.propDecidable

noncomputable def tailMatchingSet (A B p q : ZFSet.{0}) : ZFSet.{0} :=
  (matchingSet A p q).sep (fun x => x ∉ B)

end TuringRigidity.InternalCohenTailHomogeneity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteShuffleCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.FiniteShuffleCertificate
open FiniteShuffle ShuffleRequirements GenericCoding

def Certificate (D : List Bool → Prop) (q : List Bool) : Prop :=
  ∃ k : ℕ, 2*k ≤ q.length ∧ ∀ s : List Bool, s.length = k →
    ∃ l ≤ k, D (initial (code (fun i => s.getD i false) (fun i => q.getD i false)) l)

end TuringRigidity.FiniteShuffleCertificate

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteShuffleComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.FiniteShuffleComputation
open Encodable EncodedForcing GenericCoding FiniteShuffle UniformOracle BinarySeries

def finiteShuffleWord (u v l : ℕ) : ℕ :=
  encode (initial (code (fun i => (word u).getD i false)
    (fun i => (word v).getD i false)) l)

end TuringRigidity.FiniteShuffleComputation

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

def DegreeOrderFormula (φ : Formula) : Prop := ∀ o Q z x y : ℕ, ∀ e : ℕ → ZFSet.{u},
    e o = ZFSet.omega → (∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q) →
    e z = natSet 0 → ∀ A B : Oracle, e x = realCode A → e y = realCode B →
      ((Formula.twoOracles φ o Q z x y).Eval e ↔ Reduces A B)

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_ParameterCoveringModels
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse
universe u

noncomputable def realSeed (A : ℕ → Oracle) (n : ℕ) : ZFSet.{u} :=
  if n.unpair.1 = 0 then natSet n.unpair.2 else realCode (A n.unpair.2)

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_AmbientDegreeSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.FullSetForcing
open BoundedSetTheory TransitiveNameModel ElementaryModel SentenceForm
universe u

noncomputable def definedSet (s : ℕ) (p : Formula) : SentenceForm :=
  all (SentenceForm.iff (.member 0 (s+1)) (fromBounded p))

noncomputable def ownPower (a s : ℕ) : SentenceForm :=
  definedSet s (.subset 0 (a+1))

end TuringRigidity.FullSetForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_CommonGenericModels
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalGeneric
open TransitiveNameModel CountableForcing
universe u

instance extension_countable (M c : ZFSet.{u}) [Countable (Conditions M)] (G : Set (Conditions c)) :
    Countable (Conditions (genericExtensionSet M c G)) := by
  have hM : (M : Set ZFSet.{u}).Countable := by
    apply (Set.countable_range (label M)).mono
    intro x hx
    exact label_surjective M hx
  have hE : (genericExtensionSet M c G : Set ZFSet.{u}).Countable := by
    rw [genericExtensionSet_coe]
    exact genericExtension_countable M c hM G
  let : Countable (genericExtensionSet M c G : Set ZFSet.{u}) := hE.to_subtype
  exact Function.Injective.countable (f := fun p : Conditions (genericExtensionSet M c G) =>
    (⟨label _ p,label_mem _ p⟩ : (genericExtensionSet M c G : Set ZFSet.{u})))
    (fun x y h => label_injective _ (congrArg (fun z : (genericExtensionSet M c G : Set ZFSet.{u}) => z.val) h))

end TuringRigidity.BoundedSetTheory.InternalGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ElementaryCheckedCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse SentenceForm
universe u

noncomputable def checkedValueFormula : SentenceForm :=
  .ex (.ex (.ex (fromBounded (.conj (CheckFormula.graph 2 1 0 5)
    (.conj (.member 4 2) (.conj (.member 3 1) (.pairMem 4 3 0)))))))

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ElementaryModelIdeal
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse SetDegreeDecoding PersistentRestrictions OracleJump
universe u

theorem model_reals_countable (M : ZFSet.{u}) [Countable (Conditions M)] : (modelReals M).Countable := by
  have hc : (M : Set ZFSet.{u}).Countable := by
    apply (Set.countable_range (label M)).mono
    intro x hx; exact label_surjective M hx
  apply (hc.image decodeReal).mono
  intro A hA
  exact ⟨realCode A,hA,decodeReal_realCode A⟩

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanTop
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanTop
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder
open InternalBooleanSyntax InternalBooleanProjection InternalProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

@[instance_reducible]
noncomputable def booleanTop (c A : ZFSet.{0}) (hcA : c ∈ A) (hc0 : c ≠ ∅) :
    Top (Conditions (positive A)) :=
  ⟨Classical.choose (label_surjective (positive A) (ZFSet.mem_sep.mpr ⟨hcA,hc0⟩))⟩

end TuringRigidity.InternalBooleanTop

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanName
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax
open InternalBooleanBits InternalProjectedGeneric InternalBooleanTop
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

noncomputable def tags (c A : ZFSet.{0}) (E : ℕ → ZFSet.{0}) (n : ℕ) : ZFSet.{0} :=
  (positive A).sep (fun U => U = bitCode c (E n))

noncomputable def booleanName (c A : ZFSet.{0}) [Top (Conditions (positive A))]
    (E : ℕ → ZFSet.{0}) : Name (Conditions (positive A)) :=
  InternalNiceName.nice (tags c A E)

end TuringRigidity.InternalBooleanName

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanExtension
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax
open InternalProjectedGeneric InternalBooleanTop InternalBooleanName InternalBooleanGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

noncomputable def hitSet (A g : ZFSet.{0}) : ZFSet.{0} :=
  (positive A).sep (fun U => ∃ p ∈ g, p ∈ U)

end TuringRigidity.InternalBooleanExtension

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCommonRequirements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalCommonRequirements
open TransitiveNameModel BoundedSetTheory InternalCohen Encodable UniformArithmetic
open EncodedForcing (word)
open TaggedProductConditions (code)
open CountableForcing CohenProductSplitting
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def requirementCodes (A : Oracle) (p q : OracleCode) : Oracle :=
  arithmeticReal (fun O n => CommonIdeal.Requirement (O 0) p q
    (word (left n)) (word (right n))) (fun _ => A)

noncomputable def denseSet (c : ZFSet.{0}) (A : Oracle) (p q : OracleCode) : ZFSet.{0} :=
  c.sep (fun z => ∃ s t : List Bool,
    z = code (wordCode s) (wordCode t) ∧ CommonIdeal.Requirement A p q s t)

end TuringRigidity.InternalCommonRequirements

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalShuffleSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory Encodable UniformArithmetic
open FiniteShuffleCertificate FiniteShuffle CohenBorelForcing CountableForcing

def shuffleOpen (D : ZFSet.{0}) (t : List Bool) : Prop :=
  ∃ r : List Bool, wordCode r ∈ D ∧ r <+: t

noncomputable def shuffleOpenCodes (D : ZFSet.{0}) : Oracle :=
  arithmeticReal (fun O n => ∃ r : List Bool, O 0 (encode r) = true ∧ r <+: EncodedForcing.word n)
    (fun _ => wordPullback D)

noncomputable def shuffleCertificateCodes (D : ZFSet.{0}) : Oracle :=
  arithmeticReal (fun O n => Certificate (fun t => O 0 (encode t) = true) (EncodedForcing.word n))
    (fun _ => shuffleOpenCodes D)

noncomputable def shuffleStar (D : ZFSet.{0}) : ZFSet.{0} :=
  conditions.sep (fun q => ∃ w : List Bool, q = wordCode w ∧ Certificate (shuffleOpen D) w)

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_CheckedMembershipSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.FullSetForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
open ElementaryModel SentenceForm
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]

noncomputable def checkedMembershipFormula : SentenceForm :=
  .ex (.conj (checkedValueFormula.rename (fun i => match i with | 0 => 0 | 1 => 1 | _ => 6))
    (code (.member 0 1) 2 3 4 (fun i => match i with | 0 => 0 | _ => 5)))

noncomputable def checkedValueSigma : SigmaFormula :=
  .existsSet (.existsSet (.existsSet (.bounded (.conj (CheckFormula.graph 2 1 0 5)
    (.conj (.member 4 2) (.conj (.member 3 1) (.pairMem 4 3 0)))))))

noncomputable def checkedMembershipSigma : SigmaFormula :=
  .existsSet (.conj
    (checkedValueSigma.rename (fun i => match i with | 0 => 0 | 1 => 1 | _ => 6))
    (BoundedForcing.SigmaCode.forcing (.bounded (.member 0 1)) 2 3 4
      (fun i => match i with | 0 => 0 | _ => 5)))

end TuringRigidity.FullSetForcing

end OAI
end


