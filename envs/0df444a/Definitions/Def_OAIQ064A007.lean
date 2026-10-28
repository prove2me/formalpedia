-- Prove2me | Definitions.Def_OAIQ064A007
-- name    : OAIQ064A007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T00:31:51.850216+00:00
-- url     : https://prove2.me/theorems/434dc10f-1164-4f45-a226-f5da308ad529
-- title:
--   Definitions bundle OAIQ064A007 of the split of OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 129 declarations of OpenAI's Lean: 105 definitions, 3 inductive types or structures, 1 instance and 20 theorems. The definitions and types are `OAI.TuringRigidity.InternalGraphEquiv.graphEquiv`, `OAI.TuringRigidity.InternalGraphEquiv.graphMap`, `OAI.TuringRigidity.InternalPositiveNameFamily.positive`, `OAI.TuringRigidity.JumpIdeal.generated`, `OAI.TuringRigidity.LocalAgreement.Cert`, `OAI.TuringRigidity.LocalAgreement.NoDisagreement`, `OAI.TuringRigidity.LocalColumnCertificates.Bad`, `OAI.TuringRigidity.LocalComputability.initial`, `OAI.TuringRigidity.LocalPair.Decisive`, `OAI.TuringRigidity.LocalPair.Outcome`, `OAI.TuringRigidity.NumericSyntax.Covers`, `OAI.TuringRigidity.NumericSyntax.Domain`, `OAI.TuringRigidity.NumericSyntax.Numeric`, `OAI.TuringRigidity.NumericSyntax.params`, `OAI.TuringRigidity.NumericSyntax.stageInputs`, `OAI.TuringRigidity.NumericalCohenProductSets.image`, `OAI.TuringRigidity.OrdinalArithmetic.ordinalAllMem`, `OAI.TuringRigidity.OrdinalArithmetic.productBundleSigma`, `OAI.TuringRigidity.OrdinalArithmetic.productMatrix`, `OAI.TuringRigidity.OrdinalArithmetic.productSigma`, `OAI.TuringRigidity.OrdinalArithmetic.sumMatrix`, `OAI.TuringRigidity.PersistentRestrictions.invariantHull`, `OAI.TuringRigidity.RationalCoding.divideIndex`, `OAI.TuringRigidity.RationalCoding.scalarLeft`, `OAI.TuringRigidity.RationalCoding.scalarRight`, `OAI.TuringRigidity.RealGeneratedModel.Contains`, `OAI.TuringRigidity.RealGeneratedModel.hull`, `OAI.TuringRigidity.RecoveryData`, `OAI.TuringRigidity.RecoveryData.branchOracle`, `OAI.TuringRigidity.RecoveryData.count`, `OAI.TuringRigidity.RecoveryData.cutTrial`, `OAI.TuringRigidity.RecoveryData.highBit`, `OAI.TuringRigidity.RecoveryData.test`, `OAI.TuringRigidity.RegularBinaryTree.children`, `OAI.TuringRigidity.RegularBinaryTree.tree`, `OAI.TuringRigidity.RegularTreeCofinality.nodesBelow`, `OAI.TuringRigidity.RegularTreeFilter.branch`, `OAI.TuringRigidity.RegularTreeRecovery.branchSet`, `OAI.TuringRigidity.RegularTreeRun.bit`, `OAI.TuringRigidity.RegularTreeRun.run` and 68 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DegreeRigidity_CohenForcing_RestrictedForcingFilter`, `DegreeRigidity_CohenForcing_TaggedProductConditions`, `DegreeRigidity_CohenForcing_TaggedProductGeneric`, `DegreeRigidity_CohenForcing_TaggedProductRecovery`, `DegreeRigidity_Computability_ArithmeticFreeConstruction`, `DegreeRigidity_Computability_BranchFrequency`, `DegreeRigidity_Computability_BranchRecovery`, `DegreeRigidity_Computability_EffectiveRecovery`, `DegreeRigidity_Computability_JumpIdeal`, `DegreeRigidity_Computability_OracleCode`, `DegreeRigidity_Computability_RecoverySetup`, `DegreeRigidity_Computability_ScalarCoding`, `DegreeRigidity_Constructibility_ConstructibleSatisfaction`, `DegreeRigidity_Constructibility_ConstructibleStages`, `DegreeRigidity_Constructibility_ConstructionInputData`, `DegreeRigidity_Constructibility_ConstructionStageBound`, `DegreeRigidity_Constructibility_DefSystemCertificate`, `DegreeRigidity_Constructibility_FiniteStageDefinition`, `DegreeRigidity_Constructibility_HierarchyGraph`, `DegreeRigidity_Constructibility_HierarchyWitnessCollection`, `DegreeRigidity_Constructibility_PersistentRestrictions`, `DegreeRigidity_Constructibility_RelativeConstruction`, `DegreeRigidity_Constructibility_RelativeModel`, `DegreeRigidity_Constructibility_RelativeSigmaSchemas`, `DegreeRigidity_Constructibility_SeedBoundStageSyntax`, `DegreeRigidity_Constructibility_SingleRealConstruction`, `DegreeRigidity_Constructibility_UniformInternalSatisfaction`, `DegreeRigidity_Constructibility_UniformTruthRecursion`, `DegreeRigidity_Constructibility_UniformTruthStep`, `DegreeRigidity_Effective_FiniteRealPacking`, `DegreeRigidity_Effective_LocalAgreement`, `DegreeRigidity_Effective_LocalColumnCertificates`, `DegreeRigidity_Effective_LocalComputability`, `DegreeRigidity_Effective_LocalPair`, `DegreeRigidity_Effective_OrderNormalForm`, `DegreeRigidity_Effective_TupleLookupAdequacy`, `DegreeRigidity_Effective_TupleSystemCertificate`, `DegreeRigidity_Effective_UniformCohenJump`, `DegreeRigidity_OrdinalCodes_NumericDomain`, `DegreeRigidity_OrdinalCodes_NumericParameters`, `DegreeRigidity_OrdinalCodes_NumericStage`, `DegreeRigidity_OrdinalCodes_NumericalCohenProductSets`, `DegreeRigidity_OrdinalCodes_OmegaStageSyntax`, `DegreeRigidity_OrdinalCodes_OrdinalOrderTypeSyntax`, `DegreeRigidity_OrdinalCodes_OrdinalProductReplacement`, `DegreeRigidity_OrdinalCodes_OrdinalProductSyntax`, `DegreeRigidity_OrdinalCodes_OrdinalSumSyntax`, `DegreeRigidity_OrdinalCodes_ProductCertificateCollection`, `DegreeRigidity_Representation_GenericFilterName`, `DegreeRigidity_Representation_OwnProgramValue`, `DegreeRigidity_Representation_OwnRealsConstruction`, `DegreeRigidity_Representation_RealGeneratedModel`, `DegreeRigidity_SetModels_InternalGraphEquiv`, `DegreeRigidity_SetModels_InternalPositiveNameFamily`, `DegreeRigidity_SetModels_InternalSatisfactionSlice`, `DegreeRigidity_SetModels_RegularBinaryTree`, `DegreeRigidity_SetModels_RegularTreeCofinality`, `DegreeRigidity_SetModels_RegularTreeFilter`, `DegreeRigidity_SetModels_RegularTreeRecovery`, `DegreeRigidity_SetModels_RegularTreeRun`, `DegreeRigidity_SetModels_SetModelArithmeticSyntax`, `DegreeRigidity_SetModels_SetModelFunctionGraphs`, `DegreeRigidity_Syntax_CheckedDefSuccessor`, `DegreeRigidity_Syntax_CheckedHierarchySyntax`, `DegreeRigidity_Syntax_DefinablePower`, `DegreeRigidity_Syntax_DefinableSubsetCertificates`, `DegreeRigidity_Syntax_FiniteGraphSatisfaction`, `DegreeRigidity_Syntax_FiniteSatisfactionCertificate`, `DegreeRigidity_Syntax_SatisfactionRecursion`, `DegreeRigidity_Syntax_SatisfactionSystemCertificate`, `DegreeRigidity_Syntax_SentenceCode`, `DegreeRigidity_Syntax_SentenceCodeFamily`, `DegreeRigidity_Syntax_SentenceSupportCertificate`, `DegreeRigidity_Syntax_SetSatisfactionBounded`.
--
--   **Imports.** It imports the published bundle `Def_DegreeRigidity`; the bundles `OAIQ064A002`, `OAIQ064A003` and `OAIQ064A004` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ064A008`; the statements `OAI.TuringRigidity.ArithmeticTree.native_internal_matrix`, `OAI.TuringRigidity.BoundedForcing.projected_arithmetic_output_cone`, `OAI.TuringRigidity.CohenNiceNameConstruction.internal_nice_name`, `OAI.TuringRigidity.GroundIteratedTriple.generic_triple_of_arithmetic`, `OAI.TuringRigidity.InternalCohen.prefix_extension_eq_hull`, `OAI.TuringRigidity.OrdinalArithmetic.internal_explicit_omega_threshold`, `OAI.TuringRigidity.OrdinalArithmetic.relative_omega_power_internal`, `OAI.TuringRigidity.OrdinalCoding.cofinal_padded_code_certificates`, `OAI.TuringRigidity.OrdinalCoding.padded_certificates_of_lower_closure`, `OAI.TuringRigidity.OrdinalCoding.vectorCode_certificates_at_levels`, `OAI.TuringRigidity.OriginalRealCohenFactorization.real_factorization`, `OAI.TuringRigidity.OriginalRealFullIteration.original_name_full_iteration`, `OAI.TuringRigidity.OriginalRealQuotientModel.original_name_quotient`, `OAI.TuringRigidity.RealHullGenericTriple.exists_generic_prefix_triple`, `OAI.TuringRigidity.RealHullGenericTriple.exists_prefix_real`, `OAI.TuringRigidity.RealHullIteration.exists_iterated_pair`, `OAI.TuringRigidity.RealHullIteration.exists_iterated_prefix_pair`, `OAI.TuringRigidity.RelativeConstructible.definablePower_mem`, `OAI.TuringRigidity.RelativeConstructible.ground_relativeModel_ordinal_iff`, `OAI.TuringRigidity.RelativeConstructible.ground_relative_context`, `OAI.TuringRigidity.RelativeConstructible.hierarchyGraph_sigmaDefinable`, `OAI.TuringRigidity.RelativeConstructible.hierarchy_checked_at_levels`, `OAI.TuringRigidity.RelativeConstructible.hierarchy_witness_collection`, `OAI.TuringRigidity.RelativeConstructible.internal_defSystem`, `OAI.TuringRigidity.RelativeConstructible.internal_defSystem_of_context`, `OAI.TuringRigidity.RelativeConstructible.internal_hierarchyGraph_collection`, `OAI.TuringRigidity.RelativeConstructible.real_hull_prescribed_transfer`, `OAI.TuringRigidity.RelativeConstructible.seed_bound_stage_at_levels`, `OAI.TuringRigidity.RelativeConstructible.stageCertificate_uniformSigma`, `OAI.TuringRigidity.RelativeConstructible.uniform_cohen_definition_extension`, `OAI.TuringRigidity.RelativeConstructible.uniform_hierarchy_certificate`, `OAI.TuringRigidity.RelativeConstructible.uniform_hierarchy_certificate_collection`, `OAI.TuringRigidity.RelativeConstructible.uniform_ordinal_definition_symmetric`, `OAI.TuringRigidity.SetModelCountability.persistent_countable_extensions` and `OAI.TuringRigidity.TwoRealHull.joined_factorization`; the proofs of `OAI.TuringRigidity.ArithmeticTree.native_nonidentity_absolute`, `OAI.TuringRigidity.ArithmeticTree.native_persistence_absolute`, `OAI.TuringRigidity.RelativeConstructible.hierarchy_witness_collection`, `OAI.TuringRigidity.RelativeConstructible.internal_defSystem_of_context`, `OAI.TuringRigidity.RelativeConstructible.internal_hierarchyGraph_collection` and `OAI.TuringRigidity.RelativeConstructible.uniform_hierarchy_certificate`.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A002
import Definitions.Def_OAIQ064A003
import Definitions.Def_OAIQ064A004

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_OracleCode
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

namespace OracleCode

theorem countable_reducible (g : ℕ →. ℕ) :
    {f : ℕ →. ℕ | TuringReducible f g}.Countable := by
  have heq : {f : ℕ →. ℕ | TuringReducible f g} = Set.range (eval g) := by
    ext f
    exact turingReducible_iff_exists_code f g
  rw [heq]
  exact Set.countable_range _

end OracleCode

theorem countable_reduces (B : Oracle) : {A : Oracle | Reduces A B}.Countable := by
  exact (OracleCode.countable_reducible (oracleFunction B)).preimage oracleFunction_injective

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_RecoverySetup
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Topology
namespace TuringRigidity

structure RecoveryData (F : ℝ → Oracle) (t u v : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt_one : radius < 1
  lo : ℝ
  hi : ℝ
  lo_gt : -radius < lo
  lo_neg : lo < 0
  hi_pos : 0 < hi
  hi_lt : hi < radius
  delta : ℚ
  delta_pos : 0 < delta
  delta_lt : (delta : ℝ) < radius
  delta_gap : 3*(delta : ℝ) < hi-lo
  bit : ℕ
  forward : ℕ
  backward : ℕ
  left : ∀ s ∈ rationalSpan t, s ∈ Icc lo (lo+(delta : ℝ)) →
    F (u+s) bit ≠ F (u+hi) bit
  right : ∀ s ∈ rationalSpan t, s ∈ Icc (hi-(delta : ℝ)) hi →
    F (u+s) bit = F (u+hi) bit
  forward_correct : ∀ s ∈ rationalSpan t, ∀ a ∈ rationalSpan t,
    |s| < radius → |a| < radius →
      OracleCode.eval (oracleFunction (join (F (u+s)) (F (v-u+a))))
        (codeEnumeration forward) = oracleFunction (F (v+s+a))
  backward_correct : ∀ s ∈ rationalSpan t, |s| < radius →
    OracleCode.eval (oracleFunction (join (F (v+s)) (F (u-v))))
      (codeEnumeration backward) = oracleFunction (F (u+s))

namespace RecoveryData
variable {F : ℝ → Oracle} {t u v : ℝ}

def test (d : RecoveryData F t u v) (s : ℝ) : Bool :=
  decide (F (u+s) d.bit = F (u+d.hi) d.bit)

end RecoveryData

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_BranchRecovery
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

namespace RecoveryData
variable {F : ℝ → Oracle} {t u v : ℝ}

def highBit (d : RecoveryData F t u v) : ℕ := if F (u+d.hi) d.bit then 1 else 0

def branchOracle (d : RecoveryData F t u v) : Oracle :=
  fun n => d.test (state d.test (d.delta : ℝ) t n)

end RecoveryData
end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_BranchFrequency
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

namespace RecoveryData
variable {F : ℝ → Oracle} {t u v : ℝ}

def count (d : RecoveryData F t u v) : ℕ → ℕ :=
  UniformOracle.runningSum (fun n => if d.branchOracle n then 1 else 0)

end RecoveryData
end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ScalarCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
namespace RationalCoding

def scalarLeft (r : ℕ) (z : ℕ × ℕ) : ℕ :=
  (positiveNumerator r*positiveNumerator z.2 + negativeNumerator r*negativeNumerator z.2)*denominator z.1 +
    negativeNumerator z.1*denominator r*denominator z.2

def scalarRight (r : ℕ) (z : ℕ × ℕ) : ℕ :=
  (positiveNumerator r*negativeNumerator z.2 + negativeNumerator r*positiveNumerator z.2)*denominator z.1 +
    positiveNumerator z.1*denominator r*denominator z.2

def divideIndex (r : ℚ) (i : ℕ) : ℕ := Encodable.encode (rationalEnumeration i/r)

end RationalCoding
end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_EffectiveRecovery
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

namespace RecoveryData
open RationalCoding EffectiveRecovery
variable {F : ℝ → Oracle} {t u v : ℝ}

def cutTrial (d : RecoveryData F t u v) (i m : ℕ) : Option ℕ :=
  window d.delta.num.natAbs d.delta.den
    (negative i,(numeratorMagnitude i,denominator i),(m+1,d.count (m+1)))

end RecoveryData

end TuringRigidity

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

noncomputable def genericFilterName (p : ZFSet.{u}) [Top (Conditions p)] : Name (Conditions p) :=
  .mk (Conditions p) (fun q => Name.check (label p q)) id

theorem mem_genericFilterSet (p : ZFSet.{u}) (G : Set (Conditions p)) (x : ZFSet.{u}) :
    x ∈ genericFilterSet p G ↔ ∃ q ∈ G, label p q = x := by
  rw [genericFilterSet,ZFSet.mem_range]
  exact ⟨fun ⟨q,hq⟩ => ⟨q.val,q.property,hq⟩,fun ⟨q,hq,hx⟩ => ⟨⟨q,hq⟩,hx⟩⟩

end TuringRigidity.TransitiveNameModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_PersistentRestrictions
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.PersistentRestrictions
open Set

theorem countable_principal_lower (a : Degree) : (Set.Iic a).Countable := by
  obtain ⟨A, rfl⟩ := degree_surjective a
  apply ((countable_reduces A).image degree).mono
  intro b hb
  obtain ⟨B, rfl⟩ := degree_surjective b
  exact ⟨B, (degree_le_iff B A).mp hb, rfl⟩

theorem countable_closureStep (π : Degree ≃o Degree) {S : Set Degree}
    (hS : S.Countable) : (closureStep π S).Countable :=
  hS.union ((hS.image π).union ((hS.image π.symm).union
    ((hS.image2 hS (· ⊔ ·)).union (hS.biUnion fun a _ => countable_principal_lower a))))

theorem countable_stage (π : Degree ≃o Degree) {S : Set Degree}
    (hS : S.Countable) : ∀ n, (stage π S n).Countable
  | 0 => hS.insert ⊥
  | n + 1 => countable_closureStep π (countable_stage π hS n)

def invariantHull (π : Degree ≃o Degree) (S : Set Degree) (hS : S.Countable) :
    CountableIdeal where
  carrier := hullSet π S
  nonempty := ⟨⊥, Set.mem_iUnion.mpr ⟨0, Or.inl rfl⟩⟩
  countable := Set.countable_iUnion (countable_stage π hS)
  lower := fun {_ _} hab hb => hullSet_lower π S hab hb
  join_mem := fun {_ _} ha hb => hullSet_join π S ha hb

end TuringRigidity.PersistentRestrictions

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

noncomputable def definedSubset (A : ZFSet.{u}) (p : SentenceForm)
    {n : ℕ} (v : Fin n → ZFSet.{u}) : ZFSet.{u} :=
  A.sep (fun x => p.Sat (A : Set ZFSet) (cons x (tupleEnv v)))

def DefinableOver (A S : ZFSet.{u}) : Prop :=
  ∃ (n : ℕ) (p : SentenceForm) (v : Fin n → ZFSet.{u}),
    p.bound ≤ n + 1 ∧ (∀ i, v i ∈ A) ∧ S = definedSubset A p v

noncomputable def definablePower (A : ZFSet.{u}) : ZFSet.{u} :=
  (ZFSet.powerset A).sep (DefinableOver A)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleSatisfaction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

noncomputable def satisfactionSet (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun t : {t : Σ n : ℕ, SentenceForm × (Fin n → Conditions A) //
      t.2.1.bound ≤ t.1 ∧ t.2.1.Sat (A : Set ZFSet)
        (tupleEnv (fun i => label A (t.2.2 i)))} =>
    ZFSet.pair (natSet (Encodable.encode t.val.2.1))
      (tupleCode (fun i => label A (t.val.2.2 i))))

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_OrderNormalForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrderNormalForm
open Encodable TableIndices IndexMatrix IndexedOrder CertificateMatrix

instance instDecidableOrderMatrix (Y : Oracle) (e₀ e₁ d q r : ℕ) : Decidable (orderMatrix Y e₀ e₁ d q r) := by
  unfold orderMatrix
  infer_instance

end TuringRigidity.OrderNormalForm

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_RestrictedForcingFilter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RestrictedForcingFilter
open TransitiveNameModel BoundedSetTheory CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def inclusion (c q : ZFSet.{0}) (hqc : q ⊆ c) (p : Conditions q) : Conditions c :=
  equivShrink c ⟨label q p,hqc (label_mem q p)⟩

theorem label_inclusion (c q : ZFSet.{0}) (hqc : q ⊆ c) (p : Conditions q) :
    label c (inclusion c q hqc p) = label q p := by simp [inclusion,label]

theorem inclusion_le_iff (c q : ZFSet.{0}) (hqc : q ⊆ c) (p r : Conditions q) :
    inclusion c q hqc p ≤ inclusion c q hqc r ↔ p ≤ r := by
  change label c (inclusion c q hqc r) ⊆ label c (inclusion c q hqc p) ↔ _
  rw [label_inclusion,label_inclusion]; rfl

noncomputable def restrict (c q : ZFSet.{0}) (hqc : q ⊆ c)
    (G : GenericFilter (Conditions c)) (hGq : ∀ p ∈ G.carrier, label c p ∈ q) :
    GenericFilter (Conditions q) where
  carrier := {p | inclusion c q hqc p ∈ G.carrier}
  nonempty := by
    obtain ⟨p,hp⟩ := G.nonempty
    obtain ⟨r,hr⟩ := label_surjective q (hGq p hp)
    have he : inclusion c q hqc r = p := label_injective c ((label_inclusion c q hqc r).trans hr)
    exact ⟨r,(show inclusion c q hqc r ∈ G.carrier from he.symm ▸ hp)⟩
  upper := fun hpr hp => G.upper ((inclusion_le_iff c q hqc _ _).mpr hpr) hp
  directed := by
    intro p r hp hr
    obtain ⟨s,hs,hsp,hsr⟩ := G.directed hp hr
    obtain ⟨t,ht⟩ := label_surjective q (hGq s hs)
    have he : inclusion c q hqc t = s := label_injective c ((label_inclusion c q hqc t).trans ht)
    exact ⟨t,(show inclusion c q hqc t ∈ G.carrier from he.symm ▸ hs),(inclusion_le_iff c q hqc t p).mp (he.symm ▸ hsp),
      (inclusion_le_iff c q hqc t r).mp (he.symm ▸ hsr)⟩

end TuringRigidity.RestrictedForcingFilter

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

noncomputable def bound (a b : ZFSet.{0}) : ZFSet.{0} :=
  code (ZFSet.sUnion a) (ZFSet.sUnion b)

end TuringRigidity.TaggedProductConditions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RegularBinaryTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RegularBinaryTree
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalProjectedGeneric RegularDecisionPartition RegularCodeSplitting

noncomputable def children (B T U D : ZFSet.{0}) : Bool → ZFSet.{0} := by
  classical
  exact if h : ∃ f : Bool → ZFSet.{0}, (∀ b, f b ∈ positive B) ∧
      ZFSet.pair (ZFSet.pair U D) (ZFSet.pair (f false) (f true)) ∈ T
    then h.choose else fun _ => ∅

noncomputable def tree (c B T : ZFSet.{0}) (E : ℕ → ZFSet.{0}) (s : List Bool) : ZFSet.{0} :=
  s.reverseRecOn c (fun t b U => children B T U (E t.length) b)

end TuringRigidity.RegularBinaryTree

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
open TransitiveNameModel BoundedSetTheory CountableForcing InternalRegularOperations
open InternalRegularAlgebra InternalBooleanGeneric InternalBooleanDense InternalBooleanSyntax
open InternalCohen
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def branch (c : ZFSet.{0}) (f : List Bool → ZFSet.{0})
    (hroot : f [] = c) (hcode : ∀ s, IsCode c (f s))
    (hm : ∀ s t, s <+: t → f t ⊆ f s)
    (hd : ∀ a u v : List Bool, ∀ p ∈ f (a ++ [false] ++ u),
      p ∉ f (a ++ [true] ++ v))
    (G : GenericFilter (Conditions c)) : GenericFilter CohenBorelForcing.Condition where
  carrier := {s | Hit G (f s.word)}
  nonempty := by
    obtain ⟨p,hp⟩ := G.nonempty
    exact ⟨⟨[]⟩,p,hp,hroot.symm ▸ label_mem c p⟩
  upper := by
    intro p q hpq hp
    obtain ⟨r,hr,hrp⟩ := hp
    exact ⟨r,hr,hm q.word p.word hpq hrp⟩
  directed := by
    intro p q hp hq
    obtain ⟨r,hr,hrp⟩ := hp
    obtain ⟨s,hs,hsq⟩ := hq
    obtain ⟨t,_,htr,hts⟩ := G.directed hr hs
    have htp := code_lower c (f p.word) (hcode _) _ hrp _ (label_mem c t) htr
    have htq := code_lower c (f q.word) (hcode _) _ hsq _ (label_mem c t) hts
    rcases RegularTreeCompatibility.comparable_of_overlap f hd _ _ _ htp htq with h|h
    · exact ⟨q,⟨s,hs,hsq⟩,h,le_rfl⟩
    · exact ⟨p,⟨r,hr,hrp⟩,le_rfl,h⟩

end TuringRigidity.RegularTreeFilter

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RegularTreeCofinality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RegularTreeCofinality
open TransitiveNameModel BoundedSetTheory CountableForcing InternalRegularOperations
open InternalRegularAlgebra InternalBooleanGeneric InternalBooleanDense RegularTreeFilter
open InternalCohen
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def nodesBelow (B A U : ZFSet.{0}) : ZFSet.{0} :=
  B.sep (fun V => ∃ w ∈ conditions, ZFSet.pair w V ∈ A ∧ V ⊆ U)

end TuringRigidity.RegularTreeCofinality

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
open TransitiveNameModel BoundedSetTheory CountableForcing InternalRegularOperations
open InternalRegularAlgebra InternalBooleanGeneric InternalBooleanDense RegularTreeFilter
open RegularTreeCofinality InternalCohen
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def branchSet (B A g : ZFSet.{0}) : ZFSet.{0} :=
  conditions.sep (fun s => ∃ U ∈ B, ZFSet.pair s U ∈ A ∧ ∃ p ∈ g, p ∈ U)

end TuringRigidity.RegularTreeRecovery

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_TaggedProductGeneric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TaggedProductGeneric
open TransitiveNameModel BoundedSetTheory CountableForcing TaggedProductConditions
open CohenProductSplitting
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def sectionSet (a b D r : ZFSet.{0}) : ZFSet.{0} :=
  a.sep (fun p => ∃ s ∈ b, ∃ z ∈ D, z = code p s ∧ r ⊆ s)

noncomputable def fiberSet (b D g : ZFSet.{0}) : ZFSet.{0} :=
  b.sep (fun s => ∃ p ∈ g, ∃ z ∈ D, z = code p s)

end TuringRigidity.TaggedProductGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_TaggedProductRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TaggedProductRecovery
open TransitiveNameModel BoundedSetTheory CountableForcing TaggedProductConditions
open CohenProductSplitting TaggedProductGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def jointSet (c g h : ZFSet.{0}) : ZFSet.{0} :=
  c.sep (fun z => ∃ p ∈ g, ∃ s ∈ h, z = code p s)

end TuringRigidity.TaggedProductRecovery

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleStages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel
universe u

noncomputable def stage (R o : ZFSet.{u}) : ZFSet.{u} :=
  seed R ∪ ZFSet.sUnion (ZFSet.range (fun i : Shrink o =>
    definablePower (stage R ((equivShrink o).symm i).val)))
termination_by o
decreasing_by exact ((equivShrink o).symm i).property

noncomputable def level (R : ZFSet.{u}) (o : Ordinal.{u}) : ZFSet.{u} := stage R o.toZFSet

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_LocalColumnCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.LocalColumnCertificates
open Encodable UniformOracle ArithmeticHierarchy EncodedForcing CodingForcing

def Bad (B : Oracle) (v : ℕ) : Prop :=
  let req := (Nat.unpair v).1
  let w := (Nat.unpair v).2
  UniformSplit.PointCert B (Nat.pair (UniformPair.request (Nat.pair (item req 1) (item req 2))) w) ∧
    Noncoding B (Nat.pair (item req 0) (Nat.pair (item req 2) (item w 2)))

theorem bad_sigma (B : Oracle) : Sigma B 1 (Bad B) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let req (i : ℕ) := item_primrec.comp f (Primrec.const i)
  have hp := (UniformSplit.pointCert_sigma B).comp (Primrec₂.natPair.comp
    (UniformPair.request_primrec.comp (Primrec₂.natPair.comp (req 1) (req 2))) r)
  have hn := (noncoding_sigma B).comp (Primrec₂.natPair.comp (req 0)
    (Primrec₂.natPair.comp (req 2) (item_primrec.comp r (Primrec.const 2))))
  exact hp.and hn

theorem guarded_search (B : Oracle) : ∃ f : ℕ → ℕ,
    Nat.RecursiveIn {oracleFunction (OracleJump.jump B)} (fun req => Part.some (f req)) ∧
    ∀ req, (f req = 0 ∧ ¬ ∃ w, Bad B (Nat.pair req w)) ∨
      (0 < f req ∧ Bad B (Nat.pair req (f req-1))) :=
  EffectiveWitness.sigma1_choice (bad_sigma B)

theorem bad_condition_iff {B : Oracle} {F : ℕ → Oracle} {codes p : ℕ}
    (h : Presents B F codes (active p)) (x w : ℕ) :
    Bad B (Nat.pair (encode [codes,x,p]) w) ↔
      UniformSplit.PointCert B (Nat.pair (UniformPair.request (Nat.pair x p)) w) ∧
        ¬ CodingLocation F (condition p) (item w 2) := by
  simp only [Bad,Nat.unpair_pair,item,encodek,Option.getD_some,List.getD_cons_zero,List.getD_cons_succ]
  exact and_congr Iff.rfl (noncoding_condition_iff h _)

end TuringRigidity.LocalColumnCertificates

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_LocalAgreement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.LocalAgreement
open Encodable UniformOracle ArithmeticHierarchy OracleJump EncodedForcing EffectiveWitness IndexMatrix
open CodingForcing UniformProgram LocalColumnCertificates

def NoDisagreement (B : Oracle) (F : ℕ → Oracle) (x : ℕ) (p : Condition) : Prop :=
  ∀ q, Extends F p q → ¬ UniformAgreement.Disagreement B x q

def Cert (B : Oracle) (v : ℕ) : Prop :=
  let req := (Nat.unpair v).1
  let x := item req 1
  let p := item req 2
  let w := (Nat.unpair v).2
  Extension B (encode [item req 0,p,item w 0]) ∧ item w 2 ≠ item w 3 ∧
    item w 2 ∈ UniformRun.run B (machine (item x 0)) (machine (item x 1)) (left (item w 0)) (item w 1) ∧
    item w 3 ∈ UniformRun.run B (machine (item x 0)) (machine (item x 2)) (right (item w 0)) (item w 1)

theorem cert_sigma (B : Oracle) : Sigma B 1 (Cert B) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let req (i : ℕ) := item_primrec.comp f (Primrec.const i)
  let x (i : ℕ) := item_primrec.comp (req 1) (Primrec.const i)
  let w (i : ℕ) := item_primrec.comp r (Primrec.const i)
  have he := (extension_sigma B).comp (Primrec.encode.comp
    (Primrec.list_cons.comp (req 0) (Primrec.list_cons.comp (req 2)
      (Primrec.list_cons.comp (w 0) (Primrec.const [])))))
  have hn := recursive_primrecPred B ((Primrec.eq.comp (w 2) (w 3)).not)
  have hl := UniformRun.graph_sigma_of B (x 0) (x 1) (Primrec.encode.comp (left_primrec.comp (w 0))) (w 1) (w 2)
  have hr := UniformRun.graph_sigma_of B (x 0) (x 2) (Primrec.encode.comp (right_primrec.comp (w 0))) (w 1) (w 3)
  unfold Cert
  simpa only [Nat.unpair_pair,word,encodek,Option.getD_some] using
    he.and ((Form.raise (n := 0) (s := true) hn).and (hl.and hr))

theorem cert_iff {B : Oracle} {F : ℕ → Oracle} {codes p : ℕ}
    (h : Presents B F codes (active p)) (x w : ℕ) :
    Cert B (Nat.pair (encode [codes,x,p]) w) ↔
      Extends F (condition p) (condition (item w 0)) ∧ item w 2 ≠ item w 3 ∧
      item w 2 ∈ UniformRun.run B (machine (item x 0)) (machine (item x 1)) (left (item w 0)) (item w 1) ∧
      item w 3 ∈ UniformRun.run B (machine (item x 0)) (machine (item x 2)) (right (item w 0)) (item w 1) := by
  simp only [Cert,Nat.unpair_pair,item,encodek,Option.getD_some,List.getD_cons_zero,List.getD_cons_succ]
  exact and_congr (extension_condition_iff h) Iff.rfl

theorem decide_exists (B : Oracle) : ∃ f : ℕ → ℕ,
    Nat.RecursiveIn {oracleFunction (jump B)} (fun v => Part.some (f v)) ∧
    ∀ (F : ℕ → Oracle) codes x p, Presents B F codes (active p) →
      Extends F (condition p) (condition (f (encode [codes,x,p]))) ∧
      (UniformAgreement.Disagreement B x (condition (f (encode [codes,x,p]))) ∨
        (f (encode [codes,x,p]) = p ∧ NoDisagreement B F x (condition p))) := by
  obtain ⟨search,hs,hsearch⟩ := sigma1_choice (cert_sigma B)
  let out : ℕ → ℕ := fun req => if search req = 0 then item req 2 else item (search req-1) 0
  have hmap : Primrec (fun v : ℕ => if (Nat.unpair v).2 = 0 then item (Nat.unpair v).1 2
      else item ((Nat.unpair v).2-1) 0) := by
    let f := Primrec.fst.comp Primrec.unpair
    let r := Primrec.snd.comp Primrec.unpair
    exact Primrec.ite (Primrec.eq.comp r (Primrec.const 0)) (item_primrec.comp f (Primrec.const 2))
      (item_primrec.comp (Primrec.nat_sub.comp r (Primrec.const 1)) (Primrec.const 0))
  refine ⟨out,?_,fun F codes x p h => ?_⟩
  · exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hmap) (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec Primrec.id) hs)).of_eq
      (fun v => by simp only [Nat.unpair_pair]; rfl)
  · rcases hsearch (encode [codes,x,p]) with ⟨hz,hn⟩ | ⟨hp,hc⟩
    · have hout : out (encode [codes,x,p]) = p := by simp only [out,ite_eq_left hz,item,encodek,Option.getD_some,List.getD_cons_zero,List.getD_cons_succ]
      rw [hout]
      refine ⟨extends_refl _ _,Or.inr ⟨rfl,fun q hpq hd => ?_⟩⟩
      obtain ⟨n,a,b,hab,ha,hb⟩ := hd
      apply hn
      refine ⟨encode [code q,n,a,b],(cert_iff h x _).2 ?_⟩
      simpa [item,← show left (code q) = q.left from congrArg Condition.left (condition_code q),
        ← show right (code q) = q.right from congrArg Condition.right (condition_code q),condition_code] using
        And.intro hpq (And.intro hab (And.intro ha hb))
    · have hz : search (encode [codes,x,p]) ≠ 0 := by omega
      simp only [out,ite_eq_right hz]
      have hc' := (cert_iff h x _).1 hc
      exact ⟨hc'.1,Or.inl ⟨_,_,_,hc'.2⟩⟩

end TuringRigidity.LocalAgreement

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

def Decisive (B : Oracle) (F : ℕ → Oracle) (x : ℕ) (p : Condition) : Prop :=
  UniformAgreement.Disagreement B x p ∨ ∃ i n, (i = 1 ∨ i = 2) ∧ ∀ q, Extends F p q →
    ∀ a, a ∉ UniformRun.run B (machine (item x 0)) (machine (item x i))
      (if i = 1 then q.left else q.right) n

theorem split_coding_or_divergence {B : Oracle} {F : ℕ → Oracle} {x : ℕ} {p r : Condition}
    (hn : LocalAgreement.NoDisagreement B F x p) (hpr : Extends F p r)
    (m : ℕ) (hm : p.left.length ≤ m) (hmr : m < r.left.length) (b : Bool)
    (n v w : ℕ) (hvw : v ≠ w)
    (hv : v ∈ UniformRun.run B (machine (item x 0)) (machine (item x 1)) r.left n)
    (hw : w ∈ UniformRun.run B (machine (item x 0)) (machine (item x 1)) (r.left.set m b) n) :
    CodingLocation F p m ∨
      ∀ q, Extends F r q → ∀ c,
        c ∉ UniformRun.run B (machine (item x 0)) (machine (item x 2)) q.right n := by
  by_cases hc : CodingLocation F p m
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

theorem bad_decisive (B : Oracle) (F : ℕ → Oracle) (x p w : ℕ)
    (hn : LocalAgreement.NoDisagreement B F x (condition p))
    (hb : UniformSplit.PointCert B (Nat.pair (request (Nat.pair x p)) w) ∧
      ¬ CodingLocation F (condition p) (item w 2)) :
    Decisive B F x (condition (EffectiveSplitConditions.update p (Nat.pair 2 w))) := by
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
      item w 4 ∈ UniformRun.run B (machine (item x 0)) (machine (item x 1)) (word (item w 1)) (item w 0) ∧
      item w 5 ∈ UniformRun.run B (machine (item x 0)) (machine (item x 1))
        ((word (item w 1)).set (item w 2) (item w 3).bodd) (item w 0) := by
    simpa [UniformSplit.PointCert,UniformSplit.start,UniformSplit.base,UniformSplit.program,
      request,item,word] using hp.2
  have hd := split_coding_or_divergence (r := q) hn (append_extends F (condition p)
    ((word (item w 1)).drop (left p).length)) (item w 2) hpoint.1
    (by simpa [hl] using hpoint.2.1) (item w 3).bodd (item w 0) (item w 4) (item w 5)
    hpoint.2.2.1 (by simpa [hl] using hpoint.2.2.2.1) (by simpa [hl] using hpoint.2.2.2.2)
  have hnc' : ¬ CodingLocation F (condition p) (item w 2) := hnc
  have he : condition (EffectiveSplitConditions.update p (Nat.pair 2 w)) = q := by
    simp [EffectiveSplitConditions.update,Nat.unpair_pair,condition_code,q]
  rw [he]
  exact Or.inr ⟨2,item w 0,Or.inr rfl,by simpa using hd.resolve_left hnc'⟩

def Outcome (B : Oracle) (F : ℕ → Oracle) (x p : ℕ) : Prop :=
  (¬ ∃ z, UniformSplit.SplitCert B (Nat.pair (request (Nat.pair x p)) z)) ∨
    ∃ w, UniformSplit.PointCert B (Nat.pair (request (Nat.pair x p)) w) ∧
      CodingLocation F (condition p) (item w 2)

theorem disagreement_mono {B : Oracle} {F : ℕ → Oracle} {x : ℕ} {p q : Condition}
    (hpq : Extends F p q) (h : UniformAgreement.Disagreement B x p) :
    UniformAgreement.Disagreement B x q := by
  obtain ⟨n,a,b,hab,ha,hb⟩ := h
  exact ⟨n,a,b,hab,UniformRun.run_mono hpq.1 n a ha,UniformRun.run_mono hpq.2.1 n b hb⟩

end
end TuringRigidity.LocalPair

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

@[simp] theorem condition_grow (p s : ℕ) :
    condition (grow p s) = atLevel (append (condition p) [false]) (s+1) := condition_code (atLevel (append (condition p) [false]) (s+1))

def initial : ℕ := Nat.pair (code ⟨[],[],rfl,0⟩) (Nat.pair (encode ([] : List ℕ)) (encode ([] : List ℕ)))

end
end TuringRigidity.LocalComputability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_JumpIdeal
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.JumpIdeal
open OracleJump IdealInterpretation PersistentRestrictions GlobalLocality
noncomputable section

def generated (x : Degree) : CountableIdeal where
  carrier := {y | ∃ n, y ≤ degreeIterate x n}
  nonempty := ⟨x,0,le_rfl⟩
  countable := by
    have he : {y | ∃ n, y ≤ degreeIterate x n} = ⋃ n, Set.Iic (degreeIterate x n) := by
      ext y
      simp only [Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_Iic]
    rw [he]
    exact Set.countable_iUnion (fun n => countable_principal_lower _)
  lower := by
    intro a b hab hb
    obtain ⟨n,hn⟩ := hb
    exact ⟨n,hab.trans hn⟩
  join_mem := by
    intro a b ha hb
    obtain ⟨m,hm⟩ := ha
    obtain ⟨n,hn⟩ := hb
    exact ⟨max m n,sup_le (hm.trans (iterate_monotone x (le_max_left m n)))
      (hn.trans (iterate_monotone x (le_max_right m n)))⟩

end
end TuringRigidity.JumpIdeal

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelFunctionGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelFunctions
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration SetModelArithmetic
universe u
noncomputable section

structure Context (M : ZFSet.{u}) : Prop where
  transitive : Transitive M
  pairing : Pairing M
  union : BoundedSetTheory.Union M
  power : PowerSet M
  separation : Separation M
  infinity : Infinity M

end
end TuringRigidity.SetModelFunctions

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
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelArithmetic SetModelFunctions
open BoundedDefinability UniformArithmetic Encodable
universe u
noncomputable section

variable {M : ZFSet.{u}}

def ArithmeticDefinition (M : ZFSet.{u}) (P : Predicate) : Prop :=
  ∃ Q : (ℕ → ZFSet.{u}) → Prop, Definable M Q ∧
    ∀ e n, e 0 = natSet n →
      (Q e ↔ P (fun i => oracleOf (e (i+1))) n)

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

def Children (C : ℕ → Prop) : SentenceForm → Prop
  | .equal _ _ | .member _ _ => True
  | .conj p q => C (Encodable.encode p) ∧ C (Encodable.encode q)
  | .neg p | .ex p => C (Encodable.encode p)

end TuringRigidity.SentenceCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SetSatisfactionBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

def setBounded : SentenceForm → ℕ → (ℕ → ℕ) → Formula
  | .equal i j, _, v => .equal (v i) (v j)
  | .member i j, _, v => .member (v i) (v j)
  | .conj p q, a, v => .conj (setBounded p a v) (setBounded q a v)
  | .neg p, a, v => .neg (setBounded p a v)
  | .ex p, a, v => .existsMem a
      (setBounded p (a+1) (fun i => match i with | 0 => 0 | j+1 => v j+1))

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_FiniteGraphSatisfaction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

def prependValues (w : ℕ → ZFSet.{u}) : ℕ → (ℕ → ZFSet.{u}) → ℕ → ZFSet.{u}
  | 0, e => e
  | n+1, e => prependValues w n (cons (w n) e)

def graphTruth (p : SentenceForm) (a g : ℕ) (idx : ℕ → ℕ) : Formula :=
  readGraph p.bound a g idx (setBounded p (p.bound+a) id)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalSatisfactionSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

noncomputable def truthSlice (A : ZFSet.{u}) (p : SentenceForm) : ZFSet.{u} :=
  (tupleSpace A).sep (fun t => ZFSet.pair (natSet (Encodable.encode p)) t ∈ satisfactionSet A)

def tupleTruth (p : SentenceForm) (o A Q b t : ℕ) (idx : ℕ → ℕ) : Formula :=
  .existsMem o (.existsMem (Q+1)
    (.conj (.orderedPair (t+2) 1 0)
      (.conj (.subset (b+2) 1) (graphTruth p (A+2) 0 (fun i => idx i+2)))))

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_FiniteSatisfactionCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

def subformulas : SentenceForm → List SentenceForm
  | .equal i j => [.equal i j]
  | .member i j => [.member i j]
  | .conj p q => .conj p q :: (subformulas p ++ subformulas q)
  | .neg p => .neg p :: subformulas p
  | .ex p => .ex p :: subformulas p

noncomputable def finiteSatisfaction (A : ZFSet.{u}) (ps : List SentenceForm) : ZFSet.{u} :=
  ZFSet.sUnion (ZFSet.range (fun i : Fin ps.length =>
    ZFSet.prod ({natSet (Encodable.encode ps[i])} : ZFSet.{u}) (truthSlice A ps[i])))

def accepts (S : ZFSet.{u}) (p : SentenceForm) {n : ℕ} (v : Fin n → ZFSet.{u}) : Prop :=
  ZFSet.pair (natSet (Encodable.encode p)) (tupleCode v) ∈ S

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SentenceCodeFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.SentenceCoding
open ElementaryModel RelativeConstructible BoundedSetTheory TransitiveNameModel
universe u

noncomputable def family (p : SentenceForm) : ZFSet.{u} :=
  ZFSet.range (fun i : Fin (subformulas p).length =>
    natSet (Encodable.encode (subformulas p)[i]))

end TuringRigidity.SentenceCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SentenceSupportCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.SentenceCoding
open ElementaryModel RelativeConstructible BoundedSetTheory TransitiveNameModel
universe u

noncomputable def supportGraph (p : SentenceForm) : ZFSet.{u} :=
  ZFSet.range (fun i : Fin (subformulas p).length =>
    ZFSet.pair (natSet (Encodable.encode (subformulas p)[i])) (natSet (subformulas p)[i].bound))

def HasBound (G : ZFSet.{u}) (p : SentenceForm) (n : ℕ) : Prop :=
  ZFSet.pair (natSet (Encodable.encode p)) (natSet n) ∈ G

def SupportStep (G : ZFSet.{u}) : SentenceForm → ℕ → Prop
  | .equal i j, b | .member i j, b => b = max i j + 1
  | .conj p q, b => ∃ i j, HasBound G p i ∧ HasBound G q j ∧ b = max i j
  | .neg p, b => HasBound G p b
  | .ex p, b => ∃ i, HasBound G p i ∧ b = i-1

def SupportRecursion (root : SentenceForm) (G : ZFSet.{u}) : Prop :=
  (∀ z ∈ G, ∃ p ∈ subformulas root, ∃ n : ℕ,
    z = ZFSet.pair (natSet (Encodable.encode p)) (natSet n)) ∧
  ∀ p ∈ subformulas root, ∀ n, HasBound G p n ↔ SupportStep G p n

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

def TuplePrefix (A G t x s : ZFSet.{u}) : Prop :=
  (tuplePrefixFormula 0 1 2 3 4 5 6).Eval
    (cons A (cons ZFSet.omega (cons G (cons t (cons x (cons s (fun _ => natSet 0)))))))

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SatisfactionRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

def truthStep (A S : ZFSet.{u}) {n : ℕ} (v : Fin n → ZFSet.{u}) : SentenceForm → Prop
  | .equal i j => tupleEnv v i = tupleEnv v j
  | .member i j => tupleEnv v i ∈ tupleEnv v j
  | .conj p q => accepts S p v ∧ accepts S q v
  | .neg p => ¬ accepts S p v
  | .ex p => ∃ x ∈ A, accepts S p (Fin.cases x v)

def TruthRecursion (A : ZFSet.{u}) (root : SentenceForm) (S : ZFSet.{u}) : Prop :=
  (∀ z ∈ S, ∃ p ∈ subformulas root, ∃ (n : ℕ) (v : Fin n → ZFSet.{u}),
    (∀ i, v i ∈ A) ∧ p.bound ≤ n ∧ z = ZFSet.pair (natSet (Encodable.encode p)) (tupleCode v)) ∧
  ∀ p ∈ subformulas root, ∀ (n : ℕ) (v : Fin n → ZFSet.{u}),
    (∀ i, v i ∈ A) → p.bound ≤ n → (accepts S p v ↔ truthStep A S v p)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformTruthStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions SetModelReals
universe u

variable {M : ZFSet.{u}}

def SetTruthStep (A G T S c t : ZFSet.{u}) : Prop :=
  (∃ i ∈ ZFSet.omega, ∃ j ∈ ZFSet.omega, ∃ x ∈ A, ∃ y ∈ A,
    BinaryGraph (fun i j => binary 0 (atom i) (atom j)) i j c ∧
      TupleLookup G t i x ∧ TupleLookup G t j y ∧ x = y) ∨
  (∃ i ∈ ZFSet.omega, ∃ j ∈ ZFSet.omega, ∃ x ∈ A, ∃ y ∈ A,
    BinaryGraph (fun i j => binary 1 (atom i) (atom j)) i j c ∧
      TupleLookup G t i x ∧ TupleLookup G t j y ∧ x ∈ y) ∨
  (∃ i ∈ ZFSet.omega, ∃ j ∈ ZFSet.omega,
    BinaryGraph (binary 2) i j c ∧ ZFSet.pair i t ∈ S ∧ ZFSet.pair j t ∈ S) ∨
  (∃ i ∈ ZFSet.omega, UnaryGraph (unary 3) i c ∧ ¬ ZFSet.pair i t ∈ S) ∨
  (∃ i ∈ ZFSet.omega, UnaryGraph (unary 4) i c ∧
    ∃ x ∈ A, ∃ s ∈ T, TuplePrefix A G t x s ∧ ZFSet.pair i s ∈ S)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformTruthRecursion
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

def SetTruthRecursion (Q B G A T F S : ZFSet.{u}) : Prop :=
  (∀ z ∈ S, ∃ c ∈ F, ∃ t ∈ T, TupleAdequate Q B G c t ∧ z = ZFSet.pair c t) ∧
    ∀ c ∈ F, ∀ t ∈ T, TupleAdequate Q B G c t →
      (ZFSet.pair c t ∈ S ↔ SetTruthStep A G T S c t)

def TruthWitness (Q B G A T c S : ZFSet.{u}) : Prop :=
  ∃ F ∈ Q, LeastFamily Q c F ∧ SetTruthRecursion Q B G A T F S

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformInternalSatisfaction
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

def SatisfactionWitness (Q B G H A T z : ZFSet.{u}) : Prop :=
  ∃ c ∈ ZFSet.omega, ∃ t ∈ T, ∃ S ∈ H,
    TruthWitness Q B G A T c S ∧ ZFSet.pair c t ∈ S ∧ z = ZFSet.pair c t

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_DefinableSubsetCertificates
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

def DefinesSubset (A G T Z c t S : ZFSet.{u}) : Prop :=
  S ⊆ A ∧ ∀ x ∈ A, x ∈ S ↔
    ∃ s ∈ T, TuplePrefix A G t x s ∧ ZFSet.pair c s ∈ Z

def DefinitionWitness (Q B G A T Z S : ZFSet.{u}) : Prop :=
  ∃ c ∈ ZFSet.omega, ∃ t ∈ T,
    ParameterAdequate Q B G c t ∧ DefinesSubset A G T Z c t S

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_TupleSystemCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

def TupleSystem (A G T : ZFSet.{u}) : Prop :=
  (∀ t ∈ T, ∃ n ∈ ZFSet.omega, ∃ g ∈ G,
    t = ZFSet.pair n g ∧ FunctionGraph n A g) ∧
  ZFSet.pair (natSet 0) (natSet 0) ∈ T ∧
  ∀ t ∈ T, ∀ x ∈ A, ∃ s ∈ T, TuplePrefix A G t x s

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SatisfactionSystemCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

def SatisfactionSystem (Q B A G T H Z : ZFSet.{u}) : Prop :=
  TupleSystem A G T ∧
  (∀ c ∈ ZFSet.omega, ∀ F ∈ Q, LeastFamily Q c F →
    ∃ S ∈ H, SetTruthRecursion Q B G A T F S) ∧
  (∀ z ∈ Z, SatisfactionWitness Q B G H A T z) ∧
  ∀ c ∈ ZFSet.omega, ∀ t ∈ T, ∀ S ∈ H,
    TruthWitness Q B G A T c S → ZFSet.pair c t ∈ S → ZFSet.pair c t ∈ Z

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_DefSystemCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

def DefSystem (Q B A G T H Z D : ZFSet.{u}) : Prop :=
  SatisfactionSystem Q B A G T H Z ∧
  (∀ S ∈ D, DefinitionWitness Q B G A T Z S) ∧
  ∀ c ∈ ZFSet.omega, ∀ t ∈ T, ParameterAdequate Q B G c t →
    ∃ S ∈ D, DefinesSubset A G T Z c t S

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

def HierarchyGraph (M s d r f : ZFSet.{u}) : Prop :=
  Transitive d ∧ FunctionGraph d r f ∧
  ∀ x ∈ d, ∀ v ∈ r, ZFSet.pair x v ∈ f →
    ∃ A ∈ M, StageStep s f r x A ∧ v = definablePower A

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel
universe u

def InRelativeModel (M R x : ZFSet.{u}) : Prop :=
  ∃ o : Ordinal.{u}, o.toZFSet ∈ M ∧ x ∈ level R o

noncomputable def relativeModel (M R : ZFSet.{u}) : ZFSet.{u} :=
  M.sep (InRelativeModel M R)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteRealPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory
universe u

def packedReal : {n : ℕ} → (Fin n → Oracle) → Oracle
  | 0, _ => FixedArithmetic.zero
  | n+1, v => join (v 0) (packedReal (fun i : Fin n => v i.succ))

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory ElementaryModel
universe u

inductive Construction : Type (u+1)
  | reals : Construction
  | parameter : Construction
  | define (o : Ordinal.{u}) (n : ℕ) (p : SentenceForm)
      (children : Fin n → Construction) : Construction

noncomputable def Construction.value (R : ZFSet.{u}) (P : Oracle) : Construction.{u} → ZFSet.{u}
  | .reals => R
  | .parameter => realCode P
  | .define o n p c => definedSubset (level R o) p
      (fun i : Fin n => (c i).value R (realPart P i))

def Construction.Certified (R : ZFSet.{u}) (P : Oracle) : Construction.{u} → Prop
  | .reals => True
  | .parameter => realCode P ∈ R
  | .define o n p c => p.bound ≤ n+1 ∧
      ∀ i, (c i).Certified R (realPart P i) ∧ (c i).value R (realPart P i) ∈ level R o

def Construction.Indexed (M : ZFSet.{u}) : Construction.{u} → Prop
  | .reals => True
  | .parameter => True
  | .define o _ _ c => o.toZFSet ∈ M ∧ ∀ i, (c i).Indexed M

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

noncomputable def ConstructionInput.value (R : ZFSet.{u}) (P : Oracle) :
    ConstructionInput.{u} → ZFSet.{u}
  | .reals => R
  | .stage o => level R o
  | .realPath path => realCode (pathReal P path)

def ConstructionInput.prefix (i : ℕ) : ConstructionInput.{u} → ConstructionInput.{u}
  | .reals => .reals
  | .stage o => .stage o
  | .realPath path => .realPath (i::path)

def ConstructionInput.Indexed (M : ZFSet.{u}) : ConstructionInput.{u} → Prop
  | .reals => True
  | .stage o => o.toZFSet ∈ M
  | .realPath _ => True

noncomputable def Construction.inputData : Construction.{u} → ℕ → ConstructionInput.{u}
  | .reals, _ => .reals
  | .parameter, _ => .realPath []
  | .define o _ _ _, 0 => .stage o
  | .define _ n _ c, k+1 =>
      if h : (Nat.unpair k).1 < n then
        ((c ⟨(Nat.unpair k).1,h⟩).inputData (Nat.unpair k).2).prefix (Nat.unpair k).1
      else .reals

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

noncomputable def Construction.stageInputs (R : ZFSet.{u}) (t : Construction.{u}) (k : ℕ) : ZFSet.{u} :=
  match t.inputData k with
  | .stage o => level R o
  | _ => R

noncomputable def Construction.singleInputs (t : Construction.{u}) (R : ZFSet.{u}) (P : Oracle) : ℕ → ZFSet.{u} :=
  cons R (cons (realCode P) (cons ZFSet.omega (cons additionSet
    (cons pairNumbers (t.stageInputs R)))))

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

noncomputable def Construction.arithmeticFreeInputs (t : Construction.{u}) (R : ZFSet.{u})
    (P : Oracle) : ℕ → ZFSet.{u} := cons R (cons (realCode P) (t.stageInputs R))

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructionStageBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

noncomputable def Construction.stageBound : Construction.{u} → Ordinal.{u}
  | .reals => 0
  | .parameter => 0
  | .define o _ _ c => max o (Finset.univ.sup (fun i => (c i).stageBound)) + 1

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_FiniteStageDefinition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelArithmetic
universe u

noncomputable def Construction.ordinalData (t : Construction.{u}) (k : ℕ) : Option Ordinal.{u} :=
  match t.inputData k with
  | .stage o => some o
  | _ => none

noncomputable def stageParameter (R : ZFSet.{u}) : Option Ordinal.{u} → ZFSet.{u}
  | none => R
  | some o => level R o

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_CheckedDefSuccessor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

def CheckedDefSuccessor (N w s A D : ZFSet.{u}) : Prop :=
  ∃ Q ∈ N, ∃ B ∈ N, (PowerBound N w Q ∧ PowerBound N s B) ∧
    ∃ G ∈ N, ∃ T ∈ N, ∃ H ∈ N, ∃ Z ∈ N, DefSystem Q B A G T H Z D

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

def replacementImageFormula (φ : SigmaFormula) : SigmaFormula :=
  .existsSet (SigmaFormula.andBounded (.member 0 2) (φ.rename replacementImageVars))

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_CheckedHierarchySyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

def CheckedHierarchyGraph (N w sq s d r f : ZFSet.{u}) : Prop :=
  Transitive d ∧ FunctionGraph d r f ∧
    ∀ x ∈ d, ∀ v ∈ r, ZFSet.pair x v ∈ f →
      ∃ A ∈ N, StageStep s f r x A ∧ CheckedDefSuccessor N w sq A v

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_HierarchyWitnessCollection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

def HierarchyRequest (Q B s f r x c : ZFSet.{u}) : Prop :=
  ∃ A ∈ c, ∃ v ∈ r, ∃ G ∈ c, ∃ T ∈ c, ∃ H ∈ c, ∃ Z ∈ c,
    ZFSet.pair x v ∈ f ∧ StageStep s f r x A ∧ DefSystem Q B A G T H Z v

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_SeedBoundStageSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

def SeedBoundStage (N w sq R x A : ZFSet.{u}) : Prop :=
  ∃ s ∈ N, ∃ d ∈ N, ∃ f ∈ N, ∃ r ∈ N,
    s = insert R R ∧ x ∈ d ∧ CheckedHierarchyGraph N w sq s d r f ∧ StageStep s f r x A

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
open Encodable UniformPrograms CommonIdeal EncodedForcing OracleJump
open ArithmeticHierarchy CohenHalting CohenLowness EffectiveCohen
noncomputable section
attribute [local instance] Classical.propDecidable

def searchTrial (Y G : Oracle) (x p : ℕ) : Option ℕ :=
  if Deciding Y G (Nat.pair x p) then
    some (if OpenHalts Y x (encode (word p)) then 1 else 0) else none

end
end TuringRigidity.UniformCohenJump

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.NumericSyntax
open BoundedSetTheory TransitiveNameModel BoundedDefinability SentenceCoding
universe u

def params (Q : ZFSet.{u}) : ℕ → ZFSet.{u} :=
  cons ZFSet.omega (cons Q (fun _ => natSet 0))

def Covers (Q : ZFSet.{u}) : Prop := ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ Q

def Numeric (P : (ℕ → ZFSet.{u}) → Prop) : Prop :=
  ∃ p : Formula, ∀ Q, Covers Q → ∀ e, p.Eval (mix e (params Q)) ↔ P e

end TuringRigidity.NumericSyntax

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.NumericSyntax
open ElementaryModel BoundedSetTheory TransitiveNameModel BoundedDefinability
universe u

def Domain (P : ZFSet.{u} → (ℕ → ZFSet.{u}) → Prop) : Prop :=
  ∃ p : SentenceForm, ∀ B, Covers B → ∀ N : ZFSet.{u}, Transitive N →
    (∀ i, params B i ∈ N) → ∀ e, (∀ i, e i ∈ N) →
      (p.Sat (N : Set ZFSet) (mix e (params B)) ↔ P N e)

end TuringRigidity.NumericSyntax

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

def stageInputs (e : ℕ → ZFSet.{u}) : ℕ → ZFSet.{u} :=
  cons (e 0) (cons (e 1) (cons (e 2) (cons ZFSet.omega
    (fun _ => ZFSet.prod ZFSet.omega ZFSet.omega))))

end TuringRigidity.NumericSyntax

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericalCohenProductSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.NumericalCohenProductSets
open TransitiveNameModel BoundedSetTheory SetModelFunctions SetModelArithmetic
open InternalCohen Encodable UniformArithmetic
open EncodedForcing (word)
open TaggedProductConditions (code)

noncomputable def image (c : ZFSet.{0}) (B : Oracle) : ZFSet.{0} :=
  c.sep (fun z => ∃ n : ℕ, B n = true ∧
    z = code (wordCode (word (left n))) (wordCode (word (right n))))

end TuringRigidity.NumericalCohenProductSets

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

def orderTypeMatrix (a d r f : ℕ) : Formula :=
  .conj (ordinalFormula a) (.conj (Code.graph d r d a f)
    (Formula.allMem a (.existsMem (d+1) (Formula.pairMem 0 1 (f+2)))))

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

def productMatrix (c a b d r f : ℕ) : Formula :=
  .conj (productDomainMatrix d a b)
    (.conj (productRelationMatrix r d a b) (orderTypeMatrix c d r f))

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalProductReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel
universe u

def productSigma : SigmaFormula :=
  .existsSet (.existsSet (.existsSet (.bounded (productMatrix 3 4 5 2 1 0))))

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

def ordinalAllMem (i : ℕ) (p : SentenceForm) : SentenceForm :=
  .all (.imp (.member 0 (i+1)) p)

end TuringRigidity.OrdinalArithmetic

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

def sumMatrix (c a b d r f z o : ℕ) : Formula :=
  .conj (.allMem z (.neg (.equal 0 0)))
    (.conj (.singleton o z) (.conj (sumDomainMatrix d a b z o)
      (.conj (sumRelationMatrix r d a b z o) (orderTypeMatrix c d r f))))

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_ProductCertificateCollection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions SentenceCoding
universe u

def productBundleSigma : SigmaFormula :=
  .existsSet (.existsSet (.existsSet (.existsSet (.bounded
    (.conj (productMatrix 3 5 6 2 1 0)
      (.conj (.member 2 4) (.conj (.member 1 4)
        (.conj (.member 0 4) (.member 3 4)))))))))

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_OwnProgramValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory PersistentRestrictions SetDegreeDecoding
open GenericIdentity TableIndices IndexMatrix

def OwnProgramAt (E f : ZFSet.{0}) (p : OracleCode) (R A : Oracle) : Prop :=
  Total p R A ∧
    ∃ u ∈ degreeUniverse (groundReals E), ∃ v ∈ degreeUniverse (groundReals E),
      realCode A ∈ u ∧ realCode (value p R A) ∈ v ∧ ZFSet.pair u v ∈ f

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

noncomputable def Construction.ownRealsSlots (t : Construction.{u}) : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | k+3 => match t.ordinalData k with | none => 0 | some _ => k+3

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_RealGeneratedModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RealGeneratedModel
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax InternalBooleanBits
open InternalGeneratedAlgebra InternalProjectedGeneric

def Contains (M X N : ZFSet.{0}) : Prop :=
  Transitive N ∧ SourceT N ∧ M ⊆ N ∧ X ∈ N

noncomputable def hull (M X : ZFSet.{0}) : ZFSet.{0} := by
  classical
  exact if h : ∃ N, Contains M X N then
    h.choose.sep (fun z => ∀ N, Contains M X N → z ∈ N)
  else ∅

attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  codeOrder codePreorder

end TuringRigidity.RealGeneratedModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalGraphEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalGraphEquiv
open TransitiveNameModel BoundedSetTheory

noncomputable def graphMap (A B f : ZFSet.{0}) (hf : FunctionGraph A B f)
    (x : Conditions A) : Conditions B :=
  equivShrink B ⟨(hf.2 (label A x) (label_mem A x)).choose,
    (hf.2 (label A x) (label_mem A x)).choose_spec.1⟩

theorem graphMap_spec (A B f : ZFSet.{0}) (hf : FunctionGraph A B f) (x : Conditions A) :
    ZFSet.pair (label A x) (label B (graphMap A B f hf x)) ∈ f := by
  simpa only [graphMap,label,Equiv.symm_apply_apply] using
    (hf.2 (label A x) (label_mem A x)).choose_spec.2.1

theorem graphMap_bijective (A B f : ZFSet.{0}) (hf : FunctionGraph A B f)
    (hi : ∀ x ∈ A, ∀ x' ∈ A, ∀ y ∈ B, ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x')
    (hs : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ f) : Function.Bijective (graphMap A B f hf) := by
  constructor
  · intro x x' he
    apply label_injective A
    exact hi _ (label_mem A x) _ (label_mem A x') _ (label_mem B (graphMap A B f hf x))
      (graphMap_spec A B f hf x) (he.symm ▸ graphMap_spec A B f hf x')
  · intro y
    obtain ⟨x,hx,hxy⟩ := hs (label B y) (label_mem B y)
    obtain ⟨x,rfl⟩ := label_surjective A hx
    exact ⟨x,label_injective B (hf.functional (label_mem A x) (graphMap_spec A B f hf x) hxy)⟩

noncomputable def graphEquiv (A B f : ZFSet.{0}) (hf : FunctionGraph A B f)
    (hi : ∀ x ∈ A, ∀ x' ∈ A, ∀ y ∈ B, ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x')
    (hs : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ f) : Conditions A ≃ Conditions B :=
  Equiv.ofBijective (graphMap A B f hf) (graphMap_bijective A B f hf hi hs)

end TuringRigidity.InternalGraphEquiv

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalPositiveNameFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalPositiveNameFamily
open TransitiveNameModel BoundedSetTheory RecursiveNames AtomicForcing
variable {c : ZFSet.{0}} [Preorder (Conditions c)] [Top (Conditions c)]

noncomputable def positive (τ : Name (Conditions c)) (n : ℕ) : ZFSet.{0} :=
  c.sep (fun p => ∃ q : Conditions c, label c q = p ∧ MemForces (Name.check (natSet n)) τ q)

end TuringRigidity.InternalPositiveNameFamily

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RegularTreeRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RegularTreeRun
open TransitiveNameModel BoundedSetTheory InternalProjectedGeneric RegularBinaryTree

noncomputable def bit (w i : ZFSet.{0}) : Bool := by
  classical
  exact decide (ZFSet.pair i (InternalCohen.bitSet true) ∈ w)

noncomputable def run (c B T : ZFSet.{0}) (E : ℕ → ZFSet.{0}) (w : ZFSet.{0}) : ℕ → ZFSet.{0}
  | 0 => c
  | n+1 => children B T (run c B T E w n) (E n) (bit w (natSet n))

end TuringRigidity.RegularTreeRun

end OAI
end


