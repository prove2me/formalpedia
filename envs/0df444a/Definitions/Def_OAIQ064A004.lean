-- Prove2me | Definitions.Def_OAIQ064A004
-- name    : OAIQ064A004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T00:30:25.891372+00:00
-- url     : https://prove2.me/theorems/0768b5f7-3651-432e-a8dd-3c6512840084
-- title:
--   Definitions bundle OAIQ064A004 of the split of OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 186 declarations of OpenAI's Lean: 158 definitions, 3 inductive types or structures, 2 instances and 23 theorems. The definitions and types are `OAI.TuringRigidity.ArithmeticTree.HasTest.col`, `OAI.TuringRigidity.ArithmeticTree.HasTest.tailTest`, `OAI.TuringRigidity.ArithmeticTree.HasTest.zeroTag`, `OAI.TuringRigidity.ArithmeticTree.Test.joinWitness`, `OAI.TuringRigidity.IndexMatrix.checkMatrix`, `OAI.TuringRigidity.IndexMatrix.validMatrix`, `OAI.TuringRigidity.IndexTuples.supIndex`, `OAI.TuringRigidity.IndexedOrder.OrderWitness`, `OAI.TuringRigidity.InternalBooleanBits.bitFormula`, `OAI.TuringRigidity.InternalBooleanGeneric.Hit`, `OAI.TuringRigidity.InternalCohen.WordDecision`, `OAI.TuringRigidity.InternalCohen.realNameFormula`, `OAI.TuringRigidity.InternalCohen.wordBit`, `OAI.TuringRigidity.InternalCohen.wordGraphFormula`, `OAI.TuringRigidity.InternalCohenBitFlip.flipMatchesFormula`, `OAI.TuringRigidity.InternalCohenBitFlip.matchingFormula`, `OAI.TuringRigidity.InternalCohenReindex.matchesFormula`, `OAI.TuringRigidity.InternalCohenRestriction.restrictionFormula`, `OAI.TuringRigidity.InternalCountableEnumeration.enumeratesFormula`, `OAI.TuringRigidity.InternalCountableFiniteUnion.entryFormula`, `OAI.TuringRigidity.InternalCountableProduct.rectangleFormula`, `OAI.TuringRigidity.InternalFiniteExhaustion.initialFormula`, `OAI.TuringRigidity.InternalQuotientConditions.coverFormula`, `OAI.TuringRigidity.InternalRealQuotient.tags`, `OAI.TuringRigidity.InternalRegularAlgebra.codeFormula`, `OAI.TuringRigidity.InternalRelationSelection.fiberFormula`, `OAI.TuringRigidity.InternalUncountableSentence.ontoMatrix`, `OAI.TuringRigidity.Introreducible.trial`, `OAI.TuringRigidity.Introreducible.trialStep`, `OAI.TuringRigidity.LocalColumnCertificates.Allowed`, `OAI.TuringRigidity.LocalColumnCertificates.Extension`, `OAI.TuringRigidity.LocalColumnCertificates.Noncoding`, `OAI.TuringRigidity.LocalColumnCertificates.Output`, `OAI.TuringRigidity.LocalColumnCertificates.Presents`, `OAI.TuringRigidity.LocalComputability.canonical`, `OAI.TuringRigidity.LocalComputability.genericCanonical`, `OAI.TuringRigidity.LocalComputability.grow`, `OAI.TuringRigidity.LocalComputability.levelCode`, `OAI.TuringRigidity.LocalComputability.state`, `OAI.TuringRigidity.LocalInputs.Data` and 121 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DegreeRigidity_CohenForcing_CohenEffectiveGeneric`, `DegreeRigidity_CohenForcing_CohenWordCodeGraph`, `DegreeRigidity_CohenForcing_InternalCohenBitFlip`, `DegreeRigidity_CohenForcing_InternalCohenHomogeneity`, `DegreeRigidity_CohenForcing_InternalCohenName`, `DegreeRigidity_CohenForcing_InternalCohenReindex`, `DegreeRigidity_CohenForcing_InternalCohenRestriction`, `DegreeRigidity_CohenForcing_TaggedProductConditions`, `DegreeRigidity_Computability_ArithmeticSkolem`, `DegreeRigidity_Computability_Introreducible`, `DegreeRigidity_Computability_JumpIdeal`, `DegreeRigidity_Computability_JumpProperties`, `DegreeRigidity_Computability_NormalizedRecovery`, `DegreeRigidity_Computability_OracleCode`, `DegreeRigidity_Computability_RealProjectionSyntax`, `DegreeRigidity_Constructibility_ConstructibleSatisfaction`, `DegreeRigidity_Constructibility_ConstructibleTupleSpace`, `DegreeRigidity_Constructibility_ConstructionInputData`, `DegreeRigidity_Constructibility_PersistenceRealClosure`, `DegreeRigidity_Constructibility_PersistenceWitnessTree`, `DegreeRigidity_Constructibility_PersistentCountability`, `DegreeRigidity_Constructibility_PersistentPresentation`, `DegreeRigidity_Constructibility_PersistentRestrictions`, `DegreeRigidity_Constructibility_RelativeModelSyntax`, `DegreeRigidity_Constructibility_SingleRealConstruction`, `DegreeRigidity_Constructibility_UniformSentenceSupport`, `DegreeRigidity_Effective_FiniteRealPacking`, `DegreeRigidity_Effective_LocalColumnCertificates`, `DegreeRigidity_Effective_LocalComputability`, `DegreeRigidity_Effective_LocalInputs`, `DegreeRigidity_Effective_LocalOpen`, `DegreeRigidity_Effective_LocalScan`, `DegreeRigidity_Effective_LocalSourceEquation`, `DegreeRigidity_Effective_LocalStage`, `DegreeRigidity_Effective_SetCoding`, `DegreeRigidity_Effective_StageNormalization`, `DegreeRigidity_Effective_StageRecords`, `DegreeRigidity_Effective_TableIndices`, `DegreeRigidity_Effective_TriplePrefix`, `DegreeRigidity_Effective_TupleLookupAdequacy`, `DegreeRigidity_Effective_TuplePrefixSyntax`, `DegreeRigidity_Effective_UniformJumpSimulation`, `DegreeRigidity_Effective_UniformProgram`, `DegreeRigidity_Effective_UniformPrograms`, `DegreeRigidity_OrdinalCodes_CanonicalAdditionSyntax`, `DegreeRigidity_OrdinalCodes_CanonicalOmegaSyntax`, `DegreeRigidity_OrdinalCodes_IndexMatrix`, `DegreeRigidity_OrdinalCodes_IndexPresentation`, `DegreeRigidity_OrdinalCodes_IndexTuples`, `DegreeRigidity_OrdinalCodes_IndexedOrder`, `DegreeRigidity_OrdinalCodes_OmegaPowerSyntax`, `DegreeRigidity_OrdinalCodes_OmegaStageSyntax`, `DegreeRigidity_OrdinalCodes_OrdinalProductSets`, `DegreeRigidity_OrdinalCodes_OrdinalProductSyntax`, `DegreeRigidity_OrdinalCodes_OrdinalSumSets`, `DegreeRigidity_OrdinalCodes_OrdinalSumSyntax`, `DegreeRigidity_Representation_GenericFilterName`, `DegreeRigidity_Representation_NativePersistenceSyntax`, `DegreeRigidity_Representation_PairGenericSelection`, `DegreeRigidity_Representation_RealGeneratedPart`, `DegreeRigidity_Representation_SourceEquationTail`, `DegreeRigidity_SetModels_BindCanonicalArithmetic`, `DegreeRigidity_SetModels_InternalBooleanBits`, `DegreeRigidity_SetModels_InternalBooleanGeneric`, `DegreeRigidity_SetModels_InternalCountableEnumeration`, `DegreeRigidity_SetModels_InternalCountableFiniteUnion`, `DegreeRigidity_SetModels_InternalCountableProduct`, `DegreeRigidity_SetModels_InternalFiniteExhaustion`, `DegreeRigidity_SetModels_InternalQuotientConditions`, `DegreeRigidity_SetModels_InternalRealQuotient`, `DegreeRigidity_SetModels_InternalRegularAlgebra`, `DegreeRigidity_SetModels_InternalRelationSelection`, `DegreeRigidity_SetModels_InternalUncountableSentence`, `DegreeRigidity_SetModels_RegularCodeSplitting`, `DegreeRigidity_SetModels_RegularDecisionPartition`, `DegreeRigidity_SetModels_RegularTreeRun`, `DegreeRigidity_SetModels_RelationPresentation`, `DegreeRigidity_SetModels_SetModelAddition`, `DegreeRigidity_SetModels_SetModelArithmeticSyntax`, `DegreeRigidity_SetModels_SetModelColumns`, `DegreeRigidity_SetModels_SetModelCountability`, `DegreeRigidity_SetModels_SetModelFunctionGraphs`, `DegreeRigidity_SetModels_SetModelFunctionIteration`, `DegreeRigidity_SetModels_SetModelGraphImage`, `DegreeRigidity_SetModels_SetModelGraphPresentation`, `DegreeRigidity_SetModels_SetModelIteration`, `DegreeRigidity_SetModels_SetModelJoin`, `DegreeRigidity_SetModels_SetModelMultiplication`, `DegreeRigidity_SetModels_SetModelMultiplicationStep`, `DegreeRigidity_SetModels_SetModelPairing`, `DegreeRigidity_SetModels_SetModelPresentedCountability`, `DegreeRigidity_SetModels_SetModelRecursion`, `DegreeRigidity_SetModels_SetModelSequences`, `DegreeRigidity_SetModels_SetPresentationDecoding`, `DegreeRigidity_Syntax_DefinableSubsetCertificates`, `DegreeRigidity_Syntax_FiniteGraphSatisfaction`, `DegreeRigidity_Syntax_SentenceCodeDefinability`, `DegreeRigidity_Syntax_SentenceCodeFamily`, `DegreeRigidity_Syntax_SentenceFamilyFormula`, `DegreeRigidity_Syntax_SentenceSupportFormula`.
--
--   **Imports.** It imports the published bundle `Def_DegreeRigidity`; the bundles `OAIQ064A000` and `OAIQ064A001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ064A006` and `OAIQ064A007`; the statements `OAI.TuringRigidity.ArithmeticPersistence.persistent_iff`, `OAI.TuringRigidity.ArithmeticTree.native_nonidentity_absolute`, `OAI.TuringRigidity.ArithmeticTree.native_persistence_absolute`, `OAI.TuringRigidity.ArithmeticTree.setGenericallyPersistent_iff`, `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.real_collapse_reconstructs` and `OAI.TuringRigidity.SetModelPersistence.persistent_decoding`.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A000
import Definitions.Def_OAIQ064A001

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_OracleCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

theorem oracleFunction_injective : Function.Injective oracleFunction := by
  intro A B hab
  funext n
  have h := congrFun hab n
  cases ha : A n <;> cases hb : B n <;> simp [oracleFunction, ha, hb] at h ⊢

end TuringRigidity

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

def trial (Z : Oracle) (n c : ℕ) : Option ℕ :=
  if Z c = true ∧ n < codeLength c then some (codeBit n c) else none

def trialStep (p : ℕ) : ℕ :=
  let n := (Nat.unpair p).1
  let c := (Nat.unpair (Nat.unpair p).2).1
  let b := (Nat.unpair (Nat.unpair p).2).2
  encode (if b = 1 ∧ n < codeLength c then some (codeBit n c) else none)

end Introreducible
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
open FiniteShuffle ShuffleRequirements GenericCoding Set

def ColumnRequirement (D : List Bool → Prop) (b : Bool) (s : List Bool) : Prop :=
  ∃ t, D t ∧ ∀ G, Realizes s G → Realizes t (column b G)

end TuringRigidity.PairGenericSelection

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

def Runs {X : Type*} (O : X → ℕ →. ℕ) (f : X → ℕ →. ℕ) : Prop :=
  ∃ p : OracleCode, ∀ x, OracleCode.eval (O x) p = f x

end TuringRigidity.UniformPrograms

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

def filterCodeFormula : Formula :=
  .existsMem 1 (.existsMem 4 (.conj (.pairMem 1 0 4) (.orderedPair 2 0 1)))

end TuringRigidity.TransitiveNameModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_PersistentRestrictions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.PersistentRestrictions
open Set

def closureStep (π : Degree ≃o Degree) (S : Set Degree) : Set Degree :=
  S ∪ (π '' S ∪ (π.symm '' S ∪
    (Set.image2 (· ⊔ ·) S S ∪ ⋃ a ∈ S, Set.Iic a)))

def stage (π : Degree ≃o Degree) (S : Set Degree) : ℕ → Set Degree
  | 0 => insert ⊥ S
  | n + 1 => closureStep π (stage π S n)

theorem stage_mono (π : Degree ≃o Degree) (S : Set Degree) : Monotone (stage π S) := by
  apply monotone_nat_of_le_succ
  intro n a ha
  exact Or.inl ha

def hullSet (π : Degree ≃o Degree) (S : Set Degree) : Set Degree := ⋃ n, stage π S n

theorem hullSet_lower (π : Degree ≃o Degree) (S : Set Degree)
    {a b : Degree} (hab : a ≤ b) (hb : b ∈ hullSet π S) : a ∈ hullSet π S := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hb
  apply Set.mem_iUnion.mpr
  refine ⟨n + 1, Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩
  exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hn, hab⟩⟩

theorem hullSet_join (π : Degree ≃o Degree) (S : Set Degree)
    {a b : Degree} (ha : a ∈ hullSet π S) (hb : b ∈ hullSet π S) :
    a ⊔ b ∈ hullSet π S := by
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp ha
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hb
  apply Set.mem_iUnion.mpr
  refine ⟨max m n + 1, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
  exact ⟨a, stage_mono π S (le_max_left m n) hm,
    b, stage_mono π S (le_max_right m n) hn, rfl⟩

def restrict (π : Degree ≃o Degree) (I : CountableIdeal)
    (hf : ∀ a ∈ I.carrier, π a ∈ I.carrier)
    (hb : ∀ a ∈ I.carrier, π.symm a ∈ I.carrier) : I ≃o I where
  toFun a := ⟨π a.val, hf a.val a.property⟩
  invFun a := ⟨π.symm a.val, hb a.val a.property⟩
  left_inv a := Subtype.ext (π.symm_apply_apply a.val)
  right_inv a := Subtype.ext (π.apply_symm_apply a.val)
  map_rel_iff' := π.map_rel_iff

def Extends {I J : CountableIdeal} (hIJ : I.carrier ⊆ J.carrier)
    (ρ : I ≃o I) (σ : J ≃o J) : Prop :=
  ∀ a : I, (σ ⟨a.val, hIJ a.property⟩).val = (ρ a).val

def Persistent (I : CountableIdeal) (ρ : I ≃o I) : Prop :=
  ∀ x : Degree, ∃ (J : CountableIdeal) (hIJ : I.carrier ⊆ J.carrier)
    (σ : J ≃o J), x ∈ J.carrier ∧ Extends hIJ ρ σ

def RestrictsTo (π : Degree ≃o Degree) (I : CountableIdeal) (ρ : I ≃o I) : Prop :=
  ∀ a : I, π a.val = (ρ a).val

end TuringRigidity.PersistentRestrictions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_SourceEquationTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SourceEquationTail
open Set CountableForcing
variable {P Q : Type*} [Preorder P] [Preorder Q]

def productFilter (G : GenericFilter P) (H : GenericFilter Q) : GenericFilter (P × Q) where
  carrier := {p | p.1 ∈ G.carrier ∧ p.2 ∈ H.carrier}
  nonempty := by
    obtain ⟨p,hp⟩ := G.nonempty
    obtain ⟨q,hq⟩ := H.nonempty
    exact ⟨(p,q),hp,hq⟩
  upper := fun hpq hp => ⟨G.upper hpq.1 hp.1,H.upper hpq.2 hp.2⟩
  directed := by
    intro p q hp hq
    obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp.1 hq.1
    obtain ⟨s,hs,hsp,hsq⟩ := H.directed hp.2 hq.2
    exact ⟨(r,s),⟨hr,hs⟩,⟨hrp,hsp⟩,⟨hrq,hsq⟩⟩

end TuringRigidity.SourceEquationTail

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

theorem represents_unique {Y A B : Oracle} {d : Nat.Partrec.Code}
    (hA : Represents Y d A) (hB : Represents Y d B) : A = B := by
  apply oracleFunction_injective
  funext n
  obtain ⟨z, a, ha⟩ := hA.2 n
  have hh := (hA.1 n z a ha).symm.trans (hB.1 n z a ha)
  exact congrArg Part.some hh

theorem output_represents (Y : Oracle) (d : {d : Nat.Partrec.Code // Valid Y d}) :
    Represents Y d.val (output Y d) :=
  Classical.choose_spec ((valid_iff_represents Y d.val).mp d.property)

end TuringRigidity.TableIndices

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_IndexMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IndexMatrix
open Encodable UniformOracle CommonIdeal TableIndices

def validMatrix (Y : Oracle) (e q r : ℕ) : Prop :=
  run Y (machine e) (Nat.unpair q).1 (Nat.unpair r).1 =
      some (bit (Nat.unpair r).2.bodd) ∧
    let a := run Y (machine e) (Nat.unpair q).1 (Nat.unpair (Nat.unpair q).2).1
    let b := run Y (machine e) (Nat.unpair q).1 (Nat.unpair (Nat.unpair q).2).2
    a = none ∨ b = none ∨ a = b

instance instDecidableValidMatrix (Y : Oracle) (e q r : ℕ) : Decidable (validMatrix Y e q r) := by
  unfold validMatrix
  infer_instance

def checkMatrix (v : ℕ) : ℕ :=
  let wanted := (Nat.unpair v).1
  let s := (decode (α := Option ℕ) (Nat.unpair (Nat.unpair v).2).1).getD none
  let a := (decode (α := Option ℕ) (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).1).getD none
  let b := (decode (α := Option ℕ) (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).2).getD none
  if s = some (bit wanted.bodd) ∧ (a = none ∨ b = none ∨ a = b) then 1 else 0

end TuringRigidity.IndexMatrix

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_IndexedOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IndexedOrder
open Encodable CommonIdeal UniformOracle TableIndices IndexMatrix

def OrderWitness (Y : Oracle) (e₀ e₁ d : Nat.Partrec.Code) : Prop :=
  (∀ n a b z w, Certificate Y e₁ d n a z → Certificate Y e₁ d n b w → a = b) ∧
    ∀ n, ∃ a z w, Certificate Y e₁ d n a z ∧ TableIndices.run Y e₀ n w = some a

end TuringRigidity.IndexedOrder

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_IndexPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IndexPresentation
open Encodable TableIndices IndexMatrix OrderNormalForm

theorem value_eq {Y A : Oracle} {e : ℕ} (h : Represents Y (machine e) A) :
    value Y e = degree A := by
  have hv : Dom Y e := (valid_iff_represents _ _).mpr ⟨A, h⟩
  simp only [value, dite_eq_left hv]
  rw [represents_unique (output_represents _ _) h]

end TuringRigidity.IndexPresentation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetPresentationDecoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetPresentationDecoding
open BoundedSetTheory TransitiveNameModel
universe u

noncomputable def quotientSet (d E a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun c => ∃ x ∈ a, c = classSet d E x) (ZFSet.powerset d)

@[simp] theorem mem_quotientSet (d E a c : ZFSet.{u}) :
    c ∈ quotientSet d E a ↔ ∃ x ∈ a, c = classSet d E x := by
  simp only [quotientSet,ZFSet.mem_sep,ZFSet.mem_powerset]
  constructor
  · exact And.right
  · rintro ⟨x,hx,rfl⟩
    exact ⟨fun y hy => (mem_classSet _ _ _ _).mp hy |>.1,⟨x,hx,rfl⟩⟩

noncomputable def actionGraph (d E a R : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ a, ∃ y ∈ a,
    ZFSet.pair x y ∈ R ∧ z = ZFSet.pair (classSet d E x) (classSet d E y))
    (ZFSet.prod (quotientSet d E a) (quotientSet d E a))

@[simp] theorem mem_actionGraph (d E a R z : ZFSet.{u}) :
    z ∈ actionGraph d E a R ↔ ∃ x ∈ a, ∃ y ∈ a,
      ZFSet.pair x y ∈ R ∧ z = ZFSet.pair (classSet d E x) (classSet d E y) := by
  rw [actionGraph,ZFSet.mem_sep]
  constructor
  · exact And.right
  · intro h
    obtain ⟨x,hx,y,hy,hxy,rfl⟩ := h
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨(mem_quotientSet _ _ _ _).mpr ⟨x,hx,rfl⟩,
      (mem_quotientSet _ _ _ _).mpr ⟨y,hy,rfl⟩⟩,⟨x,hx,y,hy,hxy,rfl⟩⟩

def actionFormula : Formula :=
  .existsMem 1 (.existsMem 2 (.conj (.pairMem 1 0 6)
    (.existsMem 7 (.existsMem 8 (.conj (classFormula 1 3 6 7)
      (.conj (classFormula 0 2 6 7) (.orderedPair 4 1 0)))))))

end TuringRigidity.SetPresentationDecoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelIteration
open BoundedSetTheory TransitiveNameModel SetModelReals
universe u
noncomputable section

def traceFormula (n x y p v g w z : ℕ) : Formula :=
  .conj (.pairMem z x p)
    (.conj (.allMem n (.allMem (v+1) (.imp (.pairMem 1 0 (p+2))
      (.existsMem (w+2) (.conj (.successor 0 2)
        (.existsMem (v+3) (.conj (.pairMem 1 0 (p+4)) (.pairMem 2 0 (g+4)))))))))
      (.allMem v (.imp (.pairMem (n+1) 0 (p+1)) (.equal 0 (y+1)))))

def Trace (v g : ZFSet.{u}) (n : ℕ) (x y p : ZFSet.{u}) : Prop :=
  ZFSet.pair (natSet 0) x ∈ p ∧
  (∀ i < n, ∀ a ∈ v, ZFSet.pair (natSet i) a ∈ p →
    ∃ b ∈ v, ZFSet.pair (natSet (i+1)) b ∈ p ∧ ZFSet.pair a b ∈ g) ∧
  ∀ b ∈ v, ZFSet.pair (natSet n) b ∈ p → b = y

end
end TuringRigidity.SetModelIteration

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelIteration
open BoundedSetTheory TransitiveNameModel SetModelReals
universe u
noncomputable section

def iterationSet (v : ZFSet.{u}) (F : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ n : ℕ, ∃ x ∈ v,
    z = ZFSet.pair (ZFSet.pair (natSet n) x) (F^[n] x))
    (ZFSet.prod (ZFSet.prod ZFSet.omega v) v)

def iterationFormula : Formula :=
  .existsMem 1 (.existsMem 3 (.existsMem 4 (.existsMem 9 (.existsMem 8
    (.conj (.orderedPair 5 1 2) (.conj (.orderedPair 1 4 3)
      (traceFormula 4 3 2 0 7 8 6 10)))))))

end
end TuringRigidity.SetModelIteration

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
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration
universe u
noncomputable section

def successorFormula : Formula :=
  .existsMem 1 (.existsMem 2 (.conj (.orderedPair 2 1 0) (.successor 0 1)))

def additionSet : ZFSet.{u} := iterationSet ZFSet.omega setSucc

end
end TuringRigidity.SetModelArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelMultiplicationStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration
universe u
noncomputable section

def addStep (x : ZFSet.{u}) : ZFSet.{u} :=
  let q := Function.invFun numberPair x
  numberPair (q.1,q.1+q.2)

def addStepSet : ZFSet.{u} := ZFSet.sep (fun z => ∃ x ∈ pairNumbers, z = ZFSet.pair x (addStep x))
  (ZFSet.prod pairNumbers pairNumbers)

def addStepFormula : Formula :=
  .existsMem 1 (.existsMem 2 (.existsMem 3 (.existsMem 5 (.existsMem 6
    (.conj (.orderedPair 5 1 0) (.conj (.orderedPair 1 4 3)
      (.conj (.orderedPair 0 4 2) (.pairMem 1 2 8))))))))

def multiplicationIteration : ZFSet.{u} := iterationSet pairNumbers addStep

end
end TuringRigidity.SetModelArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelMultiplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration
universe u
noncomputable section

def mulFormula (n m k i d D z : ℕ) : Formula :=
  .existsMem d (.existsMem (d+1) (.existsMem (D+2)
    (.conj (.orderedPair 2 (m+3) (z+3)) (.conj (.orderedPair 1 (m+3) (k+3))
      (.conj (.orderedPair 0 (n+3) 2) (.pairMem 0 1 (i+3)))))))

def multiplicationSet : ZFSet.{u} := ZFSet.sep
  (fun z => ∃ n m, z = ZFSet.pair (numberPair (n,m)) (natSet (n*m)))
  (ZFSet.prod pairNumbers ZFSet.omega)

def multiplicationFormula : Formula :=
  .existsMem 1 (.existsMem 2 (.existsMem 3 (.existsMem 5
    (.conj (.orderedPair 4 0 1) (.conj (.orderedPair 0 3 2)
      (mulFormula 3 2 1 7 6 8 9))))))

end
end TuringRigidity.SetModelArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_JumpProperties
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OracleJump
open Encodable UniformOracle CommonIdeal TableIndices IndexMatrix ArithmeticHierarchy

theorem reduces_jump (Y : Oracle) : Reduces Y (jump Y) := by
  have h : RecursivePred Y (fun x => Y x = true) := by
    classical
    have hq : Nat.RecursiveIn {oracleFunction Y} (oracleFunction Y) :=
      .oracle _ (Set.mem_singleton _)
    exact hq.of_eq (fun x => by cases hy : Y x <;> simp [oracleFunction,hy])
  apply RecursiveIn.iff_nat.mpr
  exact (recursive_lift h).of_eq (fun x => by cases hy : Y x <;> simp [oracleFunction,hy])

theorem degree_le_jump (x : Degree) : x ≤ degreeJump x := by
  obtain ⟨Y,rfl⟩ := degree_surjective x
  exact reduces_jump Y

end TuringRigidity.OracleJump

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

def represent : OracleCode → Code
  | .zero => .zero
  | .succ => .succ
  | .left => .left
  | .right => .right
  | .query => .rfind' .zero
  | .pair c d => .pair (represent c) (represent d)
  | .comp c d => .comp (represent c) (represent d)
  | .prec c d => .prec (represent c) (represent d)
  | .find c => .rfind' (.comp (represent c) (.pair .left .right))

end TuringRigidity.UniformProgram

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

def Output (B : Oracle) (v : ℕ) : Prop :=
  ∃ z, (Nat.unpair (Nat.unpair v).2).2 ∈ TableIndices.run B
    (IndexMatrix.machine (Nat.unpair v).1) (Nat.unpair (Nat.unpair v).2).1 z

theorem output_sigma (B : Oracle) : Sigma B 1 (Output B) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hr := _root_.OAI.TuringRigidity.UniformOracle.total_comp (IndexMatrix.run_uniform_recursive B) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec
    (Primrec₂.natPair.comp (f.comp f) (Primrec₂.natPair.comp (f.comp (r.comp f)) r)))
  have heq := Primrec.ite (Primrec.eq.comp
    (Primrec.option_getD.comp (Primrec.decode.comp f) (Primrec.const none))
    (Primrec.option_some.comp r)) (Primrec.const 1) (Primrec.const 0)
  have hh : RecursivePred B (fun v => (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).2 ∈
      TableIndices.run B (IndexMatrix.machine (Nat.unpair (Nat.unpair v).1).1)
        (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).1 (Nat.unpair v).2) := by
    exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec heq) (_root_.OAI.TuringRigidity.UniformOracle.total_pair hr (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (r.comp (r.comp f))))).of_eq
      (fun v => by simp [Option.mem_def])
  apply (exists_form (n := 0) hh).congr
  intro v
  simp only [Output,Nat.unpair_pair]

def Presents (B : Oracle) (F : ℕ → Oracle) (codes count : ℕ) : Prop :=
  ∀ k, k < count → TableIndices.Represents B (IndexMatrix.machine (item codes k)) (F k)

theorem output_iff {B : Oracle} {F : ℕ → Oracle} {codes count k : ℕ}
    (h : Presents B F codes count) (hk : k < count) (a v : ℕ) :
    Output B (Nat.pair (item codes k) (Nat.pair a v)) ↔ v = CommonIdeal.bit (F k a) := by
  constructor
  · rintro ⟨z,hz⟩
    exact (h k hk).1 a z v (by simpa only [Nat.unpair_pair] using hz)
  · intro hv
    obtain ⟨z,b,hb⟩ := (h k hk).2 a
    have he := (h k hk).1 a z b hb
    exact ⟨z,by simpa only [Nat.unpair_pair,hv,he] using hb⟩

def Noncoding (B : Oracle) (v : ℕ) : Prop :=
  let codes := (Nat.unpair v).1
  let p := (Nat.unpair (Nat.unpair v).2).1
  let m := (Nat.unpair (Nat.unpair v).2).2
  m < (left p).length ∨ active p ≤ (Nat.unpair m).1 ∨
    Output B (Nat.pair (item codes (Nat.unpair m).1) (Nat.pair (Nat.unpair m).2 0))

theorem noncoding_sigma (B : Oracle) : Sigma B 1 (Noncoding B) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let p := f.comp r
  let m := r.comp r
  have hl := recursive_primrecPred B (Primrec.nat_lt.comp m (Primrec.list_length.comp (left_primrec.comp p)))
  have hk := recursive_primrecPred B (Primrec.nat_le.comp (active_primrec.comp p) (f.comp m))
  have ho := (output_sigma B).comp (Primrec₂.natPair.comp (item_primrec.comp f (f.comp m))
    (Primrec₂.natPair.comp (r.comp m) (Primrec.const 0)))
  exact (Form.raise (n := 0) (s := true) hl).or ((Form.raise (n := 0) (s := true) hk).or ho)

theorem noncoding_condition_iff {B : Oracle} {F : ℕ → Oracle} {codes : ℕ} {p : ℕ}
    (h : Presents B F codes (active p)) (m : ℕ) :
    Noncoding B (Nat.pair codes (Nat.pair p m)) ↔ ¬ CodingLocation F (condition p) m := by
  simp only [Noncoding,Nat.unpair_pair,CodingLocation,condition]
  by_cases hk : (Nat.unpair m).1 < active p
  · rw [output_iff h hk]
    cases F (Nat.unpair m).1 (Nat.unpair m).2 <;> simp [CommonIdeal.bit,hk]
  · simp [hk,show active p ≤ (Nat.unpair m).1 from Nat.le_of_not_gt hk]

def Allowed (B : Oracle) (v : ℕ) : Prop :=
  let req := (Nat.unpair v).1
  let m := (Nat.unpair v).2
  (left (item req 2)).getD m false = (right (item req 2)).getD m false ∨
    Noncoding B (Nat.pair (item req 0) (Nat.pair (item req 1) m))

theorem allowed_sigma (B : Oracle) : Sigma B 1 (Allowed B) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let req (i : ℕ) := item_primrec.comp f (Primrec.const i)
  have he := recursive_primrecPred B (Primrec.eq.comp
    ((Primrec.list_getD false).comp (left_primrec.comp (req 2)) r)
    ((Primrec.list_getD false).comp (right_primrec.comp (req 2)) r))
  have hn := (noncoding_sigma B).comp (Primrec₂.natPair.comp (req 0) (Primrec₂.natPair.comp (req 1) r))
  exact (Form.raise (n := 0) (s := true) he).or hn

def Extension (B : Oracle) (req : ℕ) : Prop :=
  left (item req 1) <+: left (item req 2) ∧ right (item req 1) <+: right (item req 2) ∧
    active (item req 1) ≤ active (item req 2) ∧
    ∀ m < (left (item req 2)).length, Allowed B (Nat.pair req m)

theorem extension_sigma (B : Oracle) : Sigma B 1 (Extension B) := by
  let req (i : ℕ) := item_primrec.comp Primrec.id (Primrec.const i)
  have hl := prefix_recursive B (left_primrec.comp (req 1)) (left_primrec.comp (req 2))
  have hr := prefix_recursive B (right_primrec.comp (req 1)) (right_primrec.comp (req 2))
  have ha := recursive_primrecPred B (Primrec.nat_le.comp (active_primrec.comp (req 1)) (active_primrec.comp (req 2)))
  have hc := (allowed_sigma B).bounded_all (Primrec.list_length.comp (left_primrec.comp (req 2)))
  exact (Form.raise (n := 0) (s := true) hl).and ((Form.raise (n := 0) (s := true) hr).and
    ((Form.raise (n := 0) (s := true) ha).and hc))

theorem extension_condition_iff {B : Oracle} {F : ℕ → Oracle} {codes p q : ℕ}
    (h : Presents B F codes (active p)) :
    Extension B (encode [codes,p,q]) ↔ Extends F (condition p) (condition q) := by
  have hm (m : ℕ) : Allowed B (Nat.pair (encode [codes,p,q]) m) ↔
      (left q).getD m false = (right q).getD m false ∨ ¬ CodingLocation F (condition p) m := by
    simp only [Allowed,Nat.unpair_pair,item,encodek,Option.getD_some,List.getD_cons_zero,List.getD_cons_succ]
    exact or_congr Iff.rfl (noncoding_condition_iff h m)
  change (_ ∧ _ ∧ _ ∧ ∀ m < (left (item (encode [codes,p,q]) 2)).length,
    Allowed B (Nat.pair (encode [codes,p,q]) m)) ↔ _
  simp only [hm,item,encodek,Option.getD_some,List.getD_cons_zero,List.getD_cons_succ]
  constructor
  · rintro ⟨hl,hr,ha,hc⟩
    exact ⟨hl,hr,ha,fun m hm hlen => (hc m hlen).resolve_right (not_not.mpr hm)⟩
  · rintro ⟨hl,hr,ha,hc⟩
    refine ⟨hl,hr,ha,fun m hlen => ?_⟩
    by_cases hm : CodingLocation F (condition p) m
    · exact Or.inl (hc m hm hlen)
    · exact Or.inr hm

end TuringRigidity.LocalColumnCertificates

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_LocalOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.LocalOpen
open Encodable UniformOracle ArithmeticHierarchy OracleJump EffectiveWitness EncodedForcing CodingForcing
open LocalColumnCertificates

theorem uniform_open_decision (B : Oracle) :
    ∃ step : ℕ → ℕ,
      Nat.RecursiveIn {oracleFunction (jump B)} (fun x => Part.some (step x)) ∧
      ∀ (F : ℕ → Oracle) codes e p, Presents B F codes (active p) →
        Extends F (condition p) (condition (step (encode [codes,e,p]))) ∧
        (Halts B e (step (encode [codes,e,p])) ∨
          (step (encode [codes,e,p]) = p ∧
            ∀ q, Extends F (condition p) (condition q) → ¬ Halts B e q)) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let req (i : ℕ) := item_primrec.comp f (Primrec.const i)
  let P : ℕ → Prop := fun v =>
    Extension B (encode [item (Nat.unpair v).1 0,item (Nat.unpair v).1 2,(Nat.unpair v).2]) ∧
      Halts B (item (Nat.unpair v).1 1) (Nat.unpair v).2
  have hext := (extension_sigma B).comp (Primrec.encode.comp
    (Primrec.list_cons.comp (req 0) (Primrec.list_cons.comp (req 2)
      (Primrec.list_cons.comp r (Primrec.const [])))))
  have hhalt := (halts_sigma B).comp (Primrec₂.natPair.comp (req 1) r)
  have hP : Sigma B 1 P := by
    simpa only [P,Nat.unpair_pair] using hext.and hhalt
  obtain ⟨g,hg,hs⟩ := sigma1_choice hP
  let step : ℕ → ℕ := fun x => EffectiveForcing.answer (Nat.pair (item x 2) (g x))
  have hstep := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := {oracleFunction (jump B)}) EffectiveForcing.answer_primrec)
    (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (item_primrec.comp Primrec.id (Primrec.const 2))) hg)
  refine ⟨step,hstep,fun F codes e p h => ?_⟩
  rcases hs (encode [codes,e,p]) with ⟨hz,hn⟩ | ⟨hp,hw⟩
  · have he : step (encode [codes,e,p]) = p := by simp only [step,EffectiveForcing.answer,Nat.unpair_pair,ite_eq_left hz,item,encodek,Option.getD_some,List.getD_cons_zero,List.getD_cons_succ]
    rw [he]
    refine ⟨extends_refl _ _,Or.inr ⟨rfl,fun q hq hhalt => ?_⟩⟩
    apply hn
    refine ⟨q,?_⟩
    simpa only [P,Nat.unpair_pair,item,encodek,Option.getD_some,List.getD_cons_zero,List.getD_cons_succ] using
      And.intro ((extension_condition_iff h).2 hq) hhalt
  · have hz : g (encode [codes,e,p]) ≠ 0 := by omega
    have he : step (encode [codes,e,p]) = g (encode [codes,e,p]) - 1 := by simp only [step,EffectiveForcing.answer,Nat.unpair_pair,ite_eq_right hz]
    rw [he]
    have hh : Extension B (encode [codes,p,g (encode [codes,e,p])-1]) ∧ Halts B e (g (encode [codes,e,p])-1) := by
      simpa only [P,Nat.unpair_pair,item,encodek,Option.getD_some,List.getD_cons_zero,List.getD_cons_succ] using hw
    exact ⟨(extension_condition_iff h).1 hh.1,Or.inl hh.2⟩

end TuringRigidity.LocalOpen

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

structure Data where
  B : Oracle
  X : Oracle
  F : ℕ → Oracle
  codes : ℕ → ℕ
  codes_recursive : Nat.RecursiveIn {oracleFunction X} (fun n => Part.some (codes n))
  codes_valid : ∀ n, LocalColumnCertificates.Presents B F (codes n) n

def Data.bound (D : Data) : Oracle := join D.X (jump D.B)

def Data.request (D : Data) (v : ℕ) : ℕ :=
  encode [D.codes (active (Nat.unpair v).2),(Nat.unpair v).1,(Nat.unpair v).2]

def Data.openProcedure (D : Data) (v : ℕ) : ℕ :=
  Classical.choose (LocalOpen.uniform_open_decision D.B) (D.request v)

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

def openProcedure (D : LocalInputs.Data) : ℕ → ℕ := D.openProcedure

structure State where
  condition : Condition
  done : Finset ℕ
  seen : Finset ℕ

def generic (D : LocalInputs.Data) (p : State) : Condition :=
  EncodedForcing.condition (openProcedure D (Nat.pair (FiniteInjurySchedule.visit p.seen) (code p.condition)))

end
end TuringRigidity.LocalStage

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
open Encodable UniformOracle EncodedForcing FiniteInjurySchedule

def doneUpdate (n a : ℕ) : ℕ :=
  if a = 0 then n else encode ((a-1) :: (record n).filter (fun i => i < a-1))

def seenReset (n a : ℕ) : ℕ :=
  if a = 0 then n else encode ((record n).filter (fun i => i < a))

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
open Encodable UniformOracle EncodedForcing CodingForcing FiniteInjury StageRecords
noncomputable section
attribute [local instance] Classical.propDecidable

def levelCode (p t : ℕ) : ℕ := Nat.pair (encode (left p)) (Nat.pair (encode (right p)) t)

@[simp] theorem condition_levelCode (p t : ℕ) : condition (levelCode p t) = atLevel (condition p) t :=
  condition_code (atLevel (condition p) t)

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

def state (v : ℕ) : LocalStage.State :=
  ⟨condition (Nat.unpair v).1,members (Nat.unpair (Nat.unpair v).2).1,members (Nat.unpair (Nat.unpair v).2).2⟩

def canonical (p : ℕ) : ℕ := levelCode p (active p)

def genericCanonical (D : LocalInputs.Data) (v : ℕ) : ℕ := LocalStage.openProcedure D
  (Nat.pair (nextVisit (Nat.unpair (Nat.unpair v).2).2) (canonical (Nat.unpair v).1))

@[simp] theorem generic_eq (D : LocalInputs.Data) (v : ℕ) :
    condition (genericCanonical D v) = LocalStage.generic D (state v) := rfl

def grow (p s : ℕ) : ℕ := Nat.pair (encode (left p ++ [false]))
  (Nat.pair (encode (right p ++ [false])) (s+1))

end
end TuringRigidity.LocalComputability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_StageNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.StageNormalization
open Encodable UniformOracle EncodedForcing StageRecords

def prefixStep (A : Oracle) (v : ℕ) : ℕ := UniformOracle.appendEncoded
  (Nat.unpair (Nat.unpair v).2).2
  (CommonIdeal.bit (A (Nat.pair (Nat.unpair v).1 (Nat.unpair (Nat.unpair v).2).1)))

def columnPrefix (A : Oracle) (k n : ℕ) : ℕ :=
  recur (fun _ => encode ([] : List ℕ)) (prefixStep A) k n

end TuringRigidity.StageNormalization

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_SetCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetCoding
open AntichainParameters

def SetCode.Holds (p : SetCode) (x : Degree) : Prop := ∃ c, p.Graph x c

end TuringRigidity.SetCoding

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
open Encodable IndexPresentation IndexMatrix TableIndices

noncomputable def supIndex : ℕ → ℕ → ℕ
  | 0, _ => zeroIndex
  | n+1, t => joinIndex ((Nat.unpair t).1) (supIndex n (Nat.unpair t).2)

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
open IndexPresentation IndexTuples ArithmeticHierarchy AntichainDecoding
open SetCoding RelationCoding

def ACode.Good (Y : Oracle) (p : ACode) : Prop :=
  Dom Y p.bound ∧ Dom Y p.left ∧ Dom Y p.right
noncomputable def ACode.decode (Y : Oracle) (p : ACode) : AntichainCode :=
  ⟨value Y p.bound, value Y p.left, value Y p.right⟩
def ACode.Holds (Y : Oracle) (p : ACode) (x : ℕ) : Prop :=
  Antichain Y p.bound p.left p.right x

def SCode.Good (Y : Oracle) (p : SCode) : Prop :=
  Dom Y p.bound ∧ p.tags.Good Y ∧ p.decorated.Good Y
noncomputable def SCode.decode (Y : Oracle) (p : SCode) : SetCode :=
  ⟨value Y p.bound, p.tags.decode Y, p.decorated.decode Y⟩
def SCode.Graph (Y : Oracle) (p : SCode) (x c : ℕ) : Prop :=
  LE Y x p.bound ∧ p.tags.Holds Y c ∧ p.decorated.Holds Y (joinIndex x c)

def RCode.Good {n} (Y : Oracle) (p : RCode n) : Prop :=
  (∀ i, (p.coordinates i).Good Y) ∧ p.tuples.Good Y
noncomputable def RCode.decode {n} (Y : Oracle) (p : RCode n) : RelationCode n :=
  ⟨fun i => (p.coordinates i).decode Y, p.tuples.decode Y⟩

def RCode.Holds {n} (Y : Oracle) (p : RCode n) (v : ℕ) : Prop :=
  (∀ i : Fin n, Dom Y (entry i.val v)) ∧ ∃ t : ℕ,
    (∀ i : Fin n, Dom Y (entry i.val t) ∧
      (p.coordinates i).Graph Y (entry i.val v) (entry i.val t)) ∧
    p.tuples.Holds Y (supIndex n t)

end TuringRigidity.RelationPresentation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_NormalizedRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.NormalizedRecovery
open EncodedForcing Encodable UniformOracle Introreducible StageNormalization

def trial (B : Oracle) (n c : ℕ) : Option ℕ :=
  if B (Nat.pair (Nat.unpair n).1 c) = true ∧ (Nat.unpair n).2 < codeLength c
    then some (codeBit (Nat.unpair n).2 c) else none

end TuringRigidity.NormalizedRecovery

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_JumpIdeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.JumpIdeal
open OracleJump IdealInterpretation PersistentRestrictions GlobalLocality
noncomputable section

theorem iterate_monotone (x : Degree) : Monotone (degreeIterate x) := by
  apply monotone_nat_of_le_succ
  intro n
  exact degree_le_jump _

end
end TuringRigidity.JumpIdeal

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_PersistentPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.PersistentPresentation
open EncodedForcing OracleJump ArithmeticHierarchy IdealInterpretation PersistentRestrictions
noncomputable section

def Presented (I : CountableIdeal) (H : Oracle) : Prop :=
  ∀ x, x ∈ I.carrier ↔ ∃ k, degree (columns H k) = x

def entry {I : CountableIdeal} {H : Oracle} (hpres : Presented I H) (n : ℕ) : I :=
  ⟨degree (columns H n),(hpres _).mpr ⟨n,rfl⟩⟩

def Graph {I : CountableIdeal} (ρ : I ≃o I) {H : Oracle} (hpres : Presented I H) (v : ℕ) : Prop :=
  (ρ (entry hpres (Nat.unpair v).1)).val = degree (columns H (Nat.unpair v).2)

end
end TuringRigidity.PersistentPresentation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_PersistentCountability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.PersistentCountability
open EncodedForcing OracleJump ArithmeticHierarchy PersistentRestrictions PersistentPresentation
noncomputable section
attribute [local instance] Classical.propDecidable

def graphOracle {I : CountableIdeal} {H : Oracle} (hpres : Presented I H)
    (ρ : I ≃o I) : Oracle := fun n => decide (Graph ρ hpres n)

end
end TuringRigidity.PersistentCountability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_PersistenceRealClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.PersistenceRealClosure
open EncodedForcing OracleJump ArithmeticHierarchy UniformArithmetic JumpIdealPresentation
open PersistentRestrictions PersistentPresentation PersistentCountability NumericalIdeal
open NumericalAutomorphism NumericalExtension
noncomputable section

structure Closed (M : Set Oracle) : Prop where
  lower : ∀ {A B}, B ∈ M → Reduces A B → A ∈ M
  join : ∀ {A B}, A ∈ M → B ∈ M → TuringRigidity.join A B ∈ M
  omega : ∀ {A}, A ∈ M → omegaJump A ∈ M

end
end TuringRigidity.PersistenceRealClosure

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelSequences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelSequences
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration
universe u
noncomputable section

def sliceFormula : Formula :=
  .existsMem 1 (.existsMem 3 (.existsMem 7
    (.conj (.orderedPair 3 2 1) (.conj (.orderedPair 0 2 6) (.pairMem 0 1 7)))))

def PairingCode (p : ZFSet.{u}) : Prop := ∀ n k m : ℕ,
  ZFSet.pair (ZFSet.pair (natSet n) (natSet k)) (natSet m) ∈ p ↔ m = Nat.pair n k

def flattenFormula : Formula :=
  .existsMem 1 (.existsMem 2 (.existsMem 7 (.existsMem 5
    (.conj (.orderedPair 1 3 2) (.conj (.pairMem 1 4 8)
      (.conj (.pairMem 3 0 7) (.member 2 0)))))))

end
end TuringRigidity.SetModelSequences

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration SetModelSequences
universe u
noncomputable section

def pairFormula (n m k a b d w : ℕ) : Formula :=
  .disj (.conj (.member n m) (.existsMem w
    (.conj (tripleFormula (m+1) (m+1) 0 (b+1) (d+1))
      (tripleFormula 0 (n+1) (k+1) (a+1) (d+1)))))
    (.conj (.neg (.member n m)) (.existsMem w
      (.conj (tripleFormula (n+1) (n+1) 0 (b+1) (d+1))
        (.existsMem (w+1) (.conj (tripleFormula 1 (n+2) 0 (a+2) (d+2))
          (tripleFormula 0 (m+2) (k+2) (a+2) (d+2)))))))

def pairingFormula : Formula :=
  .existsMem 1 (.existsMem 2 (.existsMem 3 (.existsMem 5
    (.conj (.orderedPair 4 0 1) (.conj (.orderedPair 0 3 2)
      (pairFormula 3 2 1 7 8 6 5))))))

end
end TuringRigidity.SetModelArithmetic

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

variable {M : ZFSet.{u}}

abbrev GraphCode (g : ZFSet.{u}) (f : ℕ → ℕ) : Prop :=
  ∀ n m, ZFSet.pair (natSet n) (natSet m) ∈ g ↔ m = f n

def HasGraph (M : ZFSet.{u}) (f : ℕ → ℕ) : Prop :=
  ∃ g ∈ M, GraphCode g f

end
end TuringRigidity.SetModelFunctions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelFunctionIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelFunctions
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration SetModelArithmetic
universe u
noncomputable section
variable {M : ZFSet.{u}}

def natIteration (f : ℕ → ℕ) : ZFSet.{u} := iterationSet ZFSet.omega (natLift f)

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

def PairCode (x y z : ZFSet.{u}) : Prop :=
  ZFSet.pair x y ∈ pairNumbers ∧ ZFSet.pair (ZFSet.pair x y) z ∈ pairingSet

end
end TuringRigidity.SetModelSyntax

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

def wordBit (v : ℕ) : ℕ :=
  if (word (Nat.unpair v).1).getD (Nat.unpair v).2 false then 1 else 0

def wordGraphFormula : Formula :=
  .existsMem 4 (.conj (.pairMem 2 0 3)
    (.conj (.functionGraph 1 0 6)
      (.allMem 0 (.existsMem 6 (.existsMem 7
        (.conj (tripleFormula 5 2 1 11 10)
          (.conj (.pairMem 1 0 7) (.pairMem 2 0 4))))))))

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

def WordDecision (Y : Oracle) (e : ℕ) (p : List Bool) : Prop :=
  Halts Y e (encode p) ∨ ∀ q : List Bool, p <+: q → ¬ Halts Y e (encode q)

end TuringRigidity.InternalCohen

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

noncomputable def tupleCode {n : ℕ} (v : Fin n → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair (natSet n) (ZFSet.range (fun i : Fin n => ZFSet.pair (natSet i.val) (v i)))

end TuringRigidity.RelativeConstructible

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

noncomputable def tupleSpace (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun t : Σ n : ℕ, Fin n → Conditions A =>
    tupleCode (fun i => label A (t.2 i)))

def tupleFormula (o A Q t : ℕ) : Formula :=
  .existsMem o (.existsMem (Q+1)
    (.conj (.orderedPair (t+2) 1 0) (.functionGraph 0 1 (A+2))))

end TuringRigidity.RelativeConstructible

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
open TransitiveNameModel BoundedSetTheory CohenSymmetry
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

def flipMatchesFormula (A B p q z0 z1 : ℕ) : Formula :=
  .allMem A (.conj
    (.iff (.pairMem 0 (z0+1) (q+1))
      (.disj (.conj (.member 0 (B+1)) (.pairMem 0 (z1+1) (p+1)))
        (.conj (.neg (.member 0 (B+1))) (.pairMem 0 (z0+1) (p+1)))))
    (.iff (.pairMem 0 (z1+1) (q+1))
      (.disj (.conj (.member 0 (B+1)) (.pairMem 0 (z0+1) (p+1)))
        (.conj (.neg (.member 0 (B+1))) (.pairMem 0 (z1+1) (p+1))))))

end TuringRigidity.InternalCohenBitFlip

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
open TransitiveNameModel BoundedSetTheory CohenSymmetry
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

def matchingFormula (x p q z1 : ℕ) : Formula :=
  .disj (.conj (.pairMem x z1 p) (.neg (.pairMem x z1 q)))
    (.conj (.neg (.pairMem x z1 p)) (.pairMem x z1 q))

end TuringRigidity.InternalCohenBitFlip

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

def realNameFormula : BoundedSetTheory.Formula :=
  .existsMem 1 (.existsMem 3 (.existsMem 6
    (.conj (.pairMem 1 0 6) (.conj (.pairMem 1 8 2) (.orderedPair 3 0 2)))))

end TuringRigidity.InternalCohen

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

def entryFormula (U g d k x : ℕ) : Formula := .disj (.pairMem k x g)
  (.conj (.equal x d) (.allMem U (.neg (.pairMem (k+1) 0 (g+1)))))

end TuringRigidity.InternalCountableFiniteUnion

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

def fiberFormula (Y R x a : ℕ) : Formula := .conj (.subset a Y)
  (.allMem Y (.iff (.member 0 (a+1)) (.pairMem (x+1) 0 (R+1))))

end TuringRigidity.InternalRelationSelection

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenReindex
open TransitiveNameModel BoundedSetTheory CohenSymmetry
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

def matchesFormula (A B f p q bit : ℕ) : Formula :=
  .allMem A (.allMem (B+1) (.imp (.pairMem 1 0 (f+2))
    (.allMem (bit+2) (.iff (.pairMem 2 0 (p+3)) (.pairMem 1 0 (q+3))))))

end TuringRigidity.InternalCohenReindex

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
open TransitiveNameModel BoundedSetTheory

def restrictionFormula (B V p q : ℕ) : Formula := .conj (.subset q p)
  (.allMem p (.iff (.member 0 (q+1))
    (.existsMem (B+1) (.existsMem (V+2) (.orderedPair 2 1 0)))))

end TuringRigidity.InternalCohenRestriction

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

def enumeratesFormula (ω E g : ℕ) : Formula :=
  .disj (.conj (.empty E) (.empty g))
    (.conj (.functionGraph g ω E) (.allMem E (.existsMem (ω+1) (.pairMem 0 1 (g+2)))))

end TuringRigidity.InternalCountableEnumeration

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

def initialFormula (g n x : ℕ) : Formula := .existsMem n (.pairMem 0 (x+1) (g+1))

end TuringRigidity.InternalFiniteExhaustion

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCountableProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCountableProduct
open TransitiveNameModel BoundedSetTheory InternalFiniteExhaustion

def rectangleFormula (A B f g n p : ℕ) : Formula :=
  .existsMem A (.existsMem (B+1) (.conj (.orderedPair (p+2) 1 0)
    (.conj (initialFormula (f+2) (n+2) 1) (initialFormula (g+2) (n+2) 0))))

end TuringRigidity.InternalCountableProduct

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

def codeFormula (p s z z0 z1 : ℕ) : Formula :=
  .conj (.allMem z (.disj
    (.existsMem (p+1) (.orderedPair 1 (z0+2) 0))
    (.existsMem (s+1) (.orderedPair 1 (z1+2) 0))))
    (.conj (.allMem p (.pairMem (z0+1) 0 (z+1)))
      (.allMem s (.pairMem (z1+1) 0 (z+1))))

end TuringRigidity.TaggedProductConditions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticSkolem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic
noncomputable section

namespace HasTest

def col (k : ℕ) (t : Test) : Test :=
  t.subst .input (fun s => .witness (.pair (.const k) s))

def tailTest (t : Test) : Test :=
  t.subst .input (fun s => .witness (.prim Nat.succ Primrec.succ s))

def zeroTag : Test :=
  .pure (fun n => n = 0) (Primrec.eq.comp Primrec.id (Primrec.const 0))
    (.witness (.const 0))

end HasTest

end
end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SentenceCodeDefinability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.SentenceCoding
open BoundedSetTheory TransitiveNameModel BoundedDefinability SetModelFunctions SetModelSyntax
universe u

variable {M : ZFSet.{u}}

def UnaryGraph (f : ℕ → ℕ) (x y : ZFSet.{u}) : Prop :=
  ∃ n : ℕ, x = natSet n ∧ y = natSet (f n)

def BinaryGraph (f : ℕ → ℕ → ℕ) (x y z : ZFSet.{u}) : Prop :=
  ∃ n m : ℕ, x = natSet n ∧ y = natSet m ∧ z = natSet (f n m)

end TuringRigidity.SentenceCoding

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

def readGraph : ℕ → ℕ → ℕ → (ℕ → ℕ) → Formula → Formula
  | 0, _, _, _, ψ => ψ
  | n+1, a, g, idx, ψ => .existsMem a
      (.conj (.pairMem (idx n+1) 0 (g+1))
        (readGraph n (a+1) (g+1) (fun i => idx i+1) ψ))

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

def SetClosed (S : ZFSet.{u}) : Prop :=
  S ⊆ ZFSet.omega ∧ Closed (fun n => natSet n ∈ S)

def LeastFamily (Q c S : ZFSet.{u}) : Prop :=
  c ∈ S ∧ SetClosed S ∧
    ∀ T ∈ Q, c ∈ T → SetClosed T → S ⊆ T

end TuringRigidity.SentenceCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SentenceFamilyFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.SentenceCoding
open ElementaryModel BoundedSetTheory TransitiveNameModel BoundedDefinability SetModelFunctions
universe u

variable {M : ZFSet.{u}}

def SetStep (S c : ZFSet.{u}) : Prop :=
  (∃ x ∈ ZFSet.omega, ∃ y ∈ ZFSet.omega, BinaryGraph (fun i j => binary 0 (atom i) (atom j)) x y c) ∨
  (∃ x ∈ ZFSet.omega, ∃ y ∈ ZFSet.omega, BinaryGraph (fun i j => binary 1 (atom i) (atom j)) x y c) ∨
  (∃ x ∈ S, ∃ y ∈ S, BinaryGraph (binary 2) x y c) ∨
  (∃ x ∈ S, UnaryGraph (unary 3) x c) ∨
  (∃ x ∈ S, UnaryGraph (unary 4) x c)

end TuringRigidity.SentenceCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SentenceSupportFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.SentenceCoding
open ElementaryModel RelativeConstructible BoundedSetTheory TransitiveNameModel
open BoundedDefinability SetModelFunctions SetModelReals
universe u

variable {M : ZFSet.{u}}

def SetSupportStep (G c b : ZFSet.{u}) : Prop :=
  (∃ i ∈ ZFSet.omega, ∃ j ∈ ZFSet.omega,
    BinaryGraph (fun i j => binary 0 (atom i) (atom j)) i j c ∧ BinaryGraph (fun i j => max i j + 1) i j b) ∨
  (∃ i ∈ ZFSet.omega, ∃ j ∈ ZFSet.omega,
    BinaryGraph (fun i j => binary 1 (atom i) (atom j)) i j c ∧ BinaryGraph (fun i j => max i j + 1) i j b) ∨
  (∃ i ∈ ZFSet.omega, ∃ j ∈ ZFSet.omega, ∃ a ∈ ZFSet.omega, ∃ d ∈ ZFSet.omega,
    BinaryGraph (binary 2) i j c ∧ ZFSet.pair i a ∈ G ∧ ZFSet.pair j d ∈ G ∧ BinaryGraph max a d b) ∨
  (∃ i ∈ ZFSet.omega, UnaryGraph (unary 3) i c ∧ ZFSet.pair i b ∈ G) ∨
  (∃ i ∈ ZFSet.omega, ∃ a ∈ ZFSet.omega,
    UnaryGraph (unary 4) i c ∧ ZFSet.pair i a ∈ G ∧ UnaryGraph (fun n => n-1) a b)

def SetSupportRecursion (F G : ZFSet.{u}) : Prop :=
  (∀ z ∈ G, ∃ c ∈ F, ∃ b ∈ ZFSet.omega, z = ZFSet.pair c b) ∧
    ∀ c ∈ F, ∀ b ∈ ZFSet.omega, ZFSet.pair c b ∈ G ↔ SetSupportStep G c b

end TuringRigidity.SentenceCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformSentenceSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.SentenceCoding
open ElementaryModel RelativeConstructible BoundedSetTheory TransitiveNameModel
open BoundedDefinability SetModelFunctions
universe u

variable {M : ZFSet.{u}}

def BoundWitness (Q B c b : ZFSet.{u}) : Prop :=
  ∃ F ∈ Q, ∃ G ∈ B, LeastFamily Q c F ∧ SetSupportRecursion F G ∧ ZFSet.pair c b ∈ G

end TuringRigidity.SentenceCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_TuplePrefixSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

def PrefixGraphs (A n g m h x : ZFSet.{u}) : Prop :=
  m = insert n n ∧ FunctionGraph m A h ∧ ZFSet.pair (natSet 0) x ∈ h ∧
    ∀ i ∈ n, ∃ j ∈ m, j = insert i i ∧
      ∀ y ∈ A, ZFSet.pair i y ∈ g → ZFSet.pair j y ∈ h

def prefixGraphsFormula (A n g m h x z : ℕ) : Formula :=
  .conj (.successor m n) (.conj (.functionGraph h m A)
    (.conj (.pairMem z x h)
      (.allMem n (.existsMem (m+1) (.conj (.successor 0 1)
        (.allMem (A+2) (.imp (.pairMem 2 0 (g+3)) (.pairMem 1 0 (h+3)))))))))

def tuplePrefixFormula (A o Q t x u z : ℕ) : Formula :=
  .existsMem o (.existsMem (Q+1) (.existsMem (o+2) (.existsMem (Q+3)
    (.conj (.orderedPair (t+4) 3 2) (.conj (.orderedPair (u+4) 1 0)
      (prefixGraphsFormula (A+4) 3 2 1 0 (x+4) (z+4)))))))

end TuringRigidity.RelativeConstructible

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

def TupleAdequate (Q B G c t : ZFSet.{u}) : Prop :=
  ∃ n ∈ ZFSet.omega, ∃ g ∈ G, ∃ b ∈ ZFSet.omega,
    t = ZFSet.pair n g ∧ BoundWitness Q B c b ∧ b ⊆ n

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

def ParameterAdequate (Q B G c t : ZFSet.{u}) : Prop :=
  ∃ n ∈ ZFSet.omega, ∃ g ∈ G, ∃ b ∈ ZFSet.omega,
    t = ZFSet.pair n g ∧ BoundWitness Q B c b ∧ ∀ x ∈ b, x ∈ n ∨ x = n

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

def realPart (P : Oracle) : ℕ → Oracle
  | 0 => fun k => P (2*k)
  | i+1 => realPart (fun k => P (2*k+1)) i

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

def pathReal (P : Oracle) : List ℕ → Oracle
  | [] => P
  | i::is => pathReal (realPart P i) is

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelJoin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration
universe u
noncomputable section

def joinFormula : Formula :=
  .existsMem 1 (.disj (.conj (tripleFormula 0 0 1 5 6) (.member 0 3))
    (.existsMem 2 (.conj (tripleFormula 1 1 0 6 7)
      (.conj (.successor 2 0) (.member 1 5)))))

end
end TuringRigidity.SetModelArithmetic

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

def bitStep (b : Bool) (w a d x y : ℕ) : Formula :=
  if b then .existsMem w (.conj (tripleFormula (x+1) (x+1) 0 (a+1) (d+1))
    (.successor (y+1) 0)) else tripleFormula x x y a d

def bitIndexFormula : List Bool → ℕ → ℕ → ℕ → ℕ → ℕ → Formula
  | [], _, _, _, x, y => .equal y x
  | b::bs, w, a, d, x, y => .existsMem w
      (.conj (bitIndexFormula bs (w+1) (a+1) (d+1) (x+1) 0)
        (bitStep b (w+1) (a+1) (d+1) 0 (y+1)))

def projectionMember (bs : List Bool) (w a d P x : ℕ) : Formula :=
  .conj (.member x w) (.existsMem w
    (.conj (bitIndexFormula bs (w+1) (a+1) (d+1) (x+1) 0) (.member 0 (P+1))))

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_PersistenceWitnessTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic ArithmeticPersistence
noncomputable section
attribute [local instance] Classical.propDecidable

namespace Test

def joinWitness (H : Oracle) (f : ℕ → ℕ) : ℕ → ℕ := fun n =>
  if (Nat.unpair n).1 = 0 then (if H (Nat.unpair n).2 then 1 else 0) else f (Nat.unpair n).2

end Test

end
end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeModelSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel BoundedDefinability SetModelFunctions
universe u

def ordinalFormula (i : ℕ) : Formula :=
  .conj (.transitive i) (Formula.allMem i (.transitive 0))

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

def bitOracle (P : Oracle) (bs : List Bool) : Oracle := fun n => P (bitIndex bs n)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_LocalSourceEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.LocalSourceEquation
open Set PersistentRestrictions

instance instSemilatticeSupSubtypeDegreeMemSetCarrier (I : CountableIdeal) : SemilatticeSup I where
  sup a b := ⟨a.val ⊔ b.val,I.join_mem a.property b.property⟩
  le_sup_left a b := (le_sup_left : a.val ≤ a.val ⊔ b.val)
  le_sup_right a b := (le_sup_right : b.val ≤ a.val ⊔ b.val)
  sup_le a b c h₁ h₂ := (sup_le h₁ h₂ : a.val ⊔ b.val ≤ c.val)

end TuringRigidity.LocalSourceEquation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_TriplePrefix
attribute [-instance] _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.TriplePrefix
open FiniteShuffle ShuffleRequirements PairGenericSelection

def prefixes (s : List Bool) : List Bool × List Bool × List Bool :=
  let H : Oracle := fun i => s.getD i false
  (initial (column false H) s.length,
    initial (column false (column true H)) s.length,
    initial (column true (column true H)) s.length)

end TuringRigidity.TriplePrefix

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
open Encodable CommonIdeal TableIndices IndexMatrix OracleJump
noncomputable section
variable {X : Type*}

def haltingSearch (Y : Oracle) (v : ℕ) : Part ℕ :=
  Nat.rfind (fun z => Part.some (run Y (machine (Nat.unpair v).1) (Nat.unpair v).2 z).isSome)

end
end TuringRigidity.UniformPrograms

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

def inductiveSetFormula (w : ℕ) : Formula :=
  .conj (.existsMem w (.empty 0))
    (.allMem w (.existsMem (w+1) (.successor 0 1)))

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
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelArithmetic SetModelIteration
universe u

def additionSystemFormula (w d A : ℕ) : Formula :=
  .conj (.functionGraph A d w)
    (.conj (.existsMem w (.conj (.empty 0)
      (.allMem (w+1) (tripleFormula 0 1 0 (A+2) (d+2)))))
      (.allMem w (.allMem (w+1) (.allMem (w+2)
        (.imp (tripleFormula 2 1 0 (A+3) (d+3))
          (.allMem (w+3) (.allMem (w+4)
            (.imp (.successor 1 3) (.imp (.successor 0 2)
              (tripleFormula 4 1 0 (A+5) (d+5)))))))))))

end TuringRigidity.RelativeConstructible

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

def productLessFormula (a b x y : ℕ) : Formula :=
  .existsMem b (.existsMem (a+1) (.existsMem (b+2) (.existsMem (a+3)
    (.conj (.orderedPair (x+4) 3 2) (.conj (.orderedPair (y+4) 1 0)
      (.disj (.member 3 1) (.conj (.equal 3 1) (.member 2 0))))))))

def productRelationFormula : Formula :=
  .existsMem 1 (.existsMem 2 (.conj (.orderedPair 2 1 0)
    (productLessFormula 4 5 1 0)))

end TuringRigidity.OrdinalArithmetic

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

def productDomainMatrix (d a b : ℕ) : Formula :=
  .conj (.allMem d (.existsMem (b+1) (.existsMem (a+2) (.orderedPair 2 1 0))))
    (.allMem b (.allMem (a+1) (.pairMem 1 0 (d+2))))

def productRelationMatrix (r d a b : ℕ) : Formula :=
  .conj (.allMem r (.existsMem (d+1) (.existsMem (d+2)
    (.conj (.orderedPair 2 1 0) (productLessFormula (a+3) (b+3) 1 0)))))
    (.allMem d (.allMem (d+1) (.imp (productLessFormula (a+2) (b+2) 1 0)
      (.pairMem 1 0 (r+2)))))

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

def omegaStageMatrix (s f r x A : ℕ) : Formula :=
  .conj (.subset s A)
    (.conj (.allMem A (.disj (.member 0 (s+1))
      (.existsMem (x+1) (.existsMem (r+2)
        (.conj (.pairMem 1 0 (f+3)) (.member 2 0))))))
      (.allMem x (.allMem (r+1)
        (.imp (.pairMem 1 0 (f+2)) (.subset 0 (A+2))))))

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

def ordinalOneMatrix (s : ℕ) : Formula :=
  .conj (.allMem s (.empty 0)) (.existsMem s (.empty 0))

end TuringRigidity.OrdinalArithmetic

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

def taggedClause (a b t v x y : ℕ) (cmp : Bool) : Formula :=
  .existsMem a (.existsMem (b+1)
    (.conj (.orderedPair (x+2) (t+2) 1)
      (.conj (.orderedPair (y+2) (v+2) 0)
        (if cmp then .member 1 0 else .equal 0 0))))

def sumLessFormula (a b z o x y : ℕ) : Formula :=
  .disj (taggedClause a a z z x y true)
    (.disj (taggedClause a b z o x y false) (taggedClause b b o o x y true))

def sumRelationFormula : Formula :=
  .existsMem 1 (.existsMem 2 (.conj (.orderedPair 2 1 0)
    (sumLessFormula 4 5 6 7 1 0)))

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

def nodeMember (a t x : ℕ) : Formula :=
  .existsMem a (.orderedPair (x+1) (t+1) 0)

def sumDomainMatrix (d a b z o : ℕ) : Formula :=
  .conj (.allMem d (.disj (nodeMember (a+1) (z+1) 0) (nodeMember (b+1) (o+1) 0)))
    (.conj (.allMem a (.existsMem (d+1) (.orderedPair 0 (z+2) 1)))
      (.allMem b (.existsMem (d+1) (.orderedPair 0 (o+2) 1))))

def sumRelationMatrix (r d a b z o : ℕ) : Formula :=
  .conj (.allMem r (.existsMem (d+1) (.existsMem (d+2)
    (.conj (.orderedPair 2 1 0) (sumLessFormula (a+3) (b+3) (z+3) (o+3) 1 0)))))
    (.allMem d (.allMem (d+1) (.imp (sumLessFormula (a+2) (b+2) (z+2) (o+2) 1 0)
      (.pairMem 1 0 (r+2)))))

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelColumns
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelSequences
open EncodedForcing
universe u
noncomputable section

def columnFormula (n b a p w d : ℕ) : Formula :=
  .allMem w (.allMem (w+1) (.allMem (d+2)
    (.imp (.conj (.orderedPair 0 (n+3) 2) (.pairMem 0 1 (p+3)))
      (.iff (.member 2 (b+3)) (.member 1 (a+3))))))

def columnsFormula : Formula :=
  .existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0) (columnFormula 1 0 5 6 3 7)))

end
end TuringRigidity.SetModelColumns

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelGraphImage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelColumns
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelSequences
open EncodedForcing
universe u
noncomputable section

def graphImageFormula : Formula :=
  .existsMem 1 (.existsMem 2 (.existsMem 4 (.existsMem 5 (.existsMem 10 (.existsMem 7
    (.conj (.orderedPair 6 5 4) (.conj (.pairMem 3 5 9) (.conj (.pairMem 2 4 9)
      (.conj (.orderedPair 1 3 2) (.conj (.pairMem 1 0 11) (.member 0 10)))))))))))

end
end TuringRigidity.SetModelColumns

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelCountability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelCountability
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions
open BoundedDefinability SetModelSyntax SetDegreeDecoding SetModelSequences
open PersistentRestrictions PersistentPresentation EncodedForcing
universe u
noncomputable section

def InternalChoice (M : ZFSet.{u}) : Prop :=
  ∀ a ∈ M, (∀ x ∈ M, x ∈ a → ∃ y ∈ M, y ∈ x) →
    ∃ f ∈ M, (choiceFormula 0 1 2).Realize M
      (cons f (cons a (fun _ => ZFSet.sUnion a)))

end
end TuringRigidity.SetModelCountability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelPresentedCountability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelCountability
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelArithmetic
open SetPresentationDecoding SetDegreeDecoding SetModelSequences SetModelColumns SetModelSyntax
open PersistentRestrictions PersistentPresentation EncodedForcing
universe u
noncomputable section
variable {M : ZFSet.{u}}

def degreeSequenceFormula : Formula :=
  .existsMem 1 (.existsMem 3 (.existsMem 6
    (.conj (.orderedPair 3 2 0) (.conj (.pairMem 2 1 6) (classFormula 0 1 5 8)))))

end
end TuringRigidity.SetModelCountability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelGraphPresentation
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelSatisfaction
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax
open SetDegreeDecoding PersistentRestrictions PersistentPresentation PersistentCountability
open SetModelSequences SetModelColumns SetModelArithmetic EncodedForcing
universe u
noncomputable section

def graphPresentationFormula : Formula :=
  .existsMem 1 (.existsMem 2 (.existsMem 5 (.existsMem 6 (.existsMem 8 (.existsMem 9 (.existsMem 13
    (.conj (.orderedPair 0 6 5) (.conj (.pairMem 0 7 13)
      (.conj (.pairMem 6 4 9) (.conj (.pairMem 5 3 9)
        (.conj (.member 4 2) (.conj (.member 3 1) (.pairMem 2 1 12)))))))))))))

def graphPresentationEnv (I : CountableIdeal) (A : Oracle) (ρ : I ≃o I) : ℕ → ZFSet.{u} :=
  cons ZFSet.omega (cons (sequenceSet (columns A)) (cons (columnRange A)
    (cons (idealSet I) (cons (automorphismSet ρ) (cons pairingSet (fun _ => pairNumbers))))))

end
end TuringRigidity.SetModelSatisfaction

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
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax
open SetDegreeDecoding PersistentRestrictions SetModelCountability ArithmeticTree
universe u
noncomputable section

def InternalFormula.rename : InternalFormula → (ℕ → ℕ) → InternalFormula
  | .bounded p, v => .bounded (p.rename v)
  | .conj p q, v => .conj (p.rename v) (q.rename v)
  | .neg p, v => .neg (p.rename v)
  | .existsSet p, v => .existsSet (p.rename (liftMap v))

def setMovedFormula (f i : ℕ) : Formula :=
  .existsMem i (.existsMem (i+1) (.conj (.pairMem 1 0 (f+2)) (.neg (.equal 1 0))))

@[simp] theorem eval_setMovedFormula (f i : ℕ) (e : ℕ → ZFSet.{u}) :
    (setMovedFormula f i).Eval e ↔ SetMoved (e f) (e i) := by
  simp only [setMovedFormula,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,SetMoved]

def nonidentityFormula : InternalFormula :=
  .existsSet (.conj (.bounded (actionFormula 0 3 2))
    (.conj (.bounded (setMovedFormula 0 3)) (persistenceFormula.rename nativeSlots)))

end
end TuringRigidity.SetModelSatisfaction

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
open Set CountableForcing RegularCompletion
universe u
variable {P : Type u} [Preorder P]

def value (N : ℕ → Set P) (G : GenericFilter P) : Set ℕ :=
  {n | ∃ p ∈ G.carrier, p ∈ N n}

end TuringRigidity.RealGeneratedPart

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

def squareFormula (w d : ℕ) : Formula :=
  .conj (.allMem d (.existsMem (w+1) (.existsMem (w+2) (.orderedPair 2 1 0))))
    (.allMem w (.allMem (w+1) (.existsMem (d+2) (.orderedPair 0 2 1))))

end TuringRigidity.RelativeConstructible

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

def codeFormula (c U : ℕ) : Formula :=
  .conj (.subset U c) (.allMem c (.iff (.member 0 (U+1))
    (.allMem (c+1) (.imp (.subset 1 0) (.existsMem (U+2) (.subset 1 0))))))

end TuringRigidity.InternalRegularAlgebra

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalRealQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalRealQuotient
open Set CountableForcing TransitiveNameModel BoundedSetTheory RecursiveNames
open RegularCompletion
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

def tags (c : ZFSet.{0}) (E : ℕ → ZFSet.{0}) : ℕ → Set (Conditions c) :=
  fun n => {p | label c p ∈ E n}

end TuringRigidity.InternalRealQuotient

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
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

def bitFormula (c E V : ℕ) : Formula :=
  .conj (.subset V c) (.allMem c (.iff (.member 0 (V+1))
    (.allMem (c+1) (.imp (.subset 1 0)
      (.existsMem (c+2) (.conj (.subset 1 0)
        (.existsMem (E+3) (.subset 0 1))))))))

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
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

def Hit {c : ZFSet.{0}} (G : GenericFilter (Conditions c)) (U : ZFSet.{0}) : Prop :=
  ∃ p ∈ G.carrier, label c p ∈ U

end TuringRigidity.InternalBooleanGeneric

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
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalBooleanProjection InternalBooleanDense InternalProjectedGeneric InternalBooleanGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

def coverFormula (c A p V : ℕ) : Formula :=
  .conj (.subset V c) (.allMem c (.iff (.member 0 (V+1))
    (.allMem (A+1) (.imp (.member (p+2) 0) (.member 1 0)))))

end TuringRigidity.InternalQuotientConditions

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

def ontoMatrix (f ω A : ℕ) : Formula :=
  .conj (.functionGraph f ω A) (.allMem A (.existsMem (ω+1) (.pairMem 0 1 (f+2))))

end TuringRigidity.InternalUncountableSentence

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

def partitionFormula (U V W : ℕ) : Formula :=
  .conj (.subset V U) (.conj (.subset W U)
    (.conj (.neg (.empty V)) (.conj (.neg (.empty W))
      (.conj (.allMem V (.neg (.member 0 (W+1))))
        (.allMem U (.existsMem (U+1) (.conj (.subset 1 0)
          (.disj (.member 0 (V+2)) (.member 0 (W+2))))))))))

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

def decidesFormula (c D V : ℕ) : Formula :=
  .disj (.subset V D) (.allMem V (.conj (.member 0 (c+1))
    (.allMem (D+1) (.neg (.subset 1 0)))))

def refiningFormula (c U D V W : ℕ) : Formula :=
  .conj (partitionFormula U V W) (.conj (decidesFormula c D V) (decidesFormula c D W))

end TuringRigidity.RegularDecisionPartition

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
open TransitiveNameModel BoundedSetTheory InternalProjectedGeneric

def stepFormula (B P X Y T E w b1 i U V : ℕ) : Formula :=
  .existsMem B (.existsMem (P+1) (.existsMem (P+2)
    (.existsMem (X+3) (.existsMem (Y+4)
      (.conj (.orderedPair 1 (U+5) 4) (.conj (.orderedPair 0 3 2)
        (.conj (.pairMem (i+5) 4 (E+5)) (.conj (.pairMem 1 0 (T+5))
          (.disj (.conj (.pairMem (i+5) (b1+5) (w+5)) (.equal (V+5) 2))
            (.conj (.neg (.pairMem (i+5) (b1+5) (w+5))) (.equal (V+5) 3)))))))))))

end TuringRigidity.RegularTreeRun

end OAI
end


