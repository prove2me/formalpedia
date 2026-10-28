-- Prove2me | Definitions.Def_OAIQ064A002
-- name    : OAIQ064A002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T00:29:57.927071+00:00
-- url     : https://prove2.me/theorems/5fe4e9b7-828d-4bed-8417-5617507eeb77
-- title:
--   Definitions bundle OAIQ064A002 of the split of OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 235 declarations of OpenAI's Lean: 117 definitions, 4 inductive types or structures, 2 instances and 112 theorems. The definitions and types are `OAI.TuringRigidity.AtomicForcing.Generic`, `OAI.TuringRigidity.AtomicForcing.powerName`, `OAI.TuringRigidity.AutomorphismName.mapFilter`, `OAI.TuringRigidity.BinarySeries.Mixed`, `OAI.TuringRigidity.BinarySeries.approxDecision`, `OAI.TuringRigidity.BinarySeries.approxTrial`, `OAI.TuringRigidity.BinarySeries.bit`, `OAI.TuringRigidity.BinarySeries.digits`, `OAI.TuringRigidity.BinarySeries.fracLeft`, `OAI.TuringRigidity.BinarySeries.fracRight`, `OAI.TuringRigidity.BinarySeries.numeral`, `OAI.TuringRigidity.BinarySeries.recoverDecision`, `OAI.TuringRigidity.BinarySeries.recoverGuard`, `OAI.TuringRigidity.BinarySeries.recoverTrial`, `OAI.TuringRigidity.BinarySeries.value`, `OAI.TuringRigidity.BooleanExpressionCertificate.Certificate`, `OAI.TuringRigidity.BooleanExpressionCertificate.Step`, `OAI.TuringRigidity.BooleanExpressionCertificate.Witness`, `OAI.TuringRigidity.BooleanExpressionCertificate.certificateFormula`, `OAI.TuringRigidity.BooleanExpressionCertificate.certified`, `OAI.TuringRigidity.BooleanExpressionCertificate.goodGraphs`, `OAI.TuringRigidity.BooleanExpressionCertificate.parameters`, `OAI.TuringRigidity.BooleanExpressionCertificate.stepFormula`, `OAI.TuringRigidity.BooleanExpressionCertificate.witnessBody`, `OAI.TuringRigidity.BooleanExpressionCertificate.witnessFormula`, `OAI.TuringRigidity.BooleanExpressionTruth.Evaluated`, `OAI.TuringRigidity.BooleanExpressionTruth.GoodTruth`, `OAI.TuringRigidity.BooleanExpressionTruth.body`, `OAI.TuringRigidity.BooleanExpressionTruth.evaluatedFormula`, `OAI.TuringRigidity.BooleanExpressionTruth.evaluationBody`, `OAI.TuringRigidity.BooleanExpressionTruth.evaluationParameters`, `OAI.TuringRigidity.BooleanExpressionTruth.formula`, `OAI.TuringRigidity.BooleanExpressionTruth.goodTruthFormula`, `OAI.TuringRigidity.BooleanExpressionTruth.parameters`, `OAI.TuringRigidity.BooleanExpressionTruth.seedTruth`, `OAI.TuringRigidity.BooleanExpressionTruth.step`, `OAI.TuringRigidity.BooleanExpressionTruth.truthAt`, `OAI.TuringRigidity.BooleanExpressionTruth.value`, `OAI.TuringRigidity.BooleanExpressionTruth.valueSet`, `OAI.TuringRigidity.BorelGeneric.Meets` and 81 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DegreeRigidity_CohenForcing_AtomicForcing`, `DegreeRigidity_CohenForcing_BoundedForcing`, `DegreeRigidity_CohenForcing_BoundedForcingCode`, `DegreeRigidity_CohenForcing_ForcingWitnessCollection`, `DegreeRigidity_CohenForcing_SigmaForcing`, `DegreeRigidity_Computability_BinaryCut`, `DegreeRigidity_Computability_BinaryMachine`, `DegreeRigidity_Computability_BinaryRecovery`, `DegreeRigidity_Computability_BinarySeries`, `DegreeRigidity_Computability_Cuts`, `DegreeRigidity_Computability_RationalCoding`, `DegreeRigidity_Computability_RationalCut`, `DegreeRigidity_Constructibility_UniformSigmaDefinability`, `DegreeRigidity_Effective_CodingBounds`, `DegreeRigidity_Representation_Assembly`, `DegreeRigidity_Representation_AutomorphismName`, `DegreeRigidity_Representation_BorelGeneric`, `DegreeRigidity_Representation_HomogeneousDegreeExtension`, `DegreeRigidity_Representation_SourceTheory`, `DegreeRigidity_SetModels_ElementaryLanguage`, `DegreeRigidity_SetModels_ExtensionBasicAxioms`, `DegreeRigidity_SetModels_ExtensionPowerSet`, `DegreeRigidity_SetModels_InternalAtomicTruth`, `DegreeRigidity_SetModels_InternalBooleanSyntax`, `DegreeRigidity_SetModels_InternalBoundedTruth`, `DegreeRigidity_SetModels_InternalContainer`, `DegreeRigidity_SetModels_InternalFixedPoint`, `DegreeRigidity_SetModels_InternalHull`, `DegreeRigidity_SetModels_InternalInfinity`, `DegreeRigidity_SetModels_InternalNameValidity`, `DegreeRigidity_SetModels_IntersectionName`, `DegreeRigidity_SetModels_ModelDegreeCodes`, `DegreeRigidity_SetModels_ModelDegreeOrder`, `DegreeRigidity_SetModels_ModelDegreeUniverse`, `DegreeRigidity_SetModels_ModelProducts`, `DegreeRigidity_SetModels_ModelReals`, `DegreeRigidity_SetModels_NameEncoding`, `DegreeRigidity_SetModels_NameExtension`, `DegreeRigidity_SetModels_NameSupport`, `DegreeRigidity_SetModels_NameUnionCode`, `DegreeRigidity_SetModels_NameValidity`, `DegreeRigidity_SetModels_NameValueCover`, `DegreeRigidity_SetModels_RecursiveNames`, `DegreeRigidity_SetModels_RestrictedName`, `DegreeRigidity_SetModels_TransitiveNameModel`, `DegreeRigidity_SetModels_UnionIteration`, `DegreeRigidity_Syntax_AtomicCertificate`, `DegreeRigidity_Syntax_AtomicDecisionFormula`, `DegreeRigidity_Syntax_AtomicFormula`, `DegreeRigidity_Syntax_AtomicGraph`, `DegreeRigidity_Syntax_AtomicGraphCorrect`, `DegreeRigidity_Syntax_AtomicRequirements`, `DegreeRigidity_Syntax_AtomicTruth`, `DegreeRigidity_Syntax_BooleanEvaluationWitness`, `DegreeRigidity_Syntax_BooleanExpressionAssembly`, `DegreeRigidity_Syntax_BooleanExpressionCertificate`, `DegreeRigidity_Syntax_BooleanExpressionSyntax`, `DegreeRigidity_Syntax_BooleanExpressionTruth`, `DegreeRigidity_Syntax_BooleanTruthReading`, `DegreeRigidity_Syntax_BoundedAutomorphismOutput`, `DegreeRigidity_Syntax_BoundedCertificate`, `DegreeRigidity_Syntax_BoundedDecoding`, `DegreeRigidity_Syntax_BoundedDefinability`, `DegreeRigidity_Syntax_BoundedRelations`, `DegreeRigidity_Syntax_BoundedSetTheory`, `DegreeRigidity_Syntax_BoundedSupport`, `DegreeRigidity_Syntax_FiniteTerm`, `DegreeRigidity_Syntax_LevySigmaNormalization`, `DegreeRigidity_Syntax_SigmaDefinability`, `DegreeRigidity_Syntax_SigmaInterpretation`, `DegreeRigidity_Syntax_SigmaParameterized`, `DegreeRigidity_Syntax_SigmaSyntax`.
--
--   **Imports.** It imports the published bundle `Def_DegreeRigidity`; the bundles `OAIQ064A000` and `OAIQ064A001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ064A005`, `OAIQ064A006` and `OAIQ064A007`; the statements `OAI.TuringRigidity.ArithmeticTree.native_nonidentity_absolute`, `OAI.TuringRigidity.ArithmeticTree.native_persistence_absolute`, `OAI.TuringRigidity.ArithmeticTree.setGenericallyPersistent_iff`, `OAI.TuringRigidity.ArithmeticTree.sourceT_piOneOne_matrix`, `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.real_collapse_reconstructs`, `OAI.TuringRigidity.CohenAbsorptionGeneric.product_generic_absorption`, `OAI.TuringRigidity.CohenManyAbsorption.same_generics_absorption`, `OAI.TuringRigidity.CohenRemainderTransport.transport_to_remainder`, `OAI.TuringRigidity.EnumerationConstruction.enumeration_exists`, `OAI.TuringRigidity.LocalUnary.localized_copy`, `OAI.TuringRigidity.SetModelPersistence.persistent_decoding` and `OAI.TuringRigidity.main_of_representation`.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A000
import Definitions.Def_OAIQ064A001

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

theorem mem_val (G : Set P) (ι : Type u) (child : ι → Name P) (tag : ι → P)
    (x : ZFSet.{u}) : x ∈ val G (.mk ι child tag) ↔
      ∃ i, tag i ∈ G ∧ val G (child i) = x := by
  simp only [val, ZFSet.mem_range]
  exact ⟨fun ⟨i,h⟩ => ⟨i.val,i.property,h⟩, fun ⟨i,hi,h⟩ => ⟨⟨i,hi⟩,h⟩⟩

end Name
end TuringRigidity.RecursiveNames

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_NameEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RecursiveNames
open Set
universe u
variable {P : Type u}

theorem Name.val_eq_of_encode_eq (label : P → ZFSet.{u})
    (hl : Function.Injective label) (G : Set P) (τ σ : Name P)
    (he : encode label τ = encode label σ) : val G τ = val G σ := by
  induction τ generalizing σ with
  | mk ι child tag ih =>
    cases σ with
    | mk κ other otag =>
      apply ZFSet.ext
      intro x
      rw [mem_val,mem_val]
      constructor
      · rintro ⟨i,hi,hx⟩
        have hm : ZFSet.pair (encode label (child i)) (label (tag i)) ∈
            encode label (.mk ι child tag) := ZFSet.mem_range_self i
        rw [he] at hm
        obtain ⟨j,hj⟩ := ZFSet.mem_range.mp hm
        obtain ⟨hc,ht⟩ := ZFSet.pair_inj.mp hj
        refine ⟨j,by simpa only [hl ht] using hi,?_⟩
        exact (ih i (other j) hc.symm).symm.trans hx
      · rintro ⟨j,hj,hx⟩
        have hm : ZFSet.pair (encode label (other j)) (label (otag j)) ∈
            encode label (.mk κ other otag) := ZFSet.mem_range_self j
        rw [←he] at hm
        obtain ⟨i,hi⟩ := ZFSet.mem_range.mp hm
        obtain ⟨hc,ht⟩ := ZFSet.pair_inj.mp hi
        refine ⟨i,by simpa only [hl ht] using hj,?_⟩
        exact (ih i (other j) hc).trans hx

end TuringRigidity.RecursiveNames

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_AtomicForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames CountableForcing
universe u
variable {P : Type u} [Preorder P]

theorem eq_mono (a b : Name P) {p q : P} (hqp : q ≤ p)
    (h : EqForces a b p) : EqForces a b q := by
  cases a with
  | mk ι a s =>
    cases b with
    | mk κ b t =>
      exact ⟨fun i r hr hs => h.1 i r (hr.trans hqp) hs,
        fun j r hr ht => h.2 j r (hr.trans hqp) ht⟩

theorem mem_mono (a b : Name P) {p q : P} (hqp : q ≤ p)
    (h : MemForces a b p) : MemForces a b q := by
  cases b with
  | mk κ b t => exact fun r hr => h r (hr.trans hqp)

theorem eq_symm (a b : Name P) (p : P) : EqForces a b p → EqForces b a p := by
  induction a generalizing b p with
  | mk ι a s ih =>
    cases b with
    | mk κ b t =>
      intro h
      constructor
      · intro j q hq ht
        obtain ⟨r,hr,i,hi,he⟩ := h.2 j q hq ht
        exact ⟨r,hr,i,hi,ih i (b j) r he⟩
      · intro i q hq hs
        obtain ⟨r,hr,j,hj,he⟩ := h.1 i q hq hs
        exact ⟨r,hr,j,hj,ih i (b j) r he⟩

end TuringRigidity.AtomicForcing

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

def Name.Child : Name P → Name P → Prop
  | σ, .mk _ child _ => ∃ i, child i = σ

def extension (M : Set (Name P)) (G : Set P) : Set ZFSet.{u} := Name.val G '' M

def ChildClosed (M : Set (Name P)) : Prop :=
  ∀ τ ∈ M, ∀ σ, Name.Child σ τ → σ ∈ M

theorem extension_transitive (M : Set (Name P)) (hM : ChildClosed M) (G : Set P) :
    ∀ x ∈ extension M G, ∀ y ∈ x, y ∈ extension M G := by
  rintro x ⟨τ,hτ,rfl⟩ y hy
  cases τ with
  | mk ι child tag =>
    obtain ⟨i,_,hi⟩ := (Name.mem_val G ι child tag y).mp hy
    exact ⟨child i,hM _ hτ _ ⟨i,rfl⟩,hi⟩

namespace Name

def arity : Name P → Type u
  | .mk ι _ _ => ι

def child : (τ : Name P) → arity τ → Name P
  | .mk _ c _, i => c i

def tag : (τ : Name P) → arity τ → P
  | .mk _ _ t, i => t i

theorem mem_val_children (G : Set P) (τ : Name P) (x : ZFSet.{u}) :
    x ∈ val G τ ↔ ∃ i, tag τ i ∈ G ∧ val G (child τ i) = x := by
  cases τ
  exact mem_val _ _ _ _ _

end Name

end TuringRigidity.RecursiveNames

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_AtomicRequirements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames CountableForcing
universe u
variable {P : Type u} [Preorder P]

theorem witness_mono (a b : Name P) {p q : P} (hq : q ≤ p)
    (h : Witness a b p) : Witness a b q := by
  cases b with
  | mk κ b t =>
    obtain ⟨j,hj,he⟩ := h
    exact ⟨j,hq.trans hj,eq_mono _ _ hq he⟩

theorem witness_mem (a b : Name P) (p : P) (h : Witness a b p) : MemForces a b p := by
  cases b with
  | mk κ b t =>
    intro q hq
    exact ⟨q,le_rfl,witness_mono _ _ hq h⟩

theorem memTest_dense (a b : Name P) : Dense (MemTest a b) := by
  classical
  intro p
  by_cases h : ∃ q, q ≤ p ∧ Witness a b q
  · obtain ⟨q,hq,hw⟩ := h
    exact ⟨q,hq,Or.inl hw⟩
  · refine ⟨p,le_rfl,Or.inr ?_⟩
    intro q hq hm
    cases b with
    | mk κ b t =>
      obtain ⟨r,hr,hw⟩ := hm q le_rfl
      exact h ⟨r,hr.trans hq,hw⟩

theorem eqTest_dense (a b : Name P) : Dense (EqTest a b) := by
  classical
  cases a with
  | mk ι a s =>
    cases b with
    | mk κ b t =>
      intro p
      by_cases he : EqForces (.mk ι a s) (.mk κ b t) p
      · exact ⟨p,le_rfl,Or.inl he⟩
      · change ¬ ((∀ i, Below p (s i) _) ∧ (∀ j, Below p (t j) _)) at he
        simp only [not_and_or, not_forall, Below] at he
        rcases he with ⟨i,q,hq⟩ | ⟨j,q,hq⟩
        · obtain ⟨hqp,hqs,hn⟩ := hq
          refine ⟨q,hqp,Or.inr (Or.inl ⟨i,hqs,?_⟩)⟩
          intro r hr hm
          obtain ⟨w,hw,k,hk,hf⟩ := hm r le_rfl
          exact hn ⟨w,hw.trans hr,k,hk,hf⟩
        · obtain ⟨hqp,hqt,hn⟩ := hq
          refine ⟨q,hqp,Or.inr (Or.inr ⟨j,hqt,?_⟩)⟩
          intro r hr hm
          obtain ⟨w,hw,i,hi,hf⟩ := hm r le_rfl
          exact hn ⟨w,hw.trans hr,i,hi,eq_symm _ _ _ hf⟩

structure Generic (N : Set (Name P)) (G : GenericFilter P) : Prop where
  memTest : ∀ a ∈ N, ∀ b ∈ N, ∃ p ∈ G.carrier, p ∈ MemTest a b
  eqTest : ∀ a ∈ N, ∀ b ∈ N, ∃ p ∈ G.carrier, p ∈ EqTest a b

theorem generic_witness {N : Set (Name P)} {G : GenericFilter P}
    (hG : Generic N G) {a b : Name P} (ha : a ∈ N) (hb : b ∈ N)
    {p : P} (hp : p ∈ G.carrier) (hm : MemForces a b p) :
    ∃ q ∈ G.carrier, Witness a b q := by
  obtain ⟨q,hq,hw | hn⟩ := hG.memTest a ha b hb
  · exact ⟨q,hq,hw⟩
  · obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
    exact False.elim (hn r hrq (mem_mono _ _ hrp hm))

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_AtomicTruth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames CountableForcing
universe u
variable {P : Type u} [Preorder P]

theorem mem_truth_step {N : Set (Name P)} {G : GenericFilter P}
    (hG : Generic N G) (a : Name P) (κ : Type u) (b : κ → Name P) (t : κ → P)
    (ha : a ∈ N) (hb : Name.mk κ b t ∈ N)
    (he : ∀ j, Name.val G.carrier a = Name.val G.carrier (b j) ↔
      ∃ p ∈ G.carrier, EqForces a (b j) p) :
    Name.val G.carrier a ∈ Name.val G.carrier (.mk κ b t) ↔
      ∃ p ∈ G.carrier, MemForces a (.mk κ b t) p := by
  constructor
  · intro hm
    obtain ⟨j,hj,hv⟩ := (Name.mem_val _ _ _ _ _).mp hm
    obtain ⟨p,hp,hf⟩ := (he j).mp hv.symm
    obtain ⟨r,hr,hrp,hrj⟩ := G.directed hp hj
    exact ⟨r,hr,witness_mem _ _ _ ⟨j,hrj,eq_mono _ _ hrp hf⟩⟩
  · rintro ⟨p,hp,hm⟩
    obtain ⟨q,hq,j,hj,hf⟩ := generic_witness hG ha hb hp hm
    exact (Name.mem_val _ _ _ _ _).mpr ⟨j,G.upper hj hq,((he j).mpr ⟨q,hq,hf⟩).symm⟩

theorem eq_truth {N : Set (Name P)} (hN : ChildClosed N) (G : GenericFilter P)
    (hG : Generic N G) (a b : Name P) (ha : a ∈ N) (hb : b ∈ N) :
    Name.val G.carrier a = Name.val G.carrier b ↔
      ∃ p ∈ G.carrier, EqForces a b p := by
  induction a generalizing b with
  | mk ι a s ih =>
    cases b with
    | mk κ b t =>
      have ha' (i) : a i ∈ N := hN _ ha _ ⟨i,rfl⟩
      have hb' (j) : b j ∈ N := hN _ hb _ ⟨j,rfl⟩
      have left (i) : Name.val G.carrier (a i) ∈ Name.val G.carrier (.mk κ b t) ↔
          ∃ p ∈ G.carrier, MemForces (a i) (.mk κ b t) p :=
        mem_truth_step hG (a i) κ b t (ha' i) hb (fun j => ih i (b j) (ha' i) (hb' j))
      have right (j) : Name.val G.carrier (b j) ∈ Name.val G.carrier (.mk ι a s) ↔
          ∃ p ∈ G.carrier, MemForces (b j) (.mk ι a s) p := by
        apply mem_truth_step hG (b j) ι a s (hb' j) ha
        intro i
        constructor
        · intro he
          obtain ⟨p,hp,hf⟩ := (ih i (b j) (ha' i) (hb' j)).mp he.symm
          exact ⟨p,hp,eq_symm _ _ _ hf⟩
        · rintro ⟨p,hp,hf⟩
          exact ((ih i (b j) (ha' i) (hb' j)).mpr ⟨p,hp,eq_symm _ _ _ hf⟩).symm
      constructor
      · intro hv
        obtain ⟨p,hp,he | hn⟩ := hG.eqTest _ ha _ hb
        · exact ⟨p,hp,he⟩
        · rcases hn with ⟨i,hi,hn⟩ | ⟨j,hj,hn⟩
          · have hm : Name.val G.carrier (a i) ∈ Name.val G.carrier (.mk κ b t) := by
              rw [←hv]
              exact (Name.mem_val _ _ _ _ _).mpr ⟨i,G.upper hi hp,rfl⟩
            obtain ⟨q,hq,hf⟩ := (left i).mp hm
            obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
            exact False.elim (hn r hrp (mem_mono _ _ hrq hf))
          · have hm : Name.val G.carrier (b j) ∈ Name.val G.carrier (.mk ι a s) := by
              rw [hv]
              exact (Name.mem_val _ _ _ _ _).mpr ⟨j,G.upper hj hp,rfl⟩
            obtain ⟨q,hq,hf⟩ := (right j).mp hm
            obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
            exact False.elim (hn r hrp (mem_mono _ _ hrq hf))
      · rintro ⟨p,hp,he⟩
        apply ZFSet.ext
        intro x
        constructor
        · intro hx
          obtain ⟨i,hi,rfl⟩ := (Name.mem_val _ _ _ _ _).mp hx
          obtain ⟨r,hr,hrp,hri⟩ := G.directed hp hi
          exact (left i).mpr ⟨r,hr,fun q hq => he.1 i q (hq.trans hrp) (hq.trans hri)⟩
        · intro hx
          obtain ⟨j,hj,rfl⟩ := (Name.mem_val _ _ _ _ _).mp hx
          obtain ⟨r,hr,hrp,hrj⟩ := G.directed hp hj
          apply (right j).mpr
          refine ⟨r,hr,?_⟩
          intro q hq
          obtain ⟨w,hw,i,hi,hf⟩ := he.2 j q (hq.trans hrp) (hq.trans hrj)
          exact ⟨w,hw,i,hi,eq_symm _ _ _ hf⟩

theorem mem_truth {N : Set (Name P)} (hN : ChildClosed N) (G : GenericFilter P)
    (hG : Generic N G) (a b : Name P) (ha : a ∈ N) (hb : b ∈ N) :
    Name.val G.carrier a ∈ Name.val G.carrier b ↔
      ∃ p ∈ G.carrier, MemForces a b p := by
  cases b with
  | mk κ b t =>
    exact mem_truth_step hG a κ b t ha hb
      (fun j => eq_truth hN G hG a (b j) ha (hN _ hb _ ⟨j,rfl⟩))

end TuringRigidity.AtomicForcing

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

theorem label_mem (p : ZFSet.{u}) (q : Conditions p) : label p q ∈ p :=
  ((equivShrink p).symm q).property

def names (M p : ZFSet.{u}) : Set (Name (Conditions p)) :=
  {τ | Name.encode (label p) τ ∈ M}

def genericExtension (M p : ZFSet.{u}) (G : Set (Conditions p)) : Set ZFSet.{u} :=
  extension (names M p) G

theorem names_childClosed (M p : ZFSet.{u}) (hM : Transitive M) :
    ChildClosed (names M p) := by
  intro τ hτ σ hσ
  cases τ with
  | mk ι child tag =>
    obtain ⟨i,rfl⟩ := hσ
    change Name.encode (label p) (.mk ι child tag) ∈ M at hτ
    have hp : ZFSet.pair (Name.encode (label p) (child i)) (label p (tag i)) ∈ M :=
      hM (Name.encode (label p) (.mk ι child tag)) hτ _ (ZFSet.mem_range_self i)
    have hs : ({Name.encode (label p) (child i)} : ZFSet.{u}) ∈ M :=
      hM _ hp _ (ZFSet.mem_pair.mpr (Or.inl rfl))
    exact hM _ hs _ (ZFSet.mem_singleton.mpr rfl)

theorem genericExtension_transitive (M p : ZFSet.{u}) (hM : Transitive M)
    (G : Set (Conditions p)) :
    ∀ x ∈ genericExtension M p G, ∀ y ∈ x, y ∈ genericExtension M p G :=
  extension_transitive _ (names_childClosed M p hM) G

theorem valueOnCode_encode (p : ZFSet.{u}) (G : Set (Conditions p))
    (τ : Name (Conditions p)) :
    valueOnCode p G (Name.encode (label p) τ) = Name.val G τ := by
  classical
  have h : ∃ σ : Name (Conditions p), Name.encode (label p) σ = Name.encode (label p) τ :=
    ⟨τ,rfl⟩
  rw [valueOnCode,dite_eq_left h]
  exact Name.val_eq_of_encode_eq _ (label_injective p) G _ τ h.choose_spec

theorem genericExtensionSet_coe (M p : ZFSet.{u}) (G : Set (Conditions p)) :
    (genericExtensionSet M p G : Set ZFSet.{u}) = genericExtension M p G := by
  ext x
  change x ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨⟨⟨c,hc⟩,τ,hτ⟩,hx⟩
    refine ⟨τ,?_,?_⟩
    · change Name.encode (label p) τ ∈ M
      simpa only [hτ] using hc
    · have hv := valueOnCode_encode p G τ
      rw [hτ] at hv
      exact hv.symm.trans hx
  · rintro ⟨τ,hτ,rfl⟩
    exact ⟨⟨⟨Name.encode (label p) τ,hτ⟩,τ,rfl⟩,valueOnCode_encode p G τ⟩

theorem genericExtensionSet_transitive (M p : ZFSet.{u}) (hM : Transitive M)
    (G : Set (Conditions p)) : Transitive (genericExtensionSet M p G) := by
  intro x hx y hy
  have hx' : x ∈ genericExtension M p G := by
    rw [←genericExtensionSet_coe]; exact hx
  have hy' := genericExtension_transitive M p hM G x hx' y hy
  rw [←genericExtensionSet_coe] at hy'
  exact hy'

end TuringRigidity.TransitiveNameModel

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
open TransitiveNameModel (Transitive)
universe u

theorem Formula.absolute (φ : Formula) (M : ZFSet.{u}) (hM : Transitive M)
    (env : ℕ → ZFSet.{u}) (he : ∀ i, env i ∈ M) :
    φ.Realize M env ↔ φ.Eval env := by
  induction φ generalizing env with
  | equal => rfl
  | member => rfl
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ env he) (ihψ env he)
  | neg φ ih => exact not_congr (ih env he)
  | existsMem i φ ih =>
    constructor
    · rintro ⟨x,hx,hi,hφ⟩
      exact ⟨x,hi,(ih (cons x env) (fun n => by cases n <;> simp [cons,he,hx])).mp hφ⟩
    · rintro ⟨x,hi,hφ⟩
      have hx := hM _ (he i) _ hi
      exact ⟨x,hx,hi,(ih (cons x env) (fun n => by cases n <;> simp [cons,he,hx])).mpr hφ⟩

def Separation (M : ZFSet.{u}) : Prop :=
  ∀ (φ : Formula) (env : ℕ → ZFSet.{u}), (∀ i, env i ∈ M) →
    ∀ a ∈ M, ∃ b ∈ M, ∀ x ∈ M, x ∈ b ↔ x ∈ a ∧ φ.Realize M (cons x env)

theorem pair_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    {a b : ZFSet.{u}} (ha : a ∈ M) (hb : b ∈ M) : ({a,b} : ZFSet.{u}) ∈ M := by
  obtain ⟨c,hc,hcdef⟩ := hP a ha b hb
  have hc' : c = ({a,b} : ZFSet.{u}) := by
    apply ZFSet.ext
    intro x
    constructor
    · intro hx
      exact ZFSet.mem_pair.mpr ((hcdef x (hM c hc x hx)).mp hx)
    · intro hx
      have hx' := ZFSet.mem_pair.mp hx
      have hxM : x ∈ M := hx'.elim (fun h => h ▸ ha) (fun h => h ▸ hb)
      exact (hcdef x hxM).mpr hx'
  exact hc' ▸ hc

theorem singleton_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    {a : ZFSet.{u}} (ha : a ∈ M) : ({a} : ZFSet.{u}) ∈ M := by
  simpa using pair_mem M hM hP ha ha

theorem orderedPair_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    {a b : ZFSet.{u}} (ha : a ∈ M) (hb : b ∈ M) : ZFSet.pair a b ∈ M := by
  exact pair_mem M hM hP (singleton_mem M hM hP ha) (pair_mem M hM hP ha hb)

theorem union_mem (M : ZFSet.{u}) (hM : Transitive M) (hU : Union M)
    {a : ZFSet.{u}} (ha : a ∈ M) : ZFSet.sUnion a ∈ M := by
  obtain ⟨b,hb,hbdef⟩ := hU a ha
  have he : b = ZFSet.sUnion a := by
    apply ZFSet.ext
    intro x
    constructor
    · intro hx
      obtain ⟨y,_,hy,hxy⟩ := (hbdef x (hM b hb x hx)).mp hx
      exact ZFSet.mem_sUnion.mpr ⟨y,hy,hxy⟩
    · intro hx
      obtain ⟨y,hy,hxy⟩ := ZFSet.mem_sUnion.mp hx
      have hyM := hM a ha y hy
      exact (hbdef x (hM y hyM x hxy)).mpr ⟨y,hyM,hy,hxy⟩
  exact he ▸ hb

theorem internal_power (M : ZFSet.{u}) (hM : Transitive M) (hP : PowerSet M)
    {a : ZFSet.{u}} (ha : a ∈ M) :
    ∃ b ∈ M, ∀ x, x ∈ b ↔ x ∈ M ∧ x ⊆ a := by
  obtain ⟨b,hb,hbdef⟩ := hP a ha
  refine ⟨b,hb,fun x => ?_⟩
  constructor
  · intro hx
    have hxM := hM b hb x hx
    exact ⟨hxM,fun y hy => (hbdef x hxM).mp hx y (hM x hxM y hy) hy⟩
  · rintro ⟨hxM,hsub⟩
    exact (hbdef x hxM).mpr (fun y _ hy => hsub hy)

theorem sep_mem (M : ZFSet.{u}) (hM : Transitive M) (hS : Separation M)
    (φ : Formula) (env : ℕ → ZFSet.{u}) (he : ∀ i, env i ∈ M)
    {a : ZFSet.{u}} (ha : a ∈ M) :
    ZFSet.sep (fun x => φ.Eval (cons x env)) a ∈ M := by
  obtain ⟨b,hb,hbdef⟩ := hS φ env he a ha
  have heq : b = ZFSet.sep (fun x => φ.Eval (cons x env)) a := by
    apply ZFSet.ext
    intro x
    constructor
    · intro hx
      have hxM := hM b hb x hx
      obtain ⟨hxa,hφ⟩ := (hbdef x hxM).mp hx
      refine ZFSet.mem_sep.mpr ⟨hxa,?_⟩
      exact (φ.absolute M hM _ (fun n => by cases n <;> simp [cons,he,hxM])).mp hφ
    · intro hx
      obtain ⟨hxa,hφ⟩ := ZFSet.mem_sep.mp hx
      have hxM := hM a ha x hxa
      apply (hbdef x hxM).mpr
      exact ⟨hxa,(φ.absolute M hM _ (fun n => by cases n <;> simp [cons,he,hxM])).mpr hφ⟩
  exact heq ▸ hb

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open Set TransitiveNameModel
universe u

theorem binary_union_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : Union M) {a b : ZFSet.{u}} (ha : a ∈ M) (hb : b ∈ M) :
    a ∪ b ∈ M := by
  simpa only [ZFSet.sUnion_pair] using union_mem M hM hU (pair_mem M hM hP ha hb)

theorem pair_bound (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : Union M) (hPow : PowerSet M)
    {a b : ZFSet.{u}} (ha : a ∈ M) (hb : b ∈ M) :
    ∃ c ∈ M, ∀ x ∈ a, ∀ y ∈ b, ZFSet.pair x y ∈ c := by
  obtain ⟨q,hq,hqdef⟩ := internal_power M hM hPow (binary_union_mem M hM hP hU ha hb)
  obtain ⟨r,hr,hrdef⟩ := internal_power M hM hPow hq
  refine ⟨r,hr,fun x hx y hy => ?_⟩
  have hxM := hM a ha x hx
  have hyM := hM b hb y hy
  apply (hrdef _).mpr
  refine ⟨orderedPair_mem M hM hP hxM hyM,?_⟩
  intro z hz
  change z ∈ ({({x} : ZFSet.{u}),({x,y} : ZFSet.{u})} : ZFSet.{u}) at hz
  rcases ZFSet.mem_pair.mp hz with rfl|rfl
  · apply (hqdef _).mpr
    refine ⟨singleton_mem M hM hP hxM,?_⟩
    intro t ht
    rw [ZFSet.mem_singleton] at ht
    exact ht ▸ ZFSet.mem_union.mpr (Or.inl hx)
  · apply (hqdef _).mpr
    refine ⟨pair_mem M hM hP hxM hyM,?_⟩
    intro t ht
    rcases ZFSet.mem_pair.mp ht with rfl|rfl
    · exact ZFSet.mem_union.mpr (Or.inl hx)
    · exact ZFSet.mem_union.mpr (Or.inr hy)

def productFormula : Formula := .existsMem 1 (.existsMem 3 (.orderedPair 2 1 0))

theorem eval_productFormula (z a b : ZFSet.{u}) (env : ℕ → ZFSet.{u}) :
    productFormula.Eval (cons z (cons a (cons b env))) ↔ z ∈ ZFSet.prod a b := by
  simp only [productFormula,Formula.Eval,cons_succ,cons_zero,Formula.eval_orderedPair]
  exact ZFSet.mem_prod.symm

theorem product_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : Union M) (hPow : PowerSet M) (hS : Separation M)
    {a b : ZFSet.{u}} (ha : a ∈ M) (hb : b ∈ M) : ZFSet.prod a b ∈ M := by
  obtain ⟨c,hc,hbound⟩ := pair_bound M hM hP hU hPow ha hb
  let env := cons a (cons b (fun _ => a))
  have he : ∀ i, env i ∈ M := by
    intro i
    cases i with
    | zero => exact ha
    | succ i => cases i <;> assumption
  have hs := sep_mem M hM hS productFormula env he hc
  have hprod : ZFSet.sep (fun z => productFormula.Eval (cons z env)) c = ZFSet.prod a b := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    change (z ∈ c ∧ productFormula.Eval (cons z (cons a (cons b (fun _ => a))))) ↔ _
    rw [eval_productFormula]
    constructor
    · exact And.right
    · intro hz
      obtain ⟨x,hx,y,hy,rfl⟩ := ZFSet.mem_prod.mp hz
      exact ⟨hbound x hx y hy,ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩⟩
  exact hprod ▸ hs

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BoundedRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

inductive SigmaFormula where
  | bounded (φ : Formula)
  | existsSet (φ : SigmaFormula)

def SigmaFormula.Realize (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) : SigmaFormula → Prop
  | .bounded φ => φ.Realize M e
  | .existsSet φ => ∃ x ∈ M, φ.Realize M (cons x e)

def SigmaReplacement (M : ZFSet.{u}) : Prop :=
  ∀ (φ : SigmaFormula) (e : ℕ → ZFSet.{u}), (∀ i, e i ∈ M) →
    ∀ a ∈ M,
    (∀ x ∈ a, ∃ y ∈ M, φ.Realize M (cons y (cons x e)) ∧
      ∀ z ∈ M, φ.Realize M (cons z (cons x e)) → z = y) →
    ∃ b ∈ M, ∀ y ∈ M, y ∈ b ↔ ∃ x ∈ a, φ.Realize M (cons y (cons x e))

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
open Set RecursiveNames CountableForcing AtomicForcing
open BoundedSetTheory (Formula)
universe u
variable {P : Type u} [Preorder P]

omit [Preorder P] in
theorem child_relation (a : Name P) (i : a.arity) : Name.Child (a.child i) a := by
  cases a
  exact ⟨i,rfl⟩

def Forces (e : ℕ → Name P) : Formula → P → Prop
  | .equal i j, p => EqForces (e i) (e j) p
  | .member i j, p => MemForces (e i) (e j) p
  | .conj φ ψ, p => Forces e φ p ∧ Forces e ψ p
  | .neg φ, p => ∀ q, q ≤ p → ¬ Forces e φ q
  | .existsMem i φ, p => ∃ j, p ≤ (e i).tag j ∧ Forces (push ((e i).child j) e) φ p

theorem forces_mono (φ : Formula) (e : ℕ → Name P) {p q : P} (hqp : q ≤ p)
    (h : Forces e φ p) : Forces e φ q := by
  induction φ generalizing e with
  | equal i j => exact eq_mono _ _ hqp h
  | member i j => exact mem_mono _ _ hqp h
  | conj φ ψ ihφ ihψ => exact ⟨ihφ e h.1,ihψ e h.2⟩
  | neg φ ih => exact fun r hr => h r (hr.trans hqp)
  | existsMem i φ ih =>
    obtain ⟨j,hj,hf⟩ := h
    exact ⟨j,hqp.trans hj,ih _ hf⟩

def Decision (e : ℕ → Name P) (φ : Formula) : Set P := {p | Forces e φ p ∨ Forces e (.neg φ) p}

theorem decision_dense (e : ℕ → Name P) (φ : Formula) : Dense (Decision e φ) := by
  classical
  intro p
  by_cases h : ∃ q, q ≤ p ∧ Forces e φ q
  · obtain ⟨q,hq,hf⟩ := h
    exact ⟨q,hq,Or.inl hf⟩
  · exact ⟨p,le_rfl,Or.inr (fun q hq hf => h ⟨q,hq,hf⟩)⟩

def Generic (N : Set (Name P)) (G : GenericFilter P) : Prop :=
  ∀ φ e, (∀ i, e i ∈ N) → ∃ p ∈ G.carrier, p ∈ Decision e φ

theorem truth {N : Set (Name P)} (hN : ChildClosed N) (G : GenericFilter P)
    (hA : AtomicForcing.Generic N G) (hG : Generic N G) (φ : Formula)
    (e : ℕ → Name P) (he : ∀ i, e i ∈ N) :
    φ.Eval (fun i => (e i).val G.carrier) ↔ ∃ p ∈ G.carrier, Forces e φ p := by
  induction φ generalizing e with
  | equal i j => exact eq_truth hN G hA _ _ (he i) (he j)
  | member i j => exact mem_truth hN G hA _ _ (he i) (he j)
  | conj φ ψ ihφ ihψ =>
    constructor
    · rintro ⟨hφ,hψ⟩
      obtain ⟨p,hp,hfp⟩ := (ihφ e he).mp hφ
      obtain ⟨q,hq,hfq⟩ := (ihψ e he).mp hψ
      obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
      exact ⟨r,hr,forces_mono φ e hrp hfp,forces_mono ψ e hrq hfq⟩
    · rintro ⟨p,hp,hφ,hψ⟩
      exact ⟨(ihφ e he).mpr ⟨p,hp,hφ⟩,(ihψ e he).mpr ⟨p,hp,hψ⟩⟩
  | neg φ ih =>
    constructor
    · intro hn
      obtain ⟨p,hp,hf | hf⟩ := hG φ e he
      · exact False.elim (hn ((ih e he).mpr ⟨p,hp,hf⟩))
      · exact ⟨p,hp,hf⟩
    · rintro ⟨p,hp,hn⟩ hv
      obtain ⟨q,hq,hf⟩ := (ih e he).mp hv
      obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
      exact hn r hrp (forces_mono φ e hrq hf)
  | existsMem i φ ih =>
    have hej (j) : ∀ n, push ((e i).child j) e n ∈ N := by
      intro n
      cases n with
      | zero =>
        exact hN (e i) (he i) _ (child_relation (e i) j)
      | succ n => exact he n
    have env (j) : (fun n => (push ((e i).child j) e n).val G.carrier) =
        BoundedSetTheory.cons ((e i).child j |>.val G.carrier) (fun n => (e n).val G.carrier) := by
      funext n
      cases n <;> rfl
    constructor
    · rintro ⟨x,hx,hφ⟩
      obtain ⟨j,hj,hxj⟩ := ((e i).mem_val_children G.carrier x).mp hx
      subst x
      rw [←env j] at hφ
      obtain ⟨p,hp,hf⟩ := (ih _ (hej j)).mp hφ
      obtain ⟨q,hq,hqp,hqj⟩ := G.directed hp hj
      exact ⟨q,hq,j,hqj,forces_mono φ _ hqp hf⟩
    · rintro ⟨p,hp,j,hj,hf⟩
      refine ⟨_,((e i).mem_val_children G.carrier _).mpr ⟨j,G.upper hj hp,rfl⟩,?_⟩
      rw [←env j]
      exact (ih _ (hej j)).mpr ⟨p,hp,hf⟩

end TuringRigidity.BoundedForcing

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

theorem iterUnion_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hU : BoundedSetTheory.Union M) {a : ZFSet.{u}} (ha : a ∈ M) (n : ℕ) :
    iterUnion n a ∈ M := by
  induction n with
  | zero => exact ha
  | succ n ih => exact union_mem M hM hU ih

theorem label_surjective (p : ZFSet.{u}) {x : ZFSet.{u}} (hx : x ∈ p) :
    ∃ q : Conditions p, label p q = x := by
  exact ⟨equivShrink p ⟨x,hx⟩,by simp [label]⟩

theorem pair_mem_encode {P : Type u} (l : P → ZFSet.{u}) (τ : Name P)
    (x q : ZFSet.{u}) :
    ZFSet.pair x q ∈ τ.encode l ↔
      ∃ i, (τ.child i).encode l = x ∧ l (τ.tag i) = q := by
  cases τ with
  | mk ι child tag =>
    change ZFSet.pair x q ∈ ZFSet.range _ ↔ _
    rw [ZFSet.mem_range]
    simp only [ZFSet.pair_inj,Name.child,Name.tag]
    rfl

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
open Set RecursiveNames BoundedSetTheory CountableForcing
universe u

theorem mem_extensionSet (M p : ZFSet.{u}) (G : Set (Conditions p)) (x : ZFSet.{u}) :
    x ∈ genericExtensionSet M p G ↔
      ∃ τ : Name (Conditions p), τ.encode (label p) ∈ M ∧ τ.val G = x := by
  change x ∈ (genericExtensionSet M p G : Set ZFSet.{u}) ↔ _
  rw [genericExtensionSet_coe]
  rfl

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

theorem natSet_mem_natSet (n m : ℕ) : natSet.{u} n ∈ natSet m ↔ n < m := by
  rw [mem_natSet]
  exact ⟨fun ⟨i,hi,he⟩ => natSet_injective he ▸ hi,fun h => ⟨n,h,rfl⟩⟩

theorem natSet_transitive (n : ℕ) : Transitive (natSet.{u} n) := by
  intro x hx y hy
  obtain ⟨i,hi,rfl⟩ := (mem_natSet n x).mp hx
  obtain ⟨j,hj,rfl⟩ := (mem_natSet i y).mp hy
  exact (natSet_mem_natSet j n).mpr (Nat.lt_trans hj hi)

namespace Formula

def zeroOrSuccessor (x : ℕ) : Formula :=
  disj (empty x) (.existsMem x (successor (x+1) 0))

def finiteOrdinal (x : ℕ) : Formula := .conj (transitive x)
  (.conj (allMem x (transitive 0))
    (.conj (zeroOrSuccessor x) (allMem x (zeroOrSuccessor 0))))

theorem eval_zeroOrSuccessor (x : ℕ) (e : ℕ → ZFSet.{u}) :
    (zeroOrSuccessor x).Eval e ↔ e x = ∅ ∨ ∃ y ∈ e x, e x = insert y y := by
  simp only [zeroOrSuccessor,eval_disj,eval_empty,Eval,eval_successor,cons_zero,cons_succ]
end Formula

def FiniteOrdinal (x : ZFSet.{u}) : Prop := Transitive x ∧ (∀ y ∈ x, Transitive y) ∧
  (x = ∅ ∨ ∃ y ∈ x, x = insert y y) ∧
  ∀ y ∈ x, y = ∅ ∨ ∃ z ∈ y, y = insert z z

theorem eval_finiteOrdinal (x : ℕ) (e : ℕ → ZFSet.{u}) :
    (Formula.finiteOrdinal x).Eval e ↔ FiniteOrdinal (e x) := by
  simp only [Formula.finiteOrdinal,Formula.Eval,Formula.eval_transitive,
    Formula.eval_allMem,Formula.eval_zeroOrSuccessor,cons_zero,FiniteOrdinal]

theorem finiteOrdinal_natSet (n : ℕ) : FiniteOrdinal (natSet.{u} n) := by
  have hshape (n : ℕ) : natSet.{u} n = ∅ ∨ ∃ y ∈ natSet n, natSet n = insert y y := by
    cases n with
    | zero => exact Or.inl rfl
    | succ n => exact Or.inr ⟨_,ZFSet.mem_insert _ _,rfl⟩
  refine ⟨natSet_transitive n,?_,hshape n,?_⟩
  · intro y hy
    obtain ⟨i,_,rfl⟩ := (mem_natSet n y).mp hy
    exact natSet_transitive i
  · intro y hy
    obtain ⟨i,_,rfl⟩ := (mem_natSet n y).mp hy
    exact hshape i

theorem finiteOrdinal_iff (x : ZFSet.{u}) : FiniteOrdinal x ↔ ∃ n, x = natSet n := by
  constructor
  · induction x using ZFSet.inductionOn with
    | h x ih =>
      intro h
      rcases h.2.2.1 with he|⟨y,hy,he⟩
      · exact ⟨0,he⟩
      · have hyf : FiniteOrdinal y := ⟨h.2.1 y hy,
          fun z hz => h.2.1 z (h.1 y hy z hz),h.2.2.2 y hy,
          fun z hz => h.2.2.2 z (h.1 y hy z hz)⟩
        obtain ⟨n,rfl⟩ := ih y hy hyf
        exact ⟨n+1,he⟩
  · rintro ⟨n,rfl⟩; exact finiteOrdinal_natSet n

theorem omega_mem (M : ZFSet.{u}) (hM : Transitive M) (hS : Separation M)
    (hI : Infinity M) : ZFSet.omega.{u} ∈ M := by
  obtain ⟨a,ha,⟨e,he,hea,hee⟩,hs⟩ := hI
  have he0 : e = ∅ := by
    apply ZFSet.ext; intro z
    simp only [ZFSet.notMem_empty,iff_false]
    exact fun hz => hee z (hM e he z hz) hz
  have hn (n : ℕ) : natSet.{u} n ∈ a := by
    induction n with
    | zero => simpa only [natSet,he0] using hea
    | succ n ih =>
      obtain ⟨s,hsM,hsa,hsdef⟩ := hs _ (hM a ha _ ih) ih
      have heq : s = insert (natSet n) (natSet n) := by
        apply ZFSet.ext; intro z; rw [ZFSet.mem_insert_iff]
        constructor
        · intro hz; exact (hsdef z (hM s hsM z hz)).mp hz
        · intro hz
          have hzM : z ∈ M := hz.elim (fun h => h ▸ hM a ha _ ih)
            (fun h => hM _ (hM a ha _ ih) z h)
          exact (hsdef z hzM).mpr hz
      simpa only [natSet,←heq] using hsa
  have hsep := sep_mem M hM hS (.finiteOrdinal 0) (fun _ => a) (fun _ => ha) ha
  have heq : ZFSet.sep (fun x => (Formula.finiteOrdinal 0).Eval (cons x (fun _ => a))) a =
      ZFSet.omega := by
    apply ZFSet.ext; intro x
    simp only [ZFSet.mem_sep,eval_finiteOrdinal,cons_zero,finiteOrdinal_iff,mem_omega]
    exact ⟨And.right,fun h => ⟨by obtain ⟨n,rfl⟩ := h; exact hn n,h⟩⟩
  exact heq ▸ hsep

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

theorem UnionIteration.correct {n : ℕ} {r f a : ZFSet.{u}}
    (h : UnionIteration (natSet (n+1)) r f a) (i : ℕ) (hi : i ≤ n)
    (v : ZFSet.{u}) (hv : ZFSet.pair (natSet i) v ∈ f) : v = iterUnion i a := by
  induction i generalizing v with
  | zero => exact h.1.functional ((natSet_mem_natSet 0 (n+1)).mpr (Nat.zero_lt_succ n)) hv h.2.1
  | succ i ih =>
    have hik := (natSet_mem_natSet i (n+1)).mpr (Nat.lt_succ_of_le (Nat.le_of_succ_le hi))
    have hjk := (natSet_mem_natSet (i+1) (n+1)).mpr (Nat.lt_succ_of_le hi)
    obtain ⟨w,hw,hfw,_⟩ := h.1.2 _ hik
    have he := h.2.2 _ hik _ hjk rfl w hw v (h.1.value_mem hv) hfw hv
    rw [ih (Nat.le_of_succ_le hi) w hfw] at he
    exact he

noncomputable def unionGraph (a : ZFSet.{u}) (n : ℕ) : ZFSet.{u} :=
  ZFSet.range (fun i : Fin (n+1) => ZFSet.pair (natSet i.val) (iterUnion i.val a))

theorem mem_unionGraph (a z : ZFSet.{u}) (n : ℕ) :
    z ∈ unionGraph a n ↔ ∃ i ≤ n, z = ZFSet.pair (natSet i) (iterUnion i a) := by
  rw [unionGraph,ZFSet.mem_range]
  exact ⟨fun ⟨i,hi⟩ => ⟨i.val,Nat.le_of_lt_succ i.isLt,hi.symm⟩,
    fun ⟨i,hi,hz⟩ => ⟨⟨i,Nat.lt_succ_of_le hi⟩,hz.symm⟩⟩

theorem unionGraph_pair (a x v : ZFSet.{u}) (n : ℕ) :
    ZFSet.pair x v ∈ unionGraph a n ↔ ∃ i ≤ n, x = natSet i ∧ v = iterUnion i a := by
  rw [mem_unionGraph]
  exact exists_congr (fun i => and_congr_right (fun _ => ZFSet.pair_inj))

theorem unionGraph_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (hU : BoundedSetTheory.Union M) (hω : ZFSet.omega.{u} ∈ M)
    {a : ZFSet.{u}} (ha : a ∈ M) (n : ℕ) : unionGraph a n ∈ M := by
  have hn (n : ℕ) : natSet.{u} n ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)
  induction n with
  | zero =>
    have he : unionGraph a 0 = ({ZFSet.pair (natSet 0) a} : ZFSet.{u}) := by
      apply ZFSet.ext; intro z
      simp only [mem_unionGraph,Nat.le_zero_eq,ZFSet.mem_singleton]
      simp only [exists_eq_left,iterUnion]
    rw [he]
    exact singleton_mem M hM hP (orderedPair_mem M hM hP (hn 0) ha)
  | succ n ih =>
    have he : unionGraph a (n+1) = unionGraph a n ∪
        ({ZFSet.pair (natSet (n+1)) (iterUnion (n+1) a)} : ZFSet.{u}) := by
      apply ZFSet.ext; intro z
      rw [mem_unionGraph,ZFSet.mem_union,mem_unionGraph,ZFSet.mem_singleton]
      constructor
      · rintro ⟨i,hi,hz⟩
        rcases Nat.lt_or_eq_of_le hi with hi|rfl
        · exact Or.inl ⟨i,Nat.le_of_lt_succ hi,hz⟩
        · exact Or.inr hz
      · rintro (⟨i,hi,hz⟩|hz)
        · exact ⟨i,Nat.le.step hi,hz⟩
        · exact ⟨n+1,le_refl _,hz⟩
    rw [he]
    exact binary_union_mem M hM hP hU ih
      (singleton_mem M hM hP (orderedPair_mem M hM hP (hn (n+1))
        (iterUnion_mem M hM hU ha (n+1))))

theorem unionGraph_valid (a : ZFSet.{u}) (n : ℕ) :
    UnionIteration (natSet (n+1)) (iterUnion 2 (unionGraph a n)) (unionGraph a n) a := by
  have hpair (i : ℕ) (hi : i ≤ n) :
      ZFSet.pair (natSet i) (iterUnion i a) ∈ unionGraph a n :=
    (unionGraph_pair a _ _ n).mpr ⟨i,hi,rfl,rfl⟩
  refine ⟨⟨?_,?_⟩,hpair 0 (Nat.zero_le n),?_⟩
  · intro z hz
    obtain ⟨i,hi,rfl⟩ := (mem_unionGraph a z n).mp hz
    exact ⟨_,(natSet_mem_natSet i (n+1)).mpr (Nat.lt_succ_of_le hi),_,second_mem_doubleUnion hz,rfl⟩
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := (mem_natSet (n+1) x).mp hx
    have hp := hpair i (Nat.le_of_lt_succ hi)
    refine ⟨_,second_mem_doubleUnion hp,hp,?_⟩
    intro v _ hv
    obtain ⟨j,_,he,hv⟩ := (unionGraph_pair a _ v n).mp hv
    obtain rfl := natSet_injective he
    exact hv
  · intro x _ y _ hxy v _ w _ hxv hyw
    obtain ⟨i,_,rfl,rfl⟩ := (unionGraph_pair a x v n).mp hxv
    obtain ⟨j,_,rfl,rfl⟩ := (unionGraph_pair a y w n).mp hyw
    have he : j = i+1 := natSet_injective hxy
    rw [he]; rfl

namespace IterationFormula
open Formula

def iteration (k r f a e : ℕ) : Formula := .conj (functionGraph f k r)
  (.conj (pairMem e a f)
    (allMem k (allMem (k+1) (imp (successor 0 1)
      (allMem (r+2) (allMem (r+3)
        (imp (.conj (pairMem 3 1 (f+4)) (pairMem 2 0 (f+4))) (unionOf 0 1))))))))

theorem eval_iteration (k r f a e : ℕ) (env : ℕ → ZFSet.{u}) (he : env e = ∅) :
    (iteration k r f a e).Eval env ↔ UnionIteration (env k) (env r) (env f) (env a) := by
  simp only [iteration,Formula.Eval,eval_functionGraph,eval_pairMem,
    eval_allMem,eval_imp,eval_successor,eval_unionOf,cons_zero,cons_succ,
    UnionIteration,FunctionGraph,he,and_imp]
end IterationFormula

end TuringRigidity.TransitiveNameModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalContainer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open BoundedSetTheory
universe u

def unionCertificate : SigmaFormula := .existsSet (.existsSet (.existsSet (.bounded
  (.conj (.successor 2 4) (.conj (IterationFormula.iteration 2 1 0 5 6) (.pairMem 4 3 0))))))

theorem realize_unionCertificate (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hω : ZFSet.omega.{u} ∈ M)
    {a v : ZFSet.{u}} (ha : a ∈ M) (hv : v ∈ M) (n : ℕ) :
    unionCertificate.Realize M (cons v (cons (natSet n)
      (cons a (cons ∅ (fun _ => a))))) ↔ v = iterUnion n a := by
  have hn (i : ℕ) : natSet.{u} i ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨i,rfl⟩)
  have h0 : (∅ : ZFSet.{u}) ∈ M := hn 0
  have matrix (k r f : ZFSet.{u}) (hk : k ∈ M) (hr : r ∈ M) (hf : f ∈ M) :
      (Formula.conj (.successor 2 4)
        (.conj (IterationFormula.iteration 2 1 0 5 6) (.pairMem 4 3 0))).Realize M
          (cons f (cons r (cons k (cons v (cons (natSet n)
            (cons a (cons ∅ (fun _ => a)))))))) ↔
      k = natSet (n+1) ∧ UnionIteration k r f a ∧ ZFSet.pair (natSet n) v ∈ f := by
    have he : ∀ i, (cons f (cons r (cons k (cons v (cons (natSet n)
        (cons a (cons ∅ (fun _ => a)))))))) i ∈ M := by
      intro i
      rcases i with _|i; exact hf
      rcases i with _|i; exact hr
      rcases i with _|i; exact hk
      rcases i with _|i; exact hv
      rcases i with _|i; exact hn n
      rcases i with _|i; exact ha
      rcases i with _|i; exact h0
      exact ha
    rw [Formula.absolute _ M hM _ he]
    simp only [Formula.Eval,Formula.eval_successor,
      Formula.eval_pairMem,cons_zero,cons_succ]
    rw [IterationFormula.eval_iteration 2 1 0 5 6
      (cons f (cons r (cons k (cons v (cons (natSet n) (cons a (cons ∅ (fun _ => a)))))))) rfl]
    rfl
  change (∃ k ∈ M, ∃ r ∈ M, ∃ f ∈ M, _) ↔ _
  constructor
  · rintro ⟨k,hk,r,hr,f,hf,hc⟩
    obtain ⟨rfl,hg,hv⟩ := (matrix k r f hk hr hf).mp hc
    exact hg.correct n (le_refl n) v hv
  · intro hvEq
    have hf := unionGraph_mem M hM hP hU hω ha n
    refine ⟨natSet (n+1),hn (n+1),_,iterUnion_mem M hM hU hf 2,_,hf,?_⟩
    apply (matrix _ _ _ (hn (n+1)) (iterUnion_mem M hM hU hf 2) hf).mpr
    exact ⟨rfl,unionGraph_valid a n,(unionGraph_pair a _ v n).mpr ⟨n,le_refl n,rfl,hvEq⟩⟩

theorem collect_unionIterates (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (hU : BoundedSetTheory.Union M) (hR : SigmaReplacement M)
    (hω : ZFSet.omega.{u} ∈ M) {a : ZFSet.{u}} (ha : a ∈ M) :
    ∃ b ∈ M, ∀ y, y ∈ b ↔ ∃ n : ℕ, y = iterUnion n a := by
  have h0 : (∅ : ZFSet.{u}) ∈ M := hM _ hω _ ZFSet.omega_zero
  let e := cons a (cons ∅ (fun _ => a))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|i; exact ha
    rcases i with _|i; exact h0
    exact ha
  obtain ⟨b,hb,hbdef⟩ := hR unionCertificate e he _ hω (by
    intro x hx
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    have hv := iterUnion_mem M hM hU ha n
    refine ⟨_,hv,(realize_unionCertificate M hM hP hU hω ha hv n).mpr rfl,?_⟩
    intro z hz hφ
    exact (realize_unionCertificate M hM hP hU hω ha hz n).mp hφ)
  refine ⟨b,hb,fun y => ?_⟩
  constructor
  · intro hy
    have hyM := hM b hb y hy
    obtain ⟨x,hx,hφ⟩ := (hbdef y hyM).mp hy
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    exact ⟨n,(realize_unionCertificate M hM hP hU hω ha hyM n).mp hφ⟩
  · rintro ⟨n,rfl⟩
    have hv := iterUnion_mem M hM hU ha n
    exact (hbdef _ hv).mpr ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,
      (realize_unionCertificate M hM hP hU hω ha hv n).mpr rfl⟩

theorem internal_transitive_container (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) {a : ZFSet.{u}} (ha : a ∈ M) :
    ∃ d ∈ M, Transitive d ∧ a ∈ d := by
  have hω := omega_mem M hM hS hI
  obtain ⟨b,hb,hbdef⟩ := collect_unionIterates M hM hP hU hR hω ha
  let d := ({a} : ZFSet.{u}) ∪ ZFSet.sUnion b
  have hd : d ∈ M := binary_union_mem M hM hP hU
    (singleton_mem M hM hP ha) (union_mem M hM hU hb)
  refine ⟨d,hd,?_,ZFSet.mem_union.mpr (Or.inl (ZFSet.mem_singleton.mpr rfl))⟩
  intro x hx y hy
  apply ZFSet.mem_union.mpr
  apply Or.inr
  rcases ZFSet.mem_union.mp hx with hx|hx
  · obtain rfl := ZFSet.mem_singleton.mp hx
    exact ZFSet.mem_sUnion.mpr ⟨x,(hbdef x).mpr ⟨0,rfl⟩,hy⟩
  · obtain ⟨c,hc,hxc⟩ := ZFSet.mem_sUnion.mp hx
    obtain ⟨n,rfl⟩ := (hbdef c).mp hc
    exact ZFSet.mem_sUnion.mpr ⟨iterUnion (n+1) a,(hbdef _).mpr ⟨n+1,rfl⟩,
      ZFSet.mem_sUnion.mpr ⟨x,hxc,hy⟩⟩

end TuringRigidity.TransitiveNameModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalFixedPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem internal_fixed_point (M : ZFSet.{u}) (hM : Transitive M)
    (hU : Union M) (hPow : PowerSet M) (hS : Separation M)
    (φ : Formula) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (a : ZFSet.{u}) (ha : a ∈ M)
    (mono : ∀ f g : ZFSet.{u}, f ⊆ a → g ⊆ a → f ⊆ g →
      ∀ z ∈ a, φ.Eval (cons z (cons f e)) → φ.Eval (cons z (cons g e))) :
    ∃ g ∈ M, g ⊆ a ∧ ∀ z ∈ a,
      z ∈ g ↔ φ.Eval (cons z (cons g e)) := by
  obtain ⟨b,hb,hbdef⟩ := internal_power M hM hPow ha
  let post := Formula.allMem 0 φ
  let s := ZFSet.sep (fun f => post.Eval (cons f e)) b
  have hs : s ∈ M := sep_mem M hM hS post e he hb
  have hsdef (f : ZFSet.{u}) : f ∈ s ↔
      f ∈ M ∧ f ⊆ a ∧ ∀ z ∈ f, φ.Eval (cons z (cons f e)) := by
    simp only [s,ZFSet.mem_sep,hbdef,post,Formula.eval_allMem,cons_zero]
    exact and_assoc
  let g := ZFSet.sUnion s
  have hg : g ∈ M := union_mem M hM hU hs
  have hga : g ⊆ a := by
    intro z hz
    obtain ⟨f,hf,hzf⟩ := ZFSet.mem_sUnion.mp hz
    exact ((hsdef f).mp hf).2.1 hzf
  have hgpost : ∀ z ∈ g, φ.Eval (cons z (cons g e)) := by
    intro z hz
    obtain ⟨f,hf,hzf⟩ := ZFSet.mem_sUnion.mp hz
    have hf' := (hsdef f).mp hf
    apply mono f g hf'.2.1 hga (fun w hw => ZFSet.mem_sUnion.mpr ⟨f,hf,hw⟩) z (hga hz)
    exact hf'.2.2 z hzf
  let v := ZFSet.sep (fun z => φ.Eval (cons z (cons g e))) a
  have hv : v ∈ M := sep_mem M hM hS φ (cons g e)
    (fun i => by cases i <;> simp [hg,he]) ha
  have hva : v ⊆ a := fun z hz => (ZFSet.mem_sep.mp hz).1
  have hgv : g ⊆ v := fun z hz => ZFSet.mem_sep.mpr ⟨hga hz,hgpost z hz⟩
  have hvpost : ∀ z ∈ v, φ.Eval (cons z (cons v e)) := by
    intro z hz
    exact mono g v hga hva hgv z (hva hz) (ZFSet.mem_sep.mp hz).2
  have hvs : v ∈ s := (hsdef v).mpr ⟨hv,hva,hvpost⟩
  refine ⟨g,hg,hga,fun z hz => ⟨hgpost z,fun h => ?_⟩⟩
  exact ZFSet.mem_sUnion.mpr ⟨v,hvs,ZFSet.mem_sep.mpr ⟨hz,h⟩⟩

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_AtomicFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open TransitiveNameModel BoundedSetTheory
universe u

theorem match_mono (flip : Bool) (d c k o f g a y q : ZFSet.{u})
    (hfg : f ⊆ g) (h : Match flip d c k o f a y q) : Match flip d c k o g a y q := by
  obtain ⟨r,hr,hrq,b,hb,t,ht,hbt,hrt,v,hv,hve,hvf⟩ := h
  exact ⟨r,hr,hrq,b,hb,t,ht,hbt,hrt,v,hv,hve,hfg hvf⟩

theorem step_mono (d c k o f g x y p : ZFSet.{u}) (hfg : f ⊆ g)
    (h : Step d c k o f x y p) : Step d c k o g x y p := by
  exact ⟨fun a ha s hs hax q hq hqp hqs =>
      match_mono _ _ _ _ _ _ _ _ _ _ hfg (h.1 a ha s hs hax q hq hqp hqs),
    fun a ha s hs hay q hq hqp hqs =>
      match_mono _ _ _ _ _ _ _ _ _ _ hfg (h.2 a ha s hs hay q hq hqp hqs)⟩

theorem vertex_mono (d c k o f g z : ZFSet.{u}) (hfg : f ⊆ g)
    (h : Vertex d c k o f z) : Vertex d c k o g z := by
  obtain ⟨x,hx,y,hy,q,hq,v,hv,hve,hze,hs⟩ := h
  exact ⟨x,hx,y,hy,q,hq,v,hv,hve,hze,step_mono _ _ _ _ _ _ _ _ _ hfg hs⟩

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_AtomicGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open TransitiveNameModel BoundedSetTheory
universe u

theorem vertex_pair (d c o f x y q : ZFSet.{u}) (hx : x ∈ d) (hy : y ∈ d) (hq : q ∈ c) :
    Vertex d c (ZFSet.prod d d) o f (ZFSet.pair (ZFSet.pair x y) q) ↔
      Step d c (ZFSet.prod d d) o f x y q := by
  constructor
  · rintro ⟨a,ha,b,hb,r,hr,v,hv,hve,hze,hs⟩
    obtain ⟨hp,hq'⟩ := ZFSet.pair_inj.mp hze
    have hab := ZFSet.pair_inj.mp (hp.trans hve)
    rcases hab with ⟨rfl,rfl⟩
    simpa only [hq'] using hs
  · intro hs
    exact ⟨x,hx,y,hy,q,hq,_,ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩,rfl,rfl,hs⟩

theorem internal_atomic_graph (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    {d c o : ZFSet.{u}} (hd : d ∈ M) (hc : c ∈ M) (ho : o ∈ M) :
    ∃ f ∈ M, Graph d c o f := by
  let k := ZFSet.prod d d
  let a := ZFSet.prod k c
  have hk : k ∈ M := product_mem M hM hP hU hPow hS hd hd
  have ha : a ∈ M := product_mem M hM hP hU hPow hS hk hc
  let e := cons d (cons c (cons k (cons o (fun _ => d))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|i; exact hd
    rcases i with _|i; exact hc
    rcases i with _|i; exact hk
    rcases i with _|i; exact ho
    exact hd
  let φ := AtomicFormula.vertex 2 3 4 5 1 0
  have hφ (f z : ZFSet.{u}) : φ.Eval (cons z (cons f e)) ↔ Vertex d c k o f z :=
    AtomicFormula.eval_vertex 2 3 4 5 1 0 _
  obtain ⟨f,hf,hfa,hfdef⟩ := internal_fixed_point M hM hU hPow hS φ e he a ha (by
    intro f g _ _ hfg z _ h
    exact (hφ g z).mpr (vertex_mono _ _ _ _ _ _ _ hfg ((hφ f z).mp h)))
  refine ⟨f,hf,hfa,fun x hx y hy q hq => ?_⟩
  have hz : ZFSet.pair (ZFSet.pair x y) q ∈ a :=
    ZFSet.mem_prod.mpr ⟨_,ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩,q,hq,rfl⟩
  exact (hfdef _ hz).trans ((hφ f _).trans (vertex_pair d c o f x y q hx hy hq))

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_AtomicGraphCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

omit [Preorder (Conditions c)] in
theorem child_code_mem {d : ZFSet.{u}} (hd : Transitive d)
    (a : Name (Conditions c)) (ha : a.encode (label c) ∈ d) (i : a.arity) :
    (a.child i).encode (label c) ∈ d := by
  apply names_childClosed d c hd a ha
  cases a
  exact ⟨i,rfl⟩

theorem match_encode (flip : Bool) {d k o f a : ZFSet.{u}} (hd : Transitive d)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (b : Name (Conditions c)) (hb : b.encode (label c) ∈ d) (q : Conditions c) :
    Match flip d c k o f a (b.encode (label c)) (label c q) ↔
      ∃ r, r ≤ q ∧ ∃ j, r ≤ b.tag j ∧
        Triple k f (if flip then (b.child j).encode (label c) else a)
          (if flip then a else (b.child j).encode (label c)) (label c r) := by
  constructor
  · rintro ⟨r,hr,hrq,x,hx,t,ht,hxt,hrt,hf⟩
    obtain ⟨s,rfl⟩ := label_surjective c hr
    obtain ⟨j,hj,hjt⟩ := (pair_mem_encode (label c) b x t).mp hxt
    subst x
    subst t
    exact ⟨s,(ho s q).mp hrq,j,(ho s (b.tag j)).mp hrt,hf⟩
  · rintro ⟨r,hrq,j,hrj,hf⟩
    exact ⟨label c r,label_mem c r,(ho r q).mpr hrq,
      _,child_code_mem hd b hb j,_,label_mem c (b.tag j),
      (pair_mem_encode _ _ _ _).mpr ⟨j,rfl,rfl⟩,(ho r (b.tag j)).mpr hrj,hf⟩

theorem side_encode (flip : Bool) {d k o f : ZFSet.{u}} (hd : Transitive d)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (a b : Name (Conditions c)) (ha : a.encode (label c) ∈ d)
    (hb : b.encode (label c) ∈ d) (p : Conditions c) :
    Side flip d c k o f (a.encode (label c)) (b.encode (label c)) (label c p) ↔
      ∀ i, Below p (a.tag i) (fun r => ∃ j, r ≤ b.tag j ∧
        Triple k f (if flip then (b.child j).encode (label c) else (a.child i).encode (label c))
          (if flip then (a.child i).encode (label c) else (b.child j).encode (label c)) (label c r)) := by
  constructor
  · intro h i q hqp hqi
    have hm := h _ (child_code_mem hd a ha i) _ (label_mem c (a.tag i))
      ((pair_mem_encode _ _ _ _).mpr ⟨i,rfl,rfl⟩) _ (label_mem c q)
      ((ho q p).mpr hqp) ((ho q (a.tag i)).mpr hqi)
    exact (match_encode flip hd ho b hb q).mp hm
  · intro h x hx s hs hxs q hq hqp hqs
    obtain ⟨i,hi,his⟩ := (pair_mem_encode (label c) a x s).mp hxs
    subst x
    subst s
    obtain ⟨r,rfl⟩ := label_surjective c hq
    exact (match_encode flip hd ho b hb r).mpr
      (h i r ((ho r p).mp hqp) ((ho r (a.tag i)).mp hqs))

theorem Graph.correct {d o f : ZFSet.{u}} (hd : Transitive d)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (hf : Graph d c o f) (a b : Name (Conditions c))
    (ha : a.encode (label c) ∈ d) (hb : b.encode (label c) ∈ d) (p : Conditions c) :
    ZFSet.pair (ZFSet.pair (a.encode (label c)) (b.encode (label c))) (label c p) ∈ f ↔
      EqForces a b p := by
  induction a generalizing b p with
  | mk ι a s ih =>
    cases b with
    | mk κ b t =>
      have hai (i) : (a i).encode (label c) ∈ d := child_code_mem hd _ ha i
      have hbj (j) : (b j).encode (label c) ∈ d := child_code_mem hd _ hb j
      have hrel (i j) (q : Conditions c) :
          Triple (ZFSet.prod d d) f ((a i).encode (label c)) ((b j).encode (label c)) (label c q) ↔
            EqForces (a i) (b j) q :=
        (triple_pair (hai i) (hbj j)).trans (ih i (b j) (hai i) (hbj j) q)
      rw [hf.2 _ ha _ hb _ (label_mem c p)]
      change (Side false _ _ _ _ _ _ _ _ ∧ Side true _ _ _ _ _ _ _ _) ↔ _
      rw [side_encode false hd ho _ _ ha hb p, side_encode true hd ho _ _ hb ha p]
      simp only [Bool.false_eq_true,ite_false,ite_true,Name.arity,Name.child,Name.tag]
      simp only [Below,hrel,EqForces]

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_AtomicDecisionFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory
universe u

variable {c : ZFSet.{u}} [Preorder (Conditions c)]

omit [Preorder (Conditions c)] in
theorem child_mem {d : ZFSet.{u}} (hd : Transitive d)
    (a : Name (Conditions c)) (ha : a.encode (label c) ∈ d) (i : a.arity) :
    (a.child i).encode (label c) ∈ d := by
  apply names_childClosed d c hd a ha
  cases a
  exact ⟨i,rfl⟩

theorem codeWitness_iff {d o f : ZFSet.{u}} (hd : Transitive d)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (hf : Graph d c o f) (a b : Name (Conditions c))
    (ha : a.encode (label c) ∈ d) (hb : b.encode (label c) ∈ d) (p : Conditions c) :
    CodeWitness d c (ZFSet.prod d d) o f (a.encode (label c)) (b.encode (label c)) (label c p) ↔
      Witness a b p := by
  have hrel (j) := (triple_pair ha (child_mem hd b hb j)).trans
    (hf.correct hd ho a (b.child j) ha (child_mem hd b hb j) p)
  cases b with
  | mk κ b t =>
    constructor
    · rintro ⟨x,hx,s,hs,hxs,hps,he⟩
      obtain ⟨j,hj,hjs⟩ := (pair_mem_encode _ _ _ _).mp hxs
      subst x
      subst s
      exact ⟨j,(ho p (t j)).mp hps,(hrel j).mp he⟩
    · rintro ⟨j,hj,he⟩
      exact ⟨_,child_mem hd _ hb j,_,label_mem c (t j),
        (pair_mem_encode _ _ _ _).mpr ⟨j,rfl,rfl⟩,(ho p (t j)).mpr hj,(hrel j).mpr he⟩

theorem negMem_iff_no_witness (a b : Name (Conditions c)) (p : Conditions c) :
    NegMem a b p ↔ ∀ q, q ≤ p → ¬ Witness a b q := by
  constructor
  · intro h q hq hw
    exact h q hq (witness_mem a b q hw)
  · intro h q hq hm
    cases b with
    | mk κ b t =>
      obtain ⟨r,hr,hw⟩ := hm q le_rfl
      exact h r (hr.trans hq) hw

theorem codeNeg_iff {d o f : ZFSet.{u}} (hd : Transitive d)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (hf : Graph d c o f) (a b : Name (Conditions c))
    (ha : a.encode (label c) ∈ d) (hb : b.encode (label c) ∈ d) (p : Conditions c) :
    CodeNeg d c (ZFSet.prod d d) o f (a.encode (label c)) (b.encode (label c)) (label c p) ↔
      NegMem a b p := by
  rw [negMem_iff_no_witness]
  constructor
  · intro h q hq hw
    exact h _ (label_mem c q) ((ho q p).mpr hq) ((codeWitness_iff hd ho hf a b ha hb q).mpr hw)
  · intro h q hq hqp hw
    obtain ⟨r,rfl⟩ := label_surjective c hq
    exact h r ((ho r p).mp hqp) ((codeWitness_iff hd ho hf a b ha hb r).mp hw)

theorem codeRefute_iff {d o f : ZFSet.{u}} (hd : Transitive d)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (hf : Graph d c o f) (a b : Name (Conditions c))
    (ha : a.encode (label c) ∈ d) (hb : b.encode (label c) ∈ d) (p : Conditions c) :
    CodeRefute d c (ZFSet.prod d d) o f (a.encode (label c)) (b.encode (label c)) (label c p) ↔
      ∃ i, p ≤ a.tag i ∧ NegMem (a.child i) b p := by
  constructor
  · rintro ⟨x,hx,s,hs,hxs,hps,hn⟩
    obtain ⟨i,hi,his⟩ := (pair_mem_encode _ _ _ _).mp hxs
    subst x
    subst s
    exact ⟨i,(ho p (a.tag i)).mp hps,
      (codeNeg_iff hd ho hf _ b (child_mem hd a ha i) hb p).mp hn⟩
  · rintro ⟨i,hi,hn⟩
    exact ⟨_,child_mem hd a ha i,_,label_mem c (a.tag i),
      (pair_mem_encode _ _ _ _).mpr ⟨i,rfl,rfl⟩,(ho p (a.tag i)).mpr hi,
      (codeNeg_iff hd ho hf _ b (child_mem hd a ha i) hb p).mpr hn⟩

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalAtomicTruth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem internal_atomic_requirements (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (a b : Name (Conditions c)) (ha : a.encode (label c) ∈ M) (hb : b.encode (label c) ∈ M) :
    ∃ D ∈ M, ∃ E ∈ M,
      (∀ q, label c q ∈ D ↔ q ∈ MemTest a b) ∧ (∀ q, label c q ∈ E ↔ q ∈ EqTest a b) := by
  obtain ⟨d,hd,hdT,hdab⟩ := internal_transitive_container M hM hP hU hS hR hI
    (pair_mem M hM hP ha hb)
  have had : a.encode (label c) ∈ d := hdT _ hdab _ (ZFSet.mem_pair.mpr (Or.inl rfl))
  have hbd : b.encode (label c) ∈ d := hdT _ hdab _ (ZFSet.mem_pair.mpr (Or.inr rfl))
  obtain ⟨f,hf,hfG⟩ := internal_atomic_graph M hM hP hU hPow hS hd hc hoM
  let k := ZFSet.prod d d
  have hk : k ∈ M := product_mem M hM hP hU hPow hS hd hd
  let e := cons d (cons c (cons k (cons o (cons f
    (cons (a.encode (label c)) (cons (b.encode (label c)) (fun _ => c)))))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|i; exact hd
    rcases i with _|i; exact hc
    rcases i with _|i; exact hk
    rcases i with _|i; exact hoM
    rcases i with _|i; exact hf
    rcases i with _|i; exact ha
    rcases i with _|i; exact hb
    exact hc
  let φ := AtomicFormula.memTest 1 2 3 4 5 6 7 0
  let ψ := AtomicFormula.eqTest 1 2 3 4 5 6 7 0
  have hφ (q : Conditions c) : φ.Eval (cons (label c q) e) ↔ q ∈ MemTest a b := by
    simp only [φ,AtomicFormula.memTest,Formula.eval_disj,AtomicFormula.eval_witness,
      AtomicFormula.eval_negMem,cons_zero,cons_succ,e]
    exact or_congr (codeWitness_iff hdT ho hfG a b had hbd q)
      (codeNeg_iff hdT ho hfG a b had hbd q)
  have hψ (q : Conditions c) : ψ.Eval (cons (label c q) e) ↔ q ∈ EqTest a b := by
    simp only [ψ,AtomicFormula.eqTest,Formula.eval_disj,AtomicFormula.eval_triple,
      AtomicFormula.eval_refute,cons_zero,cons_succ,e]
    have hEq := (triple_pair had hbd).trans (hfG.correct hdT ho a b had hbd q)
    have hA := codeRefute_iff hdT ho hfG a b had hbd q
    have hB := codeRefute_iff hdT ho hfG b a hbd had q
    cases a
    cases b
    exact or_congr hEq (or_congr hA hB)
  refine ⟨ZFSet.sep (fun z => φ.Eval (cons z e)) c,sep_mem M hM hS φ e he hc,
    ZFSet.sep (fun z => ψ.Eval (cons z e)) c,sep_mem M hM hS ψ e he hc,?_,?_⟩
  · intro q
    simp only [ZFSet.mem_sep,label_mem c q,true_and,hφ]
  · intro q
    simp only [ZFSet.mem_sep,label_mem c q,true_and,hψ]

theorem groundGeneric_atomic (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) : Generic (names M c) G := by
  have requirements (a : Name (Conditions c)) (ha : a ∈ names M c)
      (b : Name (Conditions c)) (hb : b ∈ names M c) :=
    internal_atomic_requirements M hM hP hU hPow hS hR hI hc hoM ho a b ha hb
  constructor
  · intro a ha b hb
    obtain ⟨D,hD,E,hE,hDm,hEe⟩ := requirements a ha b hb
    have hd : Dense {q | label c q ∈ D} := by
      intro p
      obtain ⟨q,hq,hm⟩ := memTest_dense a b p
      exact ⟨q,hq,(hDm q).mpr hm⟩
    obtain ⟨q,hq,hqd⟩ := hG D hD hd
    exact ⟨q,hq,(hDm q).mp hqd⟩
  · intro a ha b hb
    obtain ⟨D,hD,E,hE,hDm,hEe⟩ := requirements a ha b hb
    have hd : Dense {q | label c q ∈ E} := by
      intro p
      obtain ⟨q,hq,hm⟩ := eqTest_dense a b p
      exact ⟨q,hq,(hEe q).mpr hm⟩
    obtain ⟨q,hq,hqe⟩ := hG E hE hd
    exact ⟨q,hq,(hEe q).mp hqe⟩

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_AtomicCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory
universe u

variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem eval_membership {d o f : ZFSet.{u}} (hd : Transitive d)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (hf : Graph d c o f) (a b : Name (Conditions c))
    (ha : a.encode (label c) ∈ d) (hb : b.encode (label c) ∈ d) (p : Conditions c)
    (e : ℕ → ZFSet.{u}) (di ci ki oi fi xi yi pi : ℕ)
    (he : e di = d ∧ e ci = c ∧ e ki = ZFSet.prod d d ∧ e oi = o ∧ e fi = f ∧
      e xi = a.encode (label c) ∧ e yi = b.encode (label c) ∧ e pi = label c p) :
    (AtomicFormula.membership di ci ki oi fi xi yi pi).Eval e ↔ MemForces a b p := by
  rcases he with ⟨hd',hc',hk',ho',hf',hx',hy',hp'⟩
  simp only [AtomicFormula.membership,Formula.eval_allMem,Formula.eval_imp,
    Formula.eval_pairMem,AtomicFormula.eval_matchF,cons_zero,cons_succ,
    hd',hc',hk',ho',hf',hx',hy',hp']
  have step (q : Conditions c) :
      Match false d c (ZFSet.prod d d) o f (a.encode (label c)) (b.encode (label c)) (label c q) ↔
        ∃ r, r ≤ q ∧ Witness a b r := by
    rw [match_encode false hd ho b hb q]
    simp only [Bool.false_eq_true,ite_false]
    cases b with
    | mk κ b t =>
      have hchild (j) : (b j).encode (label c) ∈ d := names_childClosed d c hd (.mk κ b t) hb (b j) ⟨j,rfl⟩
      have hrel (j) (r : Conditions c) := (triple_pair ha (hchild j)).trans
        (hf.correct hd ho a (b j) ha (hchild j) r)
      simp only [Name.arity,Name.child,Name.tag,hrel,Witness]
  cases b with
  | mk κ b t =>
    constructor
    · intro h q hq
      exact (step q).mp (h _ (label_mem c q) ((ho q p).mpr hq))
    · intro h q hq hqp
      obtain ⟨r,rfl⟩ := label_surjective c hq
      exact (step r).mpr (h r ((ho r p).mp hqp))

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_BoundedForcingCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing
universe u

def code : BoundedSetTheory.Formula → ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ) → ℕ → BoundedSetTheory.Formula
  | .equal i j, _d,_c,k,_o,f,v,p => AtomicFormula.triple k f (v i) (v j) p
  | .member i j, d,c,k,o,f,v,p => AtomicFormula.membership d c k o f (v i) (v j) p
  | .conj φ ψ, d,c,k,o,f,v,p => .conj (code φ d c k o f v p) (code ψ d c k o f v p)
  | .neg φ, d,c,k,o,f,v,p => Formula.allMem c
      (Formula.imp (Formula.pairMem 0 (p+1) (o+1))
        (.neg (code φ (d+1) (c+1) (k+1) (o+1) (f+1) (fun i => v i+1) 0)))
  | .existsMem i φ, d,c,k,o,f,v,p => .existsMem d (.existsMem (c+1)
      (.conj (Formula.pairMem 1 0 (v i+2)) (.conj (Formula.pairMem (p+2) 0 (o+2))
        (code φ (d+2) (c+2) (k+2) (o+2) (f+2) (push 1 (fun i => v i+2)) (p+2)))))

variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem eval_code (φ : BoundedSetTheory.Formula) {d o f : ZFSet.{u}} (hd : Transitive d)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (hf : Graph d c o f) (e : ℕ → Name (Conditions c))
    (he : ∀ i, (e i).encode (label c) ∈ d) (p : Conditions c)
    (env : ℕ → ZFSet.{u}) (di ci ki oi fi : ℕ) (v : ℕ → ℕ) (pi : ℕ)
    (slots : env di = d ∧ env ci = c ∧ env ki = ZFSet.prod d d ∧ env oi = o ∧ env fi = f ∧ env pi = label c p)
    (hv : ∀ i, env (v i) = (e i).encode (label c)) :
    (code φ di ci ki oi fi v pi).Eval env ↔ Forces e φ p := by
  induction φ generalizing e p env di ci ki oi fi v pi with
  | equal i j =>
    simp only [code,AtomicFormula.eval_triple,slots.2.2.1,slots.2.2.2.2.1,slots.2.2.2.2.2,hv,Forces]
    exact (triple_pair (he i) (he j)).trans (hf.correct hd ho _ _ (he i) (he j) p)
  | member i j =>
    exact eval_membership hd ho hf _ _ (he i) (he j) p env di ci ki oi fi (v i) (v j) pi
      ⟨slots.1,slots.2.1,slots.2.2.1,slots.2.2.2.1,slots.2.2.2.2.1,hv i,hv j,slots.2.2.2.2.2⟩
  | conj φ ψ ihφ ihψ =>
    exact and_congr (ihφ e he p env di ci ki oi fi v pi slots hv)
      (ihψ e he p env di ci ki oi fi v pi slots hv)
  | neg φ ih =>
    simp only [code,Formula.eval_allMem,Formula.eval_imp,Formula.eval_pairMem,Formula.Eval,
      cons_zero,cons_succ,slots.2.1,slots.2.2.2.1,slots.2.2.2.2.2]
    have sub (q : Conditions c) := ih e he q (cons (label c q) env)
      (di+1) (ci+1) (ki+1) (oi+1) (fi+1) (fun i => v i+1) 0
      ⟨slots.1,slots.2.1,slots.2.2.1,slots.2.2.2.1,slots.2.2.2.2.1,rfl⟩ hv
    constructor
    · intro h q hq hforce
      exact h _ (label_mem c q) ((ho q p).mpr hq) ((sub q).mpr hforce)
    · intro h q hq hqp hforce
      obtain ⟨r,rfl⟩ := label_surjective c hq
      exact h r ((ho r p).mp hqp) ((sub r).mp hforce)
  | existsMem i φ ih =>
    simp only [code,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,
      slots.1,slots.2.1,slots.2.2.2.1,slots.2.2.2.2.2,hv]
    have hej (j) : ∀ n, (push ((e i).child j) e n).encode (label c) ∈ d := by
      intro n
      cases n with
      | zero =>
        exact names_childClosed d c hd (e i) (he i) _ (child_relation (e i) j)
      | succ n => exact he n
    have sub (j) (s : Conditions c) := ih (push ((e i).child j) e) (hej j) p
      (cons (label c s) (cons (((e i).child j).encode (label c)) env))
      (di+2) (ci+2) (ki+2) (oi+2) (fi+2) (push 1 (fun n => v n+2)) (pi+2)
      ⟨slots.1,slots.2.1,slots.2.2.1,slots.2.2.2.1,slots.2.2.2.2.1,slots.2.2.2.2.2⟩
      (by intro n; cases n <;> simp only [push_zero,push_succ,cons_zero,cons_succ,hv])
    constructor
    · rintro ⟨x,hx,s,hs,hxs,hps,hφ⟩
      obtain ⟨j,hj,hjs⟩ := (pair_mem_encode _ _ _ _).mp hxs
      subst x
      subst s
      exact ⟨j,(ho p ((e i).tag j)).mp hps,(sub j ((e i).tag j)).mp hφ⟩
    · rintro ⟨j,hj,hφ⟩
      exact ⟨_,hej j 0,_,label_mem c ((e i).tag j),
        (pair_mem_encode _ _ _ _).mpr ⟨j,rfl,rfl⟩,(ho p ((e i).tag j)).mpr hj,
        (sub j ((e i).tag j)).mpr hφ⟩

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SigmaSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u

namespace Formula

theorem realize_rename (φ : Formula) (M : ZFSet.{u}) (v : ℕ → ℕ)
    (e : ℕ → ZFSet.{u}) : (φ.rename v).Realize M e ↔ φ.Realize M (fun i => e (v i)) := by
  induction φ generalizing v e with
  | equal => rfl
  | member => rfl
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ v e) (ihψ v e)
  | neg φ ih => exact not_congr (ih v e)
  | existsMem i φ ih =>
    simp only [rename,Realize]
    apply exists_congr
    intro x
    apply and_congr_right
    intro _
    apply and_congr_right
    intro _
    have he : (fun i => cons x e (liftMap v i)) = cons x (fun i => e (v i)) := by
      funext i; cases i <;> rfl
    exact (ih (liftMap v) (cons x e)).trans (he ▸ Iff.rfl)
end Formula

namespace SigmaFormula

def rename (v : ℕ → ℕ) : SigmaFormula → SigmaFormula
  | .bounded φ => .bounded (φ.rename v)
  | .existsSet φ => .existsSet (rename (liftMap v) φ)

theorem realize_rename (φ : SigmaFormula) (M : ZFSet.{u}) (v : ℕ → ℕ)
    (e : ℕ → ZFSet.{u}) : (φ.rename v).Realize M e ↔ φ.Realize M (fun i => e (v i)) := by
  induction φ generalizing v e with
  | bounded φ => exact φ.realize_rename M v e
  | existsSet φ ih =>
    simp only [rename,Realize]
    apply exists_congr
    intro x
    apply and_congr_right
    intro _
    have he : (fun i => cons x e (liftMap v i)) = cons x (fun i => e (v i)) := by
      funext i; cases i <;> rfl
    exact (ih (liftMap v) (cons x e)).trans (he ▸ Iff.rfl)

def andBounded (b : Formula) : SigmaFormula → SigmaFormula
  | .bounded φ => .bounded (.conj b φ)
  | .existsSet φ => .existsSet (andBounded (b.rename Nat.succ) φ)

theorem realize_andBounded (b : Formula) (φ : SigmaFormula) (M : ZFSet.{u})
    (e : ℕ → ZFSet.{u}) :
    (andBounded b φ).Realize M e ↔ b.Realize M e ∧ φ.Realize M e := by
  induction φ generalizing b e with
  | bounded => rfl
  | existsSet φ ih =>
    simp only [andBounded,Realize,ih,Formula.realize_rename,cons_succ]
    constructor
    · rintro ⟨x,hx,hb,hφ⟩; exact ⟨hb,x,hx,hφ⟩
    · rintro ⟨hb,x,hx,hφ⟩; exact ⟨x,hx,hb,hφ⟩

def conj : SigmaFormula → SigmaFormula → SigmaFormula
  | .bounded b, ψ => andBounded b ψ
  | .existsSet φ, ψ => .existsSet (conj φ (ψ.rename Nat.succ))

theorem realize_conj (φ ψ : SigmaFormula) (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (conj φ ψ).Realize M e ↔ φ.Realize M e ∧ ψ.Realize M e := by
  induction φ generalizing ψ e with
  | bounded b => exact realize_andBounded b ψ M e
  | existsSet φ ih =>
    simp only [conj,Realize,ih,realize_rename,cons_succ]
    constructor
    · rintro ⟨x,hx,hφ,hψ⟩; exact ⟨⟨x,hx,hφ⟩,hψ⟩
    · rintro ⟨⟨x,hx,hφ⟩,hψ⟩; exact ⟨x,hx,hφ,hψ⟩
end SigmaFormula

end TuringRigidity.BoundedSetTheory

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
open Set RecursiveNames TransitiveNameModel BoundedSetTheory
universe u

def bound : BoundedSetTheory.Formula → ℕ
  | .equal i j => max (i+1) (j+1)
  | .member i j => max (i+1) (j+1)
  | .conj φ ψ => max (bound φ) (bound ψ)
  | .neg φ => bound φ
  | .existsMem i φ => max (i+1) (bound φ - 1)

theorem forces_congr {P : Type u} [Preorder P] (φ : BoundedSetTheory.Formula)
    (e e' : ℕ → Name P) (h : ∀ i, i < bound φ → e i = e' i) (p : P) :
    Forces e φ p ↔ Forces e' φ p := by
  induction φ generalizing e e' p with
  | equal i j => simp only [Forces,h i (by simp [bound]),h j (by simp [bound])]
  | member i j => simp only [Forces,h i (by simp [bound]),h j (by simp [bound])]
  | conj φ ψ ihφ ihψ =>
    exact and_congr (ihφ e e' (fun i hi => h i (by simp only [bound]; omega)) p)
      (ihψ e e' (fun i hi => h i (by simp only [bound]; omega)) p)
  | neg φ ih =>
    exact forall_congr' (fun q => imp_congr_right (fun _ => not_congr (ih e e' h q)))
  | existsMem i φ ih =>
    have hei := h i (by simp only [bound]; omega)
    change (fun a : Name P => ∃ j : a.arity, p ≤ a.tag j ∧ Forces (push (a.child j) e) φ p) (e i) ↔ _
    rw [hei]
    apply exists_congr
    intro j
    apply and_congr_right
    intro _
    apply ih
    intro n hn
    cases n with
    | zero => rfl
    | succ n =>
      simp only [push_succ]
      exact h n (by simp only [bound]; omega)

theorem truncate_forces {P : Type u} [Preorder P] (φ : BoundedSetTheory.Formula)
    (e : ℕ → Name P) (p : P) : Forces (truncate (bound φ) e) φ p ↔ Forces e φ p :=
  forces_congr φ _ e (fun _ hi => ite_eq_left hi) p

theorem finite_container (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (n : ℕ) :
    ∃ d ∈ M, Transitive d ∧ e 0 ∈ d ∧ ∀ i, i < n → e i ∈ d := by
  induction n with
  | zero =>
    obtain ⟨d,hd,hdT,he0⟩ := internal_transitive_container M hM hP hU hS hR hI (he 0)
    exact ⟨d,hd,hdT,he0,fun i hi => False.elim (Nat.not_lt_zero i hi)⟩
  | succ n ih =>
    obtain ⟨d,hd,hdT,he0,hen⟩ := ih
    obtain ⟨v,hv,hvT,hvpair⟩ := internal_transitive_container M hM hP hU hS hR hI
      (pair_mem M hM hP hd (he n))
    have hdv : d ∈ v := hvT _ hvpair _ (ZFSet.mem_pair.mpr (Or.inl rfl))
    have hnv : e n ∈ v := hvT _ hvpair _ (ZFSet.mem_pair.mpr (Or.inr rfl))
    refine ⟨v,hv,hvT,hvT d hdv _ he0,fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hvT d hdv _ (hen i hi)
    · exact hnv

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBoundedTruth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem internal_decision (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (φ : BoundedSetTheory.Formula) (e : ℕ → Name (Conditions c))
    (he : ∀ i, (e i).encode (label c) ∈ M) :
    ∃ D ∈ M, ∀ q, label c q ∈ D ↔ q ∈ Decision e φ := by
  obtain ⟨d,hd,hdT,he0,hen⟩ := finite_container M hM hP hU hS hR hI
    (fun i => (e i).encode (label c)) he (bound φ)
  let e' := truncate (bound φ) e
  have he' (i) : (e' i).encode (label c) ∈ d := by
    dsimp only [e',truncate]
    split
    · exact hen i ‹_›
    · exact he0
  obtain ⟨f,hf,hfG⟩ := internal_atomic_graph M hM hP hU hPow hS hd hc hoM
  let k := ZFSet.prod d d
  have hk : k ∈ M := product_mem M hM hP hU hPow hS hd hd
  let env := cons d (cons c (cons k (cons o (cons f (fun i => (e' i).encode (label c))))))
  have henv : ∀ i, env i ∈ M := by
    intro i
    rcases i with _|i; exact hd
    rcases i with _|i; exact hc
    rcases i with _|i; exact hk
    rcases i with _|i; exact hoM
    rcases i with _|i; exact hf
    exact hM d hd _ (he' i)
  let ψ := Formula.disj (code φ 1 2 3 4 5 (fun i => i+6) 0)
    (code (.neg φ) 1 2 3 4 5 (fun i => i+6) 0)
  have hψ (q : Conditions c) : ψ.Eval (cons (label c q) env) ↔ q ∈ Decision e φ := by
    have hcφ (χ : BoundedSetTheory.Formula) := eval_code χ hdT ho hfG e' he' q
      (cons (label c q) env) 1 2 3 4 5 (fun i => i+6) 0
      ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ (fun _ => rfl)
    rw [Formula.eval_disj,hcφ φ,hcφ (.neg φ)]
    exact or_congr (truncate_forces φ e q) (truncate_forces (.neg φ) e q)
  refine ⟨ZFSet.sep (fun q => ψ.Eval (cons q env)) c,sep_mem M hM hS ψ env henv hc,?_⟩
  intro q
  simp only [ZFSet.mem_sep,label_mem c q,true_and,hψ]

theorem groundGeneric_bounded (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) : Generic (names M c) G := by
  intro φ e he
  obtain ⟨D,hD,hDdef⟩ := internal_decision M hM hP hU hPow hS hR hI hc hoM ho φ e he
  have hd : Dense {q | label c q ∈ D} := by
    intro p
    obtain ⟨q,hq,hf⟩ := decision_dense e φ p
    exact ⟨q,hq,(hDdef q).mpr hf⟩
  obtain ⟨q,hq,hqd⟩ := hG D hD hd
  exact ⟨q,hq,(hDdef q).mp hqd⟩

theorem internal_bounded_truth (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G)
    (φ : BoundedSetTheory.Formula) (e : ℕ → Name (Conditions c))
    (he : ∀ i, (e i).encode (label c) ∈ M) :
    φ.Eval (fun i => (e i).val G.carrier) ↔ ∃ p ∈ G.carrier, Forces e φ p :=
  truth (names_childClosed M c hM) G
    (groundGeneric_atomic M hM hP hU hPow hS hR hI hc hoM ho G hG)
    (groundGeneric_bounded M hM hP hU hPow hS hR hI hc hoM ho G hG) φ e he

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RestrictedName
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RecursiveNames
open Set CountableForcing
universe u
variable {P : Type u} [Preorder P]

abbrev Name.Entry (a : Name P) := Σ i : a.arity, {q : P // q ≤ a.tag i}

noncomputable def Name.entryCode (l : P → ZFSet.{u}) (a : Name P) (s : a.Entry) : ZFSet.{u} :=
  ZFSet.pair ((a.child s.1).encode l) (l s.2.val)

noncomputable def Name.support (l : P → ZFSet.{u}) (a : Name P) : ZFSet.{u} :=
  ZFSet.range (a.entryCode l)

noncomputable def Name.restrict (l : P → ZFSet.{u}) (a : Name P) (B : ZFSet.{u}) : Name P :=
  .mk {s : a.Entry // a.entryCode l s ∈ B} (fun s => a.child s.val.1) (fun s => s.val.2.val)

theorem Name.encode_restrict (l : P → ZFSet.{u}) (a : Name P) (B : ZFSet.{u})
    (hB : B ⊆ a.support l) : (a.restrict l B).encode l = B := by
  apply ZFSet.ext
  intro z
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨s,hs⟩
    exact hs ▸ s.property
  · intro hz
    obtain ⟨s,hs⟩ := ZFSet.mem_range.mp (hB hz)
    exact ⟨⟨s,hs ▸ hz⟩,hs⟩

theorem Name.mem_val_restrict (l : P → ZFSet.{u}) (a : Name P) (B : ZFSet.{u})
    (G : Set P) (x : ZFSet.{u}) : x ∈ (a.restrict l B).val G ↔
      ∃ i, ∃ q, q ≤ a.tag i ∧ ZFSet.pair ((a.child i).encode l) (l q) ∈ B ∧
        q ∈ G ∧ (a.child i).val G = x := by
  rw [Name.restrict,Name.mem_val]
  constructor
  · rintro ⟨⟨⟨i,q,hq⟩,hB⟩,hG,hx⟩
    exact ⟨i,q,hq,hB,hG,hx⟩
  · rintro ⟨i,q,hq,hB,hG,hx⟩
    exact ⟨⟨⟨i,⟨q,hq⟩⟩,hB⟩,hG,hx⟩

theorem Name.val_restrict_subset (l : P → ZFSet.{u}) (a : Name P) (B : ZFSet.{u})
    (G : GenericFilter P) : (a.restrict l B).val G.carrier ⊆ a.val G.carrier := by
  intro x hx
  obtain ⟨i,q,hq,_,hqG,hx⟩ := (a.mem_val_restrict l B G.carrier x).mp hx
  exact (a.mem_val_children G.carrier x).mpr ⟨i,G.upper hq hqG,hx⟩

end TuringRigidity.RecursiveNames

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_NameSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory
universe u

variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem support_iff {d o : ZFSet.{u}} (a : Name (Conditions c))
    (hd : ∀ i, (a.child i).encode (label c) ∈ d)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (z : ZFSet.{u}) : z ∈ a.support (label c) ↔ SupportPredicate d c o (a.encode (label c)) z := by
  constructor
  · intro hz
    obtain ⟨⟨i,q,hq⟩,hz⟩ := ZFSet.mem_range.mp hz
    exact ⟨_,hd i,_,label_mem c q,hz.symm,_,label_mem c (a.tag i),
      (pair_mem_encode _ _ _ _).mpr ⟨i,rfl,rfl⟩,(ho q (a.tag i)).mpr hq⟩
  · rintro ⟨x,hx,q,hq,rfl,s,hs,hxs,hqs⟩
    obtain ⟨i,hi,his⟩ := (pair_mem_encode _ _ _ _).mp hxs
    subst x
    subst s
    obtain ⟨r,rfl⟩ := label_surjective c hq
    exact ZFSet.mem_range.mpr ⟨⟨i,⟨r,(ho r (a.tag i)).mp hqs⟩⟩,rfl⟩

theorem support_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hc : c ∈ M) {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) : a.support (label c) ∈ M := by
  let d := iterUnion 2 (a.encode (label c))
  have hd : d ∈ M := iterUnion_mem M hM hU ha 2
  have hdi (i) : (a.child i).encode (label c) ∈ d :=
    first_mem_doubleUnion ((pair_mem_encode _ _ _ _).mpr ⟨i,rfl,rfl⟩)
  let e := cons d (cons c (cons o (cons (a.encode (label c)) (fun _ => c))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|i; exact hd
    rcases i with _|i; exact hc
    rcases i with _|i; exact hoM
    rcases i with _|i; exact ha
    exact hc
  let φ := AtomicFormula.support 1 2 3 4 0
  have hφ (z : ZFSet.{u}) : φ.Eval (cons z e) ↔ z ∈ a.support (label c) :=
    (AtomicFormula.eval_support 1 2 3 4 0 _).trans (support_iff a hdi ho z).symm
  have hcode : ZFSet.sep (fun z => φ.Eval (cons z e)) (ZFSet.prod d c) = a.support (label c) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep,hφ]
    constructor
    · exact And.right
    · intro hz
      obtain ⟨x,hx,q,hq,hz',_⟩ := (support_iff a hdi ho z).mp hz
      exact ⟨ZFSet.mem_prod.mpr ⟨x,hx,q,hq,hz'⟩,hz⟩
  exact hcode ▸ sep_mem M hM hS φ e he (product_mem M hM hP hU hPow hS hd hc)

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_SigmaForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

def SigmaForces (M : ZFSet.{u}) (e : ℕ → Name (Conditions c)) : SigmaFormula → Conditions c → Prop
  | .bounded φ, p => Forces e φ p
  | .existsSet φ, p => ∃ a : Name (Conditions c), a.encode (label c) ∈ M ∧ SigmaForces M (push a e) φ p

theorem internal_sigma_truth (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G)
    (φ : SigmaFormula) (e : ℕ → Name (Conditions c))
    (he : ∀ i, (e i).encode (label c) ∈ M) :
    φ.Realize (genericExtensionSet M c G.carrier) (fun i => (e i).val G.carrier) ↔
      ∃ p ∈ G.carrier, SigmaForces M e φ p := by
  induction φ generalizing e with
  | bounded φ =>
    exact (φ.absolute _ (genericExtensionSet_transitive M c hM G.carrier) _
      (fun i => (mem_extensionSet M c G.carrier _).mpr ⟨e i,he i,rfl⟩)).trans
      (internal_bounded_truth M hM hP hU hPow hS hR hI hc hoM ho G hG φ e he)
  | existsSet φ ih =>
    have hepush (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) :
        ∀ i, (push a e i).encode (label c) ∈ M := by
      intro i
      cases i with
      | zero => exact ha
      | succ i => exact he i
    have env (a : Name (Conditions c)) : (fun i => (push a e i).val G.carrier) =
        cons (a.val G.carrier) (fun i => (e i).val G.carrier) := by
      funext i
      cases i <;> rfl
    constructor
    · rintro ⟨x,hx,hφ⟩
      obtain ⟨a,ha,rfl⟩ := (mem_extensionSet M c G.carrier x).mp hx
      rw [←env a] at hφ
      obtain ⟨p,hp,hf⟩ := (ih _ (hepush a ha)).mp hφ
      exact ⟨p,hp,a,ha,hf⟩
    · rintro ⟨p,hp,a,ha,hf⟩
      refine ⟨a.val G.carrier,(mem_extensionSet M c G.carrier _).mpr ⟨a,ha,rfl⟩,?_⟩
      rw [←env a]
      exact (ih _ (hepush a ha)).mpr ⟨p,hp,hf⟩

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
open RecursiveNames TransitiveNameModel BoundedSetTheory
universe u

theorem Certificate.decode {d c h : ZFSet.{u}} (hh : Certificate d c h)
    (x : ZFSet.{u}) (hx : x ∈ h) :
    ∃ a : Name (Conditions c), a.encode (label c) = x := by
  classical
  induction x using child_wellFounded.induction with
  | h x ih =>
    have step := (hh.2 x (hh.1 hx)).mp hx
    have entry (i : Conditions x) : ∃ a : Name (Conditions c), ∃ q : Conditions c,
        label x i = ZFSet.pair (a.encode (label c)) (label c q) := by
      obtain ⟨y,hy,q,hq,heq⟩ := step _ (label_mem x i)
      obtain ⟨a,rfl⟩ := ih y ⟨q,heq ▸ label_mem x i⟩ hy
      obtain ⟨r,rfl⟩ := label_surjective c hq
      exact ⟨a,r,heq⟩
    let a : Conditions x → Name (Conditions c) := fun i => (entry i).choose
    let q : Conditions x → Conditions c := fun i => (entry i).choose_spec.choose
    have heq (i : Conditions x) : label x i = ZFSet.pair ((a i).encode (label c)) (label c (q i)) :=
      (entry i).choose_spec.choose_spec
    refine ⟨.mk (Conditions x) a q,?_⟩
    apply ZFSet.ext
    intro z
    change z ∈ ZFSet.range _ ↔ z ∈ x
    rw [ZFSet.mem_range]
    constructor
    · rintro ⟨i,rfl⟩
      rw [←heq i]
      exact label_mem x i
    · intro hz
      obtain ⟨i,rfl⟩ := label_surjective x hz
      exact ⟨i,(heq i).symm⟩

theorem Certificate.encode_mem {d c h : ZFSet.{u}} (hd : Transitive d)
    (hh : Certificate d c h) (a : Name (Conditions c))
    (ha : a.encode (label c) ∈ d) : a.encode (label c) ∈ h := by
  induction a with
  | mk ι a q ih =>
    apply (hh.2 _ ha).mpr
    intro z hz
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hz
    have hai : (a i).encode (label c) ∈ d :=
      names_childClosed d c hd (.mk ι a q) ha (a i) ⟨i,rfl⟩
    exact ⟨_,ih i hai,_,label_mem c (q i),rfl⟩

theorem Certificate.correct {d c h : ZFSet.{u}} (hd : Transitive d)
    (hh : Certificate d c h) {x : ZFSet.{u}} (hx : x ∈ d) :
    x ∈ h ↔ ∃ a : Name (Conditions c), a.encode (label c) = x := by
  constructor
  · exact hh.decode x
  · rintro ⟨a,rfl⟩
    exact hh.encode_mem hd a hx

namespace Code
open _root_.OAI.TuringRigidity.BoundedSetTheory.Formula
def step (c h x : ℕ) : Formula :=
  allMem x (.existsMem (h+1) (.existsMem (c+2) (orderedPair 2 1 0)))

theorem eval_step (c h x : ℕ) (e : ℕ → ZFSet.{u}) :
    (step c h x).Eval e ↔ Step (e c) (e h) (e x) := by
  simp only [step,Step,eval_allMem,Formula.Eval,eval_orderedPair,cons_zero,cons_succ]

def certificate (d c h : ℕ) : Formula :=
  .conj (subset h d) (allMem d (iff (.member 0 (h+1)) (step (c+1) (h+1) 0)))

theorem eval_certificate (d c h : ℕ) (e : ℕ → ZFSet.{u}) :
    (certificate d c h).Eval e ↔ Certificate (e d) (e c) (e h) := by
  simp only [certificate,Certificate,Formula.Eval,eval_subset,eval_allMem,eval_iff,
    eval_step,cons_zero,cons_succ]
end Code

theorem internal_certificate (M : ZFSet.{u}) (hM : Transitive M)
    (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    {d c : ZFSet.{u}} (hd : d ∈ M) (hc : c ∈ M) :
    ∃ h ∈ M, Certificate d c h := by
  obtain ⟨h,hh,hs,hdef⟩ := internal_fixed_point M hM hU hPow hS
    (Code.step 2 1 0) (fun _ => c) (fun _ => hc) d hd (by
      intro f g _ _ hfg x _ hf
      rw [Code.eval_step] at hf ⊢
      intro z hz
      obtain ⟨y,hy,q,hq,heq⟩ := hf z hz
      exact ⟨y,hfg hy,q,hq,heq⟩)
  exact ⟨h,hh,hs,fun x hx => (hdef x hx).trans (Code.eval_step 2 1 0 _)⟩

end TuringRigidity.NameValidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalNameValidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.NameValidity
open RecursiveNames TransitiveNameModel BoundedSetTheory
universe u

namespace Code

def valid (c x : ℕ) : SigmaFormula := .existsSet (.existsSet (.bounded
  (.conj (.transitive 1) (.conj (.member (x+2) 1)
    (.conj (certificate 1 (c+2) 0) (.member (x+2) 0))))))
end Code

theorem realize_valid (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (c x : ℕ) :
    (Code.valid c x).Realize M e ↔
      ∃ a : Name (Conditions (e c)), a.encode (label (e c)) = e x := by
  have matrix (d h : ZFSet.{u}) (hd : d ∈ M) (hh : h ∈ M) :
      (Formula.conj (.transitive 1) (.conj (.member (x+2) 1)
        (.conj (Code.certificate 1 (c+2) 0) (.member (x+2) 0)))).Realize M
          (cons h (cons d e)) ↔
        Transitive d ∧ e x ∈ d ∧ Certificate d (e c) h ∧ e x ∈ h := by
    rw [Formula.absolute _ M hM _ (by
      intro i; rcases i with _|i; exact hh
      rcases i with _|i; exact hd
      exact he i)]
    simp only [Formula.Eval,Formula.eval_transitive,Code.eval_certificate,cons_zero,cons_succ]
  change (∃ d ∈ M, ∃ h ∈ M, _) ↔ _
  constructor
  · rintro ⟨d,hd,h,hh,hφ⟩
    obtain ⟨_,_,hcert,hx⟩ := (matrix d h hd hh).mp hφ
    exact hcert.decode _ hx
  · rintro ⟨a,ha⟩
    obtain ⟨d,hd,hdT,hxd⟩ := internal_transitive_container M hM hP hU hS hR hI (he x)
    obtain ⟨h,hh,hcert⟩ := internal_certificate M hM hU hPow hS hd (he c)
    exact ⟨d,hd,h,hh,(matrix d h hd hh).mpr
      ⟨hdT,hxd,hcert,(hcert.correct hdT hxd).mpr ⟨a,ha⟩⟩⟩

end TuringRigidity.NameValidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BoundedCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing
universe u

namespace CertificateCode

def slots : ℕ → ℕ → (ℕ → ℕ) → Formula
  | 0, d, _v => .equal d d
  | n+1, d, v => .conj (slots n d v) (.member (v n) d)

theorem eval_slots (n d : ℕ) (v : ℕ → ℕ) (env : ℕ → ZFSet.{u}) :
    (slots n d v).Eval env ↔ ∀ i, i < n → env (v i) ∈ env d := by
  induction n with
  | zero => simp [slots,Formula.Eval]
  | succ n ih =>
    simp only [slots,Formula.Eval,ih]
    constructor
    · rintro ⟨h,hlast⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi|rfl
      · exact h i hi
      · exact hlast
    · intro h; exact ⟨fun i hi => h i (by omega),h n (by omega)⟩

def matrix (φ : Formula) (ci oi pi : ℕ) (v : ℕ → ℕ) : Formula :=
  .conj (.transitive 2) (.conj (AtomicFormula.product 2 1)
    (.conj (AtomicFormula.graph 2 (ci+3) 1 (oi+3) 0)
      (.conj (slots (bound φ+1) 2 (fun i => v i+3))
        (code φ 2 (ci+3) 1 (oi+3) 0
          (fun i => truncate (bound φ+1) v i+3) (pi+3)))))

def certificate (φ : Formula) (ci oi pi : ℕ) (v : ℕ → ℕ) : SigmaFormula :=
  .existsSet (.existsSet (.existsSet (.bounded (matrix φ ci oi pi v))))
end CertificateCode

variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem eval_certificate_matrix (φ : Formula) (d k f o : ZFSet.{u})
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (e : ℕ → Name (Conditions c)) (p : Conditions c)
    (env : ℕ → ZFSet.{u}) (ci oi pi : ℕ) (v : ℕ → ℕ)
    (hc : env ci = c) (ho' : env oi = o) (hp : env pi = label c p)
    (hv : ∀ i, env (v i) = (e i).encode (label c)) :
    (CertificateCode.matrix φ ci oi pi v).Eval (cons f (cons k (cons d env))) ↔
      Transitive d ∧ k = ZFSet.prod d d ∧ Graph d c o f ∧
        (∀ i, i < bound φ+1 → (e i).encode (label c) ∈ d) ∧ Forces e φ p := by
  have query (hd : Transitive d) (hk : k = ZFSet.prod d d) (hf : Graph d c o f)
      (hs : ∀ i, i < bound φ+1 → (e i).encode (label c) ∈ d) :
      (code φ 2 (ci+3) 1 (oi+3) 0
        (fun i => truncate (bound φ+1) v i+3) (pi+3)).Eval
          (cons f (cons k (cons d env))) ↔ Forces e φ p := by
    let e' := truncate (bound φ+1) e
    have he' (i) : (e' i).encode (label c) ∈ d := by
      dsimp only [e',truncate]
      split
      · exact hs i (by assumption)
      · exact hs 0 (by omega)
    have ht (i) : env (truncate (bound φ+1) v i) = (e' i).encode (label c) := by
      dsimp only [e',truncate]
      split <;> exact hv _
    exact (eval_code φ hd ho hf e' he' p (cons f (cons k (cons d env)))
      2 (ci+3) 1 (oi+3) 0 (fun i => truncate (bound φ+1) v i+3) (pi+3)
      ⟨rfl,hc,hk,ho',rfl,hp⟩ ht).trans
      (forces_congr φ e' e (fun i hi => ite_eq_left (by omega)) p)
  simp only [CertificateCode.matrix,Formula.Eval,Formula.eval_transitive,
    AtomicFormula.eval_product,CertificateCode.eval_slots,cons_zero,cons_succ,hv]
  constructor
  · rintro ⟨hd,hk,hgraph,hs,hquery⟩
    have hf : Graph d c o f := by
      have h := (AtomicFormula.eval_graph 2 (ci+3) 1 (oi+3) 0 _ hk).mp hgraph
      simpa only [cons_zero,cons_succ,hc,ho'] using h
    exact ⟨hd,hk,hf,hs,(query hd hk hf hs).mp hquery⟩
  · rintro ⟨hd,hk,hf,hs,hq⟩
    refine ⟨hd,hk,?_,hs,(query hd hk hf hs).mpr hq⟩
    apply (AtomicFormula.eval_graph 2 (ci+3) 1 (oi+3) 0 _ hk).mpr
    simpa only [cons_zero,cons_succ,hc,ho'] using hf

theorem realize_boundedCertificate (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M)
    {o : ZFSet.{u}}
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (φ : Formula) (e : ℕ → Name (Conditions c)) (p : Conditions c)
    (env : ℕ → ZFSet.{u}) (henv : ∀ i, env i ∈ M)
    (ci oi pi : ℕ) (v : ℕ → ℕ)
    (hc : env ci = c) (ho' : env oi = o) (hp : env pi = label c p)
    (hv : ∀ i, env (v i) = (e i).encode (label c)) :
    (CertificateCode.certificate φ ci oi pi v).Realize M env ↔ Forces e φ p := by
  have matrix (d k f : ZFSet.{u}) (hd : d ∈ M) (hk : k ∈ M) (hf : f ∈ M) :=
    (Formula.absolute (CertificateCode.matrix φ ci oi pi v) M hM
      (cons f (cons k (cons d env))) (by
        intro i; rcases i with _|i; exact hf
        rcases i with _|i; exact hk
        rcases i with _|i; exact hd
        exact henv i)).trans (eval_certificate_matrix φ d k f o ho e p env ci oi pi v hc ho' hp hv)
  change (∃ d ∈ M, ∃ k ∈ M, ∃ f ∈ M, _) ↔ _
  constructor
  · rintro ⟨d,hd,k,hk,f,hf,hm⟩
    exact ((matrix d k f hd hk hf).mp hm).2.2.2.2
  · intro hforce
    have he (i) : (e i).encode (label c) ∈ M := hv i ▸ henv (v i)
    obtain ⟨d,hd,hdT,_,hs⟩ := finite_container M hM hP hU hS hR hI
      (fun i => (e i).encode (label c)) he (bound φ+1)
    have hk := product_mem M hM hP hU hPow hS hd hd
    obtain ⟨f,hf,hfG⟩ := internal_atomic_graph M hM hP hU hPow hS hd
      (hc ▸ henv ci) (ho' ▸ henv oi)
    exact ⟨d,hd,_,hk,f,hf,(matrix d _ f hd hk hf).mpr ⟨hdT,rfl,hfG,hs,hforce⟩⟩

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SigmaDefinability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing
universe u

namespace SigmaCode

def forcing : SigmaFormula → ℕ → ℕ → ℕ → (ℕ → ℕ) → SigmaFormula
  | .bounded φ, ci,oi,pi,v => CertificateCode.certificate φ ci oi pi v
  | .existsSet φ, ci,oi,pi,v => .existsSet
      (SigmaFormula.conj (NameValidity.Code.valid (ci+1) 0)
        (forcing φ (ci+1) (oi+1) (pi+1) (push 0 (fun i => v i+1))))
end SigmaCode

end TuringRigidity.BoundedForcing

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

def hullMemberFormula : Formula :=
  .allMem 2 (.imp (.conj (.transitive 0) (.member 2 0)) (.member 1 0))

end TuringRigidity.BoundedSetTheory

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

variable {X : Type*} [MeasurableSpace X]
variable (R : X → ℕ → ℕ → Prop)
variable (hd : ∀ x n s, ∃ t, Ext s t ∧ R x n t)

noncomputable def generic (x : X) : Oracle :=
  fun i => (word (stage R hd (i+1) x)).getD i false

def Meets (A : Oracle) (s : ℕ) : Prop :=
  ∀ i, i < (word s).length → A i = (word s).getD i false

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

noncomputable def cut (x : ℝ) : Oracle := fun n => decide ((rationalEnumeration n : ℝ) < x)

@[simp] theorem cut_eq_true (x : ℝ) (n : ℕ) :
    cut x n = true ↔ (rationalEnumeration n : ℝ) < x := by simp [cut]

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_BinarySeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BinarySeries

def bit (B : Oracle) (n : ℕ) : ℕ := if B n then 1 else 0

def digits (B : Oracle) (n : ℕ) : Fin 2 := ⟨bit B n, by unfold bit; split <;> omega⟩

noncomputable def value (B : Oracle) : ℝ := Real.ofDigits (digits B)

def numeral (B : Oracle) : ℕ → ℕ
  | 0 => 0
  | n+1 => 2 * numeral B n + bit B n

def Mixed (B : Oracle) : Prop := ∀ N, (∃ n, N ≤ n ∧ B n = true) ∧ (∃ n, N ≤ n ∧ B n = false)

end TuringRigidity.BinarySeries

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_RationalCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
open Encodable

namespace RationalCoding

def valid (n : ℕ) : Prop :=
  0 < (Nat.unpair n).2 ∧ (magnitude (Nat.unpair n).1).Coprime (Nat.unpair n).2

instance instDecidableValid (n : ℕ) : Decidable (valid n) := inferInstanceAs (Decidable (_ ∧ _))

def canonicalCode (n : ℕ) : ℕ := if valid n then n else encode (0 : ℚ)

def numeratorCode (n : ℕ) : ℕ := (Nat.unpair (canonicalCode n)).1
def numeratorMagnitude (n : ℕ) : ℕ := magnitude (numeratorCode n)
def denominator (n : ℕ) : ℕ := (Nat.unpair (canonicalCode n)).2
def negative (n : ℕ) : Bool := (numeratorCode n).bodd

end RationalCoding
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

def positiveNumerator (n : ℕ) : ℕ := if negative n then 0 else numeratorMagnitude n
def negativeNumerator (n : ℕ) : ℕ := if negative n then numeratorMagnitude n else 0

end RationalCoding

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
open UniformOracle RationalCoding Encodable

def fracLeft (z : ℕ × ℕ × ℕ) : ℕ := positiveNumerator z.1 * z.2.2
def fracRight (z : ℕ × ℕ × ℕ) : ℕ := z.2.1 * denominator z.1 + negativeNumerator z.1 * z.2.2

end TuringRigidity.BinarySeries

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

def BorelRepresentation : Prop :=
  ∀ π : Degree ≃o Degree, ∃ F : Oracle → Oracle,
    Measurable F ∧ ∀ A, degree (F A) = π (degree A)

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_BinaryCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BinarySeries
open UniformOracle RationalCoding Encodable Filter

def approxDecision (z : ℕ × ℕ × ℕ) : Option ℕ :=
  if fracLeft (z.1,z.2.2,2^z.2.1) < fracRight (z.1,z.2.2,2^z.2.1) then some 1
  else if fracRight (z.1,z.2.2+1,2^z.2.1) < fracLeft (z.1,z.2.2+1,2^z.2.1) then some 0
  else none

def approxTrial (B : Oracle) (q n : ℕ) : Option ℕ := approxDecision (q,n,numeral B n)

end TuringRigidity.BinarySeries

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_BinaryRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BinarySeries
open UniformOracle RationalCoding Encodable

def recoverGuard (z : ℕ × ℕ × ℕ × ℕ) : Prop :=
  fracLeft (z.2.2.1,z.2.1,2^(z.1+1)) = fracRight (z.2.2.1,z.2.1,2^(z.1+1)) ∧
  fracLeft (z.2.2.2,z.2.1+1,2^(z.1+1)) = fracRight (z.2.2.2,z.2.1+1,2^(z.1+1))
instance instDecidableRecoverGuard (z : ℕ × ℕ × ℕ × ℕ) : Decidable (recoverGuard z) := inferInstanceAs (Decidable (_ ∧ _))

def recoverDecision (z : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ)) : Option ℕ :=
  if recoverGuard z.1 ∧ z.2.1=1 ∧ z.2.2=0 then some (z.1.2.1%2) else none

noncomputable def recoverTrial (B : Oracle) (n m : ℕ) : Option ℕ :=
  let k := (Nat.unpair m).1
  let i := (Nat.unpair (Nat.unpair m).2).1
  let j := (Nat.unpair (Nat.unpair m).2).2
  recoverDecision ((n,k,i,j),(bit (cut (value B)) i,bit (cut (value B)) j))

end TuringRigidity.BinarySeries

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_AutomorphismName
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AutomorphismName
open Set CountableForcing
variable {P Q α : Type*} [Preorder P] [Preorder Q]

def mapFilter (e : P ≃o Q) (G : GenericFilter P) : GenericFilter Q where
  carrier := {q | e.symm q ∈ G.carrier}
  nonempty := by
    obtain ⟨p,hp⟩ := G.nonempty
    exact ⟨e p,by simpa using hp⟩
  upper := fun hpq hp => G.upper (e.symm.monotone hpq) hp
  directed := by
    intro p q hp hq
    obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
    exact ⟨e r,by simpa using hr,by simpa using e.monotone hrp,by simpa using e.monotone hrq⟩

end TuringRigidity.AutomorphismName

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

def SigmaSeparation (M : ZFSet.{u}) : Prop :=
  ∀ (φ : SigmaFormula) (e : ℕ → ZFSet.{u}), (∀ i, e i ∈ M) →
    ∀ a ∈ M, ∃ b ∈ M, ∀ x ∈ M, x ∈ b ↔ x ∈ a ∧ φ.Realize M (cons x e)

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

noncomputable def tag (n : ℕ) (x : ZFSet.{u}) : ZFSet.{u} := ZFSet.pair (natSet n) x

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
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]
namespace WitnessCode

def request (φ : SigmaFormula) : SigmaFormula :=
  .existsSet (.existsSet (SigmaFormula.andBounded (.orderedPair 3 1 0)
    (SigmaFormula.conj (NameValidity.Code.valid 4 2) (SigmaCode.forcing φ 4 5 0 vars))))
end WitnessCode

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_IntersectionName
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing
universe u

variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem internal_intersection_name (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G)
    (a b : Name (Conditions c)) (ha : a.encode (label c) ∈ M) (hb : b.encode (label c) ∈ M) :
    ∃ B ∈ M, B ⊆ a.support (label c) ∧
      (a.restrict (label c) B).val G.carrier = a.val G.carrier ∩ b.val G.carrier := by
  obtain ⟨d,hd,hdT,hdab⟩ := internal_transitive_container M hM hP hU hS hR hI
    (pair_mem M hM hP ha hb)
  have had : a.encode (label c) ∈ d := hdT _ hdab _ (ZFSet.mem_pair.mpr (Or.inl rfl))
  have hbd : b.encode (label c) ∈ d := hdT _ hdab _ (ZFSet.mem_pair.mpr (Or.inr rfl))
  have hai (i) : (a.child i).encode (label c) ∈ d := by
    apply names_childClosed d c hdT a had
    cases a
    exact ⟨i,rfl⟩
  obtain ⟨f,hf,hfG⟩ := internal_atomic_graph M hM hP hU hPow hS hd hc hoM
  let k := ZFSet.prod d d
  have hk : k ∈ M := product_mem M hM hP hU hPow hS hd hd
  let e := cons d (cons c (cons k (cons o (cons f (cons (b.encode (label c)) (fun _ => c))))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|i; exact hd
    rcases i with _|i; exact hc
    rcases i with _|i; exact hk
    rcases i with _|i; exact hoM
    rcases i with _|i; exact hf
    rcases i with _|i; exact hb
    exact hc
  let φ := AtomicFormula.select 1 2 3 4 5 6 0
  let B := ZFSet.sep (fun z => φ.Eval (cons z e)) (a.support (label c))
  have hBM : B ∈ M := sep_mem M hM hS φ e he (support_mem M hM hP hU hPow hS hc hoM ho a ha)
  have hBsub : B ⊆ a.support (label c) := fun z hz => (ZFSet.mem_sep.mp hz).1
  have hB (i : a.arity) (q : Conditions c) (hq : q ≤ a.tag i) :
      ZFSet.pair ((a.child i).encode (label c)) (label c q) ∈ B ↔ Witness (a.child i) b q := by
    have hs : ZFSet.pair ((a.child i).encode (label c)) (label c q) ∈ a.support (label c) :=
      ZFSet.mem_range.mpr ⟨⟨i,⟨q,hq⟩⟩,rfl⟩
    change _ ∈ ZFSet.sep _ _ ↔ _
    rw [ZFSet.mem_sep,and_iff_right hs]
    change (AtomicFormula.select 1 2 3 4 5 6 0).Eval (cons _ e) ↔ _
    rw [AtomicFormula.eval_select]
    change (∃ x ∈ d, ∃ r ∈ c,
      ZFSet.pair ((a.child i).encode (label c)) (label c q) = ZFSet.pair x r ∧
        CodeWitness d c k o f x (b.encode (label c)) r) ↔ _
    constructor
    · rintro ⟨x,hx,r,hr,hxr,hw⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hxr
      exact (codeWitness_iff hdT ho hfG _ b (hai i) hbd q).mp hw
    · intro hw
      exact ⟨_,hai i,_,label_mem c q,rfl,(codeWitness_iff hdT ho hfG _ b (hai i) hbd q).mpr hw⟩
  have hg := groundGeneric_atomic M hM hP hU hPow hS hR hI hc hoM ho G hG
  have hiM (i) : a.child i ∈ names M c := by
    apply names_childClosed M c hM a ha
    cases a
    exact ⟨i,rfl⟩
  refine ⟨B,hBM,hBsub,?_⟩
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_inter]
  constructor
  · intro hx
    have hxa := a.val_restrict_subset (label c) B G hx
    obtain ⟨i,q,hqi,hqb,hqG,hix⟩ := (a.mem_val_restrict (label c) B G.carrier x).mp hx
    have hw := (hB i q hqi).mp hqb
    have hxb := (mem_truth (names_childClosed M c hM) G hg _ b (hiM i) hb).mpr
      ⟨q,hqG,witness_mem _ _ q hw⟩
    exact ⟨hxa,hix ▸ hxb⟩
  · rintro ⟨hxa,hxb⟩
    obtain ⟨i,hi,hix⟩ := (a.mem_val_children G.carrier x).mp hxa
    have hmem : (a.child i).val G.carrier ∈ b.val G.carrier := hix ▸ hxb
    obtain ⟨p,hp,hm⟩ := (mem_truth (names_childClosed M c hM) G hg _ b (hiM i) hb).mp hmem
    obtain ⟨q,hq,hw⟩ := generic_witness hg (hiM i) hb hp hm
    obtain ⟨r,hr,hrq,hri⟩ := G.directed hq hi
    exact (a.mem_val_restrict (label c) B G.carrier x).mpr
      ⟨i,r,hri,(hB i r hri).mpr (witness_mono _ _ hrq hw),hr,hix⟩

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ExtensionPowerSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]

noncomputable def powerName (a : Name (Conditions c)) (W : ZFSet.{u}) : Name (Conditions c) :=
  .mk (Conditions W) (fun s => a.restrict (label c) (label W s)) (fun _ => ⊤)

theorem encode_powerName (a : Name (Conditions c)) (W : ZFSet.{u})
    (hW : ∀ B ∈ W, B ⊆ a.support (label c)) :
    (powerName a W).encode (label c) = ZFSet.prod W ({label c ⊤} : ZFSet.{u}) := by
  apply ZFSet.ext
  intro z
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨s,hs⟩
    rw [Name.encode_restrict _ _ _ (hW _ (label_mem W s))] at hs
    exact ZFSet.mem_prod.mpr ⟨_,label_mem W s,_,ZFSet.mem_singleton.mpr rfl,hs.symm⟩
  · intro hz
    obtain ⟨B,hB,t,ht,hz⟩ := ZFSet.mem_prod.mp hz
    obtain rfl := ZFSet.mem_singleton.mp ht
    obtain ⟨s,rfl⟩ := label_surjective W hB
    exact ⟨s,by rw [Name.encode_restrict _ _ _ (hW _ hB)]; exact hz.symm⟩

theorem mem_val_powerName (a : Name (Conditions c)) (W : ZFSet.{u})
    (G : Set (Conditions c)) (hG : ⊤ ∈ G) (x : ZFSet.{u}) :
    x ∈ (powerName a W).val G ↔ ∃ B ∈ W, (a.restrict (label c) B).val G = x := by
  rw [powerName,Name.mem_val]
  constructor
  · rintro ⟨s,_,hs⟩
    exact ⟨_,label_mem W s,hs⟩
  · rintro ⟨B,hB,hx⟩
    obtain ⟨s,rfl⟩ := label_surjective W hB
    exact ⟨s,hG,hx⟩

theorem extension_powerSet (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (htop : ⊤ ∈ G.carrier) :
    PowerSet (genericExtensionSet M c G.carrier) := by
  intro x hx
  obtain ⟨a,ha,rfl⟩ := (mem_extensionSet M c G.carrier x).mp hx
  have hsupport := support_mem M hM hP hU hPow hS hc hoM ho a ha
  obtain ⟨W,hW,hWdef⟩ := internal_power M hM hPow hsupport
  have hWsub : ∀ B ∈ W, B ⊆ a.support (label c) := fun B hB => ((hWdef B).mp hB).2
  have hpower : (powerName a W).encode (label c) ∈ M := by
    rw [encode_powerName a W hWsub]
    exact product_mem M hM hP hU hPow hS hW
      (singleton_mem M hM hP (hM c hc _ (label_mem c ⊤)))
  refine ⟨(powerName a W).val G.carrier,(mem_extensionSet M c G.carrier _).mpr
    ⟨_,hpower,rfl⟩,?_⟩
  intro z hz
  constructor
  · intro hzPower y _ hyz
    obtain ⟨B,hB,hBz⟩ := (mem_val_powerName a W G.carrier htop z).mp hzPower
    rw [←hBz] at hyz
    exact a.val_restrict_subset (label c) B G hyz
  · intro hsub
    obtain ⟨b,hb,rfl⟩ := (mem_extensionSet M c G.carrier z).mp hz
    have hba : b.val G.carrier ⊆ a.val G.carrier := fun y hy => hsub y
      (genericExtensionSet_transitive M c hM G.carrier _
        ((mem_extensionSet M c G.carrier _).mpr ⟨b,hb,rfl⟩) y hy) hy
    obtain ⟨B,hBM,hBS,hBval⟩ := internal_intersection_name M hM hP hU hPow hS hR hI hc hoM ho G hG a b ha hb
    apply (mem_val_powerName a W G.carrier htop _).mpr
    refine ⟨B,(hWdef B).mpr ⟨hBM,hBS⟩,hBval.trans ?_⟩
    apply ZFSet.ext
    intro y
    rw [ZFSet.mem_inter]
    exact ⟨And.right,fun hy => ⟨hba hy,hy⟩⟩

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_NameValueCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}}

noncomputable def coverChild (W : ZFSet.{u})
    (hW : ∀ x ∈ W, ∃ a : Name (Conditions c), a.encode (label c) = x)
    (i : Conditions W) : Name (Conditions c) := (hW _ (label_mem W i)).choose

theorem coverChild_code (W : ZFSet.{u})
    (hW : ∀ x ∈ W, ∃ a : Name (Conditions c), a.encode (label c) = x) (i : Conditions W) :
    (coverChild W hW i).encode (label c) = label W i := (hW _ (label_mem W i)).choose_spec

noncomputable def coverName (W : ZFSet.{u})
    (hW : ∀ x ∈ W, ∃ a : Name (Conditions c), a.encode (label c) = x)
    (p : Conditions c) : Name (Conditions c) := .mk (Conditions W) (coverChild W hW) (fun _ => p)

theorem encode_coverName (W : ZFSet.{u})
    (hW : ∀ x ∈ W, ∃ a : Name (Conditions c), a.encode (label c) = x) (p : Conditions c) :
    (coverName W hW p).encode (label c) = ZFSet.prod W ({label c p} : ZFSet.{u}) := by
  apply ZFSet.ext; intro z
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨i,rfl⟩
    rw [coverChild_code]
    exact ZFSet.mem_prod.mpr ⟨_,label_mem W i,_,ZFSet.mem_singleton.mpr rfl,rfl⟩
  · intro hz
    obtain ⟨x,hx,y,hy,rfl⟩ := ZFSet.mem_prod.mp hz
    obtain rfl := ZFSet.mem_singleton.mp hy
    obtain ⟨i,rfl⟩ := label_surjective W hx
    exact ⟨i,by rw [coverChild_code]⟩

end TuringRigidity.BoundedForcing

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

inductive LevySigma where
  | bounded (φ : Formula)
  | conj (φ ψ : LevySigma)
  | disj (φ ψ : LevySigma)
  | existsSet (φ : LevySigma)
  | existsMem (a : ℕ) (φ : LevySigma)
  | allMem (a : ℕ) (φ : LevySigma)

namespace LevySigma
def Realize (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) : LevySigma → Prop
  | .bounded φ => φ.Realize M e
  | .conj φ ψ => φ.Realize M e ∧ ψ.Realize M e
  | .disj φ ψ => φ.Realize M e ∨ ψ.Realize M e
  | .existsSet φ => ∃ x ∈ M, φ.Realize M (cons x e)
  | .existsMem a φ => ∃ x ∈ M, x ∈ e a ∧ φ.Realize M (cons x e)
  | .allMem a φ => ∀ x ∈ M, x ∈ e a → φ.Realize M (cons x e)

end LevySigma

def LevySigmaSeparation (M : ZFSet.{u}) : Prop :=
  ∀ (φ : LevySigma) (e : ℕ → ZFSet.{u}), (∀ i, e i ∈ M) → ∀ a ∈ M,
    ∃ b ∈ M, ∀ x ∈ M, x ∈ b ↔ x ∈ a ∧ φ.Realize M (cons x e)

def LevySigmaReplacement (M : ZFSet.{u}) : Prop :=
  ∀ (φ : LevySigma) (e : ℕ → ZFSet.{u}), (∀ i, e i ∈ M) → ∀ a ∈ M,
    (∀ x ∈ a, ∃ y ∈ M, φ.Realize M (cons y (cons x e)) ∧
      ∀ z ∈ M, φ.Realize M (cons z (cons x e)) → z = y) →
    ∃ b ∈ M, ∀ y ∈ M, y ∈ b ↔ ∃ x ∈ a, φ.Realize M (cons y (cons x e))

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_SourceTheory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

structure SourceT (M : ZFSet.{u}) : Prop where
  extensionality : BasicAxioms.Extensionality M
  empty : BasicAxioms.EmptySet M
  pairing : Pairing M
  union : BoundedSetTheory.Union M
  powerSet : PowerSet M
  infinity : Infinity M
  foundation : BasicAxioms.Foundation M
  choice : Choice M
  separation : LevySigmaSeparation M
  replacement : LevySigmaReplacement M

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BoundedDecoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedDecoding
open AntichainParameters SetCoding RelationCoding

def AntichainBelow (p : AntichainCode) (y : Degree) : Prop :=
  p.bound ≤ y ∧ p.left ≤ y ∧ p.right ≤ y

def LocalNontrivial (y b g₀ g₁ x : Degree) : Prop :=
  x ≤ b ∧ ∃ z : Degree, z ≤ y ∧ z ≤ g₀ ⊔ x ∧ z ≤ g₁ ⊔ x ∧ ¬ z ≤ x

def LocalAntichain (y : Degree) (p : AntichainCode) (x : Degree) : Prop :=
  LocalNontrivial y p.bound p.left p.right x ∧
    ∀ w : Degree, w ≤ y → LocalNontrivial y p.bound p.left p.right w →
      w ≤ x → x ≤ w

def SetBelow (p : SetCode) (y : Degree) : Prop :=
  p.bound ≤ y ∧ AntichainBelow p.tags y ∧ AntichainBelow p.decorated y

def RelationBelow {n : ℕ} (p : RelationCode n) (y : Degree) : Prop :=
  (∀ i, SetBelow (p.coordinates i) y) ∧ AntichainBelow p.tuples y

end TuringRigidity.BoundedDecoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedDecoding
open SetCoding RelationCoding ArithmeticModelDecoding

def unary (p : SetCode) : RelationCode 1 := ⟨fun _ => p,p.tags⟩

end TuringRigidity.BoundedDecoding

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
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions
universe u
noncomputable section

def Definable (M : ZFSet.{u}) (P : (ℕ → ZFSet.{u}) → Prop) : Prop :=
  ∃ p : Formula, ∃ d : ℕ → ZFSet.{u}, (∀ i, d i ∈ M) ∧
    ∀ e, p.Eval (mix e d) ↔ P e

end
end TuringRigidity.BoundedDefinability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SigmaParameterized
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedDefinability
open BoundedSetTheory TransitiveNameModel SetModelFunctions
universe u

def SigmaDefinable (M : ZFSet.{u}) (P : (ℕ → ZFSet.{u}) → Prop) : Prop :=
  ∃ p : SigmaFormula, ∃ d : ℕ → ZFSet.{u}, (∀ i, d i ∈ M) ∧
    ∀ e, (∀ i, e i ∈ M) → (p.Realize M (mix e d) ↔ P e)

end TuringRigidity.BoundedDefinability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformSigmaDefinability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedDefinability
open BoundedSetTheory TransitiveNameModel SetModelFunctions
universe u

def UniformSigmaDefinable (M : ZFSet.{u})
    (P : ZFSet.{u} → (ℕ → ZFSet.{u}) → Prop) : Prop :=
  ∃ p : SigmaFormula, ∃ d : ℕ → ZFSet.{u}, (∀ i, d i ∈ M) ∧
    ∀ E : ZFSet.{u}, Transitive E → SourceT E → M ⊆ E →
      ∀ e, (∀ i, e i ∈ E) → (p.Realize E (mix e d) ↔ P E e)

end TuringRigidity.BoundedDefinability

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

def Sat (D : Set ZFSet.{u}) (e : ℕ → ZFSet.{u}) : SentenceForm → Prop
  | .equal i j => e i = e j
  | .member i j => e i ∈ e j
  | .conj p q => p.Sat D e ∧ q.Sat D e
  | .neg p => ¬ p.Sat D e
  | .ex p => ∃ x ∈ D, p.Sat D (cons x e)

@[simp] theorem sat_disj (p q : SentenceForm) (D : Set ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (disj p q).Sat D e ↔ p.Sat D e ∨ q.Sat D e := by classical simp only [disj,Sat]; tauto
@[simp] theorem sat_imp (p q : SentenceForm) (D : Set ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (imp p q).Sat D e ↔ (p.Sat D e → q.Sat D e) := by classical simp [imp,Sat]
@[simp] theorem sat_iff (p q : SentenceForm) (D : Set ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (iff p q).Sat D e ↔ (p.Sat D e ↔ q.Sat D e) := by simp [iff,Sat,iff_def]
@[simp] theorem sat_all (p : SentenceForm) (D : Set ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (all p).Sat D e ↔ ∀ x ∈ D, p.Sat D (cons x e) := by classical simp [all,Sat]

end SentenceForm

end TuringRigidity.ElementaryModel

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

noncomputable def realCode (A : Oracle) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∃ n, x = natSet n ∧ A n = true) ZFSet.omega

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelDegreeCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

noncomputable def degreeCode (R : ZFSet.{u}) (A : Oracle) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ B : Oracle, z = realCode B ∧ degree B = degree A) R

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

noncomputable def degreeUniverse (R : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun D => ∃ A : Oracle, realCode A ∈ R ∧ D = degreeCode R A) (ZFSet.powerset R)

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

def degreeCodeLE (D E : ZFSet.{u}) : Prop :=
  ∃ A B : Oracle, realCode A ∈ D ∧ realCode B ∈ E ∧ Reduces A B

noncomputable def degreeOrder (R : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun p => ∃ D ∈ degreeUniverse R, ∃ E ∈ degreeUniverse R,
    p = ZFSet.pair D E ∧ degreeCodeLE D E) (ZFSet.prod (degreeUniverse R) (degreeUniverse R))

end TuringRigidity.BoundedSetTheory

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

def negFormula (c U V : ℕ) : Formula :=
  .conj (.subset V c) (.allMem c (.iff (.member 0 (V+1))
    (.allMem (U+1) (.neg (.subset 1 0)))))

def supFormula (c F V : ℕ) : Formula :=
  .conj (.subset V c) (.allMem c (.iff (.member 0 (V+1))
    (.allMem (c+1) (.imp (.subset 1 0)
      (.existsMem (F+2) (.existsMem 0 (.subset 2 0)))))))

end TuringRigidity.InternalBooleanSyntax

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_HomogeneousDegreeExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open RelativeConstructible SetModelSatisfaction
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

def OwnDegreeExtension (E I ρ f : ZFSet.{0}) : Prop :=
  IsAction f (degreeUniverse (groundReals E)) (degreeOrder (groundReals E)) ∧
    I ⊆ degreeUniverse (groundReals E) ∧ ρ ⊆ f

def degreeExtensionFormula : BoundedSetTheory.Formula :=
  .conj (actionFormula 0 1 2) (.conj (.subset 3 1) (.subset 4 0))

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BooleanExpressionCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BooleanExpressionCertificate
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalBooleanGeneric CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

def Step (c B Q S K g t U : ZFSet.{0}) : Prop :=
  (U ∈ S ∧ t = FiniteTerm.tag 0 U) ∨
  (∃ s ∈ K, ∃ V ∈ B, t = FiniteTerm.tag 1 s ∧
    ZFSet.pair s V ∈ g ∧ U = neg c V) ∨
  (∃ T ∈ K, ∃ F ∈ Q, t = FiniteTerm.tag 2 T ∧ U = supCode c F ∧
    (∀ s ∈ T, ∃ V ∈ F, ZFSet.pair s V ∈ g) ∧
    (∀ V ∈ F, ∃ s ∈ T, ZFSet.pair s V ∈ g))

def Certificate (c B Q S K g : ZFSet.{0}) : Prop :=
  ∀ z ∈ g, ∃ t ∈ K, ∃ U ∈ B, z = ZFSet.pair t U ∧ Step c B Q S K g t U

end TuringRigidity.BooleanExpressionCertificate

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BooleanExpressionSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BooleanExpressionCertificate
open TransitiveNameModel BoundedSetTheory InternalBooleanSyntax

def stepFormula (c B Q S K g t U z0 z1 z2 : ℕ) : Formula :=
  .disj (.conj (.member U S) (.orderedPair t z0 U))
    (.disj
      (.existsMem K (.existsMem (B+1)
        (.conj (.orderedPair (t+2) (z1+2) 1)
          (.conj (.pairMem 1 0 (g+2)) (negFormula (c+2) 0 (U+2))))))
      (.existsMem K (.existsMem (Q+1)
        (.conj (.orderedPair (t+2) (z2+2) 1)
          (.conj (supFormula (c+2) 0 (U+2))
            (.conj (.allMem 1 (.existsMem 1 (.pairMem 1 0 (g+4))))
              (.allMem 0 (.existsMem 2 (.pairMem 0 1 (g+4))))))))))

def certificateFormula (c B Q S K g z0 z1 z2 : ℕ) : Formula :=
  .allMem g (.existsMem (K+1) (.existsMem (B+2)
    (.conj (.orderedPair 2 1 0)
      (stepFormula (c+3) (B+3) (Q+3) (S+3) (K+3) (g+3) 1 0 (z0+3) (z1+3) (z2+3)))))

def Witness (c B Q S K U : ZFSet.{0}) : Prop :=
  Transitive K ∧ ∃ g ∈ K, Certificate c B Q S K g ∧
    ∃ t ∈ K, ZFSet.pair t U ∈ g

def witnessFormula (c B Q S K U z0 z1 z2 : ℕ) : Formula :=
  .conj (.allMem K (.subset 0 (K+1)))
    (.existsMem K (.conj
      (certificateFormula (c+1) (B+1) (Q+1) (S+1) (K+1) 0 (z0+1) (z1+1) (z2+1))
      (.existsMem (K+1) (.pairMem 0 (U+2) 1))))

def parameters (c B Q S : ZFSet.{0}) : ℕ → ZFSet.{0} :=
  cons c (cons B (cons Q (cons S (cons (natSet 0) (cons (natSet 1) (fun _ => natSet 2))))))

def witnessBody : Formula := witnessFormula 2 3 4 5 0 1 6 7 8

noncomputable def certified (M c B Q S : ZFSet.{0}) : ZFSet.{0} :=
  B.sep (fun U => ∃ K ∈ M, Witness c B Q S K U)

end TuringRigidity.BooleanExpressionCertificate

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

noncomputable def goodGraphs (a c B Q S K : ZFSet.{0}) : ZFSet.{0} :=
  a.sep (Certificate c B Q S K)

end TuringRigidity.BooleanExpressionCertificate

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

def body (B R t : ZFSet.{0}) (rec : ∀ s : ZFSet.{0}, ZFSet.rank s < ZFSet.rank t → Prop) : Prop :=
  (∃ U ∈ B, t = FiniteTerm.tag 0 U ∧ U ∈ R) ∨
  (∃ s, ∃ h : t = FiniteTerm.tag 1 s,
    ¬ rec s (by rw [h]; exact FiniteTerm.pair_rank_right _ _)) ∨
  (∃ T, ∃ h : t = FiniteTerm.tag 2 T, ∃ s, ∃ hs : s ∈ T,
    rec s (by rw [h]; exact (ZFSet.rank_lt_of_mem hs).trans (FiniteTerm.pair_rank_right _ _)))

noncomputable def value (B R : ZFSet.{0}) : ZFSet.{0} → Prop := rankWF.fix (body B R)

def step (K B R Y t : ZFSet.{0}) : Prop :=
  (∃ U ∈ B, t = FiniteTerm.tag 0 U ∧ U ∈ R) ∨
  (∃ s ∈ K, t = FiniteTerm.tag 1 s ∧ s ∉ Y) ∨
  (∃ T ∈ K, t = FiniteTerm.tag 2 T ∧ ∃ s ∈ T, s ∈ Y)

def formula : Formula :=
  .disj (.existsMem 3 (.conj (.orderedPair 1 6 0) (.member 0 5)))
    (.disj (.existsMem 2 (.conj (.orderedPair 1 7 0) (.neg (.member 0 2))))
      (.existsMem 2 (.conj (.orderedPair 1 8 0) (.existsMem 0 (.member 0 3)))))

def parameters (K B R : ZFSet.{0}) : ℕ → ZFSet.{0} :=
  cons K (cons B (cons R (cons (natSet 0) (cons (natSet 1) (fun _ => natSet 2)))))

noncomputable def valueSet (K B R : ZFSet.{0}) : ZFSet.{0} := K.sep (value B R)

end TuringRigidity.BooleanExpressionTruth

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BooleanTruthReading
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BooleanExpressionTruth
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalBooleanBits InternalBooleanGeneric
open BooleanExpressionCertificate
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def seedTruth (c B : ZFSet.{0}) (E : ℕ → ZFSet.{0}) (X : ZFSet.{0}) : ZFSet.{0} :=
  B.sep (fun U => ∃ n, natSet n ∈ X ∧ U = bitCode c (E n))

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

def GoodTruth (K B R Y : ZFSet.{0}) : Prop :=
  Y ⊆ K ∧ ∀ t ∈ K, t ∈ Y ↔ step K B R Y t

def Evaluated (c B Q S R K Y U : ZFSet.{0}) : Prop :=
  Transitive K ∧ GoodTruth K B R Y ∧ ∃ g ∈ K, Certificate c B Q S K g ∧
    ∃ t ∈ K, ZFSet.pair t U ∈ g ∧ t ∈ Y

def truthAt (t Y K B R z0 z1 z2 : ℕ) : Formula := formula.rename (truthSlots t Y K B R z0 z1 z2)

def goodTruthFormula (K B R Y z0 z1 z2 : ℕ) : Formula :=
  .conj (.subset Y K) (.allMem K (.iff (.member 0 (Y+1))
    (truthAt 0 (Y+1) (K+1) (B+1) (R+1) (z0+1) (z1+1) (z2+1))))

def evaluatedFormula (c B Q S R K Y U z0 z1 z2 : ℕ) : Formula :=
  .conj (.transitive K) (.conj (goodTruthFormula K B R Y z0 z1 z2)
    (.existsMem K (.conj (certificateFormula (c+1) (B+1) (Q+1) (S+1) (K+1) 0 (z0+1) (z1+1) (z2+1))
      (.existsMem (K+1) (.conj (.pairMem 0 (U+2) 1) (.member 0 (Y+2)))))))

def evaluationParameters (W c B Q S R : ZFSet.{0}) : ℕ → ZFSet.{0} :=
  cons W (cons c (cons B (cons Q (cons S (cons R
    (cons (natSet 0) (cons (natSet 1) (fun _ => natSet 2))))))))

def evaluationBody : Formula := .existsMem 2 (evaluatedFormula 4 5 6 7 8 0 1 2 9 10 11)

end TuringRigidity.BooleanExpressionTruth

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BoundedAutomorphismOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open TransitiveNameModel BoundedSetTheory SetDegreeDecoding PersistentRestrictions
universe u

def boundedOutputFormula : Formula :=
  .existsMem 3 (.existsMem 4 (.conj (.member 3 1)
    (.conj (.member 4 0) (.pairMem 1 0 2))))

end TuringRigidity.BoundedForcing

end OAI
end


