-- Prove2me | Definitions.Def_OAIQ064A005
-- name    : OAIQ064A005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T00:32:47.772996+00:00
-- url     : https://prove2.me/theorems/a9cd5d64-2cfc-439e-b956-5514a73c4f94
-- title:
--   Definitions bundle OAIQ064A005 of the split of OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 126 declarations of OpenAI's Lean: 15 definitions, 1 inductive type or structure and 110 theorems. The definitions and types are `OAI.TuringRigidity.BoundedSetTheory.FiniteTerm.Certificate`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTerm.Eval`, `OAI.TuringRigidity.BoundedSetTheory.FiniteTerm.Step`, `OAI.TuringRigidity.BoundedSetTheory.SigmaFormula.matrix`, `OAI.TuringRigidity.BoundedSetTheory.SigmaFormula.prefixLength`, `OAI.TuringRigidity.BoundedSetTheory.SigmaFormula.scope`, `OAI.TuringRigidity.CategorySearch.pairOracle`, `OAI.TuringRigidity.InternalRank.rankCertificate`, `OAI.TuringRigidity.RecursiveNames.Name.union`, `OAI.TuringRigidity.RelationCollapse.Code.full`, `OAI.TuringRigidity.RelationCollapse.certificate`, `OAI.TuringRigidity.RelationCollapse.structureMap`, `OAI.TuringRigidity.RelationCollapse.value`, `OAI.TuringRigidity.TransitiveNameModel.NameCodeFormula.orderedName`, `OAI.TuringRigidity.TransitiveNameModel.checkCertificate`, `OAI.TuringRigidity.TransitiveNameModel.evaluationOutputFormula`.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DegreeRigidity_CohenForcing_ForcingWitnessCollection`, `DegreeRigidity_CohenForcing_SigmaForcing`, `DegreeRigidity_Computability_CutTranscript`, `DegreeRigidity_Constructibility_InternalRankRecursion`, `DegreeRigidity_Effective_FiniteCodeBound`, `DegreeRigidity_Effective_FiniteExtensionCode`, `DegreeRigidity_Effective_FiniteTuple`, `DegreeRigidity_Effective_TupleRelation`, `DegreeRigidity_OrdinalCodes_RankDefinability`, `DegreeRigidity_OrdinalCodes_RankGraphConstruction`, `DegreeRigidity_Representation_GroundInclusion`, `DegreeRigidity_SetModels_ChoiceFromOrdinalCover`, `DegreeRigidity_SetModels_ChoiceTraceFormula`, `DegreeRigidity_SetModels_CollapseCertificate`, `DegreeRigidity_SetModels_CollapseCoding`, `DegreeRigidity_SetModels_CollapseCollection`, `DegreeRigidity_SetModels_EvaluationNameCode`, `DegreeRigidity_SetModels_ExtensionBasicAxioms`, `DegreeRigidity_SetModels_ExtensionChoice`, `DegreeRigidity_SetModels_ExtensionSigmaSeparation`, `DegreeRigidity_SetModels_ExtensionWitnessCover`, `DegreeRigidity_SetModels_FiniteSkolem`, `DegreeRigidity_SetModels_GeneratedHull`, `DegreeRigidity_SetModels_InternalCheckRecursion`, `DegreeRigidity_SetModels_InternalChoice`, `DegreeRigidity_SetModels_InternalCoverInjection`, `DegreeRigidity_SetModels_InternalHartogs`, `DegreeRigidity_SetModels_InternalHull`, `DegreeRigidity_SetModels_InternalOrdinalEnumeration`, `DegreeRigidity_SetModels_InternalRelationCollapse`, `DegreeRigidity_SetModels_InternalStructureCollapse`, `DegreeRigidity_SetModels_InternalUniformization`, `DegreeRigidity_SetModels_NameEvaluationGraph`, `DegreeRigidity_SetModels_NameExtension`, `DegreeRigidity_SetModels_NameUnionCode`, `DegreeRigidity_SetModels_NameValueCover`, `DegreeRigidity_SetModels_OrderedNameCode`, `DegreeRigidity_SetModels_RecursiveNames`, `DegreeRigidity_SetModels_RelationCollapse`, `DegreeRigidity_SetModels_RelationHull`, `DegreeRigidity_SetModels_SkolemOperations`, `DegreeRigidity_SetModels_TransitiveNameModel`, `DegreeRigidity_Syntax_BoundedRelations`, `DegreeRigidity_Syntax_CheckGraphConstruction`, `DegreeRigidity_Syntax_FiniteTerm`, `DegreeRigidity_Syntax_SigmaCollection`, `DegreeRigidity_Syntax_SigmaDefinability`, `DegreeRigidity_Syntax_SigmaHull`, `DegreeRigidity_Syntax_SigmaInterpretation`, `DegreeRigidity_Syntax_SigmaSeparationName`, `DegreeRigidity_Syntax_TermCertificate`, `DegreeRigidity_Syntax_TermEvaluationGraph`, `DegreeRigidity_Syntax_TermFormula`, `DegreeRigidity_Syntax_TermFunctionality`.
--
--   **Imports.** It imports the published bundle `Def_DegreeRigidity`; the bundles `OAIQ064A002` and `OAIQ064A003` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ064A008`; the proofs of `OAI.TuringRigidity.ArithmeticTree.native_nonidentity_absolute`, `OAI.TuringRigidity.ArithmeticTree.native_persistence_absolute`, `OAI.TuringRigidity.RelativeConstructible.internal_hierarchyGraph_collection` and `OAI.TuringRigidity.RelativeConstructible.uniform_hierarchy_certificate`.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A002
import Definitions.Def_OAIQ064A003

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

theorem val_checkPSet [Top P] (G : Set P) (hG : ⊤ ∈ G) (x : PSet.{u}) :
    val G (checkPSet x : Name P) = ZFSet.mk x := by
  induction x with
  | mk ι child ih =>
    apply ZFSet.ext
    intro y
    induction y using Quotient.inductionOn with
    | h y =>
      change ZFSet.mk y ∈ val G (.mk ι (fun index => checkPSet (child index))
        (fun _ => ⊤)) ↔ ZFSet.mk y ∈ ZFSet.mk (.mk ι child)
      rw [mem_val]
      simp only [hG, true_and, ih]
      change (∃ i, ZFSet.mk (child i) = ZFSet.mk y) ↔
        ∃ i, PSet.Equiv y (child i)
      simp only [ZFSet.eq]
      exact exists_congr (fun i => PSet.Equiv.comm)

theorem val_check [Top P] (G : Set P) (hG : ⊤ ∈ G) (x : ZFSet.{u}) :
    val G (check x : Name P) = x := by
  rw [check, val_checkPSet G hG, ZFSet.mk_out]

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

theorem ground_subset_extension [Top P] (M : Set (Name P)) (V : Set ZFSet.{u})
    (hM : ∀ x ∈ V, Name.check x ∈ M) (G : Set P) (hG : ⊤ ∈ G) :
    V ⊆ extension M G := fun x hx => ⟨Name.check x,hM x hx,Name.val_check G hG x⟩

namespace Name

theorem val_pair [Top P] (G : Set P) (hG : ⊤ ∈ G) (σ τ : Name P) :
    val G (pair σ τ) = ({val G σ,val G τ} : ZFSet.{u}) := by
  apply ZFSet.ext
  intro x
  simp only [pair,mem_val,hG,true_and,ZFSet.mem_pair]
  constructor
  · rintro ⟨⟨b⟩,hb⟩
    cases b
    · exact Or.inr hb.symm
    · exact Or.inl hb.symm
  · rintro (h|h)
    · exact ⟨⟨true⟩,h.symm⟩
    · exact ⟨⟨false⟩,h.symm⟩

def union [Preorder P] (τ : Name P) : Name P :=
  .mk (Σ i : arity τ, Σ j : arity (child τ i),
      {p : P // p ≤ tag τ i ∧ p ≤ tag (child τ i) j})
    (fun t => child (child τ t.1) t.2.1) (fun t => t.2.2.val)

theorem val_union [Preorder P] (G : GenericFilter P) (τ : Name P) :
    val G.carrier (union τ) = ZFSet.sUnion (val G.carrier τ) := by
  apply ZFSet.ext
  intro x
  rw [union,mem_val,ZFSet.mem_sUnion]
  constructor
  · rintro ⟨⟨i,j,p,hpi,hpj⟩,hp,hx⟩
    refine ⟨val G.carrier (child τ i),?_,?_⟩
    · exact (mem_val_children _ _ _).mpr ⟨i,G.upper hpi hp,rfl⟩
    · exact (mem_val_children _ _ _).mpr ⟨j,G.upper hpj hp,hx⟩
  · rintro ⟨y,hy,hx⟩
    obtain ⟨i,hi,rfl⟩ := (mem_val_children _ _ _).mp hy
    obtain ⟨j,hj,hx⟩ := (mem_val_children _ _ _).mp hx
    obtain ⟨p,hp,hpi,hpj⟩ := G.directed hi hj
    exact ⟨⟨i,j,p,hpi,hpj⟩,hp,hx⟩

end Name

end TuringRigidity.RecursiveNames

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

theorem ground_subset (M p : ZFSet.{u}) [Top (Conditions p)]
    (hcheck : ∀ x ∈ M, Name.encode (label p) (Name.check x) ∈ M)
    (G : Set (Conditions p)) (hG : ⊤ ∈ G) :
    (M : Set ZFSet.{u}) ⊆ genericExtension M p G :=
  ground_subset_extension _ _ hcheck G hG

end TuringRigidity.TransitiveNameModel

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

theorem replacement_image (M : ZFSet.{u}) (hM : Transitive M)
    (hR : SigmaReplacement M) (φ : SigmaFormula) (e : ℕ → ZFSet.{u})
    (he : ∀ i, e i ∈ M) {a : ZFSet.{u}} (ha : a ∈ M)
    (F : ZFSet.{u} → ZFSet.{u}) (hF : ∀ x ∈ a, F x ∈ M)
    (hφ : ∀ x ∈ a, ∀ y ∈ M, φ.Realize M (cons y (cons x e)) ↔ y = F x) :
    ∃ b ∈ M, ∀ y, y ∈ b ↔ ∃ x ∈ a, F x = y := by
  obtain ⟨b,hb,hbdef⟩ := hR φ e he a ha (fun x hx =>
    ⟨F x,hF x hx,(hφ x hx _ (hF x hx)).mpr rfl,
      fun z hz h => (hφ x hx z hz).mp h⟩)
  refine ⟨b,hb,fun y => ?_⟩
  constructor
  · intro hy
    have hyM := hM b hb y hy
    obtain ⟨x,hx,hxy⟩ := (hbdef y hyM).mp hy
    exact ⟨x,hx,((hφ x hx y hyM).mp hxy).symm⟩
  · rintro ⟨x,hx,rfl⟩
    exact (hbdef _ (hF x hx)).mpr ⟨x,hx,(hφ x hx _ (hF x hx)).mpr rfl⟩

end TuringRigidity.BoundedSetTheory

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

theorem space_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) {d : ZFSet.{u}} (hd : d ∈ M) (n : ℕ) : space d n ∈ M := by
  have h0 : (∅ : ZFSet.{u}) ∈ M := by
    have hs := sep_mem M hM hS (.neg (.equal 0 0)) (fun _ => d) (fun _ => hd) hd
    have heq : ZFSet.sep (fun x => (Formula.neg (.equal 0 0)).Eval (cons x (fun _ => d))) d = ∅ := by
      apply ZFSet.ext; intro x; simp [ZFSet.mem_sep,Formula.Eval]
    exact heq ▸ hs
  induction n with
  | zero => exact singleton_mem M hM hP h0
  | succ n ih => exact product_mem M hM hP hU hPow hS hd ih

end FiniteTuple
end TuringRigidity.BoundedSetTheory

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

theorem unionCode_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M)
    {t p r : ZFSet.{u}} (ht : t ∈ M) (hp : p ∈ M) (hr : r ∈ M) :
    unionCode t p r ∈ M := by
  let env := cons t (cons (iterUnion 2 t) (cons (iterUnion 5 t) (cons p (cons r (fun _ => t)))))
  have h2 := iterUnion_mem M hM hU ht 2
  have h5 := iterUnion_mem M hM hU ht 5
  have he : ∀ i, env i ∈ M := by
    intro i
    rcases i with _|_|_|_|_|i <;> assumption
  have hs := sep_mem M hM hS unionFormula env he (product_mem M hM hP hU hPow hS h5 hp)
  have heq : ZFSet.sep (fun z => unionFormula.Eval (cons z env)) (ZFSet.prod (iterUnion 5 t) p) =
      unionCode t p r := by
    apply ZFSet.ext
    intro z
    simp only [unionCode,ZFSet.mem_sep]
    exact and_congr Iff.rfl (eval_unionFormula t p r z _)
  exact heq ▸ hs

theorem encode_union (p r : ZFSet.{u}) [Preorder (Conditions p)]
    (hr : ∀ q s : Conditions p, ZFSet.pair (label p q) (label p s) ∈ r ↔ q ≤ s)
    (τ : Name (Conditions p)) :
    (Name.union τ).encode (label p) = unionCode (τ.encode (label p)) p r := by
  apply ZFSet.ext
  intro z
  rw [mem_unionCode]
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨⟨i,j,s,hsq,hsv⟩,hz⟩
    have hi : ZFSet.pair ((τ.child i).encode (label p)) (label p (τ.tag i)) ∈ τ.encode (label p) :=
      (pair_mem_encode _ _ _ _).mpr ⟨i,rfl,rfl⟩
    have hj : ZFSet.pair (((τ.child i).child j).encode (label p)) (label p ((τ.child i).tag j)) ∈
        (τ.child i).encode (label p) := (pair_mem_encode _ _ _ _).mpr ⟨j,rfl,rfl⟩
    exact ⟨_,second_child_bound hi hj,_,label_mem p s,hz.symm,
      _,first_mem_doubleUnion hi,_,label_mem p _,_,label_mem p _,hi,hj,
      (hr _ _).mpr hsq,(hr _ _).mpr hsv⟩
  · rintro ⟨d,_,s,hs,rfl,c,_,q,_,v,_,hc,hd,hq,hv⟩
    obtain ⟨i,rfl,rfl⟩ := (pair_mem_encode _ _ _ _).mp hc
    obtain ⟨j,rfl,rfl⟩ := (pair_mem_encode _ _ _ _).mp hd
    obtain ⟨s,rfl⟩ := label_surjective p hs
    exact ⟨⟨i,j,s,(hr _ _).mp hq,(hr _ _).mp hv⟩,rfl⟩

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

theorem names_pair_closed (M p : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hp : p ∈ M)
    {σ τ : Name (Conditions p)} (hσ : σ ∈ names M p) (hτ : τ ∈ names M p) :
    Name.pair σ τ ∈ names M p := by
  have ht := hM p hp (label p ⊤) (label_mem p ⊤)
  change (Name.pair σ τ).encode (label p) ∈ M
  rw [encode_pair]
  exact pair_mem M hM hP (orderedPair_mem M hM hP hσ ht) (orderedPair_mem M hM hP hτ ht)

theorem extension_pairing (M p : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hp : p ∈ M)
    (G : Set (Conditions p)) (hG : ⊤ ∈ G) : Pairing (genericExtensionSet M p G) := by
  intro a ha b hb
  obtain ⟨σ,hσ,rfl⟩ := (mem_extensionSet M p G a).mp ha
  obtain ⟨τ,hτ,rfl⟩ := (mem_extensionSet M p G b).mp hb
  refine ⟨({σ.val G,τ.val G} : ZFSet.{u}),?_,fun x _ => ZFSet.mem_pair⟩
  exact (mem_extensionSet M p G _).mpr
    ⟨Name.pair σ τ,names_pair_closed M p hM hP hp hσ hτ,Name.val_pair G hG σ τ⟩

theorem names_union_closed (M p r : ZFSet.{u}) [Preorder (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hp : p ∈ M) (hrM : r ∈ M)
    (hr : ∀ q s : Conditions p, ZFSet.pair (label p q) (label p s) ∈ r ↔ q ≤ s)
    {τ : Name (Conditions p)} (hτ : τ ∈ names M p) :
    Name.union τ ∈ names M p := by
  change (Name.union τ).encode (label p) ∈ M
  rw [encode_union p r hr]
  exact unionCode_mem M hM hP hU hPow hS hτ hp hrM

theorem extension_union (M p r : ZFSet.{u}) [Preorder (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hp : p ∈ M) (hrM : r ∈ M)
    (hr : ∀ q s : Conditions p, ZFSet.pair (label p q) (label p s) ∈ r ↔ q ≤ s)
    (G : GenericFilter (Conditions p)) : BoundedSetTheory.Union (genericExtensionSet M p G.carrier) := by
  intro a ha
  obtain ⟨τ,hτ,rfl⟩ := (mem_extensionSet M p G.carrier a).mp ha
  refine ⟨ZFSet.sUnion (τ.val G.carrier),?_,?_⟩
  · exact (mem_extensionSet M p G.carrier _).mpr
      ⟨Name.union τ,names_union_closed M p r hM hP hU hPow hS hp hrM hr hτ,Name.val_union G τ⟩
  · intro x _
    rw [ZFSet.mem_sUnion]
    constructor
    · rintro ⟨y,hy,hxy⟩
      exact ⟨y,genericExtensionSet_transitive M p hM G.carrier _ ha y hy,hy,hxy⟩
    · rintro ⟨y,_,hy,hxy⟩
      exact ⟨y,hy,hxy⟩

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

theorem taggedImage_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    {x f t : ZFSet.{u}} (hx : x ∈ M) (hf : f ∈ M) (ht : t ∈ M) :
    taggedImage x f t ∈ M := by
  have hr := iterUnion_mem M hM hU hf 2
  let e := cons x (cons f (cons (iterUnion 2 f) (cons t (fun _ => x))))
  have he : ∀ i, e i ∈ M := by
    intro i; cases i with
    | zero => exact hx
    | succ i => cases i with
      | zero => exact hf
      | succ i => cases i with
        | zero => exact hr
        | succ i => cases i <;> assumption
  have hs := sep_mem M hM hS taggedImageFormula e he
    (product_mem M hM hP hU hPow hS hr (singleton_mem M hM hP ht))
  have heq : ZFSet.sep (fun z => taggedImageFormula.Eval (cons z e))
      (ZFSet.prod (iterUnion 2 f) ({t} : ZFSet.{u})) = taggedImage x f t := by
    apply ZFSet.ext
    intro z
    simp only [taggedImage,ZFSet.mem_sep]
    exact and_congr_right (fun _ => eval_taggedImageFormula z x f _ t _)
  exact heq ▸ hs

end TuringRigidity.TransitiveNameModel

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

theorem relation_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M)
    {d : ZFSet.{u}} (hd : d ∈ M) (n : ℕ) (φ : Formula)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) : relation d n φ e ∈ M := by
  have hs := space_mem M hM hP hU hPow hS hd n
  obtain ⟨c,hc,hct,hsc⟩ := internal_transitive_container M hM hP hU hS hR hI hs
  have h0 : (∅ : ZFSet.{u}) ∈ M := hM _ (omega_mem M hM hS hI) _ ZFSet.omega_zero
  let env := cons (space d n) (cons d (cons c (cons ∅ e)))
  have henv : ∀ i, env i ∈ M := by
    intro i; rcases i with _|i; exact hs
    rcases i with _|i; exact hd
    rcases i with _|i; exact hc
    rcases i with _|i; exact h0
    exact he i
  have hsep := sep_mem M hM hS (relationFormula n φ) env henv
    (product_mem M hM hP hU hPow hS hs hd)
  have heq : ZFSet.sep (fun z => (relationFormula n φ).Eval (cons z env))
      (ZFSet.prod (space d n) d) = relation d n φ e := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,eval_relationFormula d c z n φ e hct (fun x hx => hct _ hsc x hx)]
    exact and_iff_right_of_imp (fun hz => (ZFSet.mem_sep.mp hz).1)
  exact heq ▸ hsep

end FiniteTuple
end TuringRigidity.BoundedSetTheory

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

theorem sigma_mono (M : ZFSet.{u}) (φ : SigmaFormula) (e : ℕ → Name (Conditions c))
    {p q : Conditions c} (hqp : q ≤ p) (h : SigmaForces M e φ p) : SigmaForces M e φ q := by
  induction φ generalizing e with
  | bounded φ => exact forces_mono φ e hqp h
  | existsSet φ ih =>
    obtain ⟨a,ha,hf⟩ := h
    exact ⟨a,ha,ih _ hf⟩

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

variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem realize_sigmaForcing (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M)
    {o : ZFSet.{u}}
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (φ : SigmaFormula) (e : ℕ → Name (Conditions c)) (p : Conditions c)
    (env : ℕ → ZFSet.{u}) (henv : ∀ i, env i ∈ M)
    (ci oi pi : ℕ) (v : ℕ → ℕ)
    (hc : env ci = c) (ho' : env oi = o) (hp : env pi = label c p)
    (hv : ∀ i, env (v i) = (e i).encode (label c)) :
    (SigmaCode.forcing φ ci oi pi v).Realize M env ↔ SigmaForces M e φ p := by
  induction φ generalizing e env ci oi pi v with
  | bounded φ =>
    exact realize_boundedCertificate M hM hP hU hPow hS hR hI ho φ e p env henv ci oi pi v hc ho' hp hv
  | existsSet φ ih =>
    have henv' (x : ZFSet.{u}) (hx : x ∈ M) : ∀ i, cons x env i ∈ M := by
      intro i; cases i <;> simp only [cons_zero,cons_succ]; exact hx; exact henv _
    have valid (x : ZFSet.{u}) (hx : x ∈ M) :
        (NameValidity.Code.valid (ci+1) 0).Realize M (cons x env) ↔
          ∃ a : Name (Conditions c), a.encode (label c) = x := by
      have h := NameValidity.realize_valid M hM hP hU hPow hS hR hI
        (cons x env) (henv' x hx) (ci+1) 0
      change (NameValidity.Code.valid (ci+1) 0).Realize M (cons x env) ↔
        (∃ a : Name (Conditions (env ci)), a.encode (label (env ci)) = x) at h
      rw [hc] at h
      exact h
    have sub (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) :=
      ih (push a e) (cons (a.encode (label c)) env) (henv' _ ha)
        (ci+1) (oi+1) (pi+1) (push 0 (fun i => v i+1)) hc ho' hp
        (by intro i; cases i <;> simp only [push_zero,push_succ,cons_zero,cons_succ,hv])
    simp only [SigmaCode.forcing,SigmaFormula.Realize,SigmaFormula.realize_conj]
    constructor
    · rintro ⟨x,hx,hvalid,hforce⟩
      obtain ⟨a,rfl⟩ := (valid x hx).mp hvalid
      exact ⟨a,hx,(sub a hx).mp hforce⟩
    · rintro ⟨a,ha,hforce⟩
      exact ⟨_,ha,(valid _ ha).mpr ⟨a,rfl⟩,(sub a ha).mpr hforce⟩

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

theorem eval_hullMemberFormula (z x q : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    hullMemberFormula.Eval (cons z (cons x (cons q e))) ↔
      ∀ c ∈ q, Transitive c → x ∈ c → z ∈ c := by
  simp only [hullMemberFormula, Formula.eval_allMem, Formula.eval_imp,
    Formula.Eval, Formula.eval_transitive, cons_zero, cons_succ]
  exact forall_congr' (fun c => forall_congr' (fun _ => and_imp))

theorem hull_mem (M d q : ZFSet.{u}) (hM : Transitive M) (hS : Separation M)
    (hdM : d ∈ M) (hqM : q ∈ M) {x : ZFSet.{u}} (hxM : x ∈ M) :
    hull d q x ∈ M := by
  have he : ∀ i, cons x (cons q (fun _ => d)) i ∈ M := by
    intro i; cases i with
    | zero => exact hxM
    | succ i => cases i <;> assumption
  have hs := sep_mem M hM hS hullMemberFormula _ he hdM
  have heq : ZFSet.sep (fun z => hullMemberFormula.Eval
      (cons z (cons x (cons q (fun _ => d))))) d = hull d q x := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sep, eval_hullMemberFormula, mem_hull]
  exact heq ▸ hs

theorem isHull_iff (M d q : ZFSet.{u}) (hM : Transitive M)
    (hS : Separation M) (hdM : d ∈ M) (hqM : q ∈ M) (hd : Transitive d)
    (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d) {x c : ZFSet.{u}}
    (hx : x ∈ d) (hc : c ∈ M) :
    (c ∈ q ∧ Transitive c ∧ x ∈ c ∧
      ∀ b ∈ q, Transitive b → x ∈ b → c ⊆ b) ↔ c = hull d q x := by
  have hhM := hull_mem M d q hM hS hdM hqM (hM d hdM x hx)
  have hhq := (hq _).mpr ⟨hhM,hull_subset d q x⟩
  have hht := hull_transitive d q x hd
  have hhx := self_mem_hull d q hx
  constructor
  · rintro ⟨hcq,hct,hxc,hmin⟩
    apply ZFSet.ext
    intro z
    exact ⟨fun hz => hmin _ hhq hht hhx hz,fun hz => hull_least d q x c hcq hct hxc hz⟩
  · rintro rfl
    exact ⟨hhq,hht,hhx,fun b hb ht hx => hull_least d q x b hb ht hx⟩

theorem collect_hulls (M d q : ZFSet.{u}) (hM : Transitive M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hdM : d ∈ M) (hqM : q ∈ M) (hd : Transitive d)
    (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d) {x : ZFSet.{u}} (hx : x ∈ d) :
    ∃ b ∈ M, ∀ c, c ∈ b ↔ ∃ y ∈ x, hull d q y = c := by
  let e := cons d (cons q (fun _ => d))
  have he : ∀ i, e i ∈ M := by
    intro i; cases i with
    | zero => exact hdM
    | succ i => cases i <;> assumption
  apply replacement_image M hM hR (.bounded (.isHull 0 1 2 3)) e he
    (hM d hdM x hx) (hull d q)
  · intro y hy
    exact hull_mem M d q hM hS hdM hqM (hM _ (hM d hdM x hx) y hy)
  · intro y hy c hc
    change (Formula.isHull 0 1 2 3).Realize M (cons c (cons y e)) ↔ _
    have he' : ∀ i, cons c (cons y e) i ∈ M := by
      intro i; cases i with
      | zero => exact hc
      | succ i => cases i with
        | zero => exact hM _ (hM d hdM x hx) y hy
        | succ i => exact he i
    rw [Formula.absolute _ M hM _ he', Formula.eval_isHull]
    exact isHull_iff M d q hM hS hdM hqM hd hq (hd x hx y hy) hc

theorem hull_unfold (M d q : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : Union M) (hS : Separation M) (hR : SigmaReplacement M)
    (hdM : d ∈ M) (hqM : q ∈ M) (hd : Transitive d)
    (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d) {x : ZFSet.{u}} (hx : x ∈ d) :
    ∀ z, z ∈ hull d q x ↔ z = x ∨ ∃ y ∈ x, z ∈ hull d q y := by
  obtain ⟨b,hb,hbdef⟩ := collect_hulls M d q hM hS hR hdM hqM hd hq hx
  let a := ({x} : ZFSet.{u}) ∪ ZFSet.sUnion b
  have haM : a ∈ M := binary_union_mem M hM hP hU
    (singleton_mem M hM hP (hM d hdM x hx)) (union_mem M hM hU hb)
  have ha (z : ZFSet.{u}) : z ∈ a ↔ z = x ∨ ∃ y ∈ x, z ∈ hull d q y := by
    simp only [a,ZFSet.mem_union,ZFSet.mem_singleton,ZFSet.mem_sUnion]
    constructor
    · rintro (h|⟨c,hc,hzc⟩)
      · exact Or.inl h
      · obtain ⟨y,hy,rfl⟩ := (hbdef c).mp hc
        exact Or.inr ⟨y,hy,hzc⟩
    · rintro (h|⟨y,hy,hzy⟩)
      · exact Or.inl h
      · exact Or.inr ⟨_,(hbdef _).mpr ⟨y,hy,rfl⟩,hzy⟩
  have had : a ⊆ d := by
    intro z hz
    rcases (ha z).mp hz with rfl|⟨y,_,hzy⟩
    · exact hx
    · exact hull_subset d q y hzy
  have hat : Transitive a := by
    intro z hz w hw
    apply (ha w).mpr
    rcases (ha z).mp hz with rfl|⟨y,hy,hzy⟩
    · exact Or.inr ⟨w,hw,self_mem_hull d q (hd _ hx w hw)⟩
    · exact Or.inr ⟨y,hy,hull_transitive d q y hd z hzy w hw⟩
  have hhM := hull_mem M d q hM hS hdM hqM (hM d hdM x hx)
  have hhq := (hq _).mpr ⟨hhM,hull_subset d q x⟩
  intro z
  constructor
  · intro hz
    exact (ha z).mp (hull_least d q x a ((hq _).mpr ⟨haM,had⟩) hat
      ((ha x).mpr (Or.inl rfl)) hz)
  · rintro (rfl|⟨y,hy,hzy⟩)
    · exact self_mem_hull d q hx
    · exact hull_least d q y _ hhq (hull_transitive d q x hd)
        (hull_transitive d q x hd x (self_mem_hull d q hx) y hy) hzy

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCheckRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open RecursiveNames BoundedSetTheory
universe u

def checkCertificate : SigmaFormula := .existsSet (.existsSet (.bounded
  (.conj (.isHull 1 3 4 5) (CheckFormula.graph 1 0 2 6))))

theorem realize_checkCertificate (M d q t : ZFSet.{u}) (hM : Transitive M)
    (hS : Separation M) (hdM : d ∈ M) (hqM : q ∈ M) (htM : t ∈ M)
    (hd : Transitive d) (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d)
    {x f : ZFSet.{u}} (hx : x ∈ d) (hf : f ∈ M) :
    checkCertificate.Realize M (cons f (cons x (cons d (cons q (cons t (fun _ => d)))))) ↔
      ∃ r ∈ M, CheckGraph (hull d q x) r f t := by
  have hxM := hM d hdM x hx
  have matrix (c r : ZFSet.{u}) (hc : c ∈ M) (hr : r ∈ M) :
      (Formula.conj (.isHull 1 3 4 5) (CheckFormula.graph 1 0 2 6)).Realize M
        (cons r (cons c (cons f (cons x (cons d (cons q (cons t (fun _ => d)))))))) ↔
      c = hull d q x ∧ CheckGraph c r f t := by
    have he : ∀ i, (cons r (cons c (cons f (cons x
        (cons d (cons q (cons t (fun _ => d)))))))) i ∈ M := by
      intro i
      rcases i with _|i; exact hr
      rcases i with _|i; exact hc
      rcases i with _|i; exact hf
      rcases i with _|i; exact hxM
      rcases i with _|i; exact hdM
      rcases i with _|i; exact hqM
      rcases i with _|i; exact htM
      exact hdM
    rw [Formula.absolute _ M hM _ he]
    simp only [Formula.Eval,Formula.eval_isHull,CheckFormula.eval_graph,cons_zero,cons_succ]
    exact and_congr (isHull_iff M d q hM hS hdM hqM hd hq hx hc) Iff.rfl
  change (∃ c ∈ M, ∃ r ∈ M, _) ↔ _
  constructor
  · rintro ⟨c,hc,r,hr,h⟩
    obtain ⟨rfl,hg⟩ := (matrix c r hc hr).mp h
    exact ⟨r,hr,hg⟩
  · rintro ⟨r,hr,hg⟩
    have hc := hull_mem M d q hM hS hdM hqM hxM
    exact ⟨_,hc,r,hr,(matrix _ r hc hr).mpr ⟨rfl,hg⟩⟩

theorem internal_checkGraph (M d q t : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hdM : d ∈ M) (hqM : q ∈ M) (htM : t ∈ M) (hd : Transitive d)
    (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d) (x : ZFSet.{u}) (hx : x ∈ d) :
    ∃ f ∈ M, CheckGraph (hull d q x) (iterUnion 2 f) f t := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    have hxM := hM d hdM x hx
    let e := cons d (cons q (cons t (fun _ => d)))
    have he : ∀ i, e i ∈ M := by
      intro i
      rcases i with _|i; exact hdM
      rcases i with _|i; exact hqM
      rcases i with _|i; exact htM
      exact hdM
    have cert (y f : ZFSet.{u}) (hy : y ∈ x) (hf : f ∈ M) :
        checkCertificate.Realize M (cons f (cons y e)) ↔
          ∃ r ∈ M, CheckGraph (hull d q y) r f t :=
      realize_checkCertificate M d q t hM hS hdM hqM htM hd hq (hd x hx y hy) hf
    obtain ⟨b,hb,hbdef⟩ := hR checkCertificate e he x hxM (by
      intro y hy
      obtain ⟨f,hf,hfg⟩ := ih y hy (hd x hx y hy)
      refine ⟨f,hf,(cert y f hy hf).mpr
        ⟨_,iterUnion_mem M hM hU hf 2,hfg⟩,?_⟩
      intro g hg hcg
      obtain ⟨r,_,hgg⟩ := (cert y g hy hg).mp hcg
      exact hgg.unique hfg)
    have hbg (f : ZFSet.{u}) : f ∈ b ↔
        ∃ y ∈ x, ∃ r ∈ M, CheckGraph (hull d q y) r f t := by
      constructor
      · intro hf
        have hfM := hM b hb f hf
        obtain ⟨y,hy,hc⟩ := (hbdef f hfM).mp hf
        exact ⟨y,hy,(cert y f hy hfM).mp hc⟩
      · rintro ⟨y,hy,r,hr,hg⟩
        obtain ⟨f',hf',hg'⟩ := ih y hy (hd x hx y hy)
        have heq := hg.unique hg'
        have hfM : f ∈ M := heq ▸ hf'
        exact (hbdef f hfM).mpr ⟨y,hy,(cert y f hy hfM).mpr ⟨r,hr,hg⟩⟩
    let g := ZFSet.sUnion b
    have hgM : g ∈ M := union_mem M hM hU hb
    have hg (z : ZFSet.{u}) : z ∈ g ↔
        ∃ y ∈ x, ∃ w ∈ hull d q y, z = ZFSet.pair w (checkedCode t w) := by
      constructor
      · intro hz
        obtain ⟨f,hf,hzf⟩ := ZFSet.mem_sUnion.mp hz
        obtain ⟨y,hy,r,_,hfg⟩ := (hbg f).mp hf
        exact ⟨y,hy,(hfg.mem_iff z).mp hzf⟩
      · rintro ⟨y,hy,w,hw,hz⟩
        obtain ⟨f,hf,hfg⟩ := ih y hy (hd x hx y hy)
        exact ZFSet.mem_sUnion.mpr ⟨f,(hbg f).mpr
          ⟨y,hy,_,iterUnion_mem M hM hU hf 2,hfg⟩,(hfg.mem_iff z).mpr ⟨w,hw,hz⟩⟩
    have hvalue : taggedImage x g t = checkedCode t x := by
      apply ZFSet.ext
      intro z
      rw [mem_taggedImage,mem_checkedCode]
      constructor
      · rintro ⟨y,hy,w,hw,hz⟩
        obtain ⟨a,_,v,_,hp⟩ := (hg _).mp hw
        obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
        exact ⟨y,hy,hz⟩
      · rintro ⟨y,hy,hz⟩
        exact ⟨y,hy,_,(hg _).mpr
          ⟨y,hy,y,self_mem_hull d q (hd x hx y hy),rfl⟩,hz⟩
    have hvM : checkedCode t x ∈ M := hvalue ▸
      taggedImage_mem M hM hP hU hPow hS hxM hgM htM
    let f := g ∪ ({ZFSet.pair x (checkedCode t x)} : ZFSet.{u})
    have hfM : f ∈ M := binary_union_mem M hM hP hU hgM
      (singleton_mem M hM hP (orderedPair_mem M hM hP hxM hvM))
    refine ⟨f,hfM,checkGraph_of_mem_iff _ f t (hull_transitive d q x hd) ?_⟩
    intro z
    change z ∈ g ∪ ({ZFSet.pair x (checkedCode t x)} : ZFSet.{u}) ↔ _
    rw [ZFSet.mem_union,ZFSet.mem_singleton,hg]
    constructor
    · rintro (⟨y,hy,w,hw,hz⟩|hz)
      · exact ⟨w,(hull_unfold M d q hM hP hU hS hR hdM hqM hd hq hx w).mpr
          (Or.inr ⟨y,hy,hw⟩),hz⟩
      · exact ⟨x,self_mem_hull d q hx,hz⟩
    · rintro ⟨w,hw,hz⟩
      rcases (hull_unfold M d q hM hP hU hS hR hdM hqM hd hq hx w).mp hw with rfl|⟨y,hy,hw⟩
      · exact Or.inr hz
      · exact Or.inl ⟨y,hy,w,hw,hz⟩

theorem checkedCode_mem_of_container (M d t : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hdM : d ∈ M) (htM : t ∈ M) (hd : Transitive d)
    {x : ZFSet.{u}} (hx : x ∈ d) : checkedCode t x ∈ M := by
  obtain ⟨q,hqM,hq⟩ := internal_power M hM hPow hdM
  obtain ⟨f,hf,hfg⟩ := internal_checkGraph M d q t hM hP hU hPow hS hR
    hdM hqM htM hd hq x hx
  obtain ⟨v,hv,hfv,_⟩ := hfg.2.2.1 x (self_mem_hull d q hx)
  rw [←hfg.correct x (self_mem_hull d q hx) v hv hfv]
  exact hM _ (iterUnion_mem M hM hU hf 2) v hv

theorem encoded_check_mem_of_container (M p d : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hR : SigmaReplacement M)
    (hpM : p ∈ M) (hdM : d ∈ M) (hd : Transitive d)
    {x : ZFSet.{u}} (hx : x ∈ d) : (Name.check x).encode (label p) ∈ M := by
  rw [encode_check]
  exact checkedCode_mem_of_container M d _ hM hP hU hPow hS hR hdM
    (hM p hpM _ (label_mem p ⊤)) hd hx

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

theorem encoded_check_mem (M p : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hR : SigmaReplacement M)
    (hI : Infinity M) (hp : p ∈ M) {x : ZFSet.{u}} (hx : x ∈ M) :
    (Name.check x).encode (label p) ∈ M := by
  obtain ⟨d,hdM,hd,hxd⟩ := internal_transitive_container M hM hP hU hS hR hI hx
  exact encoded_check_mem_of_container M p d hM hP hU hPow hS hR hp hdM hd hxd

theorem ground_inclusion (M p : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hR : SigmaReplacement M)
    (hI : Infinity M) (hp : p ∈ M) (G : Set (Conditions p)) (hG : ⊤ ∈ G) :
    (M : Set ZFSet.{u}) ⊆ genericExtension M p G :=
  ground_subset M p (fun _ hx => encoded_check_mem M p hM hP hU hPow hS hR hI hp hx) G hG

theorem ground_inclusion_set (M p : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hR : SigmaReplacement M)
    (hI : Infinity M) (hp : p ∈ M) (G : Set (Conditions p)) (hG : ⊤ ∈ G) :
    M ⊆ genericExtensionSet M p G := by
  intro x hx
  have hx' := ground_inclusion M p hM hP hU hPow hS hR hI hp G hG hx
  rw [←genericExtensionSet_coe] at hx'
  exact hx'

end TuringRigidity.TransitiveNameModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_CutTranscript
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set
namespace TuringRigidity

namespace CategorySearch

noncomputable def pairOracle (A : Oracle) (p : ℝ × ℝ) : Oracle := join (join A (cut p.1)) (cut p.2)

end CategorySearch
end TuringRigidity

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

theorem SigmaSeparation.bounded {M : ZFSet.{u}} (h : SigmaSeparation M) : Separation M :=
  fun φ e he a ha => h (.bounded φ) e he a ha

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SigmaSeparationName
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem sigma_sep_mem (M : ZFSet.{u}) (hM : Transitive M) (hS : SigmaSeparation M)
    (φ : SigmaFormula) (env : ℕ → ZFSet.{u}) (he : ∀ i, env i ∈ M)
    {a : ZFSet.{u}} (ha : a ∈ M) :
    ZFSet.sep (fun x => φ.Realize M (cons x env)) a ∈ M := by
  obtain ⟨b,hb,hdef⟩ := hS φ env he a ha
  have eq : b = ZFSet.sep (fun x => φ.Realize M (cons x env)) a := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep]
    constructor
    · intro hx; exact (hdef x (hM b hb x hx)).mp hx
    · intro hx; exact (hdef x (hM a ha x hx.1)).mpr hx
  exact eq ▸ hb

end TuringRigidity.BoundedSetTheory

namespace TuringRigidity.BoundedForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem sigma_separation_name (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : SigmaSeparation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G)
    (φ : SigmaFormula) (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M)
    (e : ℕ → Name (Conditions c)) (he : ∀ i, (e i).encode (label c) ∈ M) :
    ∃ B ∈ M, B ⊆ a.support (label c) ∧ ∀ x,
      x ∈ (a.restrict (label c) B).val G.carrier ↔ x ∈ a.val G.carrier ∧
        φ.Realize (genericExtensionSet M c G.carrier)
          (cons x (fun i => (e i).val G.carrier)) := by
  let env := cons c (cons o (fun i => (e i).encode (label c)))
  have henv : ∀ i, env i ∈ M := by
    intro i; rcases i with _|i; exact hc
    rcases i with _|i; exact hoM
    exact he i
  let ψ := SigmaFormula.existsSet (.existsSet
    (SigmaFormula.andBounded (.orderedPair 2 1 0)
      (SigmaCode.forcing φ 3 4 0 (push 1 (fun i => i+5)))))
  let B := ZFSet.sep (fun z => ψ.Realize M (cons z env)) (a.support (label c))
  have hBM : B ∈ M := sigma_sep_mem M hM hS ψ env henv
    (support_mem M hM hP hU hPow hS.bounded hc hoM ho a ha)
  have hBsub : B ⊆ a.support (label c) := fun z hz => (ZFSet.mem_sep.mp hz).1
  have hai (i) : (a.child i).encode (label c) ∈ M :=
    names_childClosed M c hM a ha _ (child_relation a i)
  have hpush (i) (n) : (push (a.child i) e n).encode (label c) ∈ M := by
    cases n with
    | zero => exact hai i
    | succ n => exact he n
  have hpair (z x q : ZFSet.{u}) (hz : z ∈ M) (hx : x ∈ M) (hq : q ∈ M) :
      (Formula.orderedPair 2 1 0).Realize M (cons q (cons x (cons z env))) ↔ z = ZFSet.pair x q := by
    rw [Formula.absolute _ M hM _ (by
      intro n; rcases n with _|n; exact hq
      rcases n with _|n; exact hx
      rcases n with _|n; exact hz
      exact henv n)]
    exact Formula.eval_orderedPair 2 1 0 _
  have hB (i : a.arity) (q : Conditions c) (hq : q ≤ a.tag i) :
      ZFSet.pair ((a.child i).encode (label c)) (label c q) ∈ B ↔
        SigmaForces M (push (a.child i) e) φ q := by
    let z := ZFSet.pair ((a.child i).encode (label c)) (label c q)
    have hqM := hM c hc _ (label_mem c q)
    have hz : z ∈ M := orderedPair_mem M hM hP (hai i) hqM
    have query := realize_sigmaForcing M hM hP hU hPow hS.bounded hR hI ho φ
      (push (a.child i) e) q
      (cons (label c q) (cons ((a.child i).encode (label c)) (cons z env)))
      (by
        intro n; rcases n with _|n; exact hqM
        rcases n with _|n; exact hai i
        rcases n with _|n; exact hz
        exact henv n)
      3 4 0 (push 1 (fun n => n+5)) rfl rfl rfl
      (by intro n; cases n <;> rfl)
    have hs : z ∈ a.support (label c) := ZFSet.mem_range.mpr ⟨⟨i,⟨q,hq⟩⟩,rfl⟩
    change z ∈ ZFSet.sep _ _ ↔ _
    rw [ZFSet.mem_sep,and_iff_right hs]
    simp only [ψ,SigmaFormula.Realize,SigmaFormula.realize_andBounded]
    constructor
    · rintro ⟨x,hx,r,hr,hxr,hφ⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp ((hpair z x r hz hx hr).mp hxr)
      exact query.mp hφ
    · intro hφ
      exact ⟨_,hai i,_,hqM,(hpair z _ _ hz (hai i) hqM).mpr rfl,query.mpr hφ⟩
  have ht (i : a.arity) :
      φ.Realize (genericExtensionSet M c G.carrier)
        (cons ((a.child i).val G.carrier) (fun n => (e n).val G.carrier)) ↔
        ∃ p ∈ G.carrier, SigmaForces M (push (a.child i) e) φ p := by
    have hev : (fun n => (push (a.child i) e n).val G.carrier) =
        cons ((a.child i).val G.carrier) (fun n => (e n).val G.carrier) := by
      funext n; cases n <;> rfl
    rw [←hev]
    exact internal_sigma_truth M hM hP hU hPow hS.bounded hR hI hc hoM ho G hG φ _ (hpush i)
  refine ⟨B,hBM,hBsub,fun x => ?_⟩
  constructor
  · intro hx
    have hxa := a.val_restrict_subset (label c) B G hx
    obtain ⟨i,q,hqi,hqb,hqG,hix⟩ := (a.mem_val_restrict (label c) B G.carrier x).mp hx
    have hφ := (ht i).mpr ⟨q,hqG,(hB i q hqi).mp hqb⟩
    exact ⟨hxa,hix ▸ hφ⟩
  · rintro ⟨hxa,hφ⟩
    obtain ⟨i,hi,hix⟩ := (a.mem_val_children G.carrier x).mp hxa
    obtain ⟨p,hp,hf⟩ := (ht i).mp (hix ▸ hφ)
    obtain ⟨q,hq,hqp,hqi⟩ := G.directed hp hi
    exact (a.mem_val_restrict (label c) B G.carrier x).mpr
      ⟨i,q,hqi,(hB i q hqi).mpr (sigma_mono M φ _ hqp hf),hq,hix⟩

end TuringRigidity.BoundedForcing

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

theorem internal_selector (M : ZFSet.{u}) (hM : Transitive M)
    (hPow : PowerSet M) (hS : Separation M) (hAC : Choice M)
    {t : ZFSet.{u}} (ht : t ∈ M) :
    ∃ a ∈ M, ∃ f ∈ M, ChoiceGraph a f ∧
      ∀ x, x ∈ a ↔ x ∈ M ∧ x ⊆ t ∧ ∃ y, y ∈ x := by
  obtain ⟨q,hq,hqdef⟩ := internal_power M hM hPow ht
  let a := ZFSet.sep (fun x => ∃ y, y ∈ x) q
  have ha : a ∈ M := by
    simpa only [Formula.Eval,cons_zero,iff_true,exists_prop,and_true,a] using
      sep_mem M hM hS (.existsMem 0 (.equal 0 0)) (fun _ => t) (fun _ => ht) hq
  have hadef (x : ZFSet.{u}) : x ∈ a ↔ x ∈ M ∧ x ⊆ t ∧ ∃ y, y ∈ x := by
    rw [ZFSet.mem_sep,hqdef]
    exact and_assoc
  obtain ⟨f,hf,hfg⟩ := hAC a ha (fun x hx => ((hadef x).mp hx).2.2)
  exact ⟨a,ha,f,hf,hfg,hadef⟩

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

theorem relationFiber_mem (M : ZFSet.{u}) (hM : Transitive M) (hS : Separation M)
    {b r x : ZFSet.{u}} (hb : b ∈ M) (hr : r ∈ M) (hx : x ∈ M) : relationFiber b r x ∈ M := by
  simpa only [relationFiber,Formula.eval_pairMem,cons_zero,cons_succ] using
    sep_mem M hM hS (.pairMem 1 0 2) (cons x (fun _ => r))
      (by intro i; cases i <;> assumption) hb

theorem internal_relation_choice (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hAC : Choice M)
    {a b r : ZFSet.{u}} (ha : a ∈ M) (hb : b ∈ M) (hr : r ∈ M)
    (htotal : ∀ x ∈ a, ∃ y ∈ b, ZFSet.pair x y ∈ r) :
    ∃ g ∈ M, g ⊆ r ∧
      (∀ z ∈ g, ∃ x ∈ a, ∃ y ∈ b, z = ZFSet.pair x y) ∧
      (∀ x ∈ a, ∃ y ∈ b, ZFSet.pair x y ∈ g ∧
        ∀ z ∈ b, ZFSet.pair x z ∈ g → z = y) := by
  obtain ⟨q,hq,f,hf,hfg,hqdef⟩ := internal_selector M hM hPow hS hAC hb
  let e := cons a (cons b (cons q (cons f (cons r (fun _ => a)))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|i; exact ha
    rcases i with _|i; exact hb
    rcases i with _|i; exact hq
    rcases i with _|i; exact hf
    rcases i with _|i; exact hr
    exact ha
  let g := ZFSet.sep (fun z => selectionFormula.Eval (cons z e)) (ZFSet.prod a b)
  have hg : g ∈ M := sep_mem M hM hS selectionFormula e he
    (product_mem M hM hP hU hPow hS ha hb)
  have hfiber (x : ZFSet.{u}) (hx : x ∈ a) : relationFiber b r x ∈ q := by
    apply (hqdef _).mpr
    obtain ⟨y,hy,hxy⟩ := htotal x hx
    exact ⟨relationFiber_mem M hM hS hb hr (hM a ha x hx),
      (fun _ hz => (ZFSet.mem_sep.mp hz).1),y,ZFSet.mem_sep.mpr ⟨hy,hxy⟩⟩
  have hfibereq (x s : ZFSet.{u}) (hs : s ∈ q)
      (hdef : ∀ w ∈ b, w ∈ s ↔ ZFSet.pair x w ∈ r) : s = relationFiber b r x := by
    apply ZFSet.ext
    intro w
    rw [relationFiber,ZFSet.mem_sep]
    constructor
    · intro hw
      have hwb := ((hqdef s).mp hs).2.1 hw
      exact ⟨hwb,(hdef w hwb).mp hw⟩
    · rintro ⟨hwb,hw⟩
      exact (hdef w hwb).mpr hw
  have hgpair (x y : ZFSet.{u}) : ZFSet.pair x y ∈ g ↔
      x ∈ a ∧ y ∈ b ∧ ZFSet.pair (relationFiber b r x) y ∈ f := by
    change _ ∈ ZFSet.sep _ _ ↔ _
    rw [ZFSet.mem_sep]
    have eval := eval_selectionFormula (ZFSet.pair x y) a b q f r (fun _ => a)
    change selectionFormula.Eval (cons (ZFSet.pair x y) e) ↔ _ at eval
    rw [eval]
    constructor
    · rintro ⟨_,x',hx,y',hy,hp,s,hs,hdef,hsy⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
      rw [hfibereq x s hs hdef] at hsy
      exact ⟨hx,hy,hsy⟩
    · rintro ⟨hx,hy,hsy⟩
      refine ⟨ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩,x,hx,y,hy,rfl,
        relationFiber b r x,hfiber x hx,?_,hsy⟩
      intro w hw
      exact (ZFSet.mem_sep).trans (and_iff_right hw)
  have hgshape (z : ZFSet.{u}) (hz : z ∈ g) :
      ∃ x ∈ a, ∃ y ∈ b, z = ZFSet.pair x y :=
    ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  refine ⟨g,hg,?_,hgshape,?_⟩
  · intro z hz
    obtain ⟨x,_,y,_,rfl⟩ := hgshape z hz
    have hsy := ((hgpair x y).mp hz).2.2
    obtain ⟨s,_,v,hv,heq⟩ := hfg.1 _ hsy
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
    exact (ZFSet.mem_sep.mp hv).2
  · intro x hx
    obtain ⟨y,hy,hsy,_⟩ := hfg.2 _ (hfiber x hx)
    have hyb := (ZFSet.mem_sep.mp hy).1
    refine ⟨y,hyb,(hgpair x y).mpr ⟨hx,hyb,hsy⟩,?_⟩
    intro z _ hxz
    exact hfg.functional ((hgpair x z).mp hxz).2.2 hsy

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

theorem requests_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) {d r : ZFSet.{u}} (hd : d ∈ M) (hr : r ∈ M) (n : ℕ) :
    requests d n r ∈ M := by
  simpa only [requests,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ] using
    sep_mem M hM hS (.existsMem 1 (.pairMem 1 0 3))
      (cons d (fun _ => r)) (by intro i; cases i <;> assumption)
      (space_mem M hM hP hU hPow hS hd n)

theorem internal_skolem_graph (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M)
    {d : ZFSet.{u}} (hd : d ∈ M) (n : ℕ) (φ : Formula)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    ∃ g ∈ M, SkolemGraph d n φ e g := by
  have hr := relation_mem M hM hP hU hPow hS hR hI hd n φ e he
  have ha := requests_mem M hM hP hU hPow hS hd hr n
  obtain ⟨g,hg,hgr,_,hsel⟩ := internal_relation_choice M hM hP hU hPow hS hAC ha hd hr
    (fun t ht => (ZFSet.mem_sep.mp ht).2)
  refine ⟨g,hg,hgr,?_⟩
  intro xs hlen hxs hw
  subst n
  have ht : code xs ∈ requests d xs.length (relation d xs.length φ e) := by
    obtain ⟨y,hy,hφ⟩ := hw
    exact ZFSet.mem_sep.mpr ⟨code_mem_space d xs hxs,y,hy,
      (relation_pair d y xs φ e).mpr ⟨hxs,hy,hφ⟩⟩
  exact hsel _ ht

end FiniteTuple
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

theorem hull_mem (M d r q : ZFSet.{u}) (hM : Transitive M) (hS : Separation M)
    (hd : d ∈ M) (hr : r ∈ M) (hq : q ∈ M) {x : ZFSet.{u}} (hx : x ∈ M) :
    hull d r q x ∈ M := by
  let e := cons x (cons q (cons d (cons r (fun _ => r))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|i; exact hx
    rcases i with _|i; exact hq
    rcases i with _|i; exact hd
    cases i <;> exact hr
  have hs := sep_mem M hM hS Code.member e he hd
  have eq : ZFSet.sep (fun z => Code.member.Eval (cons z e)) d = hull d r q x := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep,mem_hull]
    apply and_congr Iff.rfl
    simpa only [e,cons] using Code.eval_member z x q d r (fun _ => r)
  exact eq ▸ hs

theorem isHull_iff (M d r q : ZFSet.{u}) (hM : Transitive M) (hS : Separation M)
    (hd : d ∈ M) (hr : r ∈ M) (hqM : q ∈ M)
    (hq : ∀ b, b ∈ q ↔ b ∈ M ∧ b ⊆ d) {x b : ZFSet.{u}} (hx : x ∈ d) :
    (b ∈ q ∧ Closed d r b ∧ x ∈ b ∧
      ∀ a ∈ q, Closed d r a → x ∈ a → b ⊆ a) ↔ b = hull d r q x := by
  have hh := hull_mem M d r q hM hS hd hr hqM (hM d hd x hx)
  have hhq := (hq _).mpr ⟨hh,hull_subset d r q x⟩
  constructor
  · rintro ⟨hb,hc,hxb,hmin⟩
    apply ZFSet.ext
    intro z
    exact ⟨fun hz => hmin _ hhq (hull_closed d r q x) (self_mem d r q hx) hz,
      fun hz => hull_least d r q x b hb hc hxb hz⟩
  · rintro rfl
    exact ⟨hhq,hull_closed d r q x,self_mem d r q hx,
      fun a ha hc hx => hull_least d r q x a ha hc hx⟩

theorem predecessors_mem (M : ZFSet.{u}) (hM : Transitive M) (hS : Separation M)
    {d r x : ZFSet.{u}} (hd : d ∈ M) (hr : r ∈ M) (hx : x ∈ M) :
    predecessors d r x ∈ M := by
  simpa only [Formula.eval_pairMem,cons_zero,cons_succ,predecessors] using
    sep_mem M hM hS (.pairMem 0 1 2) (cons x (fun _ => r))
    (by intro i; cases i <;> assumption) hd

theorem collect_hulls (M d r q : ZFSet.{u}) (hM : Transitive M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hd : d ∈ M) (hr : r ∈ M) (hqM : q ∈ M)
    (hq : ∀ b, b ∈ q ↔ b ∈ M ∧ b ⊆ d) {x : ZFSet.{u}} (hx : x ∈ d) :
    ∃ b ∈ M, ∀ z, z ∈ b ↔ ∃ y ∈ predecessors d r x, hull d r q y = z := by
  let e := cons q (cons d (fun _ => r))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|i; exact hqM
    rcases i with _|i; exact hd
    exact hr
  apply replacement_image M hM hR (.bounded (Code.isHull 0 1 2 3 4)) e he
    (predecessors_mem M hM hS hd hr (hM d hd x hx)) (hull d r q)
  · intro y hy
    exact hull_mem M d r q hM hS hd hr hqM (hM d hd y ((mem_predecessors _ _ _ _).mp hy).1)
  · intro y hy b hb
    change (Code.isHull 0 1 2 3 4).Realize M (cons b (cons y e)) ↔ _
    rw [Formula.absolute _ M hM _ (by
      intro i; rcases i with _|i; exact hb
      rcases i with _|i; exact hM d hd y ((mem_predecessors _ _ _ _).mp hy).1
      exact he i),Code.eval_isHull]
    exact isHull_iff M d r q hM hS hd hr hqM hq ((mem_predecessors _ _ _ _).mp hy).1

theorem hull_unfold (M d r q : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hS : Separation M) (hR : SigmaReplacement M)
    (hd : d ∈ M) (hr : r ∈ M) (hqM : q ∈ M)
    (hq : ∀ b, b ∈ q ↔ b ∈ M ∧ b ⊆ d) {x : ZFSet.{u}} (hx : x ∈ d) (z : ZFSet.{u}) :
    z ∈ hull d r q x ↔ z = x ∨ ∃ y ∈ predecessors d r x, z ∈ hull d r q y := by
  obtain ⟨b,hb,hbdef⟩ := collect_hulls M d r q hM hS hR hd hr hqM hq hx
  let a := ({x} : ZFSet.{u}) ∪ ZFSet.sUnion b
  have ha : a ∈ M := binary_union_mem M hM hP hU
    (singleton_mem M hM hP (hM d hd x hx)) (union_mem M hM hU hb)
  have ha_def (w : ZFSet.{u}) : w ∈ a ↔ w = x ∨ ∃ y ∈ predecessors d r x, w ∈ hull d r q y := by
    simp only [a,ZFSet.mem_union,ZFSet.mem_singleton,ZFSet.mem_sUnion]
    constructor
    · rintro (h|⟨v,hv,hw⟩)
      · exact Or.inl h
      · obtain ⟨y,hy,rfl⟩ := (hbdef v).mp hv
        exact Or.inr ⟨y,hy,hw⟩
    · rintro (h|⟨y,hy,hw⟩)
      · exact Or.inl h
      · exact Or.inr ⟨_,(hbdef _).mpr ⟨y,hy,rfl⟩,hw⟩
  have had : a ⊆ d := by
    intro w hw
    rcases (ha_def w).mp hw with rfl|⟨y,_,hw⟩
    · exact hx
    · exact hull_subset d r q y hw
  have hac : Closed d r a := by
    intro w hw v hv hvw
    apply (ha_def v).mpr
    rcases (ha_def w).mp hw with rfl|⟨y,hy,hw⟩
    · exact Or.inr ⟨v,(mem_predecessors _ _ _ _).mpr ⟨hv,hvw⟩,self_mem d r q hv⟩
    · exact Or.inr ⟨y,hy,hull_closed d r q y w hw v hv hvw⟩
  have hhq := (hq _).mpr ⟨hull_mem M d r q hM hS hd hr hqM (hM d hd x hx),hull_subset d r q x⟩
  constructor
  · intro hz
    exact (ha_def z).mp (hull_least d r q x a ((hq a).mpr ⟨ha,had⟩) hac
      ((ha_def x).mpr (Or.inl rfl)) hz)
  · rintro (rfl|⟨y,hy,hz⟩)
    · exact self_mem d r q hx
    · obtain ⟨hyd,hyx⟩ := (mem_predecessors _ _ _ _).mp hy
      exact hull_least d r q y _ hhq (hull_closed d r q x)
        (hull_closed d r q x x (self_mem d r q hx) y hyd hyx) hz

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

noncomputable def value (d r : ZFSet.{u}) (wf : WellFounded (Rel d r)) : ZFSet.{u} → ZFSet.{u} :=
  wf.fix (fun x ih => ZFSet.range (fun y : Conditions (predecessors d r x) =>
    ih (label (predecessors d r x) y)
      ((mem_predecessors d r x _).mp (label_mem _ y))))

theorem mem_value (d r : ZFSet.{u}) (wf : WellFounded (Rel d r)) (x z : ZFSet.{u}) :
    z ∈ value d r wf x ↔ ∃ y ∈ d, ZFSet.pair y x ∈ r ∧ z = value d r wf y := by
  rw [value,WellFounded.fix_eq]
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨hyd,hyx⟩ := (mem_predecessors d r x _).mp (label_mem _ y)
    exact ⟨_,hyd,hyx,hy.symm⟩
  · rintro ⟨y,hyd,hyx,rfl⟩
    obtain ⟨s,rfl⟩ := label_surjective (predecessors d r x)
      ((mem_predecessors _ _ _ _).mpr ⟨hyd,hyx⟩)
    exact ⟨s,rfl⟩

theorem Graph.correct {d r a b f : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (h : Graph d r a b f) (x : ZFSet.{u}) (hx : x ∈ a)
    (v : ZFSet.{u}) (hv : v ∈ b) (hfv : ZFSet.pair x v ∈ f) :
    v = value d r wf x := by
  induction x using wf.induction generalizing v with
  | h x ih =>
    have hs := h.2.2.2.2 x hx v hv hfv
    apply ZFSet.ext
    intro z
    rw [mem_value]
    constructor
    · intro hz
      obtain ⟨y,hyd,hyx,hyz⟩ := hs.1 z hz
      obtain ⟨w,hw,t,ht,heq⟩ := h.2.2.1 _ hyz
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
      exact ⟨y,hyd,hyx,ih y ⟨hyd,hyx⟩ (h.2.1 x hx y hyd hyx) z ht hyz⟩
    · rintro ⟨y,hyd,hyx,rfl⟩
      have hya := h.2.1 x hx y hyd hyx
      obtain ⟨w,hw,hyw,_⟩ := h.2.2.2.1 y hya
      rw [←ih y ⟨hyd,hyx⟩ hya w hw hyw]
      exact hs.2 y hyd hyx w hw hyw

theorem Graph.mem_iff {d r a b f : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (h : Graph d r a b f) (z : ZFSet.{u}) :
    z ∈ f ↔ ∃ x ∈ a, z = ZFSet.pair x (value d r wf x) := by
  constructor
  · intro hz
    obtain ⟨x,hx,y,hy,rfl⟩ := h.2.2.1 z hz
    exact ⟨x,hx,congrArg (ZFSet.pair x) (h.correct wf x hx y hy hz)⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨y,hy,hxy,_⟩ := h.2.2.2.1 x hx
    rw [←h.correct wf x hx y hy hxy]
    exact hxy

theorem Graph.unique {d r a b b' f g : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (hf : Graph d r a b f) (hg : Graph d r a b' g) : f = g := by
  apply ZFSet.ext
  intro z
  exact (hf.mem_iff wf z).trans (hg.mem_iff wf z).symm

theorem graph_of_mem_iff (d r a f : ZFSet.{u}) (wf : WellFounded (Rel d r))
    (ha : a ⊆ d) (hc : Closed d r a)
    (hf : ∀ z, z ∈ f ↔ ∃ x ∈ a, z = ZFSet.pair x (value d r wf x)) :
    Graph d r a (iterUnion 2 f) f := by
  have pair (x : ZFSet.{u}) (hx : x ∈ a) : ZFSet.pair x (value d r wf x) ∈ f :=
    (hf _).mpr ⟨x,hx,rfl⟩
  have valmem (x : ZFSet.{u}) (hx : x ∈ a) : value d r wf x ∈ iterUnion 2 f :=
    second_mem_doubleUnion (pair x hx)
  refine ⟨ha,hc,?_,?_,?_⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := (hf z).mp hz
    exact ⟨x,hx,_,valmem x hx,rfl⟩
  · intro x hx
    refine ⟨_,valmem x hx,pair x hx,?_⟩
    intro y _ hxy
    obtain ⟨w,_,heq⟩ := (hf _).mp hxy
    exact (ZFSet.pair_inj.mp heq).1 ▸ (ZFSet.pair_inj.mp heq).2
  · intro x hx v _ hxv
    obtain ⟨w,hw,heq⟩ := (hf _).mp hxv
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
    constructor
    · intro z hz
      obtain ⟨y,hyd,hyx,rfl⟩ := (mem_value d r wf x z).mp hz
      exact ⟨y,hyd,hyx,pair y (hc x hx y hyd hyx)⟩
    · intro y hyd hyx z _ hyz
      obtain ⟨t,_,heq⟩ := (hf _).mp hyz
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
      exact (mem_value d r wf x _).mpr ⟨y,hyd,hyx,rfl⟩

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

theorem nextValue_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hU : BoundedSetTheory.Union M) (hS : Separation M)
    {d r x f : ZFSet.{u}} (hd : d ∈ M) (hr : r ∈ M) (hx : x ∈ M) (hf : f ∈ M) :
    nextValue d r x f ∈ M := by
  let e := cons d (cons x (cons r (cons f (fun _ => d))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|i; exact hd
    rcases i with _|i; exact hx
    rcases i with _|i; exact hr
    rcases i with _|i; exact hf
    exact hd
  simpa only [nextFormula,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e,nextValue] using
    sep_mem M hM hS nextFormula e he (iterUnion_mem M hM hU hf 2)

def certificate : SigmaFormula := .existsSet (.existsSet (.bounded
  (.conj (RelationHull.Code.isHull 1 3 4 5 6) (Code.graph 5 6 1 0 2))))

theorem realize_certificate (M d r q : ZFSet.{u}) (hM : Transitive M)
    (hS : Separation M) (hd : d ∈ M) (hr : r ∈ M) (hqM : q ∈ M)
    (hq : ∀ a, a ∈ q ↔ a ∈ M ∧ a ⊆ d)
    {x f : ZFSet.{u}} (hx : x ∈ d) (hf : f ∈ M) :
    certificate.Realize M (cons f (cons x (cons q (cons d (cons r (fun _ => d)))))) ↔
      ∃ b ∈ M, Graph d r (RelationHull.hull d r q x) b f := by
  have hxM := hM d hd x hx
  have matrix (a b : ZFSet.{u}) (ha : a ∈ M) (hb : b ∈ M) :
      (Formula.conj (RelationHull.Code.isHull 1 3 4 5 6) (Code.graph 5 6 1 0 2)).Realize M
        (cons b (cons a (cons f (cons x (cons q (cons d (cons r (fun _ => d)))))))) ↔
      a = RelationHull.hull d r q x ∧ Graph d r a b f := by
    rw [Formula.absolute _ M hM _ (by
      intro i; rcases i with _|i; exact hb
      rcases i with _|i; exact ha
      rcases i with _|i; exact hf
      rcases i with _|i; exact hxM
      rcases i with _|i; exact hqM
      rcases i with _|i; exact hd
      rcases i with _|i; exact hr
      exact hd)]
    simp only [Formula.Eval,RelationHull.Code.eval_isHull,Code.eval_graph,cons_zero,cons_succ]
    exact and_congr (RelationHull.isHull_iff M d r q hM hS hd hr hqM hq hx) Iff.rfl
  change (∃ a ∈ M, ∃ b ∈ M, _) ↔ _
  constructor
  · rintro ⟨a,ha,b,hb,h⟩
    obtain ⟨rfl,hg⟩ := (matrix a b ha hb).mp h
    exact ⟨b,hb,hg⟩
  · rintro ⟨b,hb,hg⟩
    have ha := RelationHull.hull_mem M d r q hM hS hd hr hqM hxM
    exact ⟨_,ha,b,hb,(matrix _ b ha hb).mpr ⟨rfl,hg⟩⟩

theorem internal_hull_graph (M d r q : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hd : d ∈ M) (hr : r ∈ M) (hqM : q ∈ M)
    (hq : ∀ a, a ∈ q ↔ a ∈ M ∧ a ⊆ d)
    (wf : WellFounded (Rel d r)) (x : ZFSet.{u}) (hx : x ∈ d) :
    ∃ f ∈ M, Graph d r (RelationHull.hull d r q x) (iterUnion 2 f) f := by
  induction x using wf.induction with
  | h x ih =>
    have hxM := hM d hd x hx
    let e := cons q (cons d (cons r (fun _ => d)))
    have he : ∀ i, e i ∈ M := by
      intro i; rcases i with _|i; exact hqM
      rcases i with _|i; exact hd
      rcases i with _|i; exact hr
      exact hd
    have cert (y f : ZFSet.{u}) (hy : y ∈ RelationHull.predecessors d r x) (hf : f ∈ M) :
        certificate.Realize M (cons f (cons y e)) ↔
          ∃ b ∈ M, Graph d r (RelationHull.hull d r q y) b f :=
      realize_certificate M d r q hM hS hd hr hqM hq
        ((RelationHull.mem_predecessors _ _ _ _).mp hy).1 hf
    have predM := RelationHull.predecessors_mem M hM hS hd hr hxM
    obtain ⟨B,hB,hBdef⟩ := hR certificate e he _ predM (by
      intro y hy
      have hyr := (RelationHull.mem_predecessors _ _ _ _).mp hy
      obtain ⟨f,hf,hfg⟩ := ih y hyr hyr.1
      refine ⟨f,hf,(cert y f hy hf).mpr ⟨_,iterUnion_mem M hM hU hf 2,hfg⟩,?_⟩
      intro g hg hcg
      obtain ⟨b,_,hgg⟩ := (cert y g hy hg).mp hcg
      exact hgg.unique wf hfg)
    have hBg (f : ZFSet.{u}) : f ∈ B ↔
        ∃ y ∈ RelationHull.predecessors d r x, ∃ b ∈ M,
          Graph d r (RelationHull.hull d r q y) b f := by
      constructor
      · intro hf
        have hfM := hM B hB f hf
        obtain ⟨y,hy,hc⟩ := (hBdef f hfM).mp hf
        exact ⟨y,hy,(cert y f hy hfM).mp hc⟩
      · rintro ⟨y,hy,b,hb,hg⟩
        have hyr := (RelationHull.mem_predecessors _ _ _ _).mp hy
        obtain ⟨f',hf',hg'⟩ := ih y hyr hyr.1
        have hfM : f ∈ M := hg.unique wf hg' ▸ hf'
        exact (hBdef f hfM).mpr ⟨y,hy,(cert y f hy hfM).mpr ⟨b,hb,hg⟩⟩
    let g := ZFSet.sUnion B
    have hgM : g ∈ M := union_mem M hM hU hB
    have hg (z : ZFSet.{u}) : z ∈ g ↔
        ∃ y ∈ RelationHull.predecessors d r x, ∃ w ∈ RelationHull.hull d r q y,
          z = ZFSet.pair w (value d r wf w) := by
      constructor
      · intro hz
        obtain ⟨f,hf,hzf⟩ := ZFSet.mem_sUnion.mp hz
        obtain ⟨y,hy,b,_,hfg⟩ := (hBg f).mp hf
        exact ⟨y,hy,(hfg.mem_iff wf z).mp hzf⟩
      · rintro ⟨y,hy,w,hw,hz⟩
        have hyr := (RelationHull.mem_predecessors _ _ _ _).mp hy
        obtain ⟨f,hf,hfg⟩ := ih y hyr hyr.1
        exact ZFSet.mem_sUnion.mpr ⟨f,(hBg f).mpr
          ⟨y,hy,_,iterUnion_mem M hM hU hf 2,hfg⟩,(hfg.mem_iff wf z).mpr ⟨w,hw,hz⟩⟩
    have hvalue : nextValue d r x g = value d r wf x := by
      apply ZFSet.ext
      intro z
      rw [mem_nextValue,mem_value]
      constructor
      · rintro ⟨y,hyd,hyx,hyz⟩
        obtain ⟨a,_,w,_,heq⟩ := (hg _).mp hyz
        obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
        exact ⟨y,hyd,hyx,rfl⟩
      · rintro ⟨y,hyd,hyx,rfl⟩
        exact ⟨y,hyd,hyx,(hg _).mpr
          ⟨y,(RelationHull.mem_predecessors _ _ _ _).mpr ⟨hyd,hyx⟩,
            y,RelationHull.self_mem d r q hyd,rfl⟩⟩
    have hvM : value d r wf x ∈ M := hvalue ▸ nextValue_mem M hM hU hS hd hr hxM hgM
    let f := g ∪ ({ZFSet.pair x (value d r wf x)} : ZFSet.{u})
    have hfM : f ∈ M := binary_union_mem M hM hP hU hgM
      (singleton_mem M hM hP (orderedPair_mem M hM hP hxM hvM))
    refine ⟨f,hfM,graph_of_mem_iff d r _ f wf (RelationHull.hull_subset d r q x)
      (RelationHull.hull_closed d r q x) ?_⟩
    intro z
    change z ∈ g ∪ ({ZFSet.pair x (value d r wf x)} : ZFSet.{u}) ↔ _
    rw [ZFSet.mem_union,ZFSet.mem_singleton,hg]
    constructor
    · rintro (⟨y,hy,w,hw,hz⟩|hz)
      · exact ⟨w,(RelationHull.hull_unfold M d r q hM hP hU hS hR hd hr hqM hq hx w).mpr
          (Or.inr ⟨y,hy,hw⟩),hz⟩
      · exact ⟨x,RelationHull.self_mem d r q hx,hz⟩
    · rintro ⟨w,hw,hz⟩
      rcases (RelationHull.hull_unfold M d r q hM hP hU hS hR hd hr hqM hq hx w).mp hw with rfl|⟨y,hy,hw⟩
      · exact Or.inr hz
      · exact Or.inl ⟨y,hy,w,hw,hz⟩

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

theorem internal_graph (M d r : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hd : d ∈ M) (hr : r ∈ M) (wf : WellFounded (Rel d r)) :
    ∃ f ∈ M, Graph d r d (iterUnion 2 f) f := by
  obtain ⟨q,hqM,hq⟩ := internal_power M hM hPow hd
  let e := cons q (cons d (cons r (fun _ => d)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|i; exact hqM
    rcases i with _|i; exact hd
    rcases i with _|i; exact hr
    exact hd
  have cert (x f : ZFSet.{u}) (hx : x ∈ d) (hf : f ∈ M) :
      certificate.Realize M (cons f (cons x e)) ↔
        ∃ b ∈ M, Graph d r (RelationHull.hull d r q x) b f :=
    realize_certificate M d r q hM hS hd hr hqM hq hx hf
  obtain ⟨B,hB,hBdef⟩ := hR certificate e he d hd (by
    intro x hx
    obtain ⟨f,hf,hfg⟩ := internal_hull_graph M d r q hM hP hU hS hR hd hr hqM hq wf x hx
    refine ⟨f,hf,(cert x f hx hf).mpr ⟨_,iterUnion_mem M hM hU hf 2,hfg⟩,?_⟩
    intro g hg hcg
    obtain ⟨b,_,hgg⟩ := (cert x g hx hg).mp hcg
    exact hgg.unique wf hfg)
  have hBg (f : ZFSet.{u}) : f ∈ B ↔
      ∃ x ∈ d, ∃ b ∈ M, Graph d r (RelationHull.hull d r q x) b f := by
    constructor
    · intro hf
      have hfM := hM B hB f hf
      obtain ⟨x,hx,hc⟩ := (hBdef f hfM).mp hf
      exact ⟨x,hx,(cert x f hx hfM).mp hc⟩
    · rintro ⟨x,hx,b,hb,hg⟩
      obtain ⟨g,hgM,hgg⟩ := internal_hull_graph M d r q hM hP hU hS hR hd hr hqM hq wf x hx
      have hfM : f ∈ M := hg.unique wf hgg ▸ hgM
      exact (hBdef f hfM).mpr ⟨x,hx,(cert x f hx hfM).mpr ⟨b,hb,hg⟩⟩
  refine ⟨ZFSet.sUnion B,union_mem M hM hU hB,
    graph_of_mem_iff d r d _ wf (fun _ h => h) (fun _ _ _ h _ => h) ?_⟩
  intro z
  rw [ZFSet.mem_sUnion]
  constructor
  · rintro ⟨f,hf,hzf⟩
    obtain ⟨x,_,b,_,hfg⟩ := (hBg f).mp hf
    obtain ⟨y,hy,hz⟩ := (hfg.mem_iff wf z).mp hzf
    exact ⟨y,RelationHull.hull_subset d r q x hy,hz⟩
  · rintro ⟨x,hx,hz⟩
    obtain ⟨f,hf,hfg⟩ := internal_hull_graph M d r q hM hP hU hS hR hd hr hqM hq wf x hx
    exact ⟨f,(hBg f).mpr ⟨x,hx,_,iterUnion_mem M hM hU hf 2,hfg⟩,
      (hfg.mem_iff wf z).mpr ⟨x,RelationHull.self_mem d r q hx,hz⟩⟩

namespace Code

def full (d r f : ℕ) : SigmaFormula :=
  .existsSet (.bounded (graph (d+1) (r+1) (d+1) 0 (f+1)))

theorem realize_full (M : ZFSet.{u}) (hM : Transitive M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (d r f : ℕ) :
    (full d r f).Realize M e ↔ ∃ b ∈ M, Graph (e d) (e r) (e d) b (e f) := by
  change (∃ b ∈ M, _) ↔ _
  apply exists_congr
  intro b
  apply and_congr_right
  intro hb
  simp only [SigmaFormula.Realize]
  rw [Formula.absolute _ M hM _ (by intro i; cases i with
    | zero => exact hb
    | succ i => exact he i)]
  exact eval_graph (d+1) (r+1) (d+1) 0 (f+1) _
end Code

end TuringRigidity.RelationCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_CollapseCollection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory
universe u

theorem collect_graphs (M d : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hd : d ∈ M) :
    ∃ B ∈ M, ∀ f, f ∈ B ↔ f ∈ M ∧ ∃ r ∈ M, On d r ∧ ∃ b ∈ M, Graph d r d b f := by
  obtain ⟨q,hq,hqdef⟩ := internal_power M hM hPow
    (product_mem M hM hP hU hPow hS.bounded hd hd)
  let e := fun _ : ℕ => d
  let success := SigmaFormula.existsSet (Code.full 2 1 0)
  let a := ZFSet.sep (fun r => success.Realize M (cons r e)) q
  have ha : a ∈ M := sigma_sep_mem M hM hS success e (fun _ => hd) hq
  have cert (r f : ZFSet.{u}) (hr : r ∈ M) (hf : f ∈ M) :
      (Code.full 2 1 0).Realize M (cons f (cons r e)) ↔ ∃ b ∈ M, Graph d r d b f :=
    Code.realize_full M hM _ (by
      intro i; rcases i with _|i; exact hf
      rcases i with _|i; exact hr
      exact hd) 2 1 0
  have ha_def (r : ZFSet.{u}) : r ∈ a ↔
      r ∈ M ∧ On d r ∧ ∃ f ∈ M, ∃ b ∈ M, Graph d r d b f := by
    rw [ZFSet.mem_sep,hqdef]
    change (r ∈ M ∧ On d r) ∧ (∃ f ∈ M, _) ↔ _
    constructor
    · rintro ⟨⟨hr,hrd⟩,f,hf,hc⟩
      exact ⟨hr,hrd,f,hf,(cert r f hr hf).mp hc⟩
    · rintro ⟨hr,hrd,f,hf,b,hb,hg⟩
      exact ⟨⟨hr,hrd⟩,f,hf,(cert r f hr hf).mpr ⟨b,hb,hg⟩⟩
  obtain ⟨B,hB,hBdef⟩ := hR (Code.full 2 1 0) e (fun _ => hd) a ha (by
    intro r hr
    obtain ⟨hrM,hrd,f,hf,b,hb,hfg⟩ := (ha_def r).mp hr
    refine ⟨f,hf,(cert r f hrM hf).mpr ⟨b,hb,hfg⟩,?_⟩
    intro g hg hcg
    obtain ⟨b',_,hgg⟩ := (cert r g hrM hg).mp hcg
    exact hgg.unique (hfg.wellFounded hrd) hfg)
  refine ⟨B,hB,fun f => ?_⟩
  constructor
  · intro hf
    have hfM := hM B hB f hf
    obtain ⟨r,hr,hc⟩ := (hBdef f hfM).mp hf
    obtain ⟨hrM,hrd,_⟩ := (ha_def r).mp hr
    exact ⟨hfM,r,hrM,hrd,(cert r f hrM hfM).mp hc⟩
  · rintro ⟨hf,r,hr,hrd,b,hb,hg⟩
    exact (hBdef f hf).mpr ⟨r,(ha_def r).mpr ⟨hr,hrd,f,hf,b,hb,hg⟩,
      (cert r f hr hf).mpr ⟨b,hb,hg⟩⟩

theorem internal_value_bound (M d : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hd : d ∈ M) :
    ∃ W ∈ M, ∀ r ∈ M, On d r → ∀ wf : WellFounded (Rel d r),
      ∀ x ∈ d, value d r wf x ∈ W := by
  obtain ⟨B,hB,hBdef⟩ := collect_graphs M d hM hP hU hPow hS hR hd
  let W := iterUnion 2 (ZFSet.sUnion B)
  have hW : W ∈ M := iterUnion_mem M hM hU (union_mem M hM hU hB) 2
  refine ⟨W,hW,?_⟩
  intro r hr hrd wf x hx
  obtain ⟨f,hf,hfg⟩ := internal_graph M d r hM hP hU hPow hS.bounded hR hd hr wf
  have hfB := (hBdef f).mpr ⟨hf,r,hr,hrd,_,iterUnion_mem M hM hU hf 2,hfg⟩
  have hpair := (hfg.mem_iff wf _).mpr ⟨x,hx,rfl⟩
  exact second_mem_doubleUnion (ZFSet.mem_sUnion.mpr ⟨f,hfB,hpair⟩)

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

theorem codedRelation_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    {d a f : ZFSet.{u}} (hd : d ∈ M) (ha : a ∈ M) (hf : f ∈ M) :
    codedRelation d a f ∈ M := by
  let e := cons d (cons a (cons f (fun _ => d)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|i; exact hd
    rcases i with _|i; exact ha
    rcases i with _|i; exact hf
    exact hd
  simpa only [codedFormula,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    e,cons_zero,cons_succ,codedRelation] using
    sep_mem M hM hS codedFormula e he (product_mem M hM hP hU hPow hS hd hd)

theorem codedRelation_value {d a f : ZFSet.{u}} {j : ZFSet.{u} → ZFSet.{u}}
    (ha : Transitive a) (hf : Presents a f j) (hj : ∀ x ∈ a, j x ∈ d)
    (hi : ∀ x ∈ a, ∀ y ∈ a, j x = j y → x = y)
    (wf : WellFounded (Rel d (codedRelation d a f)))
    (x : ZFSet.{u}) (hx : x ∈ a) : value d (codedRelation d a f) wf (j x) = x := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    apply ZFSet.ext
    intro z
    rw [mem_value]
    constructor
    · rintro ⟨u,_,hux,hz⟩
      obtain ⟨y,hy,w,hw,hyw,rfl,hwx⟩ := (codedRelation_pair hf hj u (j x)).mp hux
      have hwx' : x = w := hi x hx w hw hwx
      subst w
      rw [ih y hyw hy] at hz
      exact hz ▸ hyw
    · intro hz
      have hza := ha x hx z hz
      refine ⟨j z,hj z hza,(codedRelation_pair hf hj _ _).mpr
        ⟨z,hza,x,hx,hz,rfl,rfl⟩,?_⟩
      exact (ih z hz hza).symm

theorem internal_small_transitive_bound (M d : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hd : d ∈ M) :
    ∃ W ∈ M, ∀ a ∈ M, Transitive a → ∀ f ∈ M, ∀ j : ZFSet.{u} → ZFSet.{u},
      Presents a f j → (∀ x ∈ a, j x ∈ d) →
      (∀ x ∈ a, ∀ y ∈ a, j x = j y → x = y) → a ⊆ W := by
  obtain ⟨W,hW,hbound⟩ := internal_value_bound M d hM hP hU hPow hS hR hd
  refine ⟨W,hW,?_⟩
  intro a ha hat f hf j hfj hj hi x hx
  have hr := codedRelation_mem M hM hP hU hPow hS.bounded hd ha hf
  have wf := codedRelation_wellFounded hfj hj hi
  have hv := hbound _ hr (codedRelation_on d a f) wf (j x) (hj x hx)
  rw [codedRelation_value hat hfj hj hi wf x hx] at hv
  exact hv

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

noncomputable def structureMap (d : ZFSet.{u}) : ZFSet.{u} → ZFSet.{u} :=
  value d (membershipRelation d) (membershipRelation_wellFounded d)

end TuringRigidity.RelationCollapse

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

def matrix : SigmaFormula → Formula
  | .bounded φ => φ
  | .existsSet φ => matrix φ

def prefixLength : SigmaFormula → ℕ
  | .bounded _ => 0
  | .existsSet φ => prefixLength φ+1

theorem realize_iff_prefix (φ : SigmaFormula) (d : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    φ.Realize d e ↔ ∃ xs : List ZFSet.{u}, xs.length = φ.prefixLength ∧
      (∀ x ∈ xs, x ∈ d) ∧ φ.matrix.Realize d (feed xs e) := by
  induction φ generalizing e with
  | bounded φ =>
    constructor
    · intro h; exact ⟨[],rfl,by simp,h⟩
    · rintro ⟨xs,hlen,_,hφ⟩
      have heq : xs = [] := List.length_eq_zero_iff.mp hlen
      subst xs; exact hφ
  | existsSet φ ih =>
    constructor
    · rintro ⟨x,hx,hφ⟩
      obtain ⟨xs,hlen,hxs,hmat⟩ := (ih (cons x e)).mp hφ
      refine ⟨x::xs,congrArg Nat.succ hlen,?_,hmat⟩
      intro y hy; rcases List.mem_cons.mp hy with rfl|hy
      · exact hx
      · exact hxs y hy
    · rintro ⟨xs,hlen,hxs,hmat⟩
      cases xs with
      | nil => simp [prefixLength] at hlen
      | cons x xs =>
        refine ⟨x,hxs x List.mem_cons_self,(ih (cons x e)).mpr ?_⟩
        exact ⟨xs,Nat.succ.inj hlen,fun y hy => hxs y (List.mem_cons_of_mem _ hy),hmat⟩
end SigmaFormula
namespace FiniteTuple

theorem elements_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (hU : BoundedSetTheory.Union M) (h0 : (∅ : ZFSet.{u}) ∈ M)
    (xs : List ZFSet.{u}) (hxs : ∀ x ∈ xs, x ∈ M) : elements xs ∈ M := by
  induction xs with
  | nil => exact h0
  | cons x xs ih =>
    exact binary_union_mem M hM hP hU
      (singleton_mem M hM hP (hxs x List.mem_cons_self))
      (ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy)))

end FiniteTuple
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

theorem indexSpace_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hω : ZFSet.omega.{u} ∈ M) {t : ZFSet.{u}} (ht : t ∈ M) : indexSpace t ∈ M := by
  have hn (n : ℕ) : natSet.{u} n ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)
  exact binary_union_mem M hM hP hU
    (product_mem M hM hP hU hPow hS (singleton_mem M hM hP (hn 0)) ht)
    (product_mem M hM hP hU hPow hS (singleton_mem M hM hP (hn 1)) hω)

theorem internal_finite_extension_injection (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hω : ZFSet.omega.{u} ∈ M)
    {t : ZFSet.{u}} (ht : t ∈ M) (xs : List ZFSet.{u}) (hxs : ∀ x ∈ xs, x ∈ M) :
    ∃ f ∈ M, Presents (t ∪ elements xs) f (finiteIndex t xs) := by
  classical
  have hn (n : ℕ) : natSet.{u} n ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)
  have hk := indexSpace_mem M hM hP hU hPow hS hω ht
  let j := finiteIndex t xs
  have hj (x : ZFSet.{u}) : j x ∈ M := hM _ hk _ (finiteIndex_mem t xs x)
  let φ : Formula := .existsMem 2 (.conj (.orderedPair 1 2 0) (.orderedPair 0 4 2))
  let e := cons (indexSpace t) (fun _ => natSet 0)
  have he : ∀ i, e i ∈ M := by intro i; cases i with
    | zero => exact hk
    | succ => exact hn 0
  obtain ⟨b,hb,hbdef⟩ := replacement_image M hM hR (.bounded φ) e he ht
    (fun x => ZFSet.pair x (ZFSet.pair (natSet 0) x))
    (fun x hx => orderedPair_mem M hM hP (hM t ht x hx)
      (orderedPair_mem M hM hP (hn 0) (hM t ht x hx))) (by
      intro x hx y hy
      change φ.Realize M (cons y (cons x e)) ↔ _
      rw [Formula.absolute _ M hM _ (by
        intro i; rcases i with _|i; exact hy
        rcases i with _|i; exact hM t ht x hx
        exact he i)]
      simp only [φ,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e]
      constructor
      · rintro ⟨v,_,hy,rfl⟩; exact hy
      · intro hy
        have hjx := finiteIndex_mem t xs x
        rw [finiteIndex,ite_eq_left hx] at hjx
        exact ⟨_,hjx,hy,rfl⟩)
  let f := b ∪ elements (xs.map (fun x => ZFSet.pair x (j x)))
  have hf : f ∈ M := binary_union_mem M hM hP hU hb
    (elements_mem M hM hP hU (hn 0) _ (by
      intro z hz
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
      exact orderedPair_mem M hM hP (hxs x hx) (hj x)))
  refine ⟨f,hf,?_⟩
  intro z
  change z ∈ b ∪ elements (xs.map (fun x => ZFSet.pair x (j x))) ↔ _
  rw [ZFSet.mem_union,hbdef,mem_elements,List.mem_map]
  constructor
  · rintro (⟨x,hx,rfl⟩|⟨x,hx,rfl⟩)
    · refine ⟨x,ZFSet.mem_union.mpr (Or.inl hx),?_⟩
      simp only [finiteIndex,ite_eq_left hx]
    · exact ⟨x,ZFSet.mem_union.mpr (Or.inr ((mem_elements x xs).mpr hx)),rfl⟩
  · rintro ⟨x,hx,rfl⟩
    rcases ZFSet.mem_union.mp hx with hx|hx
    · apply Or.inl
      exact ⟨x,hx,by simp only [finiteIndex,ite_eq_left hx]⟩
    · exact Or.inr ⟨x,(mem_elements x xs).mp hx,rfl⟩

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

theorem FiniteCode.mem_model (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (h0 : (∅ : ZFSet.{u}) ∈ M) {t x : ZFSet.{u}} (ht : t ∈ M) (hx : FiniteCode t x) : x ∈ M := by
  induction hx with
  | atom x hx => exact hM t ht x hx
  | empty => exact h0
  | pair _ _ ihx ihy => exact pair_mem M hM hP ihx ihy

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

theorem tag_inj (n m : ℕ) (x y : ZFSet.{u}) : tag n x = tag m y ↔ n = m ∧ x = y := by
  rw [tag,tag,ZFSet.pair_inj]
  exact and_congr ⟨fun h => natSet_injective h,fun h => congrArg natSet h⟩ Iff.rfl

inductive Eval (A B L O D : ZFSet.{u}) : ZFSet.{u} → ZFSet.{u} → Prop
  | leaf {a x : ZFSet.{u}} : a ∈ A → x ∈ D → ZFSet.pair a x ∈ L → Eval A B L O D (tag 0 a) x
  | app {o c x y : ZFSet.{u}} : o ∈ B → Eval A B L O D c x → y ∈ D →
      ZFSet.pair (ZFSet.pair o x) y ∈ O → Eval A B L O D (tag 1 (ZFSet.pair o c)) y
  | pair {a b x y : ZFSet.{u}} : Eval A B L O D a x → Eval A B L O D b y →
      ZFSet.pair x y ∈ D → Eval A B L O D (tag 2 (ZFSet.pair a b)) (ZFSet.pair x y)

theorem Eval.value_mem {A B L O D c x : ZFSet.{u}} (h : Eval A B L O D c x) : x ∈ D := by
  cases h with
  | leaf _ hx _ => exact hx
  | app _ _ hx _ => exact hx
  | pair _ _ hx => exact hx

theorem Eval.code_finite {A B L O D t c x : ZFSet.{u}}
    (hA : A ⊆ t) (hB : B ⊆ t) (hn : ∀ n, natSet.{u} n ∈ t)
    (h : Eval A B L O D c x) : FiniteTuple.FiniteCode t c := by
  induction h with
  | leaf ha _ _ => exact (FiniteTuple.FiniteCode.atom _ (hn 0)).orderedPair (.atom _ (hA ha))
  | app ho _ _ _ ih =>
    exact (FiniteTuple.FiniteCode.atom _ (hn 1)).orderedPair
      ((FiniteTuple.FiniteCode.atom _ (hB ho)).orderedPair ih)
  | pair _ _ _ iha ihb => exact (FiniteTuple.FiniteCode.atom _ (hn 2)).orderedPair (iha.orderedPair ihb)

def Step (A B L O K D f c v : ZFSet.{u}) : Prop :=
  (∃ a ∈ A, c = tag 0 a ∧ ZFSet.pair a v ∈ L) ∨
  (∃ o ∈ B, ∃ a ∈ K, ∃ x ∈ D, c = tag 1 (ZFSet.pair o a) ∧
    ZFSet.pair a x ∈ f ∧ ZFSet.pair (ZFSet.pair o x) v ∈ O) ∨
  (∃ a ∈ K, ∃ b ∈ K, ∃ x ∈ D, ∃ y ∈ D, c = tag 2 (ZFSet.pair a b) ∧
    ZFSet.pair a x ∈ f ∧ ZFSet.pair b y ∈ f ∧ v = ZFSet.pair x y)

def Certificate (A B L O K D f : ZFSet.{u}) : Prop :=
  ∀ z ∈ f, ∃ c ∈ K, ∃ v ∈ D, z = ZFSet.pair c v ∧ Step A B L O K D f c v

theorem Step.mono {A B L O K D f g c v : ZFSet.{u}} (hfg : f ⊆ g)
    (h : Step A B L O K D f c v) : Step A B L O K D g c v := by
  rcases h with h|h|h
  · exact Or.inl h
  · obtain ⟨o,ho,a,ha,x,hx,hc,hax,hox⟩ := h
    exact Or.inr (Or.inl ⟨o,ho,a,ha,x,hx,hc,hfg hax,hox⟩)
  · obtain ⟨a,ha,b,hb,x,hx,y,hy,hc,hax,hby,hv⟩ := h
    exact Or.inr (Or.inr ⟨a,ha,b,hb,x,hx,y,hy,hc,hfg hax,hfg hby,hv⟩)

theorem Certificate.subset {A B L O K D f : ZFSet.{u}} (hf : Certificate A B L O K D f) :
    f ⊆ ZFSet.prod K D := by
  intro z hz
  obtain ⟨c,hc,v,hv,hz,_⟩ := hf z hz
  exact ZFSet.mem_prod.mpr ⟨c,hc,v,hv,hz⟩

theorem Certificate.step {A B L O K D f c v : ZFSet.{u}}
    (hf : Certificate A B L O K D f) (hp : ZFSet.pair c v ∈ f) :
    c ∈ K ∧ v ∈ D ∧ Step A B L O K D f c v := by
  obtain ⟨c',hc,v',hv,he,hs⟩ := hf _ hp
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  exact ⟨hc,hv,hs⟩

theorem Certificate.sound {A B L O K D f : ZFSet.{u}}
    (hf : Certificate A B L O K D f) (c v : ZFSet.{u})
    (hp : ZFSet.pair c v ∈ f) : Eval A B L O D c v := by
  have wf : WellFounded (fun a b : ZFSet.{u} => ZFSet.rank a < ZFSet.rank b) :=
    InvImage.wf ZFSet.rank Ordinal.lt_wf
  induction c using wf.induction generalizing v with
  | h c ih =>
    have hv := (hf.step hp).2.1
    rcases (hf.step hp).2.2 with h|h|h
    · obtain ⟨a,ha,rfl,hav⟩ := h
      exact .leaf ha hv hav
    · obtain ⟨o,ho,a,_,x,_,rfl,hax,hov⟩ := h
      have hlt := (pair_rank_right o a).trans (pair_rank_right (natSet 1) (ZFSet.pair o a))
      exact .app ho (ih a hlt x hax) hv hov
    · obtain ⟨a,_,b,_,x,_,y,_,rfl,hax,hby,rfl⟩ := h
      have ha := (pair_rank_left a b).trans (pair_rank_right (natSet 2) (ZFSet.pair a b))
      have hb := (pair_rank_right a b).trans (pair_rank_right (natSet 2) (ZFSet.pair a b))
      exact .pair (ih a ha x hax) (ih b hb y hby) hv

end FiniteTerm
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

theorem Certificate.union {A B L O K D f g : ZFSet.{u}}
    (hf : Certificate A B L O K D f) (hg : Certificate A B L O K D g) :
    Certificate A B L O K D (f ∪ g) := by
  intro z hz
  rcases ZFSet.mem_union.mp hz with hz|hz
  · obtain ⟨c,hc,v,hv,rfl,hs⟩ := hf z hz
    exact ⟨c,hc,v,hv,rfl,hs.mono (fun _ hx => ZFSet.mem_union.mpr (Or.inl hx))⟩
  · obtain ⟨c,hc,v,hv,rfl,hs⟩ := hg z hz
    exact ⟨c,hc,v,hv,rfl,hs.mono (fun _ hx => ZFSet.mem_union.mpr (Or.inr hx))⟩

theorem Certificate.adjoin {A B L O K D f c v : ZFSet.{u}}
    (hf : Certificate A B L O K D f) (hc : c ∈ K) (hv : v ∈ D)
    (hs : Step A B L O K D (f ∪ ({ZFSet.pair c v} : ZFSet.{u})) c v) :
    Certificate A B L O K D (f ∪ ({ZFSet.pair c v} : ZFSet.{u})) := by
  intro z hz
  rcases ZFSet.mem_union.mp hz with hz|hz
  · obtain ⟨a,ha,x,hx,rfl,hax⟩ := hf z hz
    exact ⟨a,ha,x,hx,rfl,hax.mono (fun _ hx => ZFSet.mem_union.mpr (Or.inl hx))⟩
  · obtain rfl := ZFSet.mem_singleton.mp hz
    exact ⟨c,hc,v,hv,rfl,hs⟩

end FiniteTerm
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
namespace FiniteTerm
open Formula

theorem eval_stepFormula (c v A B L O K D f z o t : ℕ) (e : ℕ → ZFSet.{u})
    (hz : e z = natSet 0) (ho : e o = natSet 1) (ht : e t = natSet 2) :
    (stepFormula c v A B L O K D f z o t).Eval e ↔
      Step (e A) (e B) (e L) (e O) (e K) (e D) (e f) (e c) (e v) := by
  simp only [stepFormula,Formula.Eval,eval_disj,eval_orderedPair,eval_rightPair,eval_pairMem,
    eval_appMem,cons_zero,cons_succ,hz,ho,ht,Step,tag]

theorem eval_certificateFormula (A B L O K D f z o t : ℕ) (e : ℕ → ZFSet.{u})
    (hz : e z = natSet 0) (ho : e o = natSet 1) (ht : e t = natSet 2) :
    (certificateFormula A B L O K D f z o t).Eval e ↔
      Certificate (e A) (e B) (e L) (e O) (e K) (e D) (e f) := by
  simp only [certificateFormula,eval_allMem,Formula.Eval,eval_orderedPair,cons_zero,cons_succ]
  apply forall_congr'; intro w
  apply forall_congr'; intro _
  apply exists_congr; intro c
  apply and_congr_right; intro _
  apply exists_congr; intro v
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  exact eval_stepFormula 1 0 (A+3) (B+3) (L+3) (O+3) (K+3) (D+3) (f+3)
    (z+3) (o+3) (t+3) (cons v (cons c (cons w e))) hz ho ht

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

theorem eval_graphFormula (z q A B L O K D : ZFSet.{u}) :
    graphFormula.Eval (cons z (cons q (cons A (cons B (cons L (cons O (cons K (cons D
      (cons (natSet 0) (cons (natSet 1) (fun _ => natSet 2))))))))))) ↔
    ∃ c ∈ K, ∃ v ∈ D, z = ZFSet.pair c v ∧ ∃ f ∈ q,
      Certificate A B L O K D f ∧ ZFSet.pair c v ∈ f := by
  simp only [graphFormula,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ]
  apply exists_congr; intro c
  apply and_congr_right; intro _
  apply exists_congr; intro v
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply exists_congr; intro f
  apply and_congr_right; intro _
  apply and_congr_left; intro _
  exact eval_certificateFormula 5 6 7 8 9 10 0 11 12 13
    (cons f (cons v (cons c (cons z (cons q (cons A (cons B (cons L (cons O (cons K (cons D
      (cons (natSet 0) (cons (natSet 1) (fun _ => natSet 2)))))))))))))) rfl rfl rfl

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

theorem Eval.unfold (A B L O D c v : ZFSet.{u}) : Eval A B L O D c v ↔
    (∃ a ∈ A, v ∈ D ∧ c = tag 0 a ∧ ZFSet.pair a v ∈ L) ∨
    (∃ o ∈ B, ∃ a x, Eval A B L O D a x ∧ v ∈ D ∧
      c = tag 1 (ZFSet.pair o a) ∧ ZFSet.pair (ZFSet.pair o x) v ∈ O) ∨
    (∃ a b x y, Eval A B L O D a x ∧ Eval A B L O D b y ∧ v ∈ D ∧
      c = tag 2 (ZFSet.pair a b) ∧ v = ZFSet.pair x y) := by
  constructor
  · intro h; cases h with
    | @leaf a x ha hx hax => exact Or.inl ⟨a,ha,hx,rfl,hax⟩
    | @app o c x y ho hx hy hox => exact Or.inr (Or.inl ⟨o,ho,c,x,hx,hy,rfl,hox⟩)
    | @pair a b x y ha hb hxy => exact Or.inr (Or.inr ⟨a,b,x,y,ha,hb,hxy,rfl,rfl⟩)
  · rintro (⟨a,ha,hv,rfl,hav⟩|⟨o,ho,a,x,hax,hv,rfl,hov⟩|⟨a,b,x,y,hax,hby,hv,rfl,rfl⟩)
    · exact .leaf ha hv hav
    · exact .app ho hax hv hov
    · exact .pair hax hby hv

theorem Eval.functional {A B L O D c x y : ZFSet.{u}} (hL : Functional L) (hO : Functional O)
    (hx : Eval A B L O D c x) (hy : Eval A B L O D c y) : x = y := by
  induction hx generalizing y with
  | @leaf a x ha hx hax =>
    rcases (Eval.unfold _ _ _ _ _ _ _).mp hy with h|h|h
    · obtain ⟨a',_,_,he,hav⟩ := h
      obtain ⟨_,rfl⟩ := (tag_inj _ _ _ _).mp he
      exact hL _ _ _ hax hav
    · obtain ⟨o,_,b,v,_,_,he,_⟩ := h
      have hh := ((tag_inj _ _ _ _).mp he).1
      omega
    · obtain ⟨b,c,v,w,_,_,_,he,_⟩ := h
      have hh := ((tag_inj _ _ _ _).mp he).1
      omega
  | @app o a x v ho hax hv hov ih =>
    rcases (Eval.unfold _ _ _ _ _ _ _).mp hy with h|h|h
    · obtain ⟨b,_,_,he,_⟩ := h
      have hh := ((tag_inj _ _ _ _).mp he).1
      omega
    · obtain ⟨o',_,a',x',hax',_,he,hov'⟩ := h
      have hp := ((tag_inj _ _ _ _).mp he).2
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
      obtain rfl := ih hax'
      exact hO _ _ _ hov hov'
    · obtain ⟨b,c,w,z,_,_,_,he,_⟩ := h
      have hh := ((tag_inj _ _ _ _).mp he).1
      omega
  | @pair a b x v hax hbv hxv iha ihb =>
    rcases (Eval.unfold _ _ _ _ _ _ _).mp hy with h|h|h
    · obtain ⟨c,_,_,he,_⟩ := h
      have hh := ((tag_inj _ _ _ _).mp he).1
      omega
    · obtain ⟨o,_,c,w,_,_,he,_⟩ := h
      have hh := ((tag_inj _ _ _ _).mp he).1
      omega
    · obtain ⟨a',b',x',v',hax',hbv',_,he,rfl⟩ := h
      have hp := ((tag_inj _ _ _ _).mp he).2
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
      obtain rfl := iha hax'
      obtain rfl := ihb hbv'
      rfl

theorem evaluation_graph_functional {A B L O D E : ZFSet.{u}}
    (hL : Functional L) (hO : Functional O)
    (hE : ∀ c v, ZFSet.pair c v ∈ E ↔ Eval A B L O D c v) : Functional E :=
  fun c x y hx hy => ((hE c x).mp hx).functional hL hO ((hE c y).mp hy)

end FiniteTerm
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

theorem inverseCover_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    {h K E : ZFSet.{u}} (hh : h ∈ M) (hK : K ∈ M) (hE : E ∈ M) : inverseCover h K E ∈ M := by
  simpa only [inverseCover,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ] using
    sep_mem M hM hS (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0) (.pairMem 0 1 5))))
      (cons h (cons K (fun _ => E))) (by
        intro i; rcases i with _|i; exact hh
        rcases i with _|i; exact hK
        exact hE) (product_mem M hM hP hU hPow hS hh hK)

theorem internal_injection_of_cover (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hAC : Choice M) {h K E : ZFSet.{u}}
    (hh : h ∈ M) (hK : K ∈ M) (hE : E ∈ M) (hfun : Functional E)
    (hcover : ∀ x ∈ h, ∃ c ∈ K, ZFSet.pair c x ∈ E) :
    ∃ f ∈ M, ∃ j : ZFSet.{u} → ZFSet.{u}, Presents h f j ∧
      (∀ x ∈ h, j x ∈ K) ∧ (∀ x ∈ h, ZFSet.pair (j x) x ∈ E) ∧
      (∀ x ∈ h, ∀ y ∈ h, j x = j y → x = y) := by
  classical
  have hr := inverseCover_mem M hM hP hU hPow hS hh hK hE
  obtain ⟨f,hf,hfr,hshape,hsel⟩ := internal_relation_choice M hM hP hU hPow hS hAC hh hK hr (by
    intro x hx
    obtain ⟨c,hc,hcx⟩ := hcover x hx
    exact ⟨c,hc,(inverseCover_pair h K E x c).mpr ⟨hx,hc,hcx⟩⟩)
  let j := fun x => if hx : x ∈ h then (hsel x hx).choose else ∅
  have hj (x : ZFSet.{u}) (hx : x ∈ h) : j x ∈ K ∧ ZFSet.pair x (j x) ∈ f ∧
      ∀ c ∈ K, ZFSet.pair x c ∈ f → c = j x := by
    simp only [j,dite_eq_left hx]
    exact (hsel x hx).choose_spec
  have hEpair (x : ZFSet.{u}) (hx : x ∈ h) : ZFSet.pair (j x) x ∈ E :=
    ((inverseCover_pair h K E x (j x)).mp (hfr (hj x hx).2.1)).2.2
  refine ⟨f,hf,j,?_,fun x hx => (hj x hx).1,hEpair,?_⟩
  · intro z
    constructor
    · intro hz
      obtain ⟨x,hx,c,hc,rfl⟩ := hshape z hz
      have hcj := (hj x hx).2.2 c hc hz
      exact ⟨x,hx,congrArg (ZFSet.pair x) hcj⟩
    · rintro ⟨x,hx,rfl⟩
      exact (hj x hx).2.1
  · intro x hx y hy he
    have hyE := hEpair y hy
    rw [← he] at hyE
    exact hfun (j x) x y (hEpair x hx) hyE

theorem internal_evaluated_injection (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hAC : Choice M) {A B L O D E K h : ZFSet.{u}}
    (hh : h ∈ M) (hK : K ∈ M) (hE : E ∈ M)
    (hL : Functional L) (hO : Functional O) (hsub : E ⊆ ZFSet.prod K D)
    (hgraph : ∀ c v, ZFSet.pair c v ∈ E ↔ Eval A B L O D c v)
    (hcover : ∀ x ∈ h, ∃ c, Eval A B L O D c x) :
    ∃ f ∈ M, ∃ j : ZFSet.{u} → ZFSet.{u}, Presents h f j ∧
      (∀ x ∈ h, j x ∈ K) ∧ (∀ x ∈ h, ∀ y ∈ h, j x = j y → x = y) := by
  have hc : ∀ x ∈ h, ∃ c ∈ K, ZFSet.pair c x ∈ E := by
    intro x hx
    obtain ⟨c,hcx⟩ := hcover x hx
    have hp := (hgraph c x).mpr hcx
    obtain ⟨c',hc',v,_,he⟩ := ZFSet.mem_prod.mp (hsub hp)
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨c,hc',hp⟩
  obtain ⟨f,hf,j,hfj,hj,_,hi⟩ := internal_injection_of_cover M hM hP hU hPow hS hAC hh hK hE
    (evaluation_graph_functional hL hO hgraph) hc
  exact ⟨f,hf,j,hfj,hj,hi⟩

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

theorem labelGraph_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    {a b g o : ZFSet.{u}} (ha : a ∈ M) (hb : b ∈ M) (hg : g ∈ M) (ho : o ∈ M) :
    labelGraph a b g o ∈ M := by
  simpa only [labelGraph,Formula.Eval,Formula.eval_leftPair,Formula.eval_pairMem,cons_zero,cons_succ] using
    sep_mem M hM hS (.existsMem 1 (.existsMem 3 (.conj (.leftPair 2 5 1 0) (.pairMem 1 0 6))))
      (cons a (cons b (cons o (fun _ => g)))) (by
        intro i; rcases i with _|i; exact ha
        rcases i with _|i; exact hb
        rcases i with _|i; exact ho
        exact hg)
      (product_mem M hM hP hU hPow hS
        (product_mem M hM hP hU hPow hS (singleton_mem M hM hP ho) ha) hb)

theorem internal_skolem_operations (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M)
    {d : ZFSet.{u}} (hd : d ∈ M) (n : ℕ) (fs : List Formula) (start : ℕ) :
    ∃ O ∈ M, Functional O ∧
      (∀ z ∈ O, ∃ i, start ≤ i ∧ ∃ c v, z = ZFSet.pair (ZFSet.pair (natSet i) c) v) ∧
      ∀ φ ∈ fs, ∃ i : ℕ, ∃ g ∈ M, FiniteTuple.SkolemGraph d n φ (fun _ => d) g ∧
        ∀ c v, ZFSet.pair c v ∈ g → ZFSet.pair (ZFSet.pair (natSet i) c) v ∈ O := by
  have hω := omega_mem M hM hS hI
  have hn (n : ℕ) : natSet.{u} n ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)
  have ha := FiniteTuple.space_mem M hM hP hU hPow hS hd n
  induction fs generalizing start with
  | nil => exact ⟨∅,hn 0,by intro a x y hx; exact False.elim (by simp at hx),by simp,by simp⟩
  | cons φ fs ih =>
    obtain ⟨O,hO,hOf,hOs,hOg⟩ := ih (start+1)
    obtain ⟨g,hg,hgs⟩ := FiniteTuple.internal_skolem_graph M hM hP hU hPow hS hR hI hAC hd n φ
      (fun _ => d) (fun _ => hd)
    let f := labelGraph (FiniteTuple.space d n) d g (natSet start)
    have hf : f ∈ M := labelGraph_mem M hM hP hU hPow hS ha hd hg (hn start)
    have hff : Functional f := labelGraph_functional (skolem_functional hgs)
    have hfshape (z : ZFSet.{u}) (hz : z ∈ f) :
        ∃ c v, z = ZFSet.pair (ZFSet.pair (natSet start) c) v := by
      obtain ⟨c,_,v,_,he,_⟩ := labelGraph_shape hz
      exact ⟨c,v,he⟩
    refine ⟨f ∪ O,binary_union_mem M hM hP hU hf hO,hff.union hOf ?_,?_,?_⟩
    · intro a x y hx hy
      obtain ⟨c,v,hc⟩ := hfshape _ hx
      obtain ⟨i,hi,b,w,hb⟩ := hOs _ hy
      have hac := (ZFSet.pair_inj.mp hc).1
      have hab := (ZFSet.pair_inj.mp hb).1
      have he := natSet_injective (ZFSet.pair_inj.mp (hac.symm.trans hab)).1
      omega
    · intro z hz
      rcases ZFSet.mem_union.mp hz with hz|hz
      · obtain ⟨c,v,he⟩ := hfshape z hz
        exact ⟨start,le_refl _,c,v,he⟩
      · obtain ⟨i,hi,c,v,he⟩ := hOs z hz
        exact ⟨i,by omega,c,v,he⟩
    · intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl|hψ
      · refine ⟨start,g,hg,hgs,?_⟩
        intro c v hcv
        exact ZFSet.mem_union.mpr (Or.inl (labelGraph_contains
          (fun z hz => (ZFSet.mem_sep.mp (hgs.1 hz)).1) hcv))
      · obtain ⟨i,v,hv,hvs,hvo⟩ := hOg ψ hψ
        exact ⟨i,v,hv,hvs,fun c x hcx => ZFSet.mem_union.mpr (Or.inr (hvo c x hcx))⟩

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

theorem internal_leaf_graph (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hω : ZFSet.omega.{u} ∈ M)
    {t : ZFSet.{u}} (ht : t ∈ M) (xs : List ZFSet.{u}) (hxs : ∀ x ∈ xs, x ∈ M) :
    ∃ L ∈ M, Functional L ∧ ∀ x ∈ t ∪ FiniteTuple.elements xs,
      ∃ a ∈ FiniteTuple.indexSpace t, ZFSet.pair a x ∈ L := by
  have h0 : (∅ : ZFSet.{u}) ∈ M := hM _ hω _ ZFSet.omega_zero
  have hs := binary_union_mem M hM hP hU ht (FiniteTuple.elements_mem M hM hP hU h0 xs hxs)
  have hA := FiniteTuple.indexSpace_mem M hM hP hU hPow hS hω ht
  obtain ⟨f,hf,hfg⟩ := FiniteTuple.internal_finite_extension_injection M hM hP hU hPow hS hR hω ht xs hxs
  let L := inverseCover (FiniteTuple.indexSpace t) (t ∪ FiniteTuple.elements xs) f
  have hL := inverseCover_mem M hM hP hU hPow hS hA hs hf
  refine ⟨L,hL,?_,?_⟩
  · intro a x y hx hy
    have hx' := (inverseCover_pair _ _ _ _ _).mp hx
    have hy' := (inverseCover_pair _ _ _ _ _).mp hy
    have hfx := (hfg.pair_iff x a).mp hx'.2.2
    have hfy := (hfg.pair_iff y a).mp hy'.2.2
    exact FiniteTuple.finiteIndex_injective t xs x hfx.1 y hfy.1 (hfx.2.symm.trans hfy.2)
  · intro x hx
    refine ⟨_,FiniteTuple.finiteIndex_mem t xs x,(inverseCover_pair _ _ _ _ _).mpr ?_⟩
    exact ⟨FiniteTuple.finiteIndex_mem t xs x,hx,(hfg.pair_iff x _).mpr ⟨hx,rfl⟩⟩

theorem eval_tuple {A B L O D : ZFSet.{u}} (hD : Transitive D)
    (hzero : ∃ c, Eval A B L O D c ∅) (xs : List ZFSet.{u})
    (hxs : ∀ x ∈ xs, ∃ c, Eval A B L O D c x) (hcode : FiniteTuple.code xs ∈ D) :
    ∃ c, Eval A B L O D c (FiniteTuple.code xs) := by
  induction xs with
  | nil => exact hzero
  | cons x xs ih =>
    obtain ⟨a,ha⟩ := hxs x List.mem_cons_self
    have htail : FiniteTuple.code xs ∈ D := (FiniteTuple.pair_components hD hcode).2
    obtain ⟨b,hb⟩ := ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) htail
    exact ⟨_,Eval.pair ha hb hcode⟩

theorem generatedRange_mem (M : ZFSet.{u}) (hM : Transitive M) (hS : Separation M)
    {d K E : ZFSet.{u}} (hd : d ∈ M) (hK : K ∈ M) (hE : E ∈ M) : generatedRange d K E ∈ M := by
  simpa only [generatedRange,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ] using
    sep_mem M hM hS (.existsMem 1 (.pairMem 0 1 3)) (cons K (fun _ => E))
      (by intro i; cases i <;> assumption) hd

theorem mem_generatedRange {A B L O D d K E : ZFSet.{u}}
    (hE : ∀ c x, ZFSet.pair c x ∈ E ↔ Eval A B L O D c x)
    (hsub : E ⊆ ZFSet.prod K D) (x : ZFSet.{u}) :
    x ∈ generatedRange d K E ↔ x ∈ d ∧ ∃ c, Eval A B L O D c x := by
  rw [generatedRange,ZFSet.mem_sep]
  apply and_congr_right; intro _
  constructor
  · rintro ⟨c,_,hc⟩; exact ⟨c,(hE c x).mp hc⟩
  · rintro ⟨c,hc⟩
    have hcx := (hE c x).mpr hc
    obtain ⟨a,ha,b,_,he⟩ := ZFSet.mem_prod.mp (hsub hcx)
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨c,ha,hcx⟩

theorem generatedRange_closed {A L O V d K E : ZFSet.{u}} (n : ℕ)
    (hV : Transitive V) (hdV : d ⊆ V) (hspace : FiniteTuple.space d n ⊆ V)
    (hE : ∀ c x, ZFSet.pair c x ∈ E ↔ Eval A ZFSet.omega L O V c x)
    (hsub : E ⊆ ZFSet.prod K V) (hzero : ∃ c, Eval A ZFSet.omega L O V c ∅)
    {g : ZFSet.{u}} (hg : g ⊆ ZFSet.prod (FiniteTuple.space d n) d) (i : ℕ)
    (hop : ∀ c x, ZFSet.pair c x ∈ g → ZFSet.pair (ZFSet.pair (natSet i) c) x ∈ O) :
    FiniteTuple.Closed n g (generatedRange d K E) := by
  intro xs hlen hxs y hy
  have hxsd : ∀ x ∈ xs, x ∈ d := fun x hx => ((mem_generatedRange hE hsub x).mp (hxs x hx)).1
  have hcode : FiniteTuple.code xs ∈ V := hspace (hlen ▸ FiniteTuple.code_mem_space d xs hxsd)
  obtain ⟨c,hc⟩ := eval_tuple hV hzero xs
    (fun x hx => ((mem_generatedRange hE hsub x).mp (hxs x hx)).2) hcode
  have hyd : y ∈ d := by
    obtain ⟨a,_,b,hb,he⟩ := ZFSet.mem_prod.mp (hg hy)
    obtain ⟨_,rfl⟩ := ZFSet.pair_inj.mp he
    exact hb
  apply (mem_generatedRange hE hsub y).mpr
  exact ⟨hyd,_,Eval.app ((mem_omega _).mpr ⟨i,rfl⟩) hc (hdV hyd) (hop _ _ hy)⟩
end FiniteTerm
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

def scope : SigmaFormula → ℕ
  | .bounded φ => φ.scope
  | .existsSet φ => φ.scope-1

end SigmaFormula

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

theorem realize_witnessRequest (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (φ : SigmaFormula) (e : ℕ → Name (Conditions c)) (he : ∀ i, (e i).encode (label c) ∈ M)
    (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) (p : Conditions c)
    {x : ZFSet.{u}} (hx : x ∈ M) :
    (WitnessCode.request φ).Realize M (cons x
      (cons (ZFSet.pair (a.encode (label c)) (label c p))
        (cons c (cons o (fun i => (e i).encode (label c)))))) ↔
      ∃ b : Name (Conditions c), b.encode (label c) = x ∧ SigmaForces M (push b (push a e)) φ p := by
  let base := cons x (cons (ZFSet.pair (a.encode (label c)) (label c p))
    (cons c (cons o (fun i => (e i).encode (label c)))))
  have hpM := hM c hc _ (label_mem c p)
  have hreq := orderedPair_mem M hM hP ha hpM
  have hbM : ∀ i, base i ∈ M := by
    intro i; rcases i with _|i; exact hx
    rcases i with _|i; exact hreq
    rcases i with _|i; exact hc
    rcases i with _|i; exact hoM
    exact he i
  have envM (z q : ZFSet.{u}) (hz : z ∈ M) (hq : q ∈ M) : ∀ i, cons q (cons z base) i ∈ M := by
    intro i; rcases i with _|i; exact hq
    rcases i with _|i; exact hz
    exact hbM i
  have pair (z q : ZFSet.{u}) (hz : z ∈ M) (hq : q ∈ M) :
      (Formula.orderedPair 3 1 0).Realize M (cons q (cons z base)) ↔
        a.encode (label c) = z ∧ label c p = q := by
    rw [Formula.absolute _ M hM _ (envM z q hz hq),Formula.eval_orderedPair]
    exact ZFSet.pair_inj
  let env := cons (label c p) (cons (a.encode (label c)) base)
  have henv : ∀ i, env i ∈ M := envM _ _ ha hpM
  have valid : (NameValidity.Code.valid 4 2).Realize M env ↔
      ∃ b : Name (Conditions c), b.encode (label c) = x :=
    NameValidity.realize_valid M hM hP hU hPow hS hR hI env henv 4 2
  have forcing (b : Name (Conditions c)) (hb : b.encode (label c) = x) :
      (SigmaCode.forcing φ 4 5 0 WitnessCode.vars).Realize M env ↔
        SigmaForces M (push b (push a e)) φ p := by
    apply realize_sigmaForcing M hM hP hU hPow hS hR hI ho φ (push b (push a e)) p env henv 4 5 0
      WitnessCode.vars rfl rfl rfl
    intro i; rcases i with _|i; exact hb.symm
    rcases i with _|i; rfl
    rfl
  change (∃ z ∈ M, ∃ q ∈ M, _) ↔ _
  simp only [SigmaFormula.realize_andBounded,SigmaFormula.realize_conj]
  constructor
  · rintro ⟨z,hz,q,hq,hpair,hvalid,hforce⟩
    obtain ⟨rfl,rfl⟩ := (pair z q hz hq).mp hpair
    obtain ⟨b,hb⟩ := valid.mp hvalid
    exact ⟨b,hb,(forcing b hb).mp hforce⟩
  · rintro ⟨b,hb,hforce⟩
    exact ⟨_,ha,_,hpM,(pair _ _ ha hpM).mpr ⟨rfl,rfl⟩,valid.mpr ⟨b,hb⟩,(forcing b hb).mpr hforce⟩

end TuringRigidity.BoundedForcing

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

theorem rankImage_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (hU : BoundedSetTheory.Union M) (hS : Separation M)
    {x f : ZFSet.{u}} (hx : x ∈ M) (hf : f ∈ M) : rankImage x f ∈ M := by
  have hr := iterUnion_mem M hM hU hf 2
  let e := cons x (cons f (cons (iterUnion 2 f) (fun _ => x)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|i; exact hx
    rcases i with _|i; exact hf
    rcases i with _|i; exact hr
    exact hx
  have hs := sep_mem M hM hS imageFormula e he
    (binary_union_mem M hM hP hU hr (union_mem M hM hU hr))
  have heq : ZFSet.sep (fun z => imageFormula.Eval (cons z e))
      (iterUnion 2 f ∪ ZFSet.sUnion (iterUnion 2 f)) = rankImage x f := by
    apply ZFSet.ext
    intro z
    simp only [rankImage,ZFSet.mem_sep]
    exact and_congr_right (fun _ => eval_imageFormula z x f _ _)
  exact heq ▸ hs

end TuringRigidity.InternalRank

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_InternalRankRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalRank
open TransitiveNameModel BoundedSetTheory
universe u

def rankCertificate : SigmaFormula := .existsSet (.existsSet (.bounded
  (.conj (.isHull 1 3 4 5) (Code.graph 1 0 2))))

theorem realize_rankCertificate (M d q : ZFSet.{u}) (hM : Transitive M)
    (hS : Separation M) (hdM : d ∈ M) (hqM : q ∈ M)
    (hd : Transitive d) (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d)
    {x f : ZFSet.{u}} (hx : x ∈ d) (hf : f ∈ M) :
    rankCertificate.Realize M (cons f (cons x (cons d (cons q (fun _ => d))))) ↔
      ∃ r ∈ M, Graph (hull d q x) r f := by
  have hxM := hM d hdM x hx
  have matrix (c r : ZFSet.{u}) (hc : c ∈ M) (hr : r ∈ M) :
      (Formula.conj (.isHull 1 3 4 5) (Code.graph 1 0 2)).Realize M
        (cons r (cons c (cons f (cons x (cons d (cons q (fun _ => d))))))) ↔
      c = hull d q x ∧ Graph c r f := by
    have he : ∀ i, (cons r (cons c (cons f (cons x
        (cons d (cons q (fun _ => d))))))) i ∈ M := by
      intro i
      rcases i with _|i; exact hr
      rcases i with _|i; exact hc
      rcases i with _|i; exact hf
      rcases i with _|i; exact hxM
      rcases i with _|i; exact hdM
      rcases i with _|i; exact hqM
      exact hdM
    rw [Formula.absolute _ M hM _ he]
    simp only [Formula.Eval,Formula.eval_isHull,Code.eval_graph,cons_zero,cons_succ]
    exact and_congr (isHull_iff M d q hM hS hdM hqM hd hq hx hc) Iff.rfl
  change (∃ c ∈ M, ∃ r ∈ M, _) ↔ _
  constructor
  · rintro ⟨c,hc,r,hr,h⟩
    obtain ⟨rfl,hg⟩ := (matrix c r hc hr).mp h
    exact ⟨r,hr,hg⟩
  · rintro ⟨r,hr,hg⟩
    have hc := hull_mem M d q hM hS hdM hqM hxM
    exact ⟨_,hc,r,hr,(matrix _ r hc hr).mpr ⟨rfl,hg⟩⟩

theorem internal_rankGraph (M d q : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hdM : d ∈ M) (hqM : q ∈ M) (hd : Transitive d)
    (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d) (x : ZFSet.{u}) (hx : x ∈ d) :
    ∃ f ∈ M, Graph (hull d q x) (iterUnion 2 f) f := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    have hxM := hM d hdM x hx
    let e := cons d (cons q (fun _ => d))
    have he : ∀ i, e i ∈ M := by
      intro i
      rcases i with _|i; exact hdM
      rcases i with _|i; exact hqM
      exact hdM
    have cert (y f : ZFSet.{u}) (hy : y ∈ x) (hf : f ∈ M) :
        rankCertificate.Realize M (cons f (cons y e)) ↔
          ∃ r ∈ M, Graph (hull d q y) r f :=
      realize_rankCertificate M d q hM hS hdM hqM hd hq (hd x hx y hy) hf
    obtain ⟨b,hb,hbdef⟩ := hR rankCertificate e he x hxM (by
      intro y hy
      obtain ⟨f,hf,hfg⟩ := ih y hy (hd x hx y hy)
      refine ⟨f,hf,(cert y f hy hf).mpr
        ⟨_,iterUnion_mem M hM hU hf 2,hfg⟩,?_⟩
      intro g hg hcg
      obtain ⟨r,_,hgg⟩ := (cert y g hy hg).mp hcg
      exact hgg.unique hfg)
    have hbg (f : ZFSet.{u}) : f ∈ b ↔
        ∃ y ∈ x, ∃ r ∈ M, Graph (hull d q y) r f := by
      constructor
      · intro hf
        have hfM := hM b hb f hf
        obtain ⟨y,hy,hc⟩ := (hbdef f hfM).mp hf
        exact ⟨y,hy,(cert y f hy hfM).mp hc⟩
      · rintro ⟨y,hy,r,hr,hg⟩
        obtain ⟨f',hf',hg'⟩ := ih y hy (hd x hx y hy)
        have heq := hg.unique hg'
        have hfM : f ∈ M := heq ▸ hf'
        exact (hbdef f hfM).mpr ⟨y,hy,(cert y f hy hfM).mpr ⟨r,hr,hg⟩⟩
    let g := ZFSet.sUnion b
    have hgM : g ∈ M := union_mem M hM hU hb
    have hg (z : ZFSet.{u}) : z ∈ g ↔
        ∃ y ∈ x, ∃ w ∈ hull d q y, z = ZFSet.pair w (rankSet w) := by
      constructor
      · intro hz
        obtain ⟨f,hf,hzf⟩ := ZFSet.mem_sUnion.mp hz
        obtain ⟨y,hy,r,_,hfg⟩ := (hbg f).mp hf
        exact ⟨y,hy,(hfg.mem_iff z).mp hzf⟩
      · rintro ⟨y,hy,w,hw,hz⟩
        obtain ⟨f,hf,hfg⟩ := ih y hy (hd x hx y hy)
        exact ZFSet.mem_sUnion.mpr ⟨f,(hbg f).mpr
          ⟨y,hy,_,iterUnion_mem M hM hU hf 2,hfg⟩,(hfg.mem_iff z).mpr ⟨w,hw,hz⟩⟩
    have hvalue : rankImage x g = rankSet x := by
      apply ZFSet.ext
      intro z
      rw [mem_rankImage,mem_rankSet]
      constructor
      · rintro ⟨y,hy,w,hw,hz⟩
        obtain ⟨a,_,v,_,hp⟩ := (hg _).mp hw
        obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
        exact ⟨y,hy,hz⟩
      · rintro ⟨y,hy,hz⟩
        exact ⟨y,hy,_,(hg _).mpr
          ⟨y,hy,y,self_mem_hull d q (hd x hx y hy),rfl⟩,hz⟩
    have hvM : rankSet x ∈ M := hvalue ▸
      rankImage_mem M hM hP hU hS hxM hgM
    let f := g ∪ ({ZFSet.pair x (rankSet x)} : ZFSet.{u})
    have hfM : f ∈ M := binary_union_mem M hM hP hU hgM
      (singleton_mem M hM hP (orderedPair_mem M hM hP hxM hvM))
    refine ⟨f,hfM,graph_of_mem_iff _ f (hull_transitive d q x hd) ?_⟩
    intro z
    change z ∈ g ∪ ({ZFSet.pair x (rankSet x)} : ZFSet.{u}) ↔ _
    rw [ZFSet.mem_union,ZFSet.mem_singleton,hg]
    constructor
    · rintro (⟨y,hy,w,hw,hz⟩|hz)
      · exact ⟨w,(hull_unfold M d q hM hP hU hS hR hdM hqM hd hq hx w).mpr
          (Or.inr ⟨y,hy,hw⟩),hz⟩
      · exact ⟨x,self_mem_hull d q hx,hz⟩
    · rintro ⟨w,hw,hz⟩
      rcases (hull_unfold M d q hM hP hU hS hR hdM hqM hd hq hx w).mp hw with rfl|⟨y,hy,hw⟩
      · exact Or.inr hz
      · exact Or.inl ⟨y,hy,w,hw,hz⟩

theorem rankSet_mem_of_container (M d : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hdM : d ∈ M) (hd : Transitive d)
    {x : ZFSet.{u}} (hx : x ∈ d) : rankSet x ∈ M := by
  obtain ⟨q,hqM,hq⟩ := internal_power M hM hPow hdM
  obtain ⟨f,hf,hfg⟩ := internal_rankGraph M d q hM hP hU hS hR
    hdM hqM hd hq x hx
  obtain ⟨v,hv,hfv,_⟩ := hfg.2.2.1 x (self_mem_hull d q hx)
  rw [←hfg.correct x (self_mem_hull d q hx) v hv hfv]
  exact hM _ (iterUnion_mem M hM hU hf 2) v hv

end TuringRigidity.InternalRank

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_RankDefinability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalRank
open TransitiveNameModel BoundedSetTheory
universe u

theorem rankSet_mem_ground (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M)
    {x : ZFSet.{u}} (hx : x ∈ M) : rankSet x ∈ M := by
  obtain ⟨d,hd,hdT,hxd⟩ := internal_transitive_container M hM hP hU hS hR hI hx
  exact rankSet_mem_of_container M d hM hP hU hPow hS hR hd hdT hxd

end TuringRigidity.InternalRank

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalHartogs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory InternalRank
universe u

theorem internal_hartogs (M d : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hd : d ∈ M) :
    ∃ α ∈ M, α.IsOrdinal ∧ ∀ f ∈ M, ∀ j : ZFSet.{u} → ZFSet.{u},
      Presents α f j → (∀ x ∈ α, j x ∈ d) →
      ¬ (∀ x ∈ α, ∀ y ∈ α, j x = j y → x = y) := by
  obtain ⟨W,hW,hbound⟩ := internal_small_transitive_bound M d hM hP hU hPow hS hR hd
  let k := rankSet W
  have hk : k ∈ M := rankSet_mem_ground M hM hP hU hPow hS.bounded hR hI hW
  have hko : k.IsOrdinal := rankSet_isOrdinal W
  let α := insert k k
  have hα : α ∈ M := by
    have eq : α = ({k} : ZFSet.{u}) ∪ k := by
      apply ZFSet.ext
      intro z
      simp only [α,ZFSet.mem_insert_iff,ZFSet.mem_union,ZFSet.mem_singleton]
    rw [eq]
    exact binary_union_mem M hM hP hU (singleton_mem M hM hP hk) hk
  have hαo : α.IsOrdinal := ZFSet.isOrdinal_succ hko
  refine ⟨α,hα,hαo,?_⟩
  intro f hf j hfj hj hi
  have hαt : Transitive α := fun x hx y hy => hαo.subset_of_mem hx hy
  have hsub := hbound α hα hαt f hf j hfj hj hi
  have hkw : k ∈ W := hsub (ZFSet.mem_insert_iff.mpr (Or.inl rfl))
  have hlt := ZFSet.rank_lt_of_mem hkw
  have heq : k.rank = W.rank := by
    rw [show k = W.rank.toZFSet from rankSet_eq_ordinal W,Ordinal.rank_toZFSet]
  exact (lt_irrefl W.rank) (heq ▸ hlt)

end TuringRigidity.RelationCollapse

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

theorem internal_maximal_trace (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    {α a q s : ZFSet.{u}} (hαM : α ∈ M) (ha : a ∈ M) (hq : q ∈ M) (hsM : s ∈ M)
    (hα : Transitive α) (hs : ChoiceGraph q s) :
    ∃ F ∈ M, Trace α a q s F ∧ ∀ f ∈ M, Trace α a q s f → f ⊆ F := by
  have hp := product_mem M hM hP hU hPow hS hαM ha
  obtain ⟨P,hP0,hPdef⟩ := internal_power M hM hPow hp
  let e := cons α (cons a (cons q (fun _ => s)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|i; exact hαM
    rcases i with _|i; exact ha
    rcases i with _|i; exact hq
    exact hsM
  let C := ZFSet.sep (fun f => (traceFormula 1 2 3 4 0).Eval (cons f e)) P
  have hC : C ∈ M := sep_mem M hM hS (traceFormula 1 2 3 4 0) e he hP0
  have hCdef (f : ZFSet.{u}) : f ∈ C ↔ f ∈ M ∧ Trace α a q s f := by
    rw [ZFSet.mem_sep,hPdef,eval_traceFormula]
    constructor
    · rintro ⟨⟨hf,_⟩,ht⟩; exact ⟨hf,ht⟩
    · rintro ⟨hf,ht⟩; exact ⟨⟨hf,ht.subset⟩,ht⟩
  refine ⟨ZFSet.sUnion C,union_mem M hM hU hC,Trace.sUnion hα hs (fun f hf => ((hCdef f).mp hf).2),?_⟩
  intro f hf htrace z hz
  exact ZFSet.mem_sUnion.mpr ⟨f,(hCdef f).mpr ⟨hf,htrace⟩,hz⟩

theorem residual_mem (M : ZFSet.{u}) (hM : Transitive M) (hS : Separation M)
    {a f i : ZFSet.{u}} (ha : a ∈ M) (hf : f ∈ M) (hi : i ∈ M) : residual a f i ∈ M := by
  simpa only [residual,Formula.Eval,eval_pairMem,cons_zero,cons_succ] using
    sep_mem M hM hS (.neg (.existsMem 2 (.pairMem 0 1 2))) (cons f (fun _ => i))
      (by intro j; cases j <;> assumption) ha

end InternalWellOrder
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalOrdinalEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse
universe u
namespace InternalWellOrder

theorem internal_ordinal_enumeration (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M)
    {a : ZFSet.{u}} (ha : a ∈ M) :
    ∃ δ ∈ M, δ.IsOrdinal ∧ ∃ F ∈ M, TransitiveNameModel.FunctionGraph δ a F ∧
      (∀ x ∈ a, ∃ i ∈ δ, ZFSet.pair i x ∈ F) ∧
      (∀ i ∈ δ, ∀ j ∈ δ, ∀ x, ZFSet.pair i x ∈ F → ZFSet.pair j x ∈ F → i = j) := by
  classical
  obtain ⟨q,hq,s,hsM,hs,hqdef⟩ := internal_selector M hM hPow hS.bounded hAC ha
  obtain ⟨α,hαM,hα,hHartogs⟩ := internal_hartogs M a hM hP hU hPow hS hR hI ha
  have hαT : Transitive α := fun i hi j hj => hα.subset_of_mem hi hj
  obtain ⟨F,hF,htrace,hmax⟩ := internal_maximal_trace M hM hP hU hPow hS.bounded hαM ha hq hsM hαT hs
  have hfun := htrace.functional hαT hs
  have hmissing : ∃ i ∈ α, ¬ ∃ x ∈ a, ZFSet.pair i x ∈ F := by
    by_contra hn
    have htotal : ∀ i ∈ α, ∃ x ∈ a, ZFSet.pair i x ∈ F := by
      intro i hi; exact Classical.byContradiction (fun h => hn ⟨i,hi,h⟩)
    have hfg : TransitiveNameModel.FunctionGraph α a F := by
      refine ⟨htrace.shape,?_⟩
      intro i hi
      obtain ⟨x,hx,hix⟩ := htotal i hi
      exact ⟨x,hx,hix,fun y _ hiy => hfun i y x hiy hix⟩
    obtain ⟨v,hv,hva⟩ := FunctionGraph.exists_presentation hfg
    apply hHartogs F hF v hv hva
    intro i hi j hj he
    have hip := (hv.pair_iff i (v i)).mpr ⟨hi,rfl⟩
    have hjp := (hv.pair_iff j (v j)).mpr ⟨hj,rfl⟩
    rw [← he] at hjp
    exact htrace.injective hα hs i j (v i) hip hjp
  have minimal (i : ZFSet.{u}) : i ∈ α → (¬ ∃ x ∈ a, ZFSet.pair i x ∈ F) →
      ∃ j ∈ α, (¬ ∃ x ∈ a, ZFSet.pair j x ∈ F) ∧
        ∀ k ∈ j, ∃ x ∈ a, ZFSet.pair k x ∈ F := by
    induction i using ZFSet.inductionOn with
    | h i ih =>
      intro hi hmiss
      by_cases hex : ∃ j ∈ i, ¬ ∃ x ∈ a, ZFSet.pair j x ∈ F
      · obtain ⟨j,hji,hjmiss⟩ := hex
        exact ih j hji (hα.subset_of_mem hi hji) hjmiss
      · refine ⟨i,hi,hmiss,?_⟩
        intro j hji
        exact Classical.byContradiction (fun h => hex ⟨j,hji,h⟩)
  obtain ⟨i,hi,hmiss⟩ := hmissing
  obtain ⟨i,hi,hmiss,hprev⟩ := minimal i hi hmiss
  have hiM := hM α hαM i hi
  have hiT : Transitive i := fun j hj k hk => (hα.mem hi).subset_of_mem hj hk
  have hdom : ∀ j y, ZFSet.pair j y ∈ F → j ∈ i := htrace.domain_before hα hi hmiss
  have hres := residual_mem M hM hS.bounded ha hF hiM
  have hrem := residual_remaining a F i
  have hempty : ¬ ∃ x, x ∈ residual a F i := by
    intro hex
    have hrq : residual a F i ∈ q := (hqdef _).mpr ⟨hres,hrem.1,hex⟩
    obtain ⟨x,hxr,hrx,_⟩ := hs.2 _ hrq
    have hxa := hrem.1 hxr
    have hpair := orderedPair_mem M hM hP hiM (hM a ha x hxa)
    have hnew := binary_union_mem M hM hP hU hF (singleton_mem M hM hP hpair)
    have hnewtrace := htrace.adjoin hi hiT hxa hrq hrem hrx hprev hdom
    have hnewsub := hmax _ hnew hnewtrace
    exact hmiss ⟨x,hxa,hnewsub (ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_singleton.mpr rfl)))⟩
  refine ⟨i,hiM,hα.mem hi,F,hF,?_,?_,?_⟩
  · refine ⟨?_,?_⟩
    · intro z hz
      obtain ⟨j,_,x,hx,rfl⟩ := htrace.shape z hz
      exact ⟨j,hdom j x hz,x,hx,rfl⟩
    · intro j hj
      obtain ⟨x,hx,hjx⟩ := hprev j hj
      exact ⟨x,hx,hjx,fun y _ hjy => hfun j y x hjy hjx⟩
  · intro x hx
    exact Classical.byContradiction (fun hn => hempty ⟨x,(hrem.2 x hx).mpr hn⟩)
  · intro j _ k _ x hjx hkx
    exact htrace.injective hα hs j k x hjx hkx

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

theorem internal_choice_of_ordinal_cover (E : ZFSet.{u}) (hE : Transitive E)
    (hP : Pairing E) (hU : BoundedSetTheory.Union E) (hPow : PowerSet E) (hS : Separation E)
    {a δ V F H : ZFSet.{u}} (ha : a ∈ E) (hδE : δ ∈ E) (hV : V ∈ E) (hFE : F ∈ E) (hHE : H ∈ E)
    (hδ : δ.IsOrdinal) (hF : TransitiveNameModel.FunctionGraph δ V F) (hH : FiniteTerm.Functional H)
    (hcover : ∀ x ∈ a, ∃ i ∈ δ, ∃ v ∈ V, ∃ y ∈ x, ZFSet.pair i v ∈ F ∧ ZFSet.pair v y ∈ H) :
    ∃ f ∈ E, ChoiceGraph a f := by
  let u := ZFSet.sUnion a
  have hu : u ∈ E := union_mem E hE hU ha
  let e := cons a (cons u (cons δ (cons V (cons F (fun _ => H)))))
  have he : ∀ i, e i ∈ E := by
    intro i; rcases i with _|i; exact ha
    rcases i with _|i; exact hu
    rcases i with _|i; exact hδE
    rcases i with _|i; exact hV
    rcases i with _|i; exact hFE
    exact hHE
  let f := ZFSet.sep (fun z => selectionFormula.Eval (cons z e)) (ZFSet.prod a u)
  have hf : f ∈ E := sep_mem E hE hS selectionFormula e he (product_mem E hE hP hU hPow hS ha hu)
  have hmem (z : ZFSet.{u}) : z ∈ f ↔
      ∃ x ∈ a, ∃ y ∈ x, z = ZFSet.pair x y ∧ LeastValue δ V F H x y := by
    simp only [f,ZFSet.mem_sep,selectionFormula,Formula.Eval,eval_orderedPair,
      eval_leastValueFormula,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨_,x,hx,y,_,hz,hmin⟩
      exact ⟨x,hx,y,hmin.1,hz,hmin⟩
    · rintro ⟨x,hx,y,hy,rfl,hmin⟩
      have hyu : y ∈ u := ZFSet.mem_sUnion.mpr ⟨x,hx,hy⟩
      exact ⟨ZFSet.mem_prod.mpr ⟨x,hx,y,hyu,rfl⟩,x,hx,y,hyu,rfl,hmin⟩
  refine ⟨f,hf,?_,?_⟩
  · intro z hz
    obtain ⟨x,hx,y,hy,hz,_⟩ := (hmem z).mp hz
    exact ⟨x,hx,y,hy,hz⟩
  · intro x hx
    obtain ⟨y,hy,hmin⟩ := leastValue_exists hδ (hcover x hx)
    refine ⟨y,hy,(hmem _).mpr ⟨x,hx,y,hy,rfl,hmin⟩,?_⟩
    intro z _ hz
    obtain ⟨x',_,z',_,heq,hmin'⟩ := (hmem _).mp hz
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
    exact hmin'.unique hδ hF hH hmin

end InternalWellOrder
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

theorem pairNameCode_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    {t x y : ZFSet.{u}} (ht : t ∈ M) (hx : x ∈ M) (hy : y ∈ M) : pairNameCode t x y ∈ M :=
  pair_mem M hM hP (orderedPair_mem M hM hP hx ht) (orderedPair_mem M hM hP hy ht)

theorem orderedNameCode_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    {t x y : ZFSet.{u}} (ht : t ∈ M) (hx : x ∈ M) (hy : y ∈ M) : orderedNameCode t x y ∈ M :=
  pairNameCode_mem M hM hP ht (pairNameCode_mem M hM hP ht hx hx)
    (pairNameCode_mem M hM hP ht hx hy)

namespace NameCodeFormula
open _root_.OAI.TuringRigidity.BoundedSetTheory.Formula

def orderedName (t x y z : ℕ) : SigmaFormula := .existsSet (.existsSet (.bounded
  (.conj (pairName (t+2) (x+2) (x+2) 1)
    (.conj (pairName (t+2) (x+2) (y+2) 0) (pairName (t+2) 1 0 (z+2))))))

theorem realize_orderedName (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (t x y z : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (orderedName t x y z).Realize M e ↔ e z = orderedNameCode (e t) (e x) (e y) := by
  have matrix (a b : ZFSet.{u}) (ha : a ∈ M) (hb : b ∈ M) :
      (Formula.conj (pairName (t+2) (x+2) (x+2) 1)
        (.conj (pairName (t+2) (x+2) (y+2) 0) (pairName (t+2) 1 0 (z+2)))).Realize M
        (cons b (cons a e)) ↔ a = pairNameCode (e t) (e x) (e x) ∧
          b = pairNameCode (e t) (e x) (e y) ∧ e z = pairNameCode (e t) a b := by
    rw [Formula.absolute _ M hM _ (by
      intro i; rcases i with _|i; exact hb
      rcases i with _|i; exact ha
      exact he i)]
    simp only [Formula.Eval,eval_pairName,cons_zero,cons_succ]
  change (∃ a ∈ M, ∃ b ∈ M, _) ↔ _
  constructor
  · rintro ⟨a,ha,b,hb,h⟩
    obtain ⟨rfl,rfl,h⟩ := (matrix a b ha hb).mp h
    exact h
  · intro h
    have ha := pairNameCode_mem M hM hP (he t) (he x) (he x)
    have hb := pairNameCode_mem M hM hP (he t) (he x) (he y)
    exact ⟨_,ha,_,hb,(matrix _ _ ha hb).mpr ⟨rfl,rfl,h⟩⟩
end NameCodeFormula

theorem val_orderedPairName {P : Type u} [Top P] (G : Set P) (htop : ⊤ ∈ G) (a b : Name P) :
    (orderedPairName a b).val G = ZFSet.pair (a.val G) (b.val G) := by
  simp [orderedPairName,Name.val_pair G htop,ZFSet.pair]

end TuringRigidity.TransitiveNameModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_EvaluationNameCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.TransitiveNameModel
open RecursiveNames BoundedSetTheory
universe u

def evaluationOutputFormula : SigmaFormula := .existsSet
  (.andBounded (.conj (.member 0 4) (.pairMem 2 0 3))
    (NameCodeFormula.orderedName 5 0 2 1))

theorem internal_evaluation_name_codes (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M)
    {V t : ZFSet.{u}} (hV : V ∈ M) (ht : t ∈ M) :
    ∃ B ∈ M, ∀ z, z ∈ B ↔ ∃ x ∈ V,
      orderedNameCode t (checkedCode t x) x = z := by
  obtain ⟨d,hdM,hd,hVd⟩ := internal_transitive_container M hM hP hU hS hR hI hV
  obtain ⟨q,hqM,hq⟩ := internal_power M hM hPow hdM
  obtain ⟨F,hF,hfg⟩ := internal_checkGraph M d q t hM hP hU hPow hS hR
    hdM hqM ht hd hq V hVd
  let r := iterUnion 2 F
  have hr : r ∈ M := iterUnion_mem M hM hU hF 2
  have hxdom (x : ZFSet.{u}) (hx : x ∈ V) : x ∈ hull d q V :=
    (hull_transitive d q V hd) V (self_mem_hull d q hVd) x hx
  have check (x : ZFSet.{u}) (hx : x ∈ V) :
      checkedCode t x ∈ r ∧ ZFSet.pair x (checkedCode t x) ∈ F := by
    obtain ⟨y,hy,hxy,_⟩ := hfg.2.2.1 x (hxdom x hx)
    have he := hfg.correct x (hxdom x hx) y hy hxy
    exact he ▸ ⟨hy,hxy⟩
  let e := cons F (cons r (fun _ => t))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|i; exact hF
    rcases i with _|i; exact hr
    exact ht
  apply replacement_image M hM hR evaluationOutputFormula e he hV
    (fun x => orderedNameCode t (checkedCode t x) x)
  · intro x hx
    exact orderedNameCode_mem M hM hP ht (hM r hr _ (check x hx).1) (hM V hV x hx)
  · intro x hx z hz
    have hxM := hM V hV x hx
    have matrix (w : ZFSet.{u}) (hw : w ∈ M) :
        (SigmaFormula.andBounded (.conj (.member 0 4) (.pairMem 2 0 3))
          (NameCodeFormula.orderedName 5 0 2 1)).Realize M (cons w (cons z (cons x e))) ↔
          w ∈ r ∧ ZFSet.pair x w ∈ F ∧ z = orderedNameCode t w x := by
      have he' : ∀ i, cons w (cons z (cons x e)) i ∈ M := by
        intro i; rcases i with _|i; exact hw
        rcases i with _|i; exact hz
        rcases i with _|i; exact hxM
        exact he i
      rw [SigmaFormula.realize_andBounded,Formula.absolute _ M hM _ he',
        NameCodeFormula.realize_orderedName M hM hP _ _ _ _ _ he']
      simp only [Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e]
      exact and_assoc
    change (∃ w ∈ M, _) ↔ _
    constructor
    · rintro ⟨w,hw,h⟩
      obtain ⟨hwr,hxw,hz⟩ := (matrix w hw).mp h
      rw [hfg.correct x (hxdom x hx) w hwr hxw] at hz
      exact hz
    · intro hz
      have hwM := hM r hr _ (check x hx).1
      exact ⟨_,hwM,(matrix _ hwM).mpr ⟨(check x hx).1,(check x hx).2,hz⟩⟩

end TuringRigidity.TransitiveNameModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ExtensionSigmaSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem extension_sigmaSeparation (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : SigmaSeparation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) :
    SigmaSeparation (genericExtensionSet M c G.carrier) := by
  classical
  intro φ env henv x hx
  obtain ⟨a,ha,rfl⟩ := (mem_extensionSet M c G.carrier x).mp hx
  have names_exist (i) := (mem_extensionSet M c G.carrier (env i)).mp (henv i)
  choose e he hval using names_exist
  obtain ⟨B,hB,hBS,hBval⟩ := sigma_separation_name M hM hP hU hPow hS hR hI hc hoM ho G hG φ a ha e he
  have hcode : (a.restrict (label c) B).encode (label c) ∈ M := by
    rw [Name.encode_restrict _ _ _ hBS]
    exact hB
  refine ⟨(a.restrict (label c) B).val G.carrier,
    (mem_extensionSet M c G.carrier _).mpr ⟨_,hcode,rfl⟩,?_⟩
  intro z _
  rw [hBval z]
  have hev : (fun i => (e i).val G.carrier) = env := funext hval
  rw [hev]

end TuringRigidity.BoundedForcing

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

theorem val_mem_coverName (W : ZFSet.{u})
    (hW : ∀ x ∈ W, ∃ a : Name (Conditions c), a.encode (label c) = x)
    (G : Set (Conditions c)) (p : Conditions c) (hp : p ∈ G)
    (b : Name (Conditions c)) (hb : b.encode (label c) ∈ W) :
    b.val G ∈ (coverName W hW p).val G := by
  obtain ⟨i,hi⟩ := label_surjective W hb
  rw [coverName,Name.mem_val]
  refine ⟨i,hp,?_⟩
  exact Name.val_eq_of_encode_eq (label c) (label_injective c) G _ b ((coverChild_code W hW i).trans hi)

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ExtensionWitnessCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}}

theorem name_of_value_member (d : ZFSet.{u}) (hd : Transitive d)
    (a : Name (Conditions c)) (ha : a.encode (label c) ∈ d) (G : Set (Conditions c))
    (x : ZFSet.{u}) (hx : x ∈ a.val G) :
    ∃ b : Name (Conditions c), b.encode (label c) ∈ d ∧ b.val G = x := by
  cases a with
  | mk ι child tag =>
    rw [Name.mem_val] at hx
    obtain ⟨i,_,hval⟩ := hx
    exact ⟨child i,names_childClosed d c hd (.mk ι child tag) ha (child i) ⟨i,rfl⟩,hval⟩

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_NameEvaluationGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory
universe u
variable {c : ZFSet.{u}}

theorem mem_val_coverName (W : ZFSet.{u})
    (hW : ∀ x ∈ W, ∃ a : Name (Conditions c), a.encode (label c) = x)
    (G : Set (Conditions c)) (p : Conditions c) (hp : p ∈ G) (z : ZFSet.{u}) :
    z ∈ (coverName W hW p).val G ↔
      ∃ b : Name (Conditions c), b.encode (label c) ∈ W ∧ b.val G = z := by
  constructor
  · intro hz
    rw [coverName,Name.mem_val] at hz
    obtain ⟨i,_,he⟩ := hz
    exact ⟨coverChild W hW i,by rw [coverChild_code]; exact label_mem W i,he⟩
  · rintro ⟨b,hb,rfl⟩
    exact val_mem_coverName W hW G p hp b hb

variable [Top (Conditions c)]

theorem internal_name_evaluation_graph (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {V : ZFSet.{u}} (hV : V ∈ M)
    (hvalid : ∀ x ∈ V, ∃ a : Name (Conditions c), a.encode (label c) = x)
    (G : Set (Conditions c)) (htop : ⊤ ∈ G) :
    ∃ H : Name (Conditions c), H.encode (label c) ∈ M ∧ ∀ z,
      z ∈ H.val G ↔ ∃ x ∈ V, ∃ a : Name (Conditions c),
        a.encode (label c) = x ∧ z = ZFSet.pair x (a.val G) := by
  have ht := hM c hc _ (label_mem c ⊤)
  obtain ⟨B,hB,hBdef⟩ := internal_evaluation_name_codes M hM hP hU hPow hS hR hI hV ht
  have hvalidB (z : ZFSet.{u}) (hz : z ∈ B) :
      ∃ a : Name (Conditions c), a.encode (label c) = z := by
    obtain ⟨x,hx,he⟩ := (hBdef z).mp hz
    obtain ⟨a,ha⟩ := hvalid x hx
    refine ⟨orderedPairName (Name.check x) a,?_⟩
    rw [encode_orderedPairName,encode_check,ha]
    exact he
  let H := coverName B hvalidB ⊤
  have hH : H.encode (label c) ∈ M := by
    rw [encode_coverName]
    exact product_mem M hM hP hU hPow hS hB (singleton_mem M hM hP ht)
  refine ⟨H,hH,?_⟩
  intro z
  rw [mem_val_coverName B hvalidB G ⊤ htop]
  constructor
  · rintro ⟨b,hb,rfl⟩
    obtain ⟨x,hx,he⟩ := (hBdef _).mp hb
    obtain ⟨a,ha⟩ := hvalid x hx
    have hcode : b.encode (label c) = (orderedPairName (Name.check x) a).encode (label c) := by
      rw [encode_orderedPairName,encode_check,ha]
      exact he.symm
    have hv := Name.val_eq_of_encode_eq (label c) (label_injective c) G _ _ hcode
    rw [val_orderedPairName G htop,Name.val_check G htop] at hv
    exact ⟨x,hx,a,ha,hv⟩
  · rintro ⟨x,hx,a,ha,rfl⟩
    refine ⟨orderedPairName (Name.check x) a,?_,?_⟩
    · apply (hBdef _).mpr
      refine ⟨x,hx,?_⟩
      rw [encode_orderedPairName,encode_check,ha]
    · rw [val_orderedPairName G htop,Name.val_check G htop]

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ExtensionChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]

theorem extension_choice (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (htop : ⊤ ∈ G.carrier) :
    Choice (genericExtensionSet M c G.carrier) := by
  classical
  let E := genericExtensionSet M c G.carrier
  have hET : Transitive E := genericExtensionSet_transitive M c hM G.carrier
  have hEP : Pairing E := extension_pairing M c hM hP hc G.carrier htop
  have hEU : BoundedSetTheory.Union E := extension_union M c o hM hP hU hPow hS.bounded hc hoM ho G
  have hEPow : PowerSet E := extension_powerSet M hM hP hU hPow hS.bounded hR hI hc hoM ho G hG htop
  have hES : Separation E := (extension_sigmaSeparation M hM hP hU hPow hS hR hI hc hoM ho G hG).bounded
  have hground : M ⊆ E := ground_inclusion_set M c hM hP hU hPow hS.bounded hR hI hc G.carrier htop
  intro X hX hnonempty
  obtain ⟨a,ha,rfl⟩ := (mem_extensionSet M c G.carrier X).mp hX
  obtain ⟨d,hdM,hd,had⟩ := internal_transitive_container M hM hP hU hS.bounded hR hI ha
  let V := ZFSet.sep (fun x => (NameValidity.Code.valid 1 0).Realize M (cons x (fun _ => c))) d
  have hV : V ∈ M := sigma_sep_mem M hM hS (NameValidity.Code.valid 1 0) (fun _ => c) (fun _ => hc) hdM
  have valid (x : ZFSet.{u}) (hx : x ∈ M) :
      (NameValidity.Code.valid 1 0).Realize M (cons x (fun _ => c)) ↔
        ∃ b : Name (Conditions c), b.encode (label c) = x :=
    NameValidity.realize_valid M hM hP hU hPow hS.bounded hR hI _
      (by intro i; cases i <;> assumption) 1 0
  have hvalid (x : ZFSet.{u}) (hx : x ∈ V) : ∃ b : Name (Conditions c), b.encode (label c) = x :=
    (valid x (hM V hV x hx)).mp (ZFSet.mem_sep.mp hx).2
  have code_mem (b : Name (Conditions c)) (hb : b.encode (label c) ∈ d) : b.encode (label c) ∈ V :=
    ZFSet.mem_sep.mpr ⟨hb,(valid _ (hM d hdM _ hb)).mpr ⟨b,rfl⟩⟩
  obtain ⟨δ,hδM,hδ,F,hFM,hF,hsurj,_⟩ :=
    InternalWellOrder.internal_ordinal_enumeration M hM hP hU hPow hS hR hI hAC hV
  obtain ⟨N,hN,hNdef⟩ := internal_name_evaluation_graph M hM hP hU hPow hS.bounded hR hI hc
    hV hvalid G.carrier htop
  have hNE : N.val G.carrier ∈ E := (mem_extensionSet M c G.carrier _).mpr ⟨N,hN,rfl⟩
  have hNfun : FiniteTerm.Functional (N.val G.carrier) := by
    intro v x y hx hy
    obtain ⟨v',_,b,hb,he⟩ := (hNdef _).mp hx
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    obtain ⟨v'',_,b',hb',he'⟩ := (hNdef _).mp hy
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he'
    exact Name.val_eq_of_encode_eq (label c) (label_injective c) G.carrier _ _ (hb.trans hb'.symm)
  apply InternalWellOrder.internal_choice_of_ordinal_cover E hET hEP hEU hEPow hES
    hX (hground hδM) (hground hV) (hground hFM) hNE hδ hF hNfun
  intro x hx
  obtain ⟨y,hy⟩ := hnonempty x hx
  obtain ⟨b,hbd,hbx⟩ := name_of_value_member d hd a had G.carrier x hx
  have hyb : y ∈ b.val G.carrier := hbx.symm ▸ hy
  obtain ⟨s,hsd,hsy⟩ := name_of_value_member d hd b hbd G.carrier y hyb
  have hsV := code_mem s hsd
  obtain ⟨i,hi,hif⟩ := hsurj _ hsV
  refine ⟨i,hi,s.encode (label c),hsV,y,hy,hif,(hNdef _).mpr ?_⟩
  exact ⟨_,hsV,s,rfl,congrArg (ZFSet.pair (s.encode (label c))) hsy.symm⟩

end TuringRigidity.BoundedForcing

end OAI
end


