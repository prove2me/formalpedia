-- Prove2me | Definitions.Def_OAIQ66So019
-- name    : OAIQ66So019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:25:50.937766+00:00
-- url     : https://prove2.me/theorems/a906a8c0-8b96-477f-a481-77abfea1d01a
-- title:
--   Definitions bundle OAIQ66So019 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 166 declarations of OpenAI's Lean: 50 definitions, 1 inductive type or structure, 4 instances and 111 theorems. The definitions and types are `OAI.FiniteAlgebraicEnvelopes.Compiler.Scan.flip`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Scan.rightStep`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Surface.cleanAnchor`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Surface.headMap`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.alphabet`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.wrapper`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.OneSided.step`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.OneSided.view`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode.codedMachine`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode.encodeCommand`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode.heads`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode.surfaces`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode.transition`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.ParameterMachine.alphabet`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.ParameterMachine.content`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.ParameterMachine.flat`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.ParameterMachine.machine`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.ParameterMachine.marked`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.TapeFold.command`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.TapeFold.machine`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.UniversalMachine.letters`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.UniversalMachine.parameter`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.UniversalMachine.restrict`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.UniversalMachine.universal`, `OAI.FiniteIdempotentDiagrams.ThreeCopies.system`, `OAI.HNNSubgroup.base`, `OAI.HNNSubgroup.baseMap`, `OAI.HNNSubgroup.equiv`, `OAI.HNNSubgroup.hom`, `OAI.HNNSubgroup.inclusion`, `OAI.HNNSubgroup.stableElement`, `OAI.ListChains.IdempotentSplittings`, `OAI.ListChains.IdempotentSplittings.conjugate`, `OAI.ListChains.boundedHomologyScIso`, `OAI.ListChains.boundedProductComplex`, `OAI.ListChains.boundedProductScIso`, `OAI.ListChains.boundedShiftChainMap`, `OAI.ListChains.flattenProduct`, `OAI.ListChains.gatherProduct`, `OAI.ListChains.groupHomologyBoundedIso` and 11 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `BooneHigman_PartialAffine`, `FiniteCompiler_Control`, `FiniteCompiler_Effectivity`, `FiniteCompiler_Normalization`, `FiniteCompiler_Quotients`, `FiniteCompiler_SelfReference`, `FiniteCompiler_TapeFolding`, `FiniteCompiler_UniformControl`, `FiniteCompiler_UniformMachines`, `FiniteCompiler_UniformPaths`, `FiniteType_AscendingHNN`, `FiniteType_BinaryPrefixOperators`, `FiniteType_CategoryTheoryShortComplex`, `FiniteType_ClassifyingSpacesFiniteExtensionGeometricFromProducts`, `FiniteType_FiniteIdempotentDiagrams`, `FiniteType_InducedFree`, `FiniteType_ListChainsFromTuplesCone`, `FiniteType_ListChainsMapChainComp`, `FiniteType_ListChainsShiftOrigin`, `FiniteType_ProductCoefficient`, `FiniteType_ProductCoefficientAffineShift`, `FiniteType_Representation`, `FiniteType_SteinbergFinitePresentation`, `FiniteType_UniformProductSupport`.
--
--   **Imports.** It imports the bundles `OAIQ66So010`, `OAIQ66So011`, `OAIQ66So012`, `OAIQ66So013` and `OAIQ66So014` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So024`, `OAIQ66So025` and `OAIQ66So026`; the statement `OAI.ListChains.uniform_fillings_from_partial_homotopy`; the proof of `OAI.ListChains.uniform_fillings_from_partial_homotopy`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So010
import Definitions.Def_OAIQ66So011
import Definitions.Def_OAIQ66So012
import Definitions.Def_OAIQ66So013
import Definitions.Def_OAIQ66So014

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Control
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Scan.instPrimcodableSector _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableBaseOfFintype _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableTagOfFintype _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite control and bounded compiler orbit normalization.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Validator
variable {S Γ : Type*}

variable (blank : Γ) [DecidableEq S] [DecidableEq Γ]

instance stepDecidable : DecidableRel (Step (S := S) blank) := fun v w => by
  letI : Decidable (Scan.Step (table blank) (toScan v) (toScan w)) :=
    inferInstanceAs (Decidable (_ = _))
  exact decidable_of_iff _ (step_iff_scan blank v w).symm

end FiniteAlgebraicEnvelopes.Compiler.Validator

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Normalization
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path.instPrimcodableShape _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Raw-run folds, full word compilation, partial budgets, and bounded normalization.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Word

section
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]

variable [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

 theorem normal_idempotent
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} {m : ℕ} (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    (w : List (Letter S Γ Q)) (hm : grade w ≤ m) :
    normal A M f (normal A M f w) = normal A M f w :=
  (normal_reduces A M hdecode h hcomp (reduces_normal A M h hcomp w hm) hm).symm

end

open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

theorem normal_contains_omega (f : List S → List S) (x y : List (Letter S Γ Q)) :
    normal A M f (x ++ .zero::y) = [.zero] := by
  rw [normal,ite_eq_left (Path.shape_zero_context x y)]

end FiniteAlgebraicEnvelopes.Compiler.Word

/- The actual partial evaluator is a finite plan followed by partial calls.
   Its definition has no budget and does not totalize an undefined program. -/

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Effectivity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Primitive recursive encodings and effective finite compiler data.
-/

/- Effectivity dependencies for the source compiler and its bounded recursive
   evaluator. No partial function is completed by classical choice. -/

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {H B T : Type*}

variable [Primcodable H] [Primcodable B] [Primcodable T]

theorem Sector.primrec_lb : Primrec (Sector.leftBoundary (Head := H) (Base := B) (Tag := T)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Sector.primrec_code)))

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open Relation
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {H B T : Type*}

def flip (v : Sector H B T) : Sector H B T :=
  ⟨v.right,v.head,v.left,v.rightBoundary,v.leftBoundary⟩

def rightStep (table : Table H B T) (v : Sector H B T) : Option (Sector H B T) :=
  match v.right with
  | [] => if v.rightBoundary then (table.boundary v.head).map fun q => {v with head := q} else none
  | (b,t)::r => (table.cell v.head b t).map fun a =>
      if a.cross then {v with left := (b,a.tag)::v.left,head := a.head,right := r}
      else {v with head := a.head,right := (b,a.tag)::r}

theorem step_rightStep (table : Table H B T) (v : Sector H B T) :
    step table v = if table.direction v.head = .right then rightStep table v
      else (rightStep table (flip v)).map flip := by
  rcases v with ⟨l,q,r,a,b⟩
  cases hd : table.direction q with
  | right =>
    cases r with
    | nil => simp [step,rightStep,hd]
    | cons c r => cases c; simp [step,rightStep,hd]
  | left =>
    cases l with
    | nil =>
      cases a <;> simp [step,rightStep,hd,flip,Option.map_map,Function.comp_def]
    | cons c l =>
      rcases c with ⟨b,t⟩
      cases hh : table.cell q b t with
      | none => simp [step,rightStep,hd,flip,hh]
      | some i => cases hi : i.cross <;> simp [step,rightStep,hd,hh,hi,flip]

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open FiniteAlgebraicEnvelopes.Effect
variable {H B T : Type*} [Primcodable H] [Primcodable B] [Primcodable T]
  [Fintype H] [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq B] [DecidableEq T]
  [LinearOrder (Sector H B T)]
  (table : Table H B T) (P Q : Sector H B T → Prop) [DecidablePred P] [DecidablePred Q]

omit [Primcodable H] [Primcodable B] [Primcodable T] in
 theorem representative_list (v : Sector H B T) :
    representative table P Q v =
      (priorityList (fun x => decide (P x)) (fun x => decide (Q x)) (componentList table v)).min?.getD v := by
  symm
  apply minList_eq
  rw [priorityList_toFinset]
  have he : (componentList table v).toFinset = literalComponent table v := by
    ext w
    simp only [List.mem_toFinset,mem_componentList,mem_literalComponent]
  simp only [decide_eq_true_eq,he]

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler
open FiniteAlgebraicEnvelopes.Effect
noncomputable instance instPrimcodableHeadOfFintype {S Q : Type*} [Fintype S] [Fintype Q] : Primcodable (Control.Head S Q) := finitePrimcodable _
noncomputable instance instPrimcodableHeadOfFintype_1 {H : Type*} [Fintype H] : Primcodable (Surface.Head H) := finitePrimcodable _

namespace Surface
open Scan
variable {S Γ H : Type*} [Fintype S] [Fintype Γ] [Fintype H]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq H] (blank : Γ)

 def cleanAnchor (c : Base S × Tag S Γ) : Bool :=
  match c.1 with
  | .anchor _ => decide (c.2 = clean blank)
  | _ => false

omit [Fintype S] [Fintype Γ] in
 theorem trimQuota_drop (l : Cells S Γ) :
    trimQuota blank l = l.dropWhile (fun c => decide (c = Validator.cell blank .workspace)) := by
  induction l with
  | nil => rfl
  | cons c l ih => by_cases h : c = Validator.cell blank .workspace <;>
      simp [trimQuota,h,ih]

omit [DecidableEq S] [DecidableEq Γ] in
 theorem primrec_cleanupOutput : Primrec (Cleanup.output (S := S) blank) := by
  have hfinite : Primrec (fun c : Base S × Tag S Γ =>
      (Cleanup.emit c).map (Cleanup.letter blank)) := Primrec.dom_finite _
  exact (Primrec.listFilterMap Primrec.id (hfinite.comp Primrec.snd).to₂).of_eq fun l => by
    simp only [Cleanup.output, List.map_filterMap, id_eq]

end Surface

end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Compiler.Simulator
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ)

theorem semanticStep_lift_head (q : Q) (l : List (Tag S Γ)) (t : Tag S Γ) (r : List (Tag S Γ))
    {d : SemanticTape Γ Q} (h : SemanticStep M (interpret A (⟨q,l,t::r⟩ : Tape)) d) :
    ∃ e, TapeStep M (⟨q,l,t::r⟩ : Tape) e ∧ interpret A e = d := by
  unfold SemanticStep semanticStep interpret at h
  simp only [List.map_cons,Stream'.appendStream',Stream'.head_cons] at h
  cases hc : M.transition q t.work with
  | none => simp only [hc,Option.map_none] at h; cases h
  | some cmd =>
    simp only [hc,Option.map_some,Option.some.injEq] at h
    subst d
    rcases cmd with ⟨q',a,mv⟩
    cases mv with
    | stay => exact ⟨_,.stay hc rfl,rfl⟩
    | right => exact ⟨_,.right hc rfl,rfl⟩
    | left =>
      cases l with
      | nil => exact ⟨_,.leftEdge hc rfl,rfl⟩
      | cons b l => exact ⟨_,.left hc rfl,rfl⟩

/-- Infinite semantic transitions can always be realized by materializing at
most one implicit blank. This is a completeness statement, not an assumption
on accepting trajectories. -/
theorem semanticStep_lift {c : Tape (S := S) (Γ := Γ) (Q := Q)}
    {d : SemanticTape Γ Q} (h : SemanticStep M (interpret A c) d) :
    ∃ e, UnboundedStep A M c e ∧ interpret A e = d := by
  rcases c with ⟨q,l,r⟩
  cases r with
  | nil =>
    have hh : SemanticStep M (interpret A (⟨q,l,[clean A.blank]⟩ : Tape)) d := by
      have hp := interpret_pad A (⟨q,l,[]⟩ : Tape) 1
      simpa only [pad,List.nil_append,List.replicate_one] using hp ▸ h
    obtain ⟨e,he,hde⟩ := semanticStep_lift_head A M q l (clean A.blank) [] hh
    exact ⟨e,.extend he,hde⟩
  | cons t r =>
    obtain ⟨e,he,hde⟩ := semanticStep_lift_head A M q l t r h
    exact ⟨e,.within he,hde⟩

 theorem semanticRun_lift {c : Tape (S := S) (Γ := Γ) (Q := Q)}
    {d : SemanticTape Γ Q} (h : ReflTransGen (SemanticStep M) (interpret A c) d) :
    ∃ e, ReflTransGen (UnboundedStep A M) c e ∧ interpret A e = d := by
  induction h with
  | refl => exact ⟨c,.refl,rfl⟩
  | tail _ hs ih =>
    rcases ih with ⟨e,he,rfl⟩
    rcases semanticStep_lift A M hs with ⟨f,hf,rfl⟩
    exact ⟨f,he.tail hf,rfl⟩

 theorem semantic_halted_iff (c : Tape (S := S) (Γ := Γ) (Q := Q)) :
    semanticStep M (interpret A c) = none ↔ Halted A M c := by
  rcases c with ⟨q,l,r⟩
  cases r <;> simp [Halted,interpret,semanticStep,Stream'.appendStream',clean,
    Stream'.head,Stream'.get,Stream'.const,Stream'.cons]

end FiniteAlgebraicEnvelopes.Compiler.Simulator

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Quotients
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical compiler quotients and effective tested classes for word problems.
-/

namespace FiniteAlgebraicEnvelopes.WordProblem

 local instance instDecidableRelProdFinBoolLetterRel_re63764_1 (n : ℕ) : DecidableRel (letterRel n) := fun _ _ => inferInstanceAs (Decidable (_ < _))
theorem primrec_letterShortlex (n : ℕ) : PrimrecRel (List.Shortlex (letterRel n)) := by
  let ord : LinearOrder (Fin n × Bool) := LinearOrder.lift' Encodable.encode Encodable.encode_injective
  exact @Bootstrap.Search.primrec_shortlex _ _ _ ord ⟨inferInstance,Primrec.dom_finite _⟩

variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)

 attribute [local instance] OAI.FiniteAlgebraicEnvelopes.WordProblem.instTrichotomousProdFinBoolLetterRel
theorem computable_testedClass (h : ComputablePred (fun w : Word n => evalWord s w=1)) :
    Computable (testedClass s) := by
  classical
  exact Bootstrap.Canonical.computable_least (letterRel_wf n) (evalWord s)
    (primrec_letterShortlex n) (computable_word_equiv s h)

end FiniteAlgebraicEnvelopes.WordProblem

end OAI
end

section
-- module Solutions.OAIQ066_SO.BooneHigman_PartialAffine
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Primitive recursive dyadic partial affine monoid and its six-letter presentation.
-/

namespace FiniteAlgebraicEnvelopes.PartialAffine

 theorem computable_testedClass : Computable testedClass := by
  classical
  apply Bootstrap.Canonical.computable_least
  · exact Bootstrap.Search.primrec_shortlex ⟨inferInstance,Primrec.dom_finite _⟩
  · exact ⟨inferInstance,primrec_word_equivalence.decide.to_comp⟩

end FiniteAlgebraicEnvelopes.PartialAffine

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_TapeFolding
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Safe tapes, literal folding, and uniform code-machine realization.
-/

namespace FiniteAlgebraicEnvelopes.MachineRealization.OneSided
open Compiler.Simulator Turing Relation
variable {Γ Q : Type*}

def step (M : Machine Q Γ) (c : Cfg Γ Q) : Option (Cfg Γ Q) :=
  (M.transition c.state (c.cell c.pos)).map fun cmd =>
    ⟨cmd.state,(match cmd.move with | .stay => c.pos | .left => c.pos-1 | .right => c.pos+1),
      Function.update c.cell c.pos cmd.write⟩

def view (c : SemanticTape Γ Q) : Cfg Γ Q := ⟨c.state,c.left.length,semanticContent c⟩

 theorem view_step (M : Machine Q Γ) (c : SemanticTape Γ Q) :
   (semanticStep M c).map view = step M (view c) := by
  rcases c with ⟨q,l,r⟩
  have hh : Stream'.appendStream' l.reverse r l.length = r.head := by
    simpa only [List.length_reverse,Nat.add_zero,Stream'.head,Stream'.get] using append_at l.reverse r 0
  simp only [semanticStep,step,view,semanticContent,hh,Option.map_map]
  congr 1
  funext cmd
  rcases cmd with ⟨q',a,mv⟩
  cases mv with
  | stay =>
      dsimp only [Function.comp_apply,view,semanticContent]
      congr 1
      simpa only [List.length_reverse,Stream'] using replace_at l.reverse r a
  | right =>
      dsimp only [Function.comp_apply,view,semanticContent,List.length_cons]
      congr 1
      simpa only [semanticContent,List.reverse_cons,Stream'.append_append_stream,List.length_cons,
        Stream'.appendStream',List.length_reverse,Stream'] using replace_at l.reverse r a
  | left =>
      cases l with
      | nil =>
          dsimp only [Function.comp_apply,view,semanticContent,List.length_nil,Nat.zero_sub]
          congr 1
          exact replace_at [] r a
      | cons b l =>
          dsimp only [Function.comp_apply,view,semanticContent,List.length_cons]
          simp only [Nat.add_sub_cancel]
          congr 1
          simpa only [semanticContent,List.reverse_cons,Stream'.append_append_stream,List.length_cons,
            Nat.add_sub_cancel,Stream'.appendStream',List.length_reverse,List.length_append,List.length_singleton,List.length_nil,Nat.zero_add,Stream'] using replace_at (l.reverse ++ [b]) r a

 theorem respects (M : Machine Q Γ) : StateTransition.Respects (step M) (semanticStep M)
   (fun a b => view b = a) := by
  intro c s hs
  rw [←hs,←view_step M s]
  cases hc : semanticStep M s with
  | none => rfl
  | some t => exact ⟨t,rfl,TransGen.single hc⟩

end FiniteAlgebraicEnvelopes.MachineRealization.OneSided

namespace FiniteAlgebraicEnvelopes.MachineRealization.TapeFold
open Turing Relation Compiler.Simulator
variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

def command (d : Side) (q : Λ) (a : Cell Γ) : TM0.Stmt Γ → Command (Side × Λ) (Cell Γ)
  | .write b => ⟨(d,q),(match d with | .pos => {a with pos := b} | .neg => {a with neg := b}),.stay⟩
  | .move dr => match d,dr with
    | .pos,.right => ⟨(.pos,q),a,.right⟩
    | .pos,.left => if a.origin then ⟨(.neg,q),a,.stay⟩ else ⟨(.pos,q),a,.left⟩
    | .neg,.left => ⟨(.neg,q),a,.right⟩
    | .neg,.right => if a.origin then ⟨(.pos,q),a,.stay⟩ else ⟨(.neg,q),a,.left⟩

def machine (M : TM0.Machine Γ Λ) (start : Λ) : Machine (Side × Λ) (Cell Γ) :=
  ⟨(.pos,start),fun q a => (M q.2 (read q.1 a)).map fun cmd => command q.1 cmd.1 a cmd.2⟩

omit [Inhabited Γ] [Inhabited Λ] in
 theorem move_position (d : Side) (dr : Dir) (q : Λ) (a : Cell Γ) (p : ℕ)
    (ha : a.origin = decide (p = 0)) :
    let cmd := command d q a (.move dr)
    position cmd.state.1 (match cmd.move with | .stay => p | .left => p-1 | .right => p+1) =
      position d p + (match dr with | .left => -1 | .right => 1) := by
  cases d <;> cases dr <;> simp only [command,ha] <;>
    (try split_ifs) <;> simp_all [position] <;> omega

omit [Inhabited Γ] [Inhabited Λ] in
 theorem move_write (d : Side) (dr : Dir) (q : Λ) (a : Cell Γ) :
    (command d q a (.move dr)).write = a := by
  cases d <;> cases dr <;> simp only [command] <;> (try split_ifs) <;> rfl

omit [Inhabited Γ] [Inhabited Λ] in
 theorem command_state (d : Side) (q : Λ) (a : Cell Γ) (stmt : TM0.Stmt Γ) :
    (command d q a stmt).state.2 = q := by
  cases stmt with
  | write b => cases d <;> rfl
  | move dr => cases d <;> cases dr <;> simp only [command] <;> (try split_ifs) <;> rfl

 theorem step_rel (M : TM0.Machine Γ Λ) (start : Λ)
    {c : TM0.Cfg Γ Λ} {s : OneSided.Cfg (Cell Γ) (Side × Λ)} (hs : Rel c s)
    {cmd : Λ × TM0.Stmt Γ} (hc : M c.q c.Tape.head = some cmd) :
    ∃ t, Rel (⟨cmd.1,match cmd.2 with | .move d => c.Tape.move d | .write b => c.Tape.write b⟩) t ∧
      OneSided.step (machine M start) s = some t := by
  let ins := command s.state.1 cmd.1 (s.cell s.pos) cmd.2
  let t : OneSided.Cfg (Cell Γ) (Side × Λ) :=
    ⟨ins.state,(match ins.move with | .stay => s.pos | .left => s.pos-1 | .right => s.pos+1),
      Function.update s.cell s.pos ins.write⟩
  refine ⟨t,?_,?_⟩
  · refine ⟨command_state _ _ _ _,fun n => ?_⟩
    obtain ⟨hor,hpo,hne⟩ := hs.2 n
    obtain ⟨hop,_,_⟩ := hs.2 s.pos
    cases hcmd : cmd.2 with
    | move d =>
      have hw : ins.write = s.cell s.pos := by dsimp [ins]; rw [hcmd,move_write]
      have hp := move_position s.state.1 d cmd.1 (s.cell s.pos) s.pos hop
      change _ = _ at hp
      have hcelt : t.cell = s.cell := by dsimp [t]; rw [hw,Function.update_eq_self]
      have hpos : position t.state.1 t.pos = position s.state.1 s.pos +
          (match d with | .left => -1 | .right => 1) := by cases d <;> simpa only [t,ins,hcmd] using hp
      change (t.cell n).origin = _ ∧ (t.cell n).pos = _ ∧ (t.cell n).neg = _
      rw [hcelt]
      refine ⟨hor,?_,?_⟩
      · rw [hpos]
        cases d <;> simp only [Tape.move_left_nth,Tape.move_right_nth] <;>
          convert hpo using 1 <;> congr 1 <;> omega
      · rw [hpos]
        cases d <;> simp only [Tape.move_left_nth,Tape.move_right_nth] <;>
          convert hne using 1 <;> congr 1 <;> omega
    | write b =>
      cases hd : s.state.1 <;>
        simp only [t,ins,hcmd,command,hd,position]
      · by_cases hn : n = s.pos
        · subst n
          simp only [Function.update_self]
          refine ⟨hop,?_,?_⟩
          · simp [Tape.write]
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hne
        · rw [Function.update_of_ne hn]
          refine ⟨hor,?_,?_⟩
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hpo
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hne
      · by_cases hn : n = s.pos
        · subst n
          simp only [Function.update_self]
          refine ⟨hop,?_,?_⟩
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hpo
          · simp [Tape.write]
        · rw [Function.update_of_ne hn]
          refine ⟨hor,?_,?_⟩
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hpo
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hne
  · simp only [OneSided.step,machine,hs.1,read_head hs,hc,Option.map_some]
    rfl

 theorem respects (M : TM0.Machine Γ Λ) (start : Λ) :
    StateTransition.Respects (TM0.step M) (OneSided.step (machine M start)) Rel := by
  intro c s hs
  cases hc : M c.q c.Tape.head with
  | none => simp only [TM0.step,hc,Option.map_none,OneSided.step,machine,hs.1,read_head hs]
  | some cmd =>
    simp only [TM0.step,hc,Option.map_some]
    obtain ⟨t,ht,hst⟩ := step_rel M start hs hc
    exact ⟨t,ht,TransGen.single hst⟩

end FiniteAlgebraicEnvelopes.MachineRealization.TapeFold

namespace FiniteAlgebraicEnvelopes.MachineRealization.TapeFold
open Turing Relation Compiler.Simulator
variable {K : Type} {Γ : K → Type} {Λ : Type} [Inhabited Λ]

 theorem marked_step (M : TM0.Machine (TM2to1.Γ' K Γ) Λ) (start : Λ)
    (hM : TapeSafety.Preserves M) {s t : OneSided.Cfg (Cell (TM2to1.Γ' K Γ)) (Side × Λ)}
    (hs : Marked s) (hst : OneSided.step (machine M start) s = some t) : Marked t := by
  unfold OneSided.step machine at hst
  cases hc : M s.state.2 (read s.state.1 (s.cell s.pos)) with
  | none => simp only [hc,Option.map_none] at hst; cases hst
  | some cmd =>
    simp only [hc,Option.map_some,Option.some.injEq] at hst
    subst t
    intro n
    dsimp only [OneSided.Cfg.cell]
    by_cases hn : n = s.pos
    · subst n
      rw [Function.update_self]
      cases hd : cmd.2 with
      | move d => simpa only [move_write] using hs s.pos
      | write b =>
        have hp := hM s.state.2 (read s.state.1 (s.cell s.pos)) cmd.1 b (by rw [←hd]; exact hc)
        cases he : s.state.1 <;> simp only [he,read] at hp
        · exact ⟨hp.trans (hs s.pos).1,(hs s.pos).2⟩
        · exact ⟨(hs s.pos).1,hp.trans (hs s.pos).2⟩
    · rw [Function.update_of_ne hn]
      exact hs n

 theorem marked_run (M : TM0.Machine (TM2to1.Γ' K Γ) Λ) (start : Λ)
    (hM : TapeSafety.Preserves M) {s t : OneSided.Cfg (Cell (TM2to1.Γ' K Γ)) (Side × Λ)}
    (hs : Marked s) (hst : ReflTransGen (fun a b => OneSided.step (machine M start) a = some b) s t) : Marked t := by
  induction hst with
  | refl => exact hs
  | tail _ h ih => exact marked_step M start hM ih h

end FiniteAlgebraicEnvelopes.MachineRealization.TapeFold

namespace FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral

open Turing Relation Compiler.Simulator TapeFold Turing.PartrecToTM2 StackLift RawTM StackTape
variable {S Λ : Type} [Inhabited Λ]

theorem folded_eval (M : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Λ)
    (start stop : Λ) (hm : TapeSafety.Preserves M) {f : List S →. List S}
    (hM : ∀ w, StateTransition.eval (TM0.step M) ⟨start,tape w⟩ =
      (f w).map (fun out => ⟨stop,tape out⟩)) (w : List S) :
    StateTransition.eval (OneSided.step (TapeFold.machine M start)) (canon start w) =
      (f w).map (canon stop) := by
  apply Part.ext
  intro s
  constructor
  · intro hs
    obtain ⟨c,hc,hce⟩ := StateTransition.tr_eval_rev (TapeFold.respects M start) (canon_rel start w) hs
    rw [hM] at hce
    obtain ⟨out,hout,rfl⟩ := (Part.mem_map_iff _).mp hce
    have hmarked := marked_run M start hm (canon_marked start w) (StateTransition.mem_eval.mp hs).1
    rw [rel_canon_unique stop out hc hmarked]
    exact Part.mem_map _ hout
  · intro hs
    obtain ⟨out,hout,rfl⟩ := (Part.mem_map_iff _).mp hs
    have hb : (⟨stop,tape out⟩ : TM0.Cfg _ _) ∈ StateTransition.eval (TM0.step M) ⟨start,tape w⟩ := by
      rw [hM]; exact Part.mem_map _ hout
    obtain ⟨s,hs,hse⟩ := StateTransition.tr_eval (TapeFold.respects M start) (canon_rel start w) hb
    have hmarked := marked_run M start hm (canon_marked start w) (StateTransition.mem_eval.mp hse).1
    exact rel_canon_unique stop out hs hmarked ▸ hse

end FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral

namespace FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral

section
open Turing Relation Compiler.Simulator TapeFold Turing.PartrecToTM2 StackLift RawTM StackTape
variable {S Λ : Type} [Inhabited Λ]

def wrapper (M : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Λ) (start : Λ) :
    Machine (State Λ) (Gamma S) :=
  ⟨none,fun q a => match q with
    | none => some ⟨some (some (.pos,start)),mark a,.stay⟩
    | some none => none
    | some (some q) => match (TapeFold.machine M start).transition q a with
      | none => some ⟨some none,clear a,.stay⟩
      | some c => some ⟨some (some c.state),c.write,c.move⟩⟩

variable (M : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Λ) (start : Λ)
theorem wrapper_lift (s : OneSided.Cfg (Gamma S) (Side × Λ)) :
    OneSided.step (wrapper M start) (lift s) =
      (OneSided.step (TapeFold.machine M start) s).elim (some (finish s)) (fun t => some (lift t)) := by
  simp only [OneSided.step,lift,wrapper]
  cases hc : (TapeFold.machine M start).transition s.state (s.cell s.pos) with
  | none => rfl
  | some cmd => cases cmd.move <;> rfl

theorem wrapper_finish (s : OneSided.Cfg (Gamma S) (Side × Λ)) :
    OneSided.step (wrapper M start) (finish s) = none := rfl

theorem wrapper_initial (w : List S) : OneSided.step (wrapper M start) (initial w) = some (lift (canon start w)) := by
  simp only [OneSided.step,wrapper,initial,Option.map_some,lift,canon]
  congr 2
  exact (canon_cells start w).symm

theorem wrapper_eval (stop : Λ) (hm : TapeSafety.Preserves M) {f : List S →. List S}
    (hM : ∀ w, StateTransition.eval (TM0.step M) ⟨start,tape w⟩ =
      (f w).map (fun out => ⟨stop,tape out⟩)) (w : List S) :
    StateTransition.eval (OneSided.step (wrapper M start)) (initial w) = (f w).map (final (Λ := Λ)) := by
  rw [StateTransition.reaches_eval (ReflTransGen.single (wrapper_initial M start w)),
    After.eval_lift (OneSided.step (TapeFold.machine M start)) (OneSided.step (wrapper M start)) lift finish
      (wrapper_lift M start) (wrapper_finish M start),folded_eval M start stop hm hM]
  simp only [Part.map_map,Function.comp_def,finish_canon]

end

open Turing Compiler.Simulator Turing.PartrecToTM2 StackLift StackTape
variable {S : Type} [DecidableEq S]

def alphabet : Alphabet S (Gamma S) where
  blank := blank
  input := input
  output := output
  output_input a := by simp [output,input,slice]
  output_blank := rfl

end FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral

namespace FiniteAlgebraicEnvelopes.Compiler.Simulator
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ)

theorem interpret_content (c : Tape (S := S) (Γ := Γ) (Q := Q)) :
    semanticContent (interpret A c) = Stream'.appendStream' ((c.left.reverse ++ c.right).map Tag.work) (Stream'.const A.blank) := by
  simp [semanticContent,interpret,List.map_append,List.map_reverse,Stream'.append_append_stream]

theorem semanticReturns_iff {c : Tape (S := S) (Γ := Γ) (Q := Q)} {w : List S} :
    SemanticReturns A (interpret A c) w ↔ Returns A c w := by
  refine ⟨?_,returns_interpret A⟩
  rintro ⟨tail,hh⟩
  let L := (c.left.reverse ++ c.right).map Tag.work
  let W := w.map A.input ++ [A.blank]
  have ht : semanticContent (interpret A c) = Stream'.appendStream' W tail := by
    simpa only [W,Stream'.append_append_stream,Stream'.appendStream'] using hh
  have hsmall : Stream'.take W.length (semanticContent (interpret A c)) = W := by
    rw [ht,Stream'.take_append_of_le_length _ _ _ (le_refl _),List.take_length]
  have hlarge : Stream'.take (L.length+W.length) (semanticContent (interpret A c)) = L++List.replicate W.length A.blank := by
    rw [interpret_content A,←Stream'.append_take,take_constant]
  have hp := Stream'.take_prefix_take_left W.length (L.length+W.length)
    (semanticContent (interpret A c)) (by omega)
  rw [hsmall,hlarge] at hp
  obtain ⟨rest,he⟩ := hp
  exact ⟨W.length,rest,by simpa only [W,List.append_assoc,List.singleton_append] using he.symm⟩

end FiniteAlgebraicEnvelopes.Compiler.Simulator

namespace FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral
open Turing Relation Compiler Compiler.Simulator TapeFold Turing.PartrecToTM2 StackLift RawTM StackTape
variable {S Λ : Type} [DecidableEq S] [Inhabited Λ]
variable (M : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Λ) (start : Λ)

theorem view_initial (w : List S) : OneSided.view (interpret alphabet (initialTape alphabet (wrapper M start) w)) = initial (Λ := Λ) w := by
  simp [OneSided.view,initialTape,interpret,semanticContent,filledWork,Function.comp_def,initial,wrapper,raw,alphabet,List.map_map]

omit [Inhabited Λ] in
theorem returns_final {s : SemanticTape (Gamma S) (State Λ)} {out : List S}
    (hs : OneSided.view s = final out) : SemanticReturns alphabet s out := by
  have hc := congrArg OneSided.Cfg.cell hs
  change semanticContent s = raw out at hc
  refine ⟨Stream'.const blank,?_⟩
  rw [hc]
  change Stream'.appendStream' (out.map input) (Stream'.const blank) =
    Stream'.appendStream' (out.map input) (Stream'.cons blank (Stream'.const blank))
  congr 1
  funext n
  cases n <;> rfl

 theorem realizes (stop : Λ) (hm : TapeSafety.Preserves M) {f : List S →. List S}
    (hM : ∀ w, StateTransition.eval (TM0.step M) ⟨start,tape w⟩ =
      (f w).map (fun out => ⟨stop,tape out⟩)) : Word.Realizes alphabet (wrapper M start) f := by
  intro w out
  constructor
  · intro ho
    have hfold : final (Λ := Λ) out ∈ StateTransition.eval (OneSided.step (wrapper M start)) (initial w) := by
      rw [wrapper_eval M start stop hm hM]
      exact Part.mem_map _ ho
    obtain ⟨s,hs,he⟩ := StateTransition.tr_eval (OneSided.respects (wrapper M start)) (view_initial M start w) hfold
    obtain ⟨hr,hhalt⟩ := StateTransition.mem_eval.mp he
    obtain ⟨c,hc,hcs⟩ := semanticRun_lift alphabet (wrapper M start) hr
    refine ⟨c,hc,?_,?_⟩
    · apply (semantic_halted_iff alphabet (wrapper M start) c).mp
      rw [hcs]; exact hhalt
    · apply (semanticReturns_iff alphabet).mp
      rw [hcs]
      exact returns_final hs
  · rintro ⟨c,hc,hh,ho⟩
    have he : interpret alphabet c ∈ StateTransition.eval (semanticStep (wrapper M start))
        (interpret alphabet (initialTape alphabet (wrapper M start) w)) :=
      StateTransition.mem_eval.mpr ⟨unboundedRun_interpret alphabet (wrapper M start) hc,
        (semantic_halted_iff alphabet (wrapper M start) c).mpr hh⟩
    obtain ⟨s,hs,he⟩ := StateTransition.tr_eval_rev (OneSided.respects (wrapper M start)) (view_initial M start w) he
    rw [wrapper_eval M start stop hm hM] at he
    obtain ⟨out',ho',rfl⟩ := (Part.mem_map_iff _).mp he
    have hu : out' = out := semanticReturns_unique alphabet (returns_final hs) (returns_interpret alphabet ho)
    exact hu ▸ ho'

end FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral

namespace FiniteAlgebraicEnvelopes.MachineRealization.WordEvaluator
open Turing Compiler Compiler.Simulator FoldLiteral
variable {S : Type} [Fintype S] [Primcodable S]
/-- Every algorithmic partial word function has an actual one-sided finite
    machine with the literal first-blank readout used by the finite compiler. -/
theorem exists_machine {f : List S →. List S} (hf : Partrec f) :
    ∃ (Γ Q : Type) (_ : Fintype Γ) (_ : Fintype Q)
      (A : Alphabet S Γ) (M : Machine Q Γ),
      (∀ g a, A.output g = some a → g = A.input a) ∧ Word.Realizes A M f := by
  classical
  obtain ⟨Λ,hΛ,iΛ,M,start,stop,hm,hM⟩ := exists_safe_tape hf
  let : Fintype Λ := hΛ
  let : Inhabited Λ := iΛ
  exact ⟨Gamma S,State Λ,inferInstance,inferInstance,alphabet,wrapper M start,
    output_decode,realizes M start stop hm hM⟩

end FiniteAlgebraicEnvelopes.MachineRealization.WordEvaluator

namespace FiniteAlgebraicEnvelopes.MachineRealization.CodeMachine
open Turing Turing.ToPartrec Turing.PartrecToTM2 StackLift RawTM StackTape

attribute [instance] Raw.finiteQ

attribute [instance] TapeProgram.finiteQ TapeProgram.inhabitedQ

end FiniteAlgebraicEnvelopes.MachineRealization.CodeMachine

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_UniformMachines
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Parameterized effective machine realization and uniform finite data.
-/

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterMachine
open Compiler.Simulator OneSided Turing Relation
variable {S Γ Q : Type*}

variable (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

def machine (p : S) (n : ℕ) : Machine (State Q n) (Bool × Γ) where
  initial := .start
  transition q a := match q with
    | .start => some ⟨.scan,(true,a.2),.stay⟩
    | .scan => if a.2=A.blank then some ⟨.emit ⟨0,by omega⟩,a,.stay⟩
        else some ⟨.scan,a,.right⟩
    | .emit k => if h : k.val<n+1 then
        some ⟨.emit ⟨k.val+1,by omega⟩,(a.1,A.input p),.right⟩
        else some ⟨.rewind,a,.stay⟩
    | .rewind => if a.1 then some ⟨.run M.initial,(false,a.2),.stay⟩
        else some ⟨.rewind,a,.left⟩
    | .run q => (M.transition q a.2).map fun c => ⟨.run c.state,(false,c.write),c.move⟩

def content (w : List S) : ℕ → Γ := Stream'.appendStream' (w.map A.input) (Stream'.const A.blank)
def marked (w : List S) : ℕ → Bool × Γ := fun i => (decide (i=0),content A w i)
def flat (w : List S) : ℕ → Bool × Γ := fun i => (false,content A w i)

omit [DecidableEq Γ] in
 theorem input_ne_blank (a : S) : A.input a≠A.blank := by
  intro h
  have hh := A.output_input a
  rw [h,A.output_blank] at hh
  cases hh

omit [DecidableEq Γ] in
 theorem content_beyond (w : List S) (i : ℕ) (hi : w.length ≤ i) : content A w i=A.blank := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hi
  simpa [content, Stream'.const] using append_at (w.map A.input) (Stream'.const A.blank) j

omit [DecidableEq Γ] in
 theorem content_before (w : List S) (i : ℕ) (hi : i<w.length) :
    content A w i=A.input w[i] := by
  induction w generalizing i with
  | nil => simp at hi
  | cons a w ih =>
    cases i with
    | zero => rfl
    | succ i =>
      exact ih i (by simpa using hi)

omit [DecidableEq Γ] in
 theorem marked_write (w : List S) (p : S) :
    Function.update (marked A w) w.length (decide (w.length=0),A.input p)=marked A (w++[p]) := by
  funext i
  apply Prod.ext
  · by_cases h : i=w.length
    · subst i; simp [marked]
    · simp [Function.update_of_ne h,marked]
  · by_cases h : i<w.length
    · have hn : i≠w.length := Nat.ne_of_lt h
      rw [Function.update_of_ne hn]
      change content A w i=content A (w++[p]) i
      rw [content_before A w i h,content_before A _ i (by simp; omega)]
      congr 1
      simp [List.getElem_append_left h]
    · by_cases he : i=w.length
      · subst i
        rw [Function.update_self]
        change A.input p=content A (w++[p]) w.length
        rw [content_before A _ _ (by simp)]
        simp
      · rw [Function.update_of_ne he]
        change content A w i=content A (w++[p]) i
        rw [content_beyond A w i (by omega),content_beyond A _ i (by simp; omega)]

omit [DecidableEq Γ] in
 theorem marked_clear (w : List S) :
    Function.update (marked A w) 0 (false,content A w 0)=flat A w := by
  funext i
  by_cases hi : i=0
  · subst i; simp [flat]
  · simp [marked,flat,hi]

variable (p : S) (n : ℕ)

 theorem start_step (w : List S) :
    step (machine A M p n) ⟨.start,0,flat A w⟩=some ⟨.scan,0,marked A w⟩ := by
  simp only [step,machine,flat,Option.map_some]
  congr 2
  funext i
  by_cases hi : i=0
  · subst i; simp [marked]
  · simp [marked,flat,hi]

 theorem scan_step (w : List S) (i : ℕ) (hi : i<w.length) :
    step (machine A M p n) ⟨.scan,i,marked A w⟩=some ⟨.scan,i+1,marked A w⟩ := by
  have hb : content A w i≠A.blank := by rw [content_before A w i hi]; exact input_ne_blank A _
  simp only [step,machine,marked,ite_eq_right hb,Option.map_some]
  congr 2
  exact Function.update_eq_self _ _

 theorem scan_end (w : List S) :
    step (machine A M p n) ⟨.scan,w.length,marked A w⟩=
      some ⟨.emit ⟨0,by omega⟩,w.length,marked A w⟩ := by
  simp only [step,machine,marked,content_beyond A w w.length le_rfl,↓reduceIte,Option.map_some]
  have he : (decide (w.length=0),A.blank)=marked A w w.length := by
    simp [marked,content_beyond A w w.length le_rfl]
  rw [he,Function.update_eq_self]

 theorem scan_run (w : List S) :
    ReflTransGen (fun a b => step (machine A M p n) a=some b)
      ⟨.scan,0,marked A w⟩ ⟨.scan,w.length,marked A w⟩ := by
  have h (i : ℕ) (hi : i ≤ w.length) :
      ReflTransGen (fun a b => step (machine A M p n) a=some b)
        ⟨.scan,0,marked A w⟩ ⟨.scan,i,marked A w⟩ := by
    induction i with
    | zero => exact .refl
    | succ i ih => exact (ih (by omega)).tail (scan_step A M p n w i (by omega))
  exact h _ le_rfl

 theorem emit_step (w : List S) (k : Fin (n+2)) (hk : k.val<n+1) :
    step (machine A M p n) ⟨.emit k,w.length,marked A w⟩=
      some ⟨.emit ⟨k.val+1,by omega⟩,(w++[p]).length,marked A (w++[p])⟩ := by
  simp only [step,machine,dite_eq_left hk,marked,Option.map_some,List.length_append,List.length_singleton]
  congr 2
  exact marked_write A w p

 theorem emit_end (w : List S) :
    step (machine A M p n) ⟨.emit ⟨n+1,by omega⟩,w.length,marked A w⟩=
      some ⟨.rewind,w.length,marked A w⟩ := by
  simp only [step,machine,dite_eq_right (Nat.lt_irrefl (n+1)),Option.map_some]
  rw [Function.update_eq_self]

 theorem emit_run (w : List S) :
    ReflTransGen (fun a b => step (machine A M p n) a=some b)
      ⟨.emit ⟨0,by omega⟩,w.length,marked A w⟩
      ⟨.emit ⟨n+1,by omega⟩,(w++List.replicate (n+1) p).length,
        marked A (w++List.replicate (n+1) p)⟩ := by
  have h (i : ℕ) (hi : i<n+2) :
      ReflTransGen (fun a b => step (machine A M p n) a=some b)
      ⟨.emit ⟨0,by omega⟩,w.length,marked A w⟩
      ⟨.emit ⟨i,hi⟩,(w++List.replicate i p).length,marked A (w++List.replicate i p)⟩ := by
    induction i with
    | zero => simpa using (ReflTransGen.refl (a:= (⟨.emit ⟨0,by omega⟩,w.length,marked A w⟩ : Cfg _ (State Q n))))
    | succ i ih =>
      have hh := (ih (by omega)).tail (emit_step A M p n (w++List.replicate i p) ⟨i,by omega⟩ (by change i<n+1; omega))
      simpa only [List.replicate_succ',List.append_assoc] using hh
  exact h _ (by omega)

 theorem rewind_step (w : List S) (i : ℕ) :
    step (machine A M p n) ⟨.rewind,i+1,marked A w⟩=some ⟨.rewind,i,marked A w⟩ := by
  simp only [step,machine,marked,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,decide_false,
    Bool.false_eq_true, ↓reduceIte,Nat.add_sub_cancel,Option.map_some]
  rw [show (false,content A w (i+1))=marked A w (i+1) by simp [marked]]
  rw [Function.update_eq_self]

 theorem rewind_run (w : List S) (i : ℕ) :
    ReflTransGen (fun a b => step (machine A M p n) a=some b)
      ⟨.rewind,i,marked A w⟩ ⟨.rewind,0,marked A w⟩ := by
  induction i with
  | zero => exact .refl
  | succ i ih => exact ReflTransGen.head (rewind_step A M p n w i) ih

 theorem rewind_end (w : List S) :
    step (machine A M p n) ⟨.rewind,0,marked A w⟩=some ⟨.run M.initial,0,flat A w⟩ := by
  simp only [step,machine,marked,decide_true,↓reduceIte,Option.map_some]
  congr 2
  exact marked_clear A w

 theorem initialize_run (w : List S) :
    ReflTransGen (fun a b => step (machine A M p n) a=some b)
      ⟨.start,0,flat A w⟩
      ⟨.run M.initial,0,flat A (w++List.replicate (n+1) p)⟩ := by
  have ht : ReflTransGen (fun a b => step (machine A M p n) a=some b)
      ⟨.start,0,flat A w⟩ ⟨.scan,0,marked A w⟩ := .single (start_step A M p n w)
  exact ((((ht.trans (scan_run A M p n w)).tail
    (scan_end A M p n w)).trans (emit_run A M p n w)).tail
      (emit_end A M p n _)).trans ((rewind_run A M p n _ _).tail (rewind_end A M p n _))

 theorem step_lift (c : Cfg Γ Q) :
    step (machine A M p n) (lift n c)=(step M c).map (lift n) := by
  simp only [step,machine,lift,Option.map_map]
  congr 1
  funext cmd
  simp only [Function.comp_apply]
  congr 1
  funext i
  by_cases hi : i=c.pos
  · subst i; simp
  · simp [Function.update_of_ne hi]

 theorem lift_respects : StateTransition.Respects (step M) (step (machine A M p n))
    (fun a b => lift n a=b) := by
  rintro c _ rfl
  rw [step_lift]
  cases hc : step M c with
  | none => rfl
  | some d => exact ⟨lift n d,rfl,TransGen.single (by rw [step_lift,hc]; rfl)⟩

 theorem eval_lift (c : Cfg Γ Q) :
    StateTransition.eval (step (machine A M p n)) (lift n c)=
      (StateTransition.eval (step M) c).map (lift n) :=
  StateTransition.tr_eval' _ _ _ (lift_respects A M p n) c

 theorem eval_initialized (w : List S) :
    StateTransition.eval (step (machine A M p n)) ⟨.start,0,flat A w⟩=
      (StateTransition.eval (step M)
        ⟨M.initial,0,content A (w++List.replicate (n+1) p)⟩).map (lift n) := by
  have hi : StateTransition.Reaches (step (machine A M p n))
    ⟨.start,0,flat A w⟩ ⟨.run M.initial,0,flat A (w++List.replicate (n+1) p)⟩ :=
    initialize_run A M p n w
  rw [StateTransition.reaches_eval hi]
  exact eval_lift A M p n
    ⟨M.initial,0,content A (w++List.replicate (n+1) p)⟩

def alphabet : Alphabet S (Bool × Γ) where
  blank := (false,A.blank)
  input s := (false,A.input s)
  output x := if x.1 then none else A.output x.2
  output_input s := A.output_input s
  output_blank := A.output_blank

omit [DecidableEq Γ] in
 theorem output_decode (hA : ∀ g a, A.output g=some a → g=A.input a) :
    ∀ g a, (alphabet A).output g=some a → g=(alphabet A).input a := by
  rintro ⟨b,g⟩ a h
  cases b with
  | true => simp [alphabet] at h
  | false => exact congrArg (false,·) (hA g a h)

omit [DecidableEq Γ] in
 theorem initial_view (w : List S) :
    view (interpret A (initialTape A M w))=⟨M.initial,0,content A w⟩ := by
  simp [view,initialTape,interpret,semanticContent,filledWork,Function.comp_def,content]

omit [DecidableEq Γ] in
 theorem returns_iff (w out : List S) :
    (∃ c, ReflTransGen (UnboundedStep A M) (initialTape A M w) c ∧
      Halted A M c ∧ Returns A c out) ↔
    (∃ c, c ∈ StateTransition.eval (step M) ⟨M.initial,0,content A w⟩ ∧
      ∃ t, c.cell=Stream'.appendStream' (out.map A.input) (Stream'.cons A.blank t)) := by
  constructor
  · rintro ⟨c,hc,hh,ho⟩
    have he : interpret A c ∈ StateTransition.eval (semanticStep M)
        (interpret A (initialTape A M w)) :=
      StateTransition.mem_eval.mpr ⟨unboundedRun_interpret A M hc,
        (semantic_halted_iff A M c).mpr hh⟩
    obtain ⟨d,hd,he⟩ := StateTransition.tr_eval_rev (OneSided.respects M) (initial_view A M w) he
    exact ⟨d,he,by rw [←hd]; exact returns_interpret A ho⟩
  · rintro ⟨c,hc,ho⟩
    obtain ⟨s,hs,he⟩ := StateTransition.tr_eval (OneSided.respects M) (initial_view A M w) hc
    obtain ⟨hr,hh⟩ := StateTransition.mem_eval.mp he
    obtain ⟨d,hd,hds⟩ := semanticRun_lift A M hr
    refine ⟨d,hd,?_,?_⟩
    · apply (semantic_halted_iff A M d).mp
      rw [hds]; exact hh
    · apply (semanticReturns_iff A).mp
      rw [hds]
      rw [←hs] at ho
      exact ho

omit [DecidableEq Γ] in
 theorem lift_returns (c : Cfg Γ Q) (out : List S) :
    (∃ t, (lift n c).cell=Stream'.appendStream' (out.map (alphabet A).input)
        (Stream'.cons (alphabet A).blank t)) ↔
    (∃ t, c.cell=Stream'.appendStream' (out.map A.input) (Stream'.cons A.blank t)) := by
  have hm (l : List Γ) (t : Stream' Γ) :
      (fun i => (false,Stream'.appendStream' l t i))=
        Stream'.appendStream' (l.map (false,·)) (fun i => (false,t i)) := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      funext i; cases i with
      | zero => rfl
      | succ i => exact congrFun ih i
  have hs (l : List (Bool × Γ)) (t : Stream' (Bool × Γ)) :
      (fun i => (Stream'.appendStream' l t i).2)=
        Stream'.appendStream' (l.map Prod.snd) (fun i => (t i).2) := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      funext i; cases i with
      | zero => rfl
      | succ i => exact congrFun ih i
  constructor
  · rintro ⟨t,h⟩
    have hh := congrArg (fun f : ℕ → Bool × Γ => fun i => (f i).2) h
    rw [hs] at hh
    refine ⟨fun i => (t i).2,?_⟩
    have ht : (fun i => (Stream'.cons (alphabet A).blank t i).2)=
        Stream'.cons A.blank (fun i => (t i).2) := by
      funext i; cases i <;> rfl
    rw [ht] at hh
    simpa only [lift,alphabet,List.map_map,Function.comp_def] using hh
  · rintro ⟨t,h⟩
    refine ⟨fun i => (false,t i),?_⟩
    change (fun i => (false,c.cell i))=_
    rw [h,hm]
    simp only [List.map_map,Function.comp_def,alphabet]
    congr 1
    funext i; cases i <;> rfl

 theorem realizes {f : List S → Part (List S)} (hM : Compiler.Word.Realizes A M f) :
    Compiler.Word.Realizes (alphabet A) (machine A M p n)
      (fun w => f (w++List.replicate (n+1) p)) := by
  intro w out
  rw [returns_iff]
  have hi : content (alphabet A) w=flat A w := by
    funext i
    induction w generalizing i with
    | nil => rfl
    | cons a w ih => cases i with
      | zero => rfl
      | succ i => exact ih i
  change out ∈ f (w++List.replicate (n+1) p) ↔ _
  rw [hi]
  change out ∈ f _ ↔ ∃ c, c ∈ StateTransition.eval (step (machine A M p n))
    ⟨.start,0,flat A w⟩ ∧ _
  rw [eval_initialized]
  constructor
  · intro ho
    obtain ⟨c,hc,hr⟩ := (returns_iff A M _ out).mp ((hM _ _).mp ho)
    exact ⟨lift n c,Part.mem_map _ hc,(lift_returns A n c out).mpr hr⟩
  · rintro ⟨c,hc,hr⟩
    obtain ⟨d,hd,rfl⟩ := (Part.mem_map_iff _).mp hc
    exact (hM _ _).mpr ((returns_iff A M _ out).mpr
      ⟨d,hd,(lift_returns A n d out).mp hr⟩)

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterMachine

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode
open Compiler.Simulator ParameterMachine
variable {S Γ Q : Type*}

def encodeCommand (n : ℕ) (c : Command (State Q n) (Bool×Γ)) : Cmd Q Γ :=
  (encode n c.state,c.write,c.move)

variable (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ] (p : S)

def transition (n : ℕ) (q : Control Q) (a : Bool×Γ) : Option (Cmd Q Γ) := match q with
  | .inr r => (M.transition r a.2).map fun c => (.inr c.state,(false,c.write),c.move)
  | .inl k => if k=0 then some (.inl 1,(true,a.2),.stay)
    else if k=1 then if a.2=A.blank then some (.inl 3,a,.stay) else some (.inl 1,a,.right)
    else if k=2 then if a.1 then some (.inr M.initial,(false,a.2),.stay)
      else some (.inl 2,a,.left)
    else if k-3<n+2 then if k-3<n+1 then some (.inl (k+1),(a.1,A.input p),.right)
      else some (.inl 2,a,.stay)
    else none

 theorem transition_encode (n : ℕ) (q : State Q n) (a : Bool×Γ) :
    transition A M p n (encode n q) a=
      ((machine A M p n).transition q a).map (encodeCommand n) := by
  cases q with
  | start => rfl
  | scan => simp [transition,encode,machine]; split <;> rfl
  | rewind => simp [transition,encode,machine]; split <;> rfl
  | run q => simp [transition,encode,machine,Option.map_map,encodeCommand,Function.comp_def]
  | emit k =>
    have h0 : k.val+3≠0 := by omega
    have h1 : k.val+3≠1 := by omega
    have h2 : k.val+3≠2 := by omega
    simp only [transition,encode,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,Nat.add_sub_cancel,
      ite_eq_left k.isLt,machine]
    split <;> simp_all [encodeCommand,encode]

variable [Fintype Q] [Fintype Γ] [Primcodable Q] [Primcodable Γ]
noncomputable instance instPrimcodableMove : Primcodable Move := Primcodable.ofEquiv (Fin (Fintype.card Move)) (Fintype.equivFin Move)

 theorem primrec_transition : Primrec (fun x : (ℕ × Control Q) × (Bool×Γ) =>
    transition A M p x.1.1 x.1.2 x.2) := by
  let X := (ℕ × Control Q) × (Bool×Γ)
  have hn : Primrec (fun x : X => x.1.1) := Primrec.fst.comp Primrec.fst
  have ha : Primrec (fun x : X => x.2) := Primrec.snd
  have hbranch : Primrec (fun z : X × ℕ =>
      if z.2=0 then (some (Sum.inl 1,(true,z.1.2.2),Move.stay) : Option (Cmd Q Γ))
      else if z.2=1 then if z.1.2.2=A.blank then some (.inl 3,z.1.2,Move.stay)
        else some (.inl 1,z.1.2,Move.right)
      else if z.2=2 then if z.1.2.1 then some (.inr M.initial,(false,z.1.2.2),Move.stay)
        else some (.inl 2,z.1.2,Move.left)
      else if z.2-3<z.1.1.1+2 then if z.2-3<z.1.1.1+1 then
        some (.inl (z.2+1),(z.1.2.1,A.input p),Move.right)
        else some (.inl 2,z.1.2,Move.stay)
      else none) := by
    have hz : Primrec (fun z : X × ℕ => z.1.2) := ha.comp Primrec.fst
    have mk (c : Control Q) (mv : Move) : Primrec (fun z : X × ℕ => some (c,z.1.2,mv)) :=
      Primrec.option_some.comp ((Primrec.const c).pair (hz.pair (Primrec.const mv)))
    have hemit : Primrec (fun z : X × ℕ =>
        some ((Sum.inl (z.2+1) : Control Q),(z.1.2.1,A.input p),Move.right)) :=
      Primrec.option_some.comp ((Primrec.sumInl.comp (Primrec.succ.comp Primrec.snd)).pair
        (((Primrec.fst.comp hz).pair (Primrec.const _)).pair (Primrec.const _)))
    apply Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
      ((Primrec.dom_finite (fun a : Bool×Γ =>
        (some (.inl 1,(true,a.2),Move.stay) : Option (Cmd Q Γ)))).comp hz)
    apply Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 1))
      ((Primrec.dom_finite (fun a : Bool×Γ => if a.2=A.blank then
        (some (.inl 3,a,Move.stay) : Option (Cmd Q Γ)) else some (.inl 1,a,Move.right))).comp hz)
    apply Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 2))
      ((Primrec.dom_finite (fun a : Bool×Γ => if a.1 then
        (some (.inr M.initial,(false,a.2),Move.stay) : Option (Cmd Q Γ)) else some (.inl 2,a,Move.left))).comp hz)
    exact Primrec.ite (Primrec.nat_lt.comp (Primrec.nat_sub.comp Primrec.snd (Primrec.const 3))
      (Primrec.nat_add.comp (hn.comp Primrec.fst) (Primrec.const 2)))
      (Primrec.ite (Primrec.nat_lt.comp (Primrec.nat_sub.comp Primrec.snd (Primrec.const 3))
        (Primrec.succ.comp (hn.comp Primrec.fst))) hemit (mk (.inl 2) .stay)) (Primrec.const none)
  exact (Primrec.sumCasesOn (Primrec.snd.comp Primrec.fst) hbranch.to₂
    ((Primrec.dom_finite (fun z : Q × (Bool×Γ) =>
      (M.transition z.1 z.2.2).map fun c =>
        ((Sum.inr c.state : Control Q),(false,c.write),c.move))).comp
          (Primrec.snd.pair (ha.comp Primrec.fst))).to₂).of_eq fun x => by
            cases x.1.2 <;> rfl

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_UniformControl
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform validation, simulation, and finite control.
-/

namespace FiniteAlgebraicEnvelopes.Compiler
open FiniteAlgebraicEnvelopes.Effect
namespace Surface.Uniform
open Surface HeadCodec
open scoped HeadCodec
open Scan
variable {S Γ H : Type*} [Fintype S] [Fintype Γ] [Primcodable H]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq H] (blank : Γ)

 theorem primrec_trimQuota : Primrec (trimQuota (S := S) blank) :=
  (Primrec.list_dropWhile (Primrec.dom_finite _)).of_eq fun l => (trimQuota_drop blank l).symm

end Surface.Uniform
end FiniteAlgebraicEnvelopes.Compiler

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_UniformPaths
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform surface and path normalization with recursive compiler interfaces.
-/

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

section
open Compiler Compiler.Simulator Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec
variable {S Γ Q : Type*}

variable (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ] (p : S)
def codedMachine (n : ℕ) : Machine (Control Q) (Bool×Γ) where
  initial := .inl 0
  transition q a := (transition A M p n q a).map (fun c => ⟨c.1,c.2.1,c.2.2⟩)

theorem coded_initial (n : ℕ) :
    (codedMachine A M p n).initial=encode n (ParameterMachine.machine A M p n).initial := rfl

variable [Fintype Q] [Fintype Γ] [Primcodable Q] [Primcodable Γ]

variable {T : Type*} [Fintype T]
noncomputable def heads (n : ℕ) : List (Compiler.Control.Head T (Control Q)) :=
  controlSupport (support n)

end

open Compiler Compiler.Simulator Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

namespace FiniteAlgebraicEnvelopes.Compiler.Surface
variable {S Γ H H' : Type*}

def headMap (i : H → H') : Head H → Head H'
  | .raw => .raw | .pending => .pending | .cleanup => .cleanup | .internal q => .internal (i q)

theorem headMap_injective {i : H → H'} (hi : Function.Injective i) : Function.Injective (headMap i) := by
  intro a b h; cases a <;> cases b <;> simp_all [headMap]
  exact hi h

end FiniteAlgebraicEnvelopes.Compiler.Surface

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

open Compiler Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec
variable {T Γ Q : Type*} [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q] [Primcodable Q]

noncomputable def surfaces (n : ℕ) : List (Surface.Head (Compiler.Control.Head T (Control Q))) :=
  [.raw,.pending,.cleanup] ++ (heads n).map Surface.Head.internal

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_SelfReference
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Controlled shorter-input evaluator calls, fixed points, totality, and tested-class realization.
-/

namespace FiniteAlgebraicEnvelopes.MachineRealization.UniversalMachine
open Compiler.Simulator OneSided ParameterMachine
variable {S Γ Q : Type*} [DecidableEq Γ]

/-- Forget the parameter delimiter as an input/output letter. Work symbols and
    transitions are not changed. -/
def restrict (A : Alphabet (S ⊕ Unit) Γ) : Alphabet S Γ where
  blank := A.blank
  input s := A.input (.inl s)
  output g := (A.output g).bind fun a => match a with | .inl s => some s | .inr _ => none
  output_input s := by simp [A.output_input]
  output_blank := by simp [A.output_blank]

omit [DecidableEq Γ] in
 theorem restrict_decode (A : Alphabet (S ⊕ Unit) Γ)
    (hA : ∀ g a, A.output g=some a → g=A.input a) :
    ∀ g a, (restrict A).output g=some a → g=(restrict A).input a := by
  intro g a h
  obtain ⟨b,hb,hba⟩ := Option.bind_eq_some_iff.mp h
  cases b with
  | inr u => cases hba
  | inl s => cases hba; exact hA _ _ hb

omit [DecidableEq Γ] in
 theorem restrict_content (A : Alphabet (S ⊕ Unit) Γ) (w : List S) :
    content (restrict A) w=content A (w.map Sum.inl) := by
  simp only [content,List.map_map,Function.comp_def,restrict]
  rfl

omit [DecidableEq Γ] in
 theorem restrict_realizes (A : Alphabet (S ⊕ Unit) Γ) (M : Machine Q Γ)
    {f : List S → Part (List S)} {g : List (S ⊕ Unit) → Part (List (S ⊕ Unit))}
    (hM : Compiler.Word.Realizes A M g)
    (hg : ∀ w, g (w.map Sum.inl)=(f w).map (List.map Sum.inl)) :
    Compiler.Word.Realizes (restrict A) M f := by
  intro w out
  have hi : (List.map Sum.inl : List S → List (S ⊕ Unit)) out ∈ g (w.map Sum.inl) ↔ out ∈ f w := by
    rw [hg]
    constructor
    · intro h
      obtain ⟨y,hy,he⟩ := (Part.mem_map_iff _).mp h
      have hyout : y=out := List.map_injective_iff.mpr Sum.inl_injective he
      exact hyout ▸ hy
    · exact Part.mem_map _
  rw [←hi,hM,returns_iff A M,returns_iff (restrict A) M,restrict_content]
  simp only [List.map_map,Function.comp_def,restrict]

def letters (w : List (S ⊕ Unit)) : List S :=
  w.filterMap fun a => match a with | .inl s => some s | .inr _ => none

def parameter (w : List (S ⊕ Unit)) : ℕ :=
  (w.filterMap fun a => match a with | .inl _ => none | .inr _ => some ()).length - 1

 theorem letters_input (w : List S) (n : ℕ) :
    letters (w.map Sum.inl ++ List.replicate (n+1) (.inr ()))=w := by
  simp [letters,List.filterMap_map]

 theorem parameter_input (w : List S) (n : ℕ) :
    parameter (w.map Sum.inl ++ List.replicate (n+1) (.inr ()))=n := by
  simp [parameter,List.filterMap_map]

variable [Primcodable S]

 theorem primrec_letters : Primrec (letters (S := S)) := by
  have h : Primrec (fun a : S ⊕ Unit => match a with | .inl s => some s | .inr _ => none) :=
    (Primrec.sumCasesOn Primrec.id (Primrec.option_some.comp Primrec.snd).to₂ (Primrec.const none).to₂).of_eq
      (fun a => by cases a <;> rfl)
  exact Primrec.listFilterMap Primrec.id (h.comp Primrec.snd).to₂

 theorem primrec_parameter : Primrec (parameter (S := S)) := by
  have h : Primrec (fun a : S ⊕ Unit => match a with | .inl _ => none | .inr _ => some ()) :=
    (Primrec.sumCasesOn Primrec.id (Primrec.const none).to₂ (Primrec.const (some ())).to₂).of_eq
      (fun a => by cases a <;> rfl)
  exact Primrec.nat_sub.comp (Primrec.list_length.comp
    (Primrec.listFilterMap Primrec.id (h.comp Primrec.snd).to₂)) (Primrec.const 1)

def universal (f : ℕ → List S → Part (List S)) (w : List (S ⊕ Unit)) :
    Part (List (S ⊕ Unit)) := (f (parameter w) (letters w)).map (List.map Sum.inl)

omit [Primcodable S] in
 theorem universal_input (f : ℕ → List S → Part (List S)) (w : List S) (n : ℕ) :
    universal f (w.map Sum.inl ++ List.replicate (n+1) (.inr ()))=
      (f n w).map (List.map Sum.inl) := by
  rw [universal,parameter_input,letters_input]

 theorem partrec_universal {f : ℕ → List S → Part (List S)} (hf : Partrec₂ f) :
    Partrec (universal f) :=
  (hf.comp primrec_parameter.to_comp primrec_letters.to_comp).map
    ((Primrec.list_map Primrec.id (Primrec.sumInl.comp Primrec.snd).to₂).to_comp.comp Computable.snd).to₂

end FiniteAlgebraicEnvelopes.MachineRealization.UniversalMachine

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_FiniteIdempotentDiagrams
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteIdempotentDiagrams

section

open Matrix
open scoped Matrix

variable {K R T : Type*} [CommRing K] [Ring R] [AddCommGroup T]

def ThreeCopies.system (C : ThreeCopies K R) : Set R :=
  {x | x = 1 ∨ ∃ (i : Fin 3) (M : Mat3 K), M * M = M ∧ C.copy i M = x}

end

open Matrix
open scoped Matrix

end FiniteIdempotentDiagrams

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChainsMapChainComp
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ListChains

section

variable (G : Type*) [Group G]

lemma mapChain_mem_controlled_of_differences {H : Type*} [Group H] (f : G → H)
    {A : Set G} {B : Set H}
    (hf : ∀ x y, x⁻¹*y ∈ A → (f x)⁻¹*f y ∈ B)
    {c : Chain G} (hc : c ∈ controlledModule G A) :
    mapChain G f c ∈ controlledModule H B := by
  apply BasedComplex.map_mem_of_support (mapChain G f) _ c
  intro s hs
  refine vertexModule_le_controlledModule H (V := f '' vertices G s) ?_
    (mapChain_mem_vertices G f (V := vertices G s) (W := f '' vertices G s)
      (fun x hx => ⟨x,hx,rfl⟩) (FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1))
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  exact hf x y (hc hs x hx y hy)

lemma leftTranslate_mem_controlled (a : G) {A : Set G} {c : Chain G}
    (hc : c ∈ controlledModule G A) :
    mapChain G (fun x => a*x) c ∈ controlledModule G A := by
  apply mapChain_mem_controlled_of_differences G _ _ hc
  intro x y h
  simpa only [mul_inv_rev,mul_assoc,inv_mul_cancel_left] using h

end

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_BinaryPrefixOperators
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ListChains
section

variable (G : Type*) [Group G]

structure IdempotentSplittings (K : Type*) [CommRing K] (f : G →* G) where
  map : BinaryPrefixOperators.idempotents K → (G →* G)
  identity : map ⟨1,BinaryPrefixOperators.identity_mem K⟩ = f
  commute : ∀ E P : BinaryPrefixOperators.idempotents K,
    ∀ _hSum : E.val + P.val ∈ BinaryPrefixOperators.idempotents K,
    E.val * P.val = 0 → P.val * E.val = 0 → ∀ u v, Commute (map E u) (map P v)
  addition : ∀ E P : BinaryPrefixOperators.idempotents K,
    ∀ hSum : E.val + P.val ∈ BinaryPrefixOperators.idempotents K,
    E.val * P.val = 0 → P.val * E.val = 0 →
    ∀ u, map ⟨E.val+P.val,hSum⟩ u = map E u * map P u

end

variable (G : Type*) {H K C D E : Type*}

lemma single_mem_cosetModule (P : Submodule ℤ (Chain G)) (c : C) {z : Chain G}
    (hz : z ∈ P) : Finsupp.single c z ∈ cosetModule G P := by
  classical
  intro d
  by_cases h : c = d
  · subst d; simpa only [Finsupp.single_eq_same] using hz
  · simpa only [Finsupp.single_eq_of_ne (Ne.symm h)] using P.zero_mem

lemma cosetMap_mem (σ : C → D) (ψ : C → G → H)
    (P : Submodule ℤ (Chain G)) (Q : Submodule ℤ (Chain H))
    (hψ : ∀ c z, z ∈ P → mapChain G (ψ c) z ∈ Q)
    {z : C →₀ Chain G} (hz : z ∈ cosetModule G P) :
    cosetMap G σ ψ z ∈ cosetModule H Q := by
  classical
  change (Finsupp.lsum ℤ _) z ∈ _
  rw [Finsupp.lsum_apply]
  apply Submodule.sum_mem
  intro c _
  exact single_mem_cosetModule H Q (σ c) (hψ c (z c) (hz c))

lemma cosetBoundary_cosetMap (σ : C → D) (ψ : C → G → H) (z : C →₀ Chain G) :
    cosetBoundary H (cosetMap G σ ψ z) = cosetMap G σ ψ (cosetBoundary G z) := by
  have h : (cosetBoundary H).comp (cosetMap G σ ψ) =
      (cosetMap G σ ψ).comp (cosetBoundary G) := by
    apply Finsupp.lhom_ext
    intro c z
    simp only [LinearMap.comp_apply,cosetMap_single,cosetBoundary_single,boundary_mapChain]
  exact LinearMap.congr_fun h z

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChainsShiftOrigin
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ListChains
section

variable (G : Type*) [Group G] {C : Type*}

lemma cosetShift_mem_controlled (f : G →* G) (σ : C → C) (δ : C → G)
    {A : Set G} {z : C →₀ Chain G}
    (hz : z ∈ cosetModule G (controlledModule G A)) :
    cosetShift G f σ δ z ∈ cosetModule G (controlledModule G (f '' A)) := by
  apply cosetMap_mem G _ _ _ _ _ hz
  intro c x hx
  have h := leftTranslate_mem_controlled G (δ c) (mapChain_mem_controlled G G f hx)
  simpa only [mapChain_comp,Function.comp_def] using h

lemma cosetShift_mem_degree (f : G →* G) (σ : C → C) (δ : C → G)
    {n : ℕ} {z : C →₀ Chain G} (hz : z ∈ cosetModule G (degreeModule G n)) :
    cosetShift G f σ δ z ∈ cosetModule G (degreeModule G n) :=
  cosetMap_mem G _ _ _ _ (fun _ _ hx => mapChain_mem_degree G _ hx) hz

lemma cosetBoundary_shift (f : G →* G) (σ : C → C) (δ : C → G) (z : C →₀ Chain G) :
    cosetBoundary G (cosetShift G f σ δ z) =
      cosetShift G f σ δ (cosetBoundary G z) :=
  cosetBoundary_cosetMap G _ _ z

end

section

variable (G I C : Type*) [Group G]

lemma productBoundary_shift (f : G →* G) (σ : C → C) (δ : C → G)
    (z : ProductAmbient G I C) :
    productBoundary G I C (productShift G I C f σ δ z) =
      productShift G I C f σ δ (productBoundary G I C z) := by
  funext i
  exact cosetBoundary_shift G f σ δ (z i)

lemma productShift_mem_chains (f : G →* G) (σ : C → C) (δ : C → G)
    {n : ℕ} {z : ProductAmbient G I C} (hz : z ∈ productChains G I C n) :
    productShift G I C f σ δ z ∈ productChains G I C n := by
  obtain ⟨⟨A,hA,hzA⟩,hzd⟩ := hz
  exact ⟨⟨f '' A,hA.image G f,fun i => cosetShift_mem_controlled G f σ δ (hzA i)⟩,
    fun i => cosetShift_mem_degree G f σ δ (hzd i)⟩

def shiftChains (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ) :
    productChains G I C n →ₗ[ℤ] productChains G I C n :=
  (productShift G I C f σ δ).restrict (fun _ hz => productShift_mem_chains G I C f σ δ hz)

end

section

variable (G : Type*) [Group G]

lemma relativeType_mem {s : Simplex G} {A : Set G}
    (hs : hasPropagation G A s) : relativeType G s ∈ simplexTypes G A (degree G s) := by
  refine ⟨relativeType_length G s,?_⟩
  intro x hx
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
  exact hs s.1 (head_mem_vertices G s) y (Or.inr hy)

theorem finite_shapes_bound {T : Set (List G)} (hT : T.Finite) :
    ∃ B : Set G, IsBound G B ∧
      ∀ s : Simplex G, relativeType G s ∈ T → hasPropagation G B s := by
  let V : Set G := insert 1 (⋃ l ∈ T, {x | x ∈ l})
  have hV : V.Finite := (hT.biUnion (fun l _ => List.finite_toSet l)).insert 1
  let B : Set G := (fun p : G × G => p.1⁻¹*p.2) '' (V ×ˢ V)
  have hB : IsBound G B := {
    finite := (hV.prod hV).image _
    one_mem := ⟨(1,1),⟨Set.mem_insert _ _,Set.mem_insert _ _⟩,by simp⟩
    inv_mem := by
      rintro _ ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩
      exact ⟨(y,x),⟨hy,hx⟩,by simp⟩ }
  refine ⟨B,hB,?_⟩
  intro s hs x hx y hy
  have hv (x : G) (hx : x ∈ vertices G s) : s.1⁻¹*x ∈ V := by
    rcases hx with rfl | hx
    · simp [V]
    · apply Set.mem_insert_of_mem
      exact Set.mem_iUnion.mpr ⟨relativeType G s,Set.mem_iUnion.mpr ⟨hs,
        List.mem_map.mpr ⟨x,hx,rfl⟩⟩⟩
  refine ⟨(s.1⁻¹*x,s.1⁻¹*y),⟨hv x hx,hv y hy⟩,?_⟩
  simp [mul_assoc]

end

variable (G C : Type*) [Group G]

lemma shapeCoordinates_support_iff (z : C →₀ Chain G) (T : Set (List G)) :
    (↑(shapeCoordinates G C z).support : Set (List G)) ⊆ T ↔
      ∀ c s, s ∈ (z c).support → relativeType G s ∈ T := by
  constructor
  · intro h c s hs
    apply h
    apply Finsupp.mem_support_iff.mpr
    intro hz
    have he := congrArg (fun a : C × G →₀ ℤ => a (c,s.1)) hz
    rw [shapeCoordinates_at_relative] at he
    exact Finsupp.mem_support_iff.mp hs he
  · intro h l hl
    by_contra hn
    apply Finsupp.mem_support_iff.mp hl
    ext ⟨c,g⟩
    rw [shapeCoordinates_apply]
    apply Finsupp.notMem_support_iff.mp
    intro hs
    have he := h c (g,l.map (fun x => g*x)) hs
    rw [relativeType_translate] at he
    exact hn he

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_UniformProductSupport
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ListChains
section

variable (G I C : Type*) [Group G]

theorem product_chain_realization {n : ℕ} (z : I → C →₀ Chain G)
    (hd : ∀ i c, z i c ∈ degreeModule G n) :
    (∃ c : List G →₀ (I → (C × G →₀ ℤ)),
      ∀ i, UniformProductSupport.evaluate (R := ℤ) (S := List G) (I := I) (M := C × G →₀ ℤ) i c = shapeCoordinates G C (z i)) ↔
    (∃ A : Set G, IsBound G A ∧ ∀ i c, z i c ∈ controlledModule G A) := by
  classical
  rw [UniformProductSupport.exists_lift_iff]
  constructor
  · rintro ⟨T,hT⟩
    obtain ⟨B,hB,h⟩ := finite_shapes_bound G T.finite_toSet
    refine ⟨B,hB,?_⟩
    intro i c s hs
    apply h s
    exact (shapeCoordinates_support_iff G C (z i) (↑T)).mp (hT i) c s hs
  · rintro ⟨A,hA,hz⟩
    let T := (simplexTypes_finite G hA.finite n).toFinset
    refine ⟨T,?_⟩
    intro i
    apply (shapeCoordinates_support_iff G C (z i) (↑T)).mpr
    intro c s hs
    change relativeType G s ∈ (simplexTypes_finite G hA.finite n).toFinset
    rw [Set.Finite.mem_toFinset]
    have h := relativeType_mem G (hz i c hs)
    rwa [hd i c hs] at h

end

variable (G I C : Type*) [Group G]

lemma realizeShapes_injective : Function.Injective (realizeShapes G I C) := by
  intro a b h
  apply UniformProductSupport.evaluate_injective (R := ℤ)
  funext i
  change UniformProductSupport.evaluate (R := ℤ) (S := List G) (M := C × G →₀ ℤ) i a =
    UniformProductSupport.evaluate (R := ℤ) (S := List G) (M := C × G →₀ ℤ) i b
  rw [← shapeCoordinates_realize,← shapeCoordinates_realize]
  exact congrArg (shapeCoordinates G C) (congrFun h i)

lemma realizeShapes_bounded (a : List G →₀ CoefficientProduct G I C) :
    realizeShapes G I C a ∈ boundedProducts G I C := by
  classical
  obtain ⟨B,hB,h⟩ := finite_shapes_bound G a.support.finite_toSet
  refine ⟨B,hB,?_⟩
  intro i c s hs
  apply h s
  apply Finsupp.mem_support_iff.mpr
  intro hz
  apply Finsupp.mem_support_iff.mp hs
  rw [realizeShapes_apply_relative,hz]
  rfl

lemma realizeShapes_degree_iff (n : ℕ) (a : List G →₀ CoefficientProduct G I C) :
    realizeShapes G I C a ∈ degreeProducts G I C n ↔
      a ∈ Finsupp.supported (CoefficientProduct G I C) ℤ {l : List G | l.length = n} := by
  constructor
  · intro h l hl
    by_contra hn
    apply Finsupp.mem_support_iff.mp hl
    ext i ⟨c,g⟩
    rw [← realizeShapes_apply]
    apply Finsupp.notMem_support_iff.mp
    intro hs
    have he := h i c hs
    exact hn (by simpa [degree] using he)
  · intro h i c s hs
    have hn : a (relativeType G s) ≠ 0 := by
      intro hz
      apply Finsupp.mem_support_iff.mp hs
      rw [realizeShapes_apply_relative,hz]
      rfl
    have he := h (Finsupp.mem_support_iff.mpr hn)
    simpa using he

def realizeDegree (n : ℕ) : shapeDomain G I C n →ₗ[ℤ] productChains G I C n :=
  ((realizeShapes G I C).comp (shapeDomain G I C n).subtype).codRestrict _ fun a =>
    ⟨realizeShapes_bounded G I C a.val,(realizeShapes_degree_iff G I C n a.val).mpr a.property⟩

lemma realizeDegree_bijective (n : ℕ) : Function.Bijective (realizeDegree G I C n) := by
  constructor
  · intro a b h
    apply Subtype.ext
    exact realizeShapes_injective G I C (congrArg Subtype.val h)
  · intro z
    obtain ⟨a,ha⟩ := (product_chain_realization G I C z.val (fun i c => z.property.2 i c)).mpr z.property.1
    have he : realizeShapes G I C a = z.val := by
      funext i
      apply (shapeCoordinates G C).injective
      rw [shapeCoordinates_realize,ha i]
    have hd : a ∈ shapeDomain G I C n :=
      (realizeShapes_degree_iff G I C n a).mp (he ▸ z.property.2)
    exact ⟨⟨a,hd⟩,Subtype.ext he⟩

def productShapeEquiv (n : ℕ) : (Shape G n →₀ CoefficientProduct G I C) ≃ₗ[ℤ]
    productChains G I C n :=
  (Finsupp.supportedEquivFinsupp {l : List G | l.length = n}).symm.trans
    (LinearEquiv.ofBijective (realizeDegree G I C n) (realizeDegree_bijective G I C n))

def productTupleEquiv (n : ℕ) : ((Fin n → G) →₀ CoefficientProduct G I C) ≃ₗ[ℤ]
    productChains G I C n :=
  (Finsupp.lcongr (tupleShapeEquiv G n) (LinearEquiv.refl ℤ _)).trans (productShapeEquiv G I C n)

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductCoefficient
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ListChains

section
variable (G I C : Type*) [Group G]

lemma shapeCoordinates_place_one (a : C × G →₀ ℤ) (l : List G) :
    shapeCoordinates G C (place G C a (Finsupp.single (1,l) 1)) = Finsupp.single l a := by
  have h : (shapeCoordinates G C).toLinearMap.comp
      ((place G C).flip (Finsupp.single (1,l) 1)) = Finsupp.lsingle l := by
    apply Finsupp.lhom_ext
    rintro ⟨c,u⟩ r
    simp only [LinearMap.comp_apply,LinearMap.flip_apply,place_single,map_smul,
      mapChain_single]
    simp [relativeType,List.map_map,Finsupp.smul_single]
  exact LinearMap.congr_fun h a

lemma productTupleEquiv_single_val (n : ℕ) (s : Fin n → G)
    (a : CoefficientProduct G I C) :
    (productTupleEquiv G I C n (Finsupp.single s a)).val =
      realizeShapes G I C (Finsupp.single (List.ofFn s) a) := by
  classical
  change realizeShapes G I C
    (((Finsupp.supportedEquivFinsupp (R := ℤ) (M := CoefficientProduct G I C) {l : List G | l.length = n}).symm
      ((Finsupp.lcongr (tupleShapeEquiv G n) (LinearEquiv.refl ℤ _))
        (Finsupp.single s a))).val) = _
  rw [Finsupp.lcongr_single,Finsupp.supportedEquivFinsupp_symm_single]
  rfl

lemma productTupleEquiv_single_place (n : ℕ) (s : Fin n → G)
    (a : CoefficientProduct G I C) (i : I) :
    (productTupleEquiv G I C n (Finsupp.single s a)).val i =
      place G C (a i) (Finsupp.single (1,List.ofFn s) 1) := by
  apply (shapeCoordinates G C).injective
  rw [productTupleEquiv_single_val,shapeCoordinates_realize,shapeCoordinates_place_one]
  simp [UniformProductSupport.evaluate]

end

end ListChains

open _root_.CategoryTheory

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_Representation
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory

namespace ListChains
open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
variable (G I C : Type) [Group G]

def standardProductEquiv (n : ℕ) :
    ((ProductCoefficient.rep G I C) ⊗ Rep.diagonal ℤ G (n+1)).ρ.Coinvariants ≃ₗ[ℤ]
      productChains G I C n :=
  (RelativeStandardFree.coinvariantEquiv ℤ G (ProductCoefficient.rep G I C) n).trans
    (productTupleEquiv G I C n)

@[simp] lemma standardProductEquiv_mk_tmul_single (n : ℕ)
    (a : ProductCoefficient.Module G I C) (s : Fin (n+1) → G) (r : ℤ) (i : I) :
    (standardProductEquiv G I C n
      (Coinvariants.mk _ (a ⊗ₜ[ℤ] MonoidAlgebra.single s r))).val i =
        place G C (a i) (fromTuples G n (Finsupp.single s r)) := by
  change (productTupleEquiv G I C n
    (RelativeStandardFree.coinvariantEquiv ℤ G (ProductCoefficient.rep G I C) n
      (Coinvariants.mk _ (a ⊗ₜ[ℤ] MonoidAlgebra.single s r)))).val i = _
  rw [RelativeStandardFree.coinvariantEquiv_mk_tmul_single,productTupleEquiv_single_place]
  change place G C (r • ProductCoefficient.rightShift G C (s 0)⁻¹ (a i)) _ = _
  rw [map_smul,LinearMap.smul_apply,place_shifted_tuple]
  have hs : Finsupp.single s r = r • Finsupp.single s (1 : ℤ) := by
    simp [Finsupp.smul_single]
  rw [hs,map_smul,map_smul]

lemma standardProductEquiv_mk_tmul (n : ℕ) (a : ProductCoefficient.Module G I C)
    (z : MonoidAlgebra ℤ (Fin (n+1) → G)) (i : I) :
    (standardProductEquiv G I C n (Coinvariants.mk _ (a ⊗ₜ[ℤ] z))).val i =
      place G C (a i) (fromTuples G n (MonoidAlgebra.coeffLinearEquiv ℤ z)) := by
  let L := (LinearMap.proj i).comp ((productChains G I C n).subtype.comp
    ((standardProductEquiv G I C n).toLinearMap.comp
      ((Coinvariants.mk _).comp ((TensorProduct.mk ℤ _ _) a))))
  have h : L = (place G C (a i)).comp
      ((fromTuples G n).comp (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap) := by
    apply MonoidAlgebra.lhom_ext'
    intro s
    apply LinearMap.ext
    intro r
    exact standardProductEquiv_mk_tmul_single G I C n a s r i
  exact LinearMap.congr_fun h z

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChainsFromTuplesCone
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
namespace ListChains
section
variable (G : Type)

lemma fromTuples_cone (a : G) (n : ℕ) (c : ControlledChains.Chain G n) :
    fromTuples G (n+1) (ControlledChains.cone G a n c) = cone G a (fromTuples G n c) := by
  have h : (fromTuples G (n+1)).comp (ControlledChains.cone G a n) =
      (cone G a).comp (fromTuples G n) := by
    apply Finsupp.lhom_ext
    intro s r
    simp only [LinearMap.comp_apply, ControlledChains.cone_single,fromTuples_single,
      Fin.cons_zero,Fin.cons_succ,cone_single,simplexCone,List.ofFn_succ]
  exact LinearMap.congr_fun h c

lemma fromTuples_augmentation_succ (n : ℕ) (c : ControlledChains.Chain G (n+1)) :
    augmentation G (fromTuples G (n+1) c) = 0 := by
  have h : (augmentation G).comp (fromTuples G (n+1)) = 0 := by
    apply Finsupp.lhom_ext
    intro s r
    simp [fromTuples_single,List.ofFn_succ]
  exact LinearMap.congr_fun h c

lemma fromTuples_boundary (n : ℕ) (c : ControlledChains.Chain G (n+1)) :
    fromTuples G n (ControlledChains.boundary G n c) = boundary G (fromTuples G (n+1) c) := by
  induction n with
  | zero =>
    have h : (fromTuples G 0).comp (ControlledChains.boundary G 0) =
        (boundary G).comp (fromTuples G 1) := by
      apply Finsupp.lhom_ext
      intro s r
      simp only [LinearMap.comp_apply]
      rw [tuple_single_as_cone,ControlledChains.boundary_cone_zero,fromTuples_cone,map_sub,
        fromTuples_single,fromTuples_single]
      simp only [List.ofFn_zero,ControlledChains.augmentation_single]
      rw [boundary_cone]
      have hz : boundary G (Finsupp.single (s (Fin.succ 0),[]) r) = 0 := by
        have he : Finsupp.single (s (Fin.succ 0),[]) r = r • vertex G (s (Fin.succ 0)) := by simp [vertex,simplexVertex]
        rw [he,map_smul,boundary_vertex,smul_zero]
      rw [hz,map_zero,sub_zero]
      simp [vertex,simplexVertex,K_apply]
    exact LinearMap.congr_fun h c
  | succ n ih =>
    have h : (fromTuples G (n+1)).comp (ControlledChains.boundary G (n+1)) =
        (boundary G).comp (fromTuples G (n+2)) := by
      apply Finsupp.lhom_ext
      intro s r
      simp only [LinearMap.comp_apply]
      rw [tuple_single_as_cone,fromTuples_cone]
      rw [eq_sub_of_add_eq (ControlledChains.boundary_cone G (s 0) n
        (Finsupp.single (fun i => s i.succ) r))]
      rw [map_sub,fromTuples_cone,ih,boundary_cone,K_apply,fromTuples_augmentation_succ,
        zero_smul,sub_zero]
    exact LinearMap.congr_fun h c

end

section
open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
variable (G I C : Type) [Group G]

def productChainD (n : ℕ) : productChains G I C (n+1) →ₗ[ℤ] productChains G I C n where
  toFun z := ⟨productBoundary G I C z.val,
    productBoundary_mem_bounded G I C z.property.1,
    productBoundary_mem_degree G I C z.property.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

@[simp] lemma productChainD_val (n : ℕ) (z : productChains G I C (n+1)) :
    (productChainD G I C n z).val = productBoundary G I C z.val := rfl

@[simp] lemma productChainD_squared (n : ℕ) (z : productChains G I C (n+2)) :
    productChainD G I C n (productChainD G I C (n+1) z) = 0 := by
  apply Subtype.ext
  exact productBoundary_squared G I C z.val

def boundedProductComplex : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of ℤ (productChains G I C n))
    (fun n => ModuleCat.ofHom (productChainD G I C n)) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact productChainD_squared G I C n)

@[simp] lemma boundedProductComplex_d (n : ℕ) :
    (boundedProductComplex G I C).d (n+1) n = ModuleCat.ofHom (productChainD G I C n) := by
  simp [boundedProductComplex]

abbrev standardProductComplex : ChainComplex (ModuleCat ℤ) ℕ :=
  (Rep.standardComplex ℤ G).coinvariantsTensorObj (ProductCoefficient.rep G I C)

lemma standardProductComplex_d_mk_tmul (n : ℕ)
    (a : ProductCoefficient.Module G I C) (z : MonoidAlgebra ℤ (Fin (n+2) → G)) :
    (standardProductComplex G I C).d (n+1) n
      (Coinvariants.mk _ (a ⊗ₜ[ℤ] z)) =
        Coinvariants.mk _ (a ⊗ₜ[ℤ] (Rep.standardComplex.d ℤ G (n+1) z)) := by
  change Coinvariants.mk _
    (Representation.IntertwiningMap.tensor (Representation.IntertwiningMap.id _)
      ((Rep.standardComplex ℤ G).d (n+1) n).hom (a ⊗ₜ[ℤ] z)) = _
  rw [Representation.IntertwiningMap.tensor_apply]
  simp only [Representation.IntertwiningMap.id_apply, Rep.standardComplex.d_apply]
  rfl

lemma standardProductEquiv_boundary (n : ℕ)
    (z : (standardProductComplex G I C).X (n+1)) :
    standardProductEquiv G I C n ((standardProductComplex G I C).d (n+1) n z) =
      productChainD G I C n (standardProductEquiv G I C (n+1) z) := by
  have h : (standardProductEquiv G I C n).toLinearMap.comp
      ((standardProductComplex G I C).d (n+1) n).hom =
      (productChainD G I C n).comp (standardProductEquiv G I C (n+1)).toLinearMap := by
    apply Coinvariants.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    funext i
    change (standardProductEquiv G I C n
      ((standardProductComplex G I C).d (n+1) n (Coinvariants.mk _ (a ⊗ₜ[ℤ] b)))).val i = _
    rw [standardProductComplex_d_mk_tmul]
    change (standardProductEquiv G I C n
      (Coinvariants.mk ((ProductCoefficient.rep G I C) ⊗ Rep.diagonal ℤ G (n+1)).ρ
        (a ⊗ₜ[ℤ] (Rep.standardComplex.d ℤ G (n+1) b)))).val i =
      cosetBoundary G ((standardProductEquiv G I C (n+1)
        (Coinvariants.mk ((ProductCoefficient.rep G I C) ⊗ Rep.diagonal ℤ G (n+2)).ρ
          (a ⊗ₜ[ℤ] b))).val i)
    rw [standardProductEquiv_mk_tmul]
    change place G C (a i) (fromTuples G n
        (ControlledChains.boundary G n (MonoidAlgebra.coeffLinearEquiv ℤ b))) =
      cosetBoundary G ((standardProductEquiv G I C (n+1)
        (Coinvariants.mk _ (a ⊗ₜ[ℤ] b))).val i)
    rw [standardProductEquiv_mk_tmul,fromTuples_boundary,boundary_place]
  exact LinearMap.congr_fun h z

def standardProductComplexIso :
    standardProductComplex G I C ≅ boundedProductComplex G I C :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => LinearEquiv.toModuleIso (standardProductEquiv G I C n)) (fun i j => by
      rintro (rfl : j+1=i)
      rw [boundedProductComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change productChainD G I C j (standardProductEquiv G I C (j+1) z) =
        standardProductEquiv G I C j ((standardProductComplex G I C).d (j+1) j z)
      exact (standardProductEquiv_boundary G I C j z).symm)

def groupHomologyBoundedIso (n : ℕ) :
    groupHomology (ProductCoefficient.rep G I C) n ≅
      (boundedProductComplex G I C).homology n := by
  classical
  exact groupHomologyIso (ProductCoefficient.rep G I C) n
    (Rep.standardResolution ℤ G) ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
        (standardProductComplexIso G I C)

end

open _root_.CategoryTheory
variable (G I C : Type) [Group G]

def productShortComplex (n : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.moduleCatMk (productChainD G I C (n+1)) (productChainD G I C n)
    (by apply LinearMap.ext; intro z; exact productChainD_squared G I C n z)

def productCycleKernelEquiv (n : ℕ) :
    productCycles G I C (n+1) ≃ₗ[ℤ] LinearMap.ker (productChainD G I C n) where
  toFun z := ⟨⟨z.val,z.property.1⟩,Subtype.ext z.property.2⟩
  invFun z := ⟨z.val.val,z.val.property,congrArg Subtype.val z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def boundedProductScIso (n : ℕ) :
    (boundedProductComplex G I C).sc' (n+2) (n+1) n ≅ productShortComplex G I C n :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      change _ ≫ ModuleCat.ofHom (productChainD G I C (n+1)) =
        (boundedProductComplex G I C).d (n+2) (n+1) ≫ _
      rw [boundedProductComplex_d]
      rfl)
    (by
      change _ ≫ ModuleCat.ofHom (productChainD G I C n) =
        (boundedProductComplex G I C).d (n+1) n ≫ _
      rw [boundedProductComplex_d]
      rfl)

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductCoefficientAffineShift
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory

namespace ListChains
open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
variable (G I C : Type) [Group G]

lemma productChainD_shift (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ)
    (z : productChains G I C (n+1)) :
    productChainD G I C n (shiftChains G I C f σ δ (n+1) z) =
      shiftChains G I C f σ δ n (productChainD G I C n z) := by
  apply Subtype.ext
  exact productBoundary_shift G I C f σ δ z.val

def boundedShiftChainMap (f : G →* G) (σ : C → C) (δ : C → G) :
    boundedProductComplex G I C ⟶ boundedProductComplex G I C :=
  HomologicalComplex.Hom.mk (fun n => ModuleCat.ofHom (shiftChains G I C f σ δ n)) (by
    intro i j h
    obtain rfl : j+1=i := h
    rw [boundedProductComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact productChainD_shift G I C f σ δ j z)

end ListChains

open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CategoryTheoryShortComplex
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
open _root_.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory

open CategoryTheory

namespace ListChains
open CategoryTheory
variable (G I C : Type) [Group G]

def boundedHomologyScIso (n : ℕ) :
    (boundedProductComplex G I C).homology (n+1) ≅
      (productShortComplex G I C n).homology :=
  (HomologicalComplex.homologyFunctorIso' (ModuleCat ℤ) (ComplexShape.down ℕ)
    (n+2) (n+1) n (by simp) (by simp)).app (boundedProductComplex G I C) ≪≫
      ShortComplex.homologyMapIso (boundedProductScIso G I C n)

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_AscendingHNN
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
open _root_.CategoryTheory _root_.OAI.CategoryTheory

namespace ListChains
variable {G H : Type} [Group G] [Group H]
variable {K : Type} [CommRing K] {f : G →* G}

def IdempotentSplittings.conjugate (F : IdempotentSplittings G K f) (e : G ≃* H) :
    IdempotentSplittings H K ((e.toMonoidHom.comp f).comp e.symm.toMonoidHom) where
  map E := (e.toMonoidHom.comp (F.map E)).comp e.symm.toMonoidHom
  identity := by rw [F.identity]
  commute E P hsum hEP hPE u v :=
    (F.commute E P hsum hEP hPE (e.symm u) (e.symm v)).map e.toMonoidHom
  addition E P hsum hEP hPE u := by
    change e (F.map ⟨_,hsum⟩ (e.symm u)) = _
    rw [F.addition E P hsum hEP hPE,map_mul]
    rfl

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ClassifyingSpacesFiniteExtensionGeometricFromProducts
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Pointwise

namespace NoncommElementary
variable {R n : Type*} [Ring R] [Fintype n] [DecidableEq n]

def swapWord (i j : n) (h : i≠j) (u : Rˣ) : (Matrix n n R)ˣ :=
  root i j h u.val*root j i h.symm (-u.inv)*root i j h u.val

lemma swapWord_val (i j : n) (h : i≠j) (u : Rˣ) :
    (swapWord i j h u).val=1-Matrix.single i i 1-Matrix.single j j 1+
      Matrix.single i j u.val-Matrix.single j i u.inv := by
  simp only [swapWord,Units.val_mul,root_val]
  simp [mul_add,add_mul,Matrix.single_mul_single_of_ne _ _ _ _ h.symm,Matrix.single_mul_single_same,
    ← Matrix.single_neg]
  abel

end NoncommElementary

open scoped commutatorElement

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_InducedFree
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation

namespace OrbitModule
open scoped MonoidalCategory
attribute [instance] Presentation.finiteα Presentation.finiteβ Presentation.epi

end OrbitModule

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

namespace ListChains
variable (G I C : Type) [groupG : Group G]
def flattenProduct (z : ProductAmbient G I C) : ProductAmbient G (I×C) PUnit.{1} :=
  fun ic => Finsupp.single PUnit.unit (z ic.1 ic.2)

def gatherProduct (T : I → Finset C) (z : ProductAmbient G (I×C) PUnit.{1}) :
    ProductAmbient G I C := fun i => ∑ c ∈ T i, Finsupp.single c (z (i,c) PUnit.unit)
end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SteinbergFinitePresentation
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise

namespace HNNSubgroup
open AscendingHNN
variable {U : Type*} [Group U] (f : U →* U) (hf : Function.Injective f)
variable (K : Subgroup (Torus f hf)) (ht : AscendingHNN.stable f hf ∈ K)

abbrev base : Subgroup U := K.comap (embed f hf)

include ht in
lemma base_invariant {u : U} (hu : u ∈ base f hf K) : f u ∈ base f hf K := by
  change embed f hf (f u) ∈ K
  have he : embed f hf (f u) = (stable f hf)⁻¹ * embed f hf u * stable f hf := by
    rw [mul_assoc,embed_mul_stable]
    group
  rw [he]
  exact K.mul_mem (K.mul_mem (K.inv_mem ht) hu) ht

def baseMap : base f hf K →* base f hf K where
  toFun u := ⟨f u,base_invariant f hf K ht u.property⟩
  map_one' := Subtype.ext f.map_one
  map_mul' u v := Subtype.ext (f.map_mul u v)

lemma baseMap_injective : Function.Injective (baseMap f hf K ht) := by
  intro u v huv
  exact Subtype.ext (hf (congrArg Subtype.val huv))

def inclusion : base f hf K →* K where
  toFun u := ⟨embed f hf u,u.property⟩
  map_one' := Subtype.ext ((embed f hf).map_one)
  map_mul' u v := Subtype.ext ((embed f hf).map_mul u.val v.val)

def stableElement : K := ⟨AscendingHNN.stable f hf,ht⟩

lemma inclusion_relation (u : base f hf K) :
    inclusion f hf K u * stableElement f hf K ht =
      stableElement f hf K ht * inclusion f hf K (baseMap f hf K ht u) :=
  Subtype.ext (embed_mul_stable f hf u)

def hom : Torus (baseMap f hf K ht) (baseMap_injective f hf K ht) →* K :=
  evaluation (baseMap f hf K ht) (baseMap_injective f hf K ht)
    (inclusion f hf K) (stableElement f hf K ht) (inclusion_relation f hf K ht)

lemma hom_injective : Function.Injective (hom f hf K ht) := by
  apply evaluation_injective (β := (heightHom f hf).comp K.subtype)
  · intro u v huv
    exact Subtype.ext (embed_injective f hf (congrArg Subtype.val huv))
  · intro u
    apply Multiplicative.toAdd.injective
    exact height_embed f hf u
  · apply Multiplicative.toAdd.injective
    exact height_stable f hf

lemma hom_surjective : Function.Surjective (hom f hf K ht) := by
  apply evaluation_surjective
  intro g
  obtain ⟨a,b,u,hu⟩ := normal_form f hf g.val
  have hm : u ∈ base f hf K := by
    change embed f hf u ∈ K
    have he : embed f hf u = ((AscendingHNN.stable f hf)^a)⁻¹ * g.val *
        (AscendingHNN.stable f hf)^b := by rw [hu]; group
    rw [he]
    exact K.mul_mem (K.mul_mem (K.inv_mem (K.pow_mem ht a)) g.property) (K.pow_mem ht b)
  exact ⟨a,b,⟨u,hm⟩,Subtype.ext hu⟩

def equiv : Torus (baseMap f hf K ht) (baseMap_injective f hf K ht) ≃* K :=
  MulEquiv.ofBijective (hom f hf K ht) ⟨hom_injective f hf K ht,hom_surjective f hf K ht⟩

end HNNSubgroup

end

end OAI
end


