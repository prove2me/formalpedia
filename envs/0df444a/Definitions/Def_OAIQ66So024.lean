-- Prove2me | Definitions.Def_OAIQ66So024
-- name    : OAIQ66So024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:30:53.870995+00:00
-- url     : https://prove2.me/theorems/8fb11911-44d5-4739-b61e-b348bdb1245c
-- title:
--   Definitions bundle OAIQ66So024 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 256 declarations of OpenAI's Lean: 65 definitions, 1 inductive type or structure, 1 instance and 189 theorems. The definitions and types are `OAI.CWEquivariant.wholeRep`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform.componentList`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform.representative`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Surface.Uniform.internalPreprocess`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Surface.Uniform.preprocess`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Word.Uniform.partialNormal`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Word.Uniform.preprocess`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Word.Uniform.sectorPreprocess`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Word.headMap`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Word.letterMap`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Word.partialNormal`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode.codedNormal`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode.codedRepresentative`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode.finiteOrder`, `OAI.FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode.letters`, `OAI.FixedSingularTightening.System`, `OAI.FixedSingularTightening.base`, `OAI.FixedSingularTightening.baseHom`, `OAI.FixedSingularTightening.boundaryHom`, `OAI.FixedSingularTightening.extend`, `OAI.FixedSingularTightening.extendHom`, `OAI.FixedSingularTightening.hom`, `OAI.FixedSingularTightening.next`, `OAI.FixedSingularTightening.system`, `OAI.HurewiczConstruction.homologyModule`, `OAI.HurewiczConstruction.homologyRep`, `OAI.HurewiczConstruction.sphereModuleClass`, `OAI.HurewiczInverse.A`, `OAI.HurewiczInverse.chainValue`, `OAI.HurewiczInverse.coherent`, `OAI.HurewiczInverse.inverse`, `OAI.HurewiczInverse.normalize`, `OAI.HurewiczNormalized.normalizedSimplex`, `OAI.PresentationGeometry.AttachingLoops.boundaryCircle`, `OAI.PresentationGeometry.AttachingLoops.liftedRelatorsOnCircle`, `OAI.PresentationGeometry.Rose.coverSet`, `OAI.PresentationGeometry.Rose.coveringCore`, `OAI.PresentationGeometry.Rose.edgeData`, `OAI.PresentationGeometry.Rose.edgeFirst`, `OAI.PresentationGeometry.Rose.edgeInterval` and 26 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `BooneHigman_MonoidAlgebras`, `FiniteCompiler_Effectivity`, `FiniteCompiler_Normalization`, `FiniteCompiler_SelfReference`, `FiniteCompiler_UniformControl`, `FiniteCompiler_UniformPaths`, `FiniteType_BasedHorn`, `FiniteType_BoundaryValueBoundarySplit`, `FiniteType_CoreDeck`, `FiniteType_HurewiczInverse`, `FiniteType_PartialResolutionPartialCyclesFg`, `FiniteType_PresentationGeometryDescend`, `FiniteType_PresentationGeometryRose`, `FiniteType_PresentationVanKampenRectanglePaths`, `FiniteType_SimplexHomotopy`, `FiniteType_SingularAction`, `FiniteType_SingularPrism`, `FiniteType_SingularSphereCycle`.
--
--   **Imports.** It imports the bundles `OAIQ66So017`, `OAIQ66So018` and `OAIQ66So019` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So027` and `OAIQ66So028`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So017
import Definitions.Def_OAIQ66So018
import Definitions.Def_OAIQ66So019

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Normalization
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path.instPrimcodableLetter _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path.instPrimcodableShape _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableBaseOfFintype _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableHeadOfFintype _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableHeadOfFintype_1 _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableTagOfFintype _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
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
open _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path
variable {S Γ Q : Type*}

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

 theorem ordinary_length {u v : List (Letter S Γ Q)} (h : Ordinary A M u v) :
    u.length ≤ 4 ∧ v.length ≤ 4 := by
  cases h with
  | internal h => obtain ⟨h₁,h₂⟩ := Scan.Literal.rule_length _ _ h; omega
  | clean c => cases he : Cleanup.emit c <;> simp
  | raw => simp
  | merge => simp
  | quota => simp
  | entry => simp
  | finish => simp

 theorem rule_length {u v : List (Letter S Γ Q)} (h : Rule A M u v) :
    u.length ≤ 4 ∧ v.length ≤ 4 := by
  cases h with
  | ordinary h => exact ordinary_length A M h
  | zero h => cases h; simp
  | exit => simp

/-- The source presentation is finite, not a schema depending on arbitrary
    sector contexts. Every defining side has at most four letters. -/
theorem rules_finite [Fintype S] [Fintype Γ] [Fintype Q] :
    {p : List (Letter S Γ Q) × List (Letter S Γ Q) | Rule A M p.1 p.2}.Finite := by
  apply ((List.finite_length_le (Letter S Γ Q) 4).prod
    (List.finite_length_le (Letter S Γ Q) 4)).subset
  rintro ⟨u,v⟩ h
  exact rule_length A M h

end

end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.Compiler.Word
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

theorem normal_grade {f : List S → List S} {m : ℕ} (h : RawRuns.Budget f m)
    (w : List (Letter S Γ Q)) (hm : grade w ≤ m) : grade (normal A M f w) ≤ grade w := by
  unfold normal
  split
  · simp [grade,Path.grade,Path.letterGrade]
  · rw [realizeList_grade]
    have hp := preprocess_grade A M w
    have hm' : RawRuns.grade grade ((preprocess A M w).map (classify A.blank)) ≤ m := by
      rw [classify_grade]; exact hp.trans hm
    exact (RawRuns.source_grade grade h _ hm').trans (by simpa using hp)

end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.Compiler.Word
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- The manuscript's partial normalizer. It is defined even for a divergent
    program; no arbitrary value is inserted for an undefined call. -/
def partialNormal (f : List S → Part (List S)) (w : List (Letter S Γ Q)) : Part (List (Letter S Γ Q)) :=
  if Path.shape w = .zero then Part.some [.zero] else
    (RawRuns.partialSource f ((preprocess A M w).map (classify A.blank))).map
      (List.flatMap (realize A.blank))

/-- Agreement only needs the values below the *input's* additive grade. -/
theorem partialNormal_total_mem {f : List S → Part (List S)} {t : List S → List S}
    (w : List (Letter S Γ Q)) (h : ∀ x, x.length ≤ grade w → t x ∈ f x) :
    normal A M t w ∈ partialNormal A M f w := by
  unfold normal partialNormal
  split
  · exact Part.mem_some _
  · apply (Part.mem_map_iff _).mpr
    refine ⟨_,RawRuns.partialSource_total_mem grade _ ?_,rfl⟩
    intro x hx
    apply h x
    apply hx.trans
    rw [classify_grade]
    exact preprocess_grade A M w

end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.Compiler.Word
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

theorem partialNormal_eq_some {f : List S → Part (List S)} {m : ℕ} (h : PartialBudget f m)
    (w : List (Letter S Γ Q)) (hw : grade w ≤ m) :
    partialNormal A M f w = Part.some (normal A M (fun x => partValue (f x)) w) := by
  apply Part.eq_some_iff.mpr
  exact partialNormal_total_mem A M w (fun x hx => partValue_mem (h.total x (hx.trans hw)))

end FiniteAlgebraicEnvelopes.Compiler.Word

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

theorem Sector.primrec_mk {α : Type*} [Primcodable α]
    {l r : α → List (B×T)} {q : α → H} {a b : α → Bool}
    (hl : Primrec l) (hq : Primrec q) (hr : Primrec r) (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => (⟨l x,q x,r x,a x,b x⟩ : Sector H B T)) :=
  Sector.primrec_decode.comp (hl.pair (hq.pair (hr.pair (ha.pair hb))))

theorem primrec_baseSkeleton : Primrec (baseSkeleton (H := H) (B := B) (T := T)) :=
  (Primrec.list_map
    (Primrec.list_append.comp (Primrec.list_reverse.comp Sector.primrec_left) Sector.primrec_right)
    (Primrec.fst.comp Primrec.snd).to₂).pair (Sector.primrec_lb.pair Sector.primrec_rb)

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open Relation
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {H B T : Type*}

variable [Primcodable H] [Primcodable B] [Primcodable T]

 theorem primrec_flip : Primrec (flip (H := H) (B := B) (T := T)) :=
  Sector.primrec_mk Sector.primrec_right Sector.primrec_head Sector.primrec_left
    Sector.primrec_rb Sector.primrec_lb

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler
open FiniteAlgebraicEnvelopes.Effect

namespace Scan
variable {H H' B T : Type*} [Primcodable H] [Primcodable H'] [Primcodable B] [Primcodable T]
 theorem primrec_mapHead {f : H → H'} (hf : Primrec f) : Primrec (mapHead (B := B) (T := T) f) :=
  Sector.primrec_mk Sector.primrec_left (hf.comp Sector.primrec_head) Sector.primrec_right
    Sector.primrec_lb Sector.primrec_rb
end Scan

end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
variable {H K B T : Type*} [Primcodable H] [Primcodable K] [Primcodable B] [Primcodable T]
 theorem primrec_literal {m : H → K} (hm : Primrec m) : Primrec (literal (B := B) (T := T) m) :=
  Path.Sector.primrec_mk Sector.primrec_left (hm.comp Sector.primrec_head) Sector.primrec_right
    Sector.primrec_lb Sector.primrec_rb
 theorem primrec_unliteral : Primrec (unliteral (H := H) (B := B) (T := T)) :=
  Sector.primrec_mk Path.Sector.primrec_left Path.Sector.primrec_head Path.Sector.primrec_right
    Path.Sector.primrec_lb Path.Sector.primrec_rb
end FiniteAlgebraicEnvelopes.Compiler.Scan

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

namespace FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {P H B T : Type*} [Primcodable P] [Primcodable H] [Primcodable B] [Primcodable T]
variable (table : P → Table H B T)
variable (hb : Primrec (fun x : P × H => (table x.1).boundary x.2))
variable (hc : Primrec (fun x : P × H × B × T => (table x.1).cell x.2.1 x.2.2.1 x.2.2.2))
variable (hd : Primrec (fun x : P × H => decide ((table x.1).direction x.2 = .right)))

include hb hc in
theorem primrec_rightStep : Primrec (fun x : P × Sector H B T => rightStep (table x.1) x.2) := by
  let X := P × Sector H B T
  have hv : Primrec (fun x : X => x.2) := Primrec.snd
  have hl := Sector.primrec_left.comp hv
  have hh := Sector.primrec_head.comp hv
  have hr := Sector.primrec_right.comp hv
  have hla := Sector.primrec_lb.comp hv
  have hra := Sector.primrec_rb.comp hv
  have hnil : Primrec (fun x : X => if x.2.rightBoundary then
      ((table x.1).boundary x.2.head).map (fun q => {x.2 with head := q}) else none) := by
    simp only [← Bool.cond_eq_ite]
    apply Primrec.cond hra
    · apply Primrec.option_map (hb.comp (Primrec.fst.pair hh))
      exact (Sector.primrec_mk (hl.comp Primrec.fst) Primrec.snd (hr.comp Primrec.fst)
        (hla.comp Primrec.fst) (hra.comp Primrec.fst)).to₂
    · exact Primrec.const none
  have hcons : Primrec₂ (fun (x : X) (p : (B×T) × List (B×T)) =>
      ((table x.1).cell x.2.head p.1.1 p.1.2).map fun a =>
        if a.cross then {x.2 with left := (p.1.1,a.tag)::x.2.left,head := a.head,right := p.2}
        else {x.2 with head := a.head,right := (p.1.1,a.tag)::p.2}) := by
    unfold Primrec₂
    apply Primrec.option_map (hc.comp
      ((Primrec.fst.comp Primrec.fst).pair ((hh.comp Primrec.fst).pair
        ((Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))))
    unfold Primrec₂
    let Y := (X × ((B×T) × List (B×T))) × Instruction H T
    have hx : Primrec (fun y : Y => y.1.1) := Primrec.fst.comp Primrec.fst
    have hp : Primrec (fun y : Y => y.1.2) := Primrec.snd.comp Primrec.fst
    have hi : Primrec (fun y : Y => y.2) := Primrec.snd
    have hcell : Primrec (fun y : Y => (y.1.2.1.1,y.2.tag)) :=
      (Primrec.fst.comp (Primrec.fst.comp hp)).pair (Instruction.primrec_tag.comp hi)
    simp only [← Bool.cond_eq_ite]
    apply Primrec.cond (Instruction.primrec_cross.comp hi)
    · exact Sector.primrec_mk (Primrec.list_cons.comp hcell (hl.comp hx))
        (Instruction.primrec_head.comp hi) (Primrec.snd.comp hp) (hla.comp hx) (hra.comp hx)
    · exact Sector.primrec_mk (hl.comp hx) (Instruction.primrec_head.comp hi)
        (Primrec.list_cons.comp hcell (Primrec.snd.comp hp)) (hla.comp hx) (hra.comp hx)
  exact (Primrec.list_casesOn hr hnil hcons).of_eq fun x => by
    cases h : x.2.right with
    | nil => simp [rightStep,h]
    | cons a l => cases a; simp [rightStep,h]

include hb hc hd in
theorem primrec_step : Primrec (fun x : P × Sector H B T => step (table x.1) x.2) := by
  have hr := primrec_rightStep table hb hc
  exact (Primrec.cond (hd.comp (Primrec.fst.pair (Sector.primrec_head.comp Primrec.snd)))
    hr (Primrec.option_map (hr.comp (Primrec.fst.pair (Scan.primrec_flip.comp Primrec.snd)))
      (Scan.primrec_flip.comp Primrec.snd).to₂)).of_eq fun x => by
        simpa only [Bool.cond_decide] using (step_rightStep (table x.1) x.2).symm

variable [Fintype B] [Fintype T]
theorem primrec_sectorList : Primrec (fun x : List H × ℕ => sectorList (B := B) (T := T) x.1 x.2) := by
  apply Primrec.list_flatMap Primrec.fst
  unfold Primrec₂
  apply Primrec.list_flatMap (primrec_wordList.comp (Primrec.snd.comp Primrec.fst))
  unfold Primrec₂
  apply Primrec.list_flatMap (primrec_wordList.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  unfold Primrec₂
  have hm (a b : Bool) : Primrec (fun p : (((List H × ℕ) × H) × List (B×T)) × List (B×T) =>
      (⟨p.1.2,p.1.1.2,p.2,a,b⟩ : Sector H B T)) :=
    Sector.primrec_mk (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
      (Primrec.const a) (Primrec.const b)
  exact Primrec.list_cons.comp (hm false false) (Primrec.list_cons.comp (hm false true)
    (Primrec.list_cons.comp (hm true false) (Primrec.list_cons.comp (hm true true) (Primrec.const []))))

variable [DecidableEq H] [DecidableEq B] [DecidableEq T]

omit [DecidableEq H] [DecidableEq T] in
theorem primrec_universeList :
    Primrec (fun x : List H × Sector H B T => universeList x.1 x.2) := by
  apply primrec_listFilter (primrec_sectorList.comp (Primrec.fst.pair
    (Primrec.nat_add.comp (Primrec.list_length.comp (Sector.primrec_left.comp Primrec.snd))
      (Primrec.list_length.comp (Sector.primrec_right.comp Primrec.snd)))))
  exact (Primrec.eq.decide.comp (primrec_baseSkeleton.comp Primrec.snd)
    (primrec_baseSkeleton.comp (Primrec.snd.comp Primrec.fst))).to₂

noncomputable def componentList (support : P → List H) (x : P × Sector H B T) : List (Sector H B T) :=
  FiniteAlgebraicEnvelopes.Effect.Graph.component (fun a b => decide (step (table x.1) a=some b)) (universeList (support x.1) x.2) x.2

include hb hc hd in
theorem primrec_componentList {support : P → List H} (hs : Primrec support) :
    Primrec (componentList table support) := by
  have he : Primrec (fun x : P × Sector H B T × Sector H B T =>
      decide (step (table x.1) x.2.1=some x.2.2)) :=
    Primrec.eq.decide.comp ((primrec_step table hb hc hd).comp
      (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
      (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd))
  exact (primrec_component_family (r := fun p a b => decide (step (table p) a=some b)) he).comp (Primrec.fst.pair
    ((primrec_universeList.comp ((hs.comp Primrec.fst).pair Primrec.snd)).pair Primrec.snd))

end FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open Simulator
open scoped HeadCodec
variable {S Γ Q Q' P : Type*}

variable [Fintype S] [Primcodable P] [Primcodable Q] [Primcodable Q']
theorem primrec_stateMap {f : P → Q → Q'} (hf : Primrec (fun x : P × Q => f x.1 x.2)) :
    Primrec (fun x : P × Simulator.Head S Q => stateMap (f x.1) x.2) := by
  exact (Primrec.sumCasesOn (primrec_simCode.comp Primrec.snd)
    (primrec_ofStatic.comp Primrec.snd).to₂
    (primrec_dynamic.comp ((Primrec.fst.comp Primrec.snd).pair
      (hf.comp ((Primrec.fst.comp Primrec.fst).pair (Primrec.snd.comp Primrec.snd))))).to₂).of_eq
        (fun x => by cases x.2 <;> rfl)

theorem primrec_controlMap {f : P → Q → Q'} (hf : Primrec (fun x : P × Q => f x.1 x.2)) :
    Primrec (fun x : P × Control.Head S Q => controlMap (f x.1) x.2) := by
  exact (Primrec.sumCasesOn (primrec_controlCode.comp Primrec.snd)
    (primrec_controlDecode.comp (Primrec.sumInl.comp Primrec.snd)).to₂
    (primrec_machine.comp ((primrec_stateMap hf).comp
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))).to₂).of_eq
        (fun x => by cases x.2 <;> rfl)

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open Simulator
open scoped HeadCodec
variable {S Γ Q P : Type*} [Fintype S] [Fintype Γ] [DecidableEq S] [DecidableEq Γ]
  [Primcodable Γ] [Primcodable Q] [Primcodable P]
variable (A : Alphabet S Γ) (M : P → Machine Q Γ)
  (hinit : Primrec (fun p => (M p).initial))
  (htrans : Primrec (fun x : P × Q × Γ => (M x.1).transition x.2.1 x.2.2))

include hinit in
omit [DecidableEq S] [Primcodable Γ] in
theorem primrec_staticCell : Primrec (fun x : P × Static S × Base S × Tag S Γ =>
    cell A (M x.1) (ofStatic x.2.1) x.2.2.1 x.2.2.2) := by
  have hc : Primrec (fun x : P × Static S × Base S × Tag S Γ =>
      cell A dummy (ofStatic x.2.1) x.2.2.1 x.2.2.2) :=
    (Primrec.dom_finite (fun y : Static S × Base S × Tag S Γ =>
      cell A dummy (ofStatic y.1) y.2.1 y.2.2)).comp Primrec.snd
  have hp := primrec_stateMap (S := S) (P := P) (Q := Unit) (Q' := Q)
    (f := fun p (_ : Unit) => (M p).initial) (hinit.comp Primrec.fst)
  have hs : Primrec₂ (fun (x : P × Static S × Base S × Tag S Γ)
      (c : Instruction (Simulator.Head S Unit) (Tag S Γ)) =>
      Scan.mapInstruction (stateMap (fun _ : Unit => (M x.1).initial)) c) :=
    (primrec_instruction (hp.comp ((Primrec.fst.comp Primrec.fst).pair
      (Instruction.primrec_head.comp Primrec.snd)))
      (Instruction.primrec_tag.comp Primrec.snd) (Instruction.primrec_cross.comp Primrec.snd)).to₂
  exact (Primrec.option_map hc hs).of_eq fun x => (static_cell A M x.1 x.2.1 x.2.2.1 x.2.2.2).symm

include hinit htrans in
theorem primrec_simCell : Primrec (fun x : P × Simulator.Head S Q × Base S × Tag S Γ =>
    (Simulator.table A (M x.1)).cell x.2.1 x.2.2.1 x.2.2.2) := by
  let X := P × Simulator.Head S Q × Base S × Tag S Γ
  have hp : Primrec (fun x : X => x.1) := Primrec.fst
  have hbt : Primrec (fun x : X => x.2.2) := Primrec.snd.comp Primrec.snd
  have hs : Primrec₂ (fun (x : X) (s : Static S) => cell A (M x.1) (ofStatic s) x.2.2.1 x.2.2.2) :=
    ((primrec_staticCell A M hinit).comp
      ((hp.comp Primrec.fst).pair (Primrec.snd.pair (hbt.comp Primrec.fst)))).to₂
  have hd : Primrec₂ (fun (x : X) (d : Bool × Q) => cell A (M x.1) (dynamic d) x.2.2.1 x.2.2.2) := by
    unfold Primrec₂
    exact (Primrec.cond (Primrec.fst.comp Primrec.snd)
      ((primrec_leftCell A M).comp ((hp.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.snd).pair (hbt.comp Primrec.fst))))
      ((primrec_runCell A M htrans).comp ((hp.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.snd).pair (hbt.comp Primrec.fst))))).of_eq fun x => by
          cases h : x.2.1 <;> simp [dynamic,h]
  exact (Primrec.sumCasesOn (primrec_simCode.comp (Primrec.fst.comp Primrec.snd)) hs hd).of_eq
    fun x => by cases x.2.1 <;> rfl

omit [Fintype Γ] [DecidableEq S] [Primcodable Γ] in
theorem primrec_simBoundary : Primrec (fun x : P × Simulator.Head S Q =>
    (Simulator.table A (M x.1)).boundary x.2) := by
  have hs : Primrec₂ (fun (_ : P × Simulator.Head S Q) (s : Static S) =>
      (staticBoundary s).map (ofStatic (Q := Q))) :=
    (Primrec.option_map ((Primrec.dom_finite (staticBoundary (S := S))).comp Primrec.snd)
      (primrec_ofStatic.comp Primrec.snd).to₂).to₂
  exact (Primrec.sumCasesOn (primrec_simCode.comp Primrec.snd) hs (Primrec.const none).to₂).of_eq
    fun x => by
      cases x.2 <;> simp [simCode,table,staticBoundary,ofStatic]
      rename_i r; cases r <;> rfl

omit [Fintype Γ] [DecidableEq S] [Primcodable Γ] in
theorem primrec_simDirection : Primrec (fun x : P × Simulator.Head S Q =>
    decide ((Simulator.table A (M x.1)).direction x.2 = .right)) := by
  have hs : Primrec₂ (fun (_ : P × Simulator.Head S Q) (s : Static S) =>
      decide ((Simulator.table A dummy).direction (ofStatic s) = .right)) :=
    ((Primrec.dom_finite (fun s : Static S =>
      decide ((Simulator.table A dummy).direction (ofStatic s) = .right))).comp Primrec.snd).to₂
  exact (Primrec.sumCasesOn (primrec_simCode.comp Primrec.snd) hs
    (Primrec.not.comp (Primrec.fst.comp Primrec.snd)).to₂).of_eq
      fun x => by cases x.2 <;> rfl

include hinit in
omit [Primcodable Γ] in
theorem primrec_controlStaticCell : Primrec (fun x : P × Fin 5 × Base S × Tag S Γ =>
    (Control.table A (M x.1)).cell (staticControl x.2.1) x.2.2.1 x.2.2.2) := by
  have hc : Primrec (fun x : P × Fin 5 × Base S × Tag S Γ =>
      (Control.table A dummy).cell (staticControl x.2.1) x.2.2.1 x.2.2.2) :=
    (Primrec.dom_finite (fun y : Fin 5 × Base S × Tag S Γ =>
      (Control.table A dummy).cell (staticControl y.1) y.2.1 y.2.2)).comp Primrec.snd
  have hp := primrec_controlMap (S := S) (P := P) (Q := Unit) (Q' := Q)
    (f := fun p (_ : Unit) => (M p).initial) (hinit.comp Primrec.fst)
  have hs : Primrec₂ (fun (x : P × Fin 5 × Base S × Tag S Γ)
      (c : Instruction (Control.Head S Unit) (Tag S Γ)) =>
      Scan.mapInstruction (controlMap (fun _ : Unit => (M x.1).initial)) c) :=
    (primrec_instruction (hp.comp ((Primrec.fst.comp Primrec.fst).pair
      (Instruction.primrec_head.comp Primrec.snd)))
      (Instruction.primrec_tag.comp Primrec.snd) (Instruction.primrec_cross.comp Primrec.snd)).to₂
  exact (Primrec.option_map hc hs).of_eq fun x => (staticControl_cell A M x.1 x.2.1 x.2.2.1 x.2.2.2).symm

include hinit htrans in
theorem primrec_controlCell : Primrec (fun x : P × Control.Head S Q × Base S × Tag S Γ =>
    (Control.table A (M x.1)).cell x.2.1 x.2.2.1 x.2.2.2) := by
  let X := P × Control.Head S Q × Base S × Tag S Γ
  have hp : Primrec (fun x : X => x.1) := Primrec.fst
  have hbt : Primrec (fun x : X => x.2.2) := Primrec.snd.comp Primrec.snd
  have hs := ((primrec_controlStaticCell A M hinit).comp
    ((hp.comp Primrec.fst).pair (Primrec.snd.pair (hbt.comp Primrec.fst)))).to₂
  have hd : Primrec₂ (fun (x : X) (q : Simulator.Head S Q) =>
      ((Simulator.table A (M x.1)).cell q x.2.2.1 x.2.2.2).map
        (Scan.mapInstruction Control.Head.machine)) := by
    unfold Primrec₂
    apply Primrec.option_map ((primrec_simCell A M hinit htrans).comp
      ((hp.comp Primrec.fst).pair (Primrec.snd.pair (hbt.comp Primrec.fst))))
    exact (primrec_instruction (primrec_machine.comp (Instruction.primrec_head.comp Primrec.snd))
      (Instruction.primrec_tag.comp Primrec.snd) (Instruction.primrec_cross.comp Primrec.snd)).to₂
  exact (Primrec.sumCasesOn (primrec_controlCode.comp (Primrec.fst.comp Primrec.snd)) hs hd).of_eq
    fun x => by cases x.2.1 <;> rfl

include hinit in
omit [Fintype Γ] [Primcodable Γ] in
theorem primrec_controlBoundary : Primrec (fun x : P × Control.Head S Q =>
    (Control.table A (M x.1)).boundary x.2) := by
  have hp := primrec_controlMap (S := S) (P := P) (Q := Unit) (Q' := Q)
    (f := fun p (_ : Unit) => (M p).initial) (hinit.comp Primrec.fst)
  have hs : Primrec₂ (fun (x : P × Control.Head S Q) (k : Fin 5) =>
      (Control.table A (M x.1)).boundary (staticControl k)) := by
    unfold Primrec₂
    exact (Primrec.option_map
      ((Primrec.dom_finite (fun k : Fin 5 => (Control.table A dummy).boundary (staticControl k))).comp Primrec.snd)
      (hp.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)).to₂).of_eq
        fun x => (staticControl_boundary A M x.1.1 x.2).symm
  have hd : Primrec₂ (fun (x : P × Control.Head S Q) (q : Simulator.Head S Q) =>
      ((Simulator.table A (M x.1)).boundary q).map Control.Head.machine) :=
    (Primrec.option_map ((primrec_simBoundary A M).comp
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))
        (primrec_machine.comp Primrec.snd).to₂).to₂
  exact (Primrec.sumCasesOn (primrec_controlCode.comp Primrec.snd) hs hd).of_eq
    fun x => by cases x.2 <;> rfl

omit [Fintype Γ] [Primcodable Γ] in
theorem primrec_controlDirection : Primrec (fun x : P × Control.Head S Q =>
    decide ((Control.table A (M x.1)).direction x.2 = .right)) := by
  have hs : Primrec₂ (fun (_ : P × Control.Head S Q) (k : Fin 5) =>
      decide ((Control.table A dummy).direction (staticControl k) = .right)) :=
    ((Primrec.dom_finite (fun k : Fin 5 =>
      decide ((Control.table A dummy).direction (staticControl k) = .right))).comp Primrec.snd).to₂
  exact (Primrec.sumCasesOn (primrec_controlCode.comp Primrec.snd) hs
    ((primrec_simDirection A M).comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂).of_eq
      fun x => by cases x.2 <;> rfl

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

namespace FiniteAlgebraicEnvelopes.Compiler
open FiniteAlgebraicEnvelopes.Effect
namespace Surface.Uniform
open Surface HeadCodec
open scoped HeadCodec
open Scan
variable {S Γ H : Type*} [Fintype S] [Fintype Γ] [Primcodable H]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq H] (blank : Γ)

omit [Fintype S] [Fintype Γ] [Primcodable H] [DecidableEq H] in
 theorem rawSweep_takeDrop (l r : Cells S Γ) (lb rb : Bool) :
    rawSweep (H := H) blank l r lb rb =
      ⟨l.dropWhile (cleanAnchor blank),.raw,
        (l.takeWhile (cleanAnchor blank)).reverse ++ r,lb,rb⟩ := by
  induction l generalizing r with
  | nil => rfl
  | cons c l ih =>
    rcases c with ⟨b,t⟩
    cases b with
    | anchor a =>
      by_cases h : t = clean blank
      · simp [rawSweep,h,cleanAnchor,ih,List.reverse_cons,List.append_assoc]
      · simp [rawSweep,h,cleanAnchor]
    | cutC | cutD | workspace => simp [rawSweep,cleanAnchor]

omit [DecidableEq H] in
 theorem primrec_rawSweep : Primrec (fun p : (Cells S Γ × Cells S Γ) × Bool × Bool =>
    rawSweep (H := H) blank p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hp := Primrec.dom_finite (cleanAnchor (S := S) blank)
  exact (Scan.Sector.primrec_mk
    ((Primrec.list_dropWhile hp).comp (Primrec.fst.comp Primrec.fst))
    (Primrec.const Head.raw)
    (Primrec.list_append.comp
      (Primrec.list_reverse.comp ((Primrec.list_takeWhile hp).comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.fst))
    (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).of_eq
      fun p => (rawSweep_takeDrop blank _ _ _ _).symm

 theorem primrec_rawNormal : Primrec (rawNormal (S := S) (H := H) blank) := by
  have hg : PrimrecPred (fun v : Sector S Γ H => v.head = .raw) :=
    Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const Head.raw)
  have hh : Primrec (fun v : Sector S Γ H => if v.head = .raw then
      rawSweep blank v.left v.right v.leftBoundary v.rightBoundary else v) :=
    Primrec.ite hg ((primrec_rawSweep blank).comp
      ((Scan.Sector.primrec_left.pair Scan.Sector.primrec_right).pair
        (Scan.Sector.primrec_lb.pair Scan.Sector.primrec_rb))) Primrec.id
  exact hh.of_eq fun v => by cases h : v.head <;> simp [rawNormal,h]

 theorem primrec_quotaNormal : Primrec (quotaNormal (S := S) (H := H) blank) := by
  have hg : PrimrecPred (fun v : Sector S Γ H =>
      v.head = .pending ∧ v.right.head? = some (Validator.cell blank .cutD)) :=
    (Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const Head.pending)).and
      (Primrec.eq.comp (Primrec.list_head?.comp Scan.Sector.primrec_right) (Primrec.const _))
  have hh : Primrec (fun v : Sector S Γ H =>
      if v.head = .pending ∧ v.right.head? = some (Validator.cell blank .cutD)
      then {v with left := trimQuota blank v.left} else v) :=
    Primrec.ite hg
      (Scan.Sector.primrec_mk ((primrec_trimQuota blank).comp Scan.Sector.primrec_left)
        Scan.Sector.primrec_head Scan.Sector.primrec_right Scan.Sector.primrec_lb Scan.Sector.primrec_rb)
      Primrec.id
  exact hh.of_eq fun v => by
    rcases v with ⟨l,q,r,lb,rb⟩
    cases q <;> cases r <;> simp [quotaNormal]

 theorem primrec_unmerge : Primrec (unmerge (S := S) (H := H) blank) := by
  have hg : PrimrecPred (fun v : Sector S Γ H =>
      v.head = .pending ∧ v.left.head? = some (Validator.cell blank .cutC) ∧
        v.right.head? = some (Validator.cell blank .cutD)) :=
    (Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const Head.pending)).and
      ((Primrec.eq.comp (Primrec.list_head?.comp Scan.Sector.primrec_left) (Primrec.const _)).and
        (Primrec.eq.comp (Primrec.list_head?.comp Scan.Sector.primrec_right) (Primrec.const _)))
  have hl : Primrec (fun v : Sector S Γ H => rawNormal (H := H) blank
      ⟨v.left.tail,.raw,[],v.leftBoundary,true⟩) :=
    (primrec_rawNormal (H := H) blank).comp (Scan.Sector.primrec_mk
      (Primrec.list_tail.comp Scan.Sector.primrec_left) (Primrec.const Head.raw)
      (Primrec.const []) Scan.Sector.primrec_lb (Primrec.const true))
  have hr : Primrec (fun v : Sector S Γ H => rawNormal (H := H) blank
      ⟨[],.raw,v.right.tail,true,v.rightBoundary⟩) :=
    (primrec_rawNormal (H := H) blank).comp (Scan.Sector.primrec_mk (Primrec.const [])
      (Primrec.const Head.raw) (Primrec.list_tail.comp Scan.Sector.primrec_right)
      (Primrec.const true) Scan.Sector.primrec_rb)
  have hh : Primrec (fun v : Sector S Γ H =>
      if v.head = .pending ∧ v.left.head? = some (Validator.cell blank .cutC) ∧
        v.right.head? = some (Validator.cell blank .cutD)
      then [rawNormal blank ⟨v.left.tail,.raw,[],v.leftBoundary,true⟩,
        rawNormal blank ⟨[],.raw,v.right.tail,true,v.rightBoundary⟩]
      else [v]) :=
    Primrec.ite hg (Primrec.list_cons.comp hl
      (Primrec.list_cons.comp hr (Primrec.const [])))
      (Primrec.list_cons.comp Primrec.id (Primrec.const []))
  exact hh.of_eq fun v => by
    rcases v with ⟨l,q,r,lb,rb⟩
    cases l with
    | nil => cases q <;> simp [unmerge]
    | cons c l =>
      cases r with
      | nil => cases q <;> simp [unmerge]
      | cons d r => cases q <;> simp [unmerge]

 theorem primrec_pendingPreprocess : Primrec (pendingPreprocess (S := S) (H := H) blank) :=
  (primrec_unmerge blank).comp (primrec_quotaNormal blank)
omit [DecidableEq S] [DecidableEq Γ] in
 theorem primrec_cleanupNormal : Primrec (cleanupNormal (S := S) (H := H) blank) := by
  have hg : PrimrecPred (fun v : Sector S Γ H => v.head = .cleanup) :=
    Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const Head.cleanup)
  have hh : Primrec (fun v : Sector S Γ H => if v.head = .cleanup then
      (⟨[],if v.leftBoundary then .raw else .cleanup,
        Cleanup.output blank v.left.reverse ++ v.right,v.leftBoundary,v.rightBoundary⟩ : Sector S Γ H)
      else v) :=
    Primrec.ite hg (Scan.Sector.primrec_mk (Primrec.const [])
      ((Primrec.dom_finite (fun b : Bool => if b then (Head.raw : Head H) else .cleanup)).comp
        Scan.Sector.primrec_lb)
      (Primrec.list_append.comp ((primrec_cleanupOutput blank).comp
        (Primrec.list_reverse.comp Scan.Sector.primrec_left)) Scan.Sector.primrec_right)
      Scan.Sector.primrec_lb Scan.Sector.primrec_rb) Primrec.id
  exact hh.of_eq fun v => by
    rcases v with ⟨l,q,r,lb,rb⟩
    cases q <;> cases lb <;> rfl

 theorem primrec_cleanupPreprocess : Primrec (cleanupPreprocess (S := S) (H := H) blank) :=
  (primrec_rawNormal blank).comp (primrec_cleanupNormal blank)
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

namespace FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {H H' B T : Type*} [Fintype B] [Fintype T]

theorem sectorList_map (i : H → H') (heads : List H) (n : ℕ) :
    sectorList (B := B) (T := T) (heads.map i) n=
      (sectorList heads n).map (mapHead i) := by
  simp only [sectorList,List.flatMap_map,List.map_flatMap]
  rfl

variable [DecidableEq H] [DecidableEq H'] [DecidableEq B] [DecidableEq T]
omit [DecidableEq H] [DecidableEq H'] [DecidableEq T] in
theorem universeList_map (i : H → H') (heads : List H) (v : Sector H B T) :
    universeList (heads.map i) (mapHead i v)=(universeList heads v).map (mapHead i) := by
  simp only [universeList,mapHead,sectorList_map,List.filter_map,baseSkeleton]
  rfl

variable (i : H → H') (hi : Function.Injective i)
  (t : Table H B T) (u : Table H' B T)
  (hd : ∀ q,u.direction (i q)=t.direction q)
  (hc : ∀ q b a,u.cell (i q) b a=(t.cell q b a).map (mapInstruction i))
  (hb : ∀ q,u.boundary (i q)=(t.boundary q).map i)

omit [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq H'] [DecidableEq B] [DecidableEq T] in
include hd hc hb in
theorem step_map (v : Sector H B T) :
    step u (mapHead i v)=(step t v).map (mapHead i) := by
  apply step_mapHead
  · exact hd _
  · exact hc _
  · exact hb _

omit [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq H'] [DecidableEq B] [DecidableEq T] in
include hi in
theorem mapHead_injective : Function.Injective (mapHead (B := B) (T := T) i) := by
  intro v w hh
  cases v; cases w
  simp only [mapHead,Sector.mk.injEq] at hh ⊢
  exact ⟨hh.1,hi hh.2.1,hh.2.2⟩

omit [Fintype B] [Fintype T] in
include hi hd hc hb in
theorem stepBool_map (v w : Sector H B T) :
    decide (step u (mapHead i v)=some (mapHead i w))=decide (step t v=some w) := by
  rw [step_map i t u hd hc hb]
  have he : (step t v).map (mapHead i)=some (mapHead i w) ↔ step t v=some w := by
    rw [Option.map_eq_some_iff]
    constructor
    · rintro ⟨a,ha,he⟩
      exact (mapHead_injective i hi he) ▸ ha
    · intro he
      exact ⟨w,he,rfl⟩
  simp only [he]

include hi hd hc hb in
theorem componentList_map (heads : List H) (v : Sector H B T) :
    componentList (fun _ : Unit => u) (fun _ => heads.map i) ((),mapHead i v)=
      (componentList (fun _ : Unit => t) (fun _ => heads) ((),v)).map (mapHead i) := by
  rw [componentList,componentList,universeList_map]
  exact component_map _ _ _ (stepBool_map i hi t u hd hc hb) _ _

end FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform
open FiniteAlgebraicEnvelopes.Effect
variable {P H B T : Type*} [Primcodable P] [Primcodable H] [Primcodable B] [Primcodable T]
  [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq B] [DecidableEq T]

omit [Primcodable H] [Primcodable B] [Primcodable T] in
theorem universeList_ext_support {u v : List H} (h : u.toFinset=v.toFinset) (a : Sector H B T) :
    (universeList u a).toFinset=(universeList v a).toFinset := by
  have hh : ∀ q,q∈u ↔ q∈v := fun q => by simpa using Finset.ext_iff.mp h q
  ext b; simp only [List.mem_toFinset,mem_universeList,hh]

omit [Primcodable P] [Primcodable H] [Primcodable B] [Primcodable T] in
theorem componentList_ext_support (table : P → Table H B T) {u v : P → List H} (p : P)
    (h : (u p).toFinset=(v p).toFinset) (a : Sector H B T) (ha : a.head∈u p) :
    (componentList table u (p,a)).toFinset=(componentList table v (p,a)).toFinset := by
  apply Graph.component_ext_universe _ (universeList_ext_support h a)
  exact mem_universeList _ a a |>.mpr ⟨ha,rfl⟩

variable [LinearOrder (Sector H B T)]
noncomputable def representative (table : P → Table H B T) (support : P → List H)
    (entry success : Sector H B T → Bool) (x : P × Sector H B T) : Sector H B T :=
  (priorityList entry success (componentList table support x)).min?.getD x.2

theorem primrec_representative (table : P → Table H B T) {support : P → List H}
    {entry success : Sector H B T → Bool}
    (hb : Primrec (fun x : P × H => (table x.1).boundary x.2))
    (hc : Primrec (fun x : P × H × B × T => (table x.1).cell x.2.1 x.2.2.1 x.2.2.2))
    (hd : Primrec (fun x : P × H => decide ((table x.1).direction x.2 = .right)))
    (hs : Primrec support) (hp : Primrec entry) (hq : Primrec success)
    (hle : PrimrecRel (fun a b : Sector H B T => a ≤ b)) :
    Primrec (representative table support entry success) :=
  Primrec.option_getD.comp ((primrec_listMin hle).comp
    ((primrec_priorityList hp hq).comp (primrec_componentList table hb hc hd hs))) Primrec.snd

end FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler
open HeadCodec FiniteAlgebraicEnvelopes.Effect
open scoped HeadCodec

namespace Surface.Uniform
variable {P S Γ Q : Type*} [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable P]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
variable (blank : Γ) (rep : P × Control.Sector S Γ Q → Control.Sector S Γ Q)

def internalPreprocess (x : P × Control.Sector S Γ Q) : List (Sector S Γ (Control.Head S Q)) :=
  let w := rep x
  if Control.Entry blank w then
    pendingPreprocess blank ⟨w.left,.pending,w.right,w.leftBoundary,w.rightBoundary⟩
  else if Control.Success w then
    [cleanupPreprocess blank ⟨w.left,.cleanup,w.right,w.leftBoundary,w.rightBoundary⟩]
  else [Scan.mapHead Head.internal w]

def preprocess (x : P × Sector S Γ (Control.Head S Q)) : List (Sector S Γ (Control.Head S Q)) :=
  match x.2.head with
  | .raw => [rawNormal blank x.2]
  | .pending => pendingPreprocess blank x.2
  | .cleanup => [cleanupPreprocess blank x.2]
  | .internal q => internalPreprocess blank rep
      (x.1,⟨x.2.left,q,x.2.right,x.2.leftBoundary,x.2.rightBoundary⟩)

theorem primrec_internalPreprocess (hrep : Primrec rep) : Primrec (internalPreprocess blank rep) := by
  have hp := primrec_pendingPreprocess (S := S) (H := Control.Head S Q) blank
  have hc := primrec_cleanupPreprocess (S := S) (H := Control.Head S Q) blank
  have hl : Primrec (fun w : Control.Sector S Γ Q =>
      pendingPreprocess blank (⟨w.left,.pending,w.right,w.leftBoundary,w.rightBoundary⟩ : Sector S Γ (Control.Head S Q))) :=
    hp.comp (Scan.Sector.primrec_mk Scan.Sector.primrec_left (Primrec.const Head.pending)
      Scan.Sector.primrec_right Scan.Sector.primrec_lb Scan.Sector.primrec_rb)
  have hr : Primrec (fun w : Control.Sector S Γ Q =>
      cleanupPreprocess blank (⟨w.left,.cleanup,w.right,w.leftBoundary,w.rightBoundary⟩ : Sector S Γ (Control.Head S Q))) :=
    hc.comp (Scan.Sector.primrec_mk Scan.Sector.primrec_left (Primrec.const Head.cleanup)
      Scan.Sector.primrec_right Scan.Sector.primrec_lb Scan.Sector.primrec_rb)
  exact (Primrec.ite (Control.Uniform.primrec_entry blank) hl
    (Primrec.ite Control.Uniform.primrec_success (Primrec.list_cons.comp hr (Primrec.const []))
      (Primrec.list_cons.comp (Scan.primrec_mapHead HeadCodec.primrec_internal)
        (Primrec.const [])))).comp hrep

theorem primrec_preprocess (hrep : Primrec rep) : Primrec (preprocess blank rep) := by
  let inside : Head (Control.Head S Q) → Control.Head S Q
    | .internal q => q
    | _ => .initial
  have hin : Primrec inside :=
    ((primrec_sumElim (Primrec.const Control.Head.initial) Primrec.id).comp primrec_surfaceCode).of_eq
      fun q => by cases q <;> rfl
  have hv : Primrec (fun x : P × Sector S Γ (Control.Head S Q) =>
      (⟨x.2.left,inside x.2.head,x.2.right,x.2.leftBoundary,x.2.rightBoundary⟩ : Control.Sector S Γ Q)) :=
    (Scan.Sector.primrec_mk Scan.Sector.primrec_left
        (hin.comp Scan.Sector.primrec_head) Scan.Sector.primrec_right
          Scan.Sector.primrec_lb Scan.Sector.primrec_rb).comp (Primrec.snd (α :=P))
  have hi : Primrec (fun x : P × Sector S Γ (Control.Head S Q) =>
      internalPreprocess blank rep
        (x.1,⟨x.2.left,inside x.2.head,x.2.right,x.2.leftBoundary,x.2.rightBoundary⟩)) :=
    (primrec_internalPreprocess blank rep hrep).comp (Primrec.fst.pair hv)
  have hg (q : Head (Control.Head S Q)) :
      PrimrecPred (fun x : P × Sector S Γ (Control.Head S Q) => x.2.head = q) :=
    Primrec.eq.comp (Scan.Sector.primrec_head.comp Primrec.snd) (Primrec.const q)
  exact (Primrec.ite (hg .raw)
      (Primrec.list_cons.comp ((primrec_rawNormal blank).comp Primrec.snd) (Primrec.const []))
      (Primrec.ite (hg .pending) ((primrec_pendingPreprocess blank).comp Primrec.snd)
        (Primrec.ite (hg .cleanup)
          (Primrec.list_cons.comp ((primrec_cleanupPreprocess blank).comp Primrec.snd) (Primrec.const [])) hi))).of_eq
    fun x => by rcases x with ⟨p,l,q,r,lb,rb⟩; cases q <;> simp [preprocess,inside]
end Surface.Uniform

namespace Word.Uniform
variable {P S Γ Q : Type*} [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable P]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
variable (blank : Γ) (rep : P × Control.Sector S Γ Q → Control.Sector S Γ Q)

def sectorPreprocess (x : P × Sector S Γ Q) : List (Sector S Γ Q) :=
  (Surface.Uniform.preprocess blank rep (x.1,Scan.unliteral x.2)).map (Scan.literal id)

def preprocess (x : P × List (Letter S Γ Q)) : List (List (Letter S Γ Q)) :=
  Path.prepare (fun v => sectorPreprocess blank rep (x.1,v)) x.2

theorem primrec_sectorPreprocess (hrep : Primrec rep) : Primrec (sectorPreprocess blank rep) :=
  Primrec.list_map ((Surface.Uniform.primrec_preprocess blank rep hrep).comp
    (Primrec.fst.pair (Scan.primrec_unliteral.comp Primrec.snd)))
    ((Scan.primrec_literal Primrec.id).comp Primrec.snd).to₂

theorem primrec_preprocess (hrep : Primrec rep) : Primrec (preprocess blank rep) :=
  Path.Uniform.primrec_prepare_family (primrec_sectorPreprocess blank rep hrep)

end Word.Uniform
end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Compiler
open HeadCodec FiniteAlgebraicEnvelopes.Effect
open scoped HeadCodec

namespace Word.Uniform
variable {P S Γ Q : Type*} [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable P] [Primcodable S]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
variable (blank : Γ) (rep : P × Control.Sector S Γ Q → Control.Sector S Γ Q)

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] in
theorem primrec_raw : Primrec (raw (S := S) (Q := Q) blank) := by
  have hp : Primrec (fun w : List S => (⟨[],Surface.Head.raw,
      w.map (Validator.cell blank ∘ Base.anchor),true,true⟩ : Surface.Sector S Γ (Control.Head S Q))) :=
    Scan.Sector.primrec_mk (Primrec.const []) (Primrec.const Surface.Head.raw)
      (Primrec.list_map Primrec.id ((Primrec.dom_finite _).comp Primrec.snd).to₂)
      (Primrec.const true) (Primrec.const true)
  exact Path.Uniform.primrec_encode.comp ((Scan.primrec_literal Primrec.id).comp hp)

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] in
theorem primrec_rawLetters : Primrec (rawLetters (S := S) (Γ := Γ) (Q := Q)) := by
  let f : Base S × Tag S Γ → Option S := fun c => match c.1 with | .anchor s => some s | _ => none
  have hp : Primrec (fun a : Letter S Γ Q => match a with
      | .right (.anchor s,_) => some s | _ => none) := by
    exact (Primrec.option_bind Path.Uniform.primrec_right?
      ((Primrec.dom_finite f).comp Primrec.snd).to₂).of_eq fun a => by
        cases a <;> simp only [Option.bind_none, Option.bind_some]
        case right c => cases c with | mk b t => cases b <;> rfl
  exact Primrec.listFilterMap Primrec.id (hp.comp Primrec.snd).to₂

theorem primrec_readRaw : Primrec (readRaw (S := S) (Q := Q) blank) :=
  Primrec.ite (Primrec.eq.comp ((primrec_raw blank).comp primrec_rawLetters) Primrec.id)
    (Primrec.option_some.comp primrec_rawLetters) (Primrec.const none)

theorem primrec_classify : Primrec (classify (S := S) (Q := Q) blank) := by
  exact (Primrec.option_casesOn (primrec_readRaw blank) Primrec.sumInl
    (Primrec.sumInr.comp Primrec.snd).to₂).of_eq fun w => by
      cases h : readRaw blank w <;> simp [classify,h]

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] in
theorem primrec_realize : Primrec (realize (S := S) (Q := Q) blank) := by
  exact (Primrec.sumCasesOn Primrec.id Primrec.snd.to₂
    ((primrec_raw blank).comp Primrec.snd).to₂).of_eq fun w => by cases w <;> rfl

def partialNormal (f : P × List S → Part (List S))
    (x : P × List (Letter S Γ Q)) : Part (List (Letter S Γ Q)) :=
  if Path.shape x.2 = .zero then Part.some [.zero] else
    (RawRuns.partialSource (fun w => f (x.1,w)) ((preprocess blank rep x).map (classify blank))).map
      (List.flatMap (realize blank))

theorem partrec_partialNormal (hrep : Primrec rep)
    {f : P × List S → Part (List S)} (hf : Partrec f) :
    Partrec (partialNormal blank rep f) := by
  have hp : Primrec (fun x : P × List (Letter S Γ Q) =>
      (preprocess blank rep x).map (classify blank)) :=
    Primrec.list_map (primrec_preprocess blank rep hrep) ((primrec_classify blank).comp Primrec.snd).to₂
  have hr : Primrec (fun w : List (Item S Γ Q) => w.flatMap (realize blank)) :=
    Primrec.list_flatMap Primrec.id ((primrec_realize blank).comp Primrec.snd).to₂
  have hb : Partrec (fun x : P × List (Letter S Γ Q) =>
      (RawRuns.partialSource (fun w => f (x.1,w)) ((preprocess blank rep x).map (classify blank))).map
        (List.flatMap (realize blank))) :=
    ((RawRuns.Uniform.partrec_partialSource hf).comp (Computable.fst.pair hp.to_comp)).map
      (hr.to_comp.comp Computable.snd).to₂
  have ho : Primrec (fun x : P × List (Letter S Γ Q) =>
      if Path.shape x.2 = .zero then none else some x) :=
    Primrec.ite (Primrec.eq.comp (Path.Uniform.primrec_shape.comp Primrec.snd) (Primrec.const Path.Shape.zero))
      (Primrec.const none) Primrec.option_some
  exact (Partrec.optionCasesOn_right ho.to_comp (Computable.const [Path.Letter.zero])
    (hb.comp Computable.snd).to₂).of_eq fun x => by
      by_cases h : Path.shape x.2 = .zero <;> simp [h,partialNormal]

end Word.Uniform
end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform
open FiniteAlgebraicEnvelopes.Effect
variable {H H' B T : Type*} [Primcodable H] [Primcodable H'] [Primcodable B] [Primcodable T]
  [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq H'] [DecidableEq B] [DecidableEq T]
  [LinearOrder (Sector H B T)] [LinearOrder (Sector H' B T)]

variable (i : H → H') (hi : Function.Injective i)
  (t : Table H B T) (u : Table H' B T)
  (hd : ∀ q,u.direction (i q)=t.direction q)
  (hc : ∀ q b a,u.cell (i q) b a=(t.cell q b a).map (mapInstruction i))
  (hb : ∀ q,u.boundary (i q)=(t.boundary q).map i)
  (ho : Monotone (mapHead (B := B) (T := T) i))
  (entry success : Sector H B T → Bool) (entry' success' : Sector H' B T → Bool)
  (he : ∀ v,entry' (mapHead i v)=entry v) (hs : ∀ v,success' (mapHead i v)=success v)

omit [Primcodable H] [Primcodable H'] [Primcodable B] [Primcodable T] in
include hi hd hc hb ho he hs in
theorem representative_map (heads : List H) (v : Sector H B T) :
    representative (fun _ : Unit => u) (fun _ => heads.map i) entry' success' ((),mapHead i v)=
      mapHead i (representative (fun _ : Unit => t) (fun _ => heads) entry success ((),v)) := by
  unfold representative
  rw [componentList_map i hi t u hd hc hb heads v,priorityList_map _ _ _ _ _ he hs,minList_map _ ho]
  cases (priorityList entry success (componentList (fun _ : Unit => t) (fun _ => heads) ((),v))).min? <;> rfl

variable {P : Type*} [Primcodable P]
omit [Primcodable P] in
theorem representative_ext_support (table : P → Table H B T) {heads heads' : P → List H}
    (p : P) (he : (heads p).toFinset=(heads' p).toFinset)
    (entry success : Sector H B T → Bool) (v : Sector H B T) (hv : v.head∈heads p) :
    representative table heads entry success (p,v)=representative table heads' entry success (p,v) := by
  unfold representative
  rw [minList_ext (priorityList_ext _ _ (componentList_ext_support table p he v hv))]

variable [Fintype H]
omit [Primcodable H] [Primcodable B] [Primcodable T] in
theorem representative_finite (t : Table H B T) (E F : Sector H B T → Prop)
    [DecidablePred E] [DecidablePred F] (v : Sector H B T) :
    representative (fun _ : Unit => t) (fun _ => finiteList H)
      (fun w => decide (E w)) (fun w => decide (F w)) ((),v)=Scan.representative t E F v :=
  (Scan.representative_list t E F v).symm

omit [Primcodable H] in
include hi hd hc hb ho he hs in
theorem representative_finite_map (heads : List H')
    (hh : heads.toFinset=((finiteList H).map i).toFinset) (v : Sector H B T) :
    representative (fun _ : Unit => u) (fun _ => heads) entry' success' ((),mapHead i v)=
      mapHead i (Scan.representative t (fun w => entry w=true) (fun w => success w=true) v) := by
  have hv : (mapHead i v).head∈heads := by
    apply List.mem_toFinset.mp
    rw [hh]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨v.head,mem_finiteList _,rfl⟩)
  rw [representative_ext_support (heads' := fun _ : Unit => (finiteList H).map i) (fun _ : Unit => u) () hh entry' success' _ hv,
    representative_map i hi t u hd hc hb ho entry success entry' success' he hs]
  congr 1
  simpa only [Bool.decide_coe] using
    representative_finite t (fun w => entry w=true) (fun w => success w=true) v

end FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

section
open Compiler Compiler.Simulator Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec
variable {S Γ Q : Type*}

variable (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ] (p : S)

theorem coded_transition (n : ℕ) (q : State Q n) (a : Bool×Γ) :
    (codedMachine A M p n).transition (encode n q) a=
      ((ParameterMachine.machine A M p n).transition q a).map (commandMap (encode n)) := by
  simp only [codedMachine,transition_encode,Option.map_map]
  rfl

variable [Fintype Q] [Fintype Γ] [Primcodable Q] [Primcodable Γ]
theorem primrec_codedTransition : Primrec (fun x : ℕ × Control Q × (Bool×Γ) =>
    (codedMachine A M p x.1).transition x.2.1 x.2.2) := by
  have ht := (primrec_transition A M p).comp
    ((Primrec.fst.pair (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd))
  exact Primrec.option_map ht
    (primrec_commandMk (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂

variable {T : Type*} [Fintype T]

theorem primrec_heads : Primrec (heads (T := T) (Q := Q)) :=
  primrec_controlSupport.comp primrec_support

omit [Primcodable Q] in
theorem mem_heads_iff (n : ℕ) (h : Compiler.Control.Head T (Control Q)) :
    h∈heads n ↔ ∃ a : Compiler.Control.Head T (State Q n),controlMap (encode n) a=h := by
  constructor
  · intro hh
    cases h with
    | initial => exact ⟨.initial,rfl⟩
    | left => exact ⟨.left,rfl⟩
    | right => exact ⟨.right,rfl⟩
    | workspace => exact ⟨.workspace,rfl⟩
    | suffix => exact ⟨.suffix,rfl⟩
    | machine h =>
      cases h with
      | start => exact ⟨.machine .start,rfl⟩
      | rewind r => exact ⟨.machine (.rewind r),rfl⟩
      | scan r => exact ⟨.machine (.scan r),rfl⟩
      | finish => exact ⟨.machine .finish,rfl⟩
      | ok => exact ⟨.machine .ok,rfl⟩
      | run q =>
        obtain ⟨a,rfl⟩ := (mem_support_iff n q).mp ((mem_controlSupport _ _).mp hh)
        exact ⟨.machine (.run a),rfl⟩
      | left q =>
        obtain ⟨a,rfl⟩ := (mem_support_iff n q).mp ((mem_controlSupport _ _).mp hh)
        exact ⟨.machine (.left a),rfl⟩
  · rintro ⟨a,rfl⟩
    cases a <;> simp only [heads,mem_controlSupport,controlMap]
    case machine a => cases a <;> simp [stateMap,mem_support]

omit [Primcodable Q] in
theorem heads_finset [DecidableEq T] [DecidableEq Q] (n : ℕ) :
    (heads (T := T) (Q := Q) n).toFinset=
      ((Scan.finiteList (Compiler.Control.Head T (State Q n))).map (controlMap (encode n))).toFinset := by
  classical
  ext h
  simp only [List.mem_toFinset,mem_heads_iff,List.mem_map,Scan.mem_finiteList,true_and]

end

open Compiler Compiler.Simulator Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec
variable {S T Γ Q : Type*} [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet S Γ) (M : Machine Q Γ) (p : S) (B : Alphabet T (Bool×Γ))

noncomputable def codedRepresentative : ℕ × Compiler.Control.Sector T (Bool×Γ) (Control Q) →
    Compiler.Control.Sector T (Bool×Γ) (Control Q) :=
  letI := Effect.codeOrder (Compiler.Control.Sector T (Bool×Γ) (Control Q))
  Scan.Uniform.representative (fun n => Compiler.Control.table B (codedMachine A M p n)) heads
    (fun v => decide (Compiler.Control.Entry B.blank v))
    (fun v => decide (Compiler.Control.Success v))

theorem primrec_codedRepresentative : Primrec (codedRepresentative A M p B) := by
  let := Effect.codeOrder (Compiler.Control.Sector T (Bool×Γ) (Control Q))
  apply Scan.Uniform.primrec_representative
  · exact primrec_controlBoundary B (codedMachine A M p) (Primrec.const _)
  · exact primrec_controlCell B (codedMachine A M p) (Primrec.const _) (primrec_codedTransition A M p)
  · exact primrec_controlDirection B (codedMachine A M p)
  · exact primrec_heads
  · exact (Compiler.Control.Uniform.primrec_entry B.blank).decide
  · exact (Compiler.Control.Uniform.primrec_success).decide
  · exact Effect.primrec_codeOrder _

@[instance_reducible]
noncomputable def finiteOrder (n : ℕ) : LinearOrder (Compiler.Control.Sector T (Bool×Γ) (State Q n)) :=
  letI := Effect.codeOrder (Compiler.Control.Sector T (Bool×Γ) (Control Q))
  LinearOrder.lift' (Scan.mapHead (controlMap (encode n)))
    (Scan.Uniform.mapHead_injective _ (controlMap_injective (encode_injective n)))

omit [Primcodable Γ] in
theorem codedRepresentative_map (n : ℕ) (v : Compiler.Control.Sector T (Bool×Γ) (State Q n)) :
    letI := finiteOrder (T := T) (Γ := Γ) (Q := Q) n
    codedRepresentative A M p B (n,Scan.mapHead (controlMap (encode n)) v)=
      Scan.mapHead (controlMap (encode n)) (Compiler.Control.representative B (machine A M p n) v) := by
  let : Primcodable (State Q n) := Effect.finitePrimcodable _
  let := Effect.codeOrder (Compiler.Control.Sector T (Bool×Γ) (Control Q))
  let := finiteOrder (T := T) (Γ := Γ) (Q := Q) n
  have h := Scan.Uniform.representative_finite_map
    (controlMap (S := T) (encode n)) (controlMap_injective (encode_injective n))
    (Compiler.Control.table B (machine A M p n)) (Compiler.Control.table B (codedMachine A M p n))
    (Compiler.Control.table_direction_map B (machine A M p n) (codedMachine A M p n) (encode n))
    (Compiler.Control.table_cell_map B (machine A M p n) (codedMachine A M p n) (encode n)
      (coded_initial A M p n) (coded_transition A M p n))
    (Compiler.Control.table_boundary_map B (machine A M p n) (codedMachine A M p n) (encode n))
    (show Monotone (Scan.mapHead (B := Base T) (T := Tag T (Bool×Γ)) (controlMap (encode n))) from
      fun _ _ h => h)
    (fun w => decide (Compiler.Control.Entry B.blank w)) (fun w => decide (Compiler.Control.Success w))
    (fun w => decide (Compiler.Control.Entry B.blank w)) (fun w => decide (Compiler.Control.Success w))
    (fun w => by simp only [Compiler.Control.entry_map])
    (fun w => by simp only [Compiler.Control.success_map])
    (heads n) (heads_finset n) v
  simpa only [codedRepresentative, Compiler.Control.representative,
    Scan.Uniform.representative, Scan.Uniform.componentList,decide_eq_true_eq] using h

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

namespace FiniteAlgebraicEnvelopes.Compiler.Surface
variable {S Γ H H' : Type*}

variable (i : H → H') (blank : Γ) [DecidableEq S] [DecidableEq Γ]

theorem rawSweep_map (l r : Cells S Γ) (lb rb : Bool) :
    rawSweep (H := H') blank l r lb rb=Scan.mapHead (headMap i) (rawSweep (H := H) blank l r lb rb) := by
  induction l generalizing r with
  | nil => rfl
  | cons c l ih =>
    rcases c with ⟨b,t⟩
    cases b <;> simp only [rawSweep]
    case anchor s => split <;> first | exact ih _ | rfl
    all_goals rfl

theorem rawNormal_map (v : Sector S Γ H) :
    rawNormal blank (Scan.mapHead (headMap i) v)=Scan.mapHead (headMap i) (rawNormal blank v) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> first | exact rawSweep_map i blank _ _ _ _ | rfl

theorem quotaNormal_map (v : Sector S Γ H) :
    quotaNormal blank (Scan.mapHead (headMap i) v)=Scan.mapHead (headMap i) (quotaNormal blank v) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> try rfl
  cases r <;> simp only [quotaNormal,Scan.mapHead,headMap]
  all_goals split <;> rfl

theorem unmerge_map (v : Sector S Γ H) :
    unmerge blank (Scan.mapHead (headMap i) v)=
      (unmerge blank v).map (Scan.mapHead (headMap i)) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases l <;> cases q <;> cases r <;> simp only [Scan.mapHead,headMap,unmerge,List.map_cons,List.map_nil]
  split
  · simp only [List.map_cons,List.map_nil]
    refine congrArg₂ (fun (a b : Sector S Γ H') => [a,b]) ?_ ?_
    · exact rawSweep_map (S := S) i blank _ _ _ _
    · exact rawSweep_map (S := S) i blank _ _ _ _
  · rfl

theorem pendingPreprocess_map (v : Sector S Γ H) :
    pendingPreprocess blank (Scan.mapHead (headMap i) v)=
      (pendingPreprocess blank v).map (Scan.mapHead (headMap i)) := by
  simp only [pendingPreprocess,quotaNormal_map,unmerge_map]

omit [DecidableEq S] [DecidableEq Γ] in
theorem ofCleanup_map (v : Cleanup.Sector S Γ) :
    (ofCleanup v : Sector S Γ H')=Scan.mapHead (headMap i) (ofCleanup v : Sector S Γ H) := by
  rcases v with ⟨l,q,r,lb,rb⟩; cases q <;> rfl

omit [DecidableEq S] [DecidableEq Γ] in
theorem cleanupNormal_map (v : Sector S Γ H) :
    cleanupNormal blank (Scan.mapHead (headMap i) v)=Scan.mapHead (headMap i) (cleanupNormal blank v) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> try rfl
  exact ofCleanup_map i _

theorem cleanupPreprocess_map (v : Sector S Γ H) :
    cleanupPreprocess blank (Scan.mapHead (headMap i) v)=Scan.mapHead (headMap i) (cleanupPreprocess blank v) := by
  simp only [cleanupPreprocess,cleanupNormal_map,rawNormal_map]
end FiniteAlgebraicEnvelopes.Compiler.Surface

namespace FiniteAlgebraicEnvelopes.Compiler.Surface.Uniform
open HeadCodec
open scoped HeadCodec
variable {P S Γ Q Q' : Type*} [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable Q'] [Primcodable P]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] [DecidableEq Q']
variable (i : Q → Q') (blank : Γ)
  (rep : P × Control.Sector S Γ Q → Control.Sector S Γ Q)
  (rep' : P × Control.Sector S Γ Q' → Control.Sector S Γ Q')
  (hr : ∀ p v,rep' (p,Scan.mapHead (controlMap i) v)=Scan.mapHead (controlMap i) (rep (p,v)))

omit [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable Q'] [Primcodable P] in
include hr in
theorem internalPreprocess_map (p : P) (v : Control.Sector S Γ Q) :
    internalPreprocess blank rep' (p,Scan.mapHead (controlMap i) v)=
      (internalPreprocess blank rep (p,v)).map (Scan.mapHead (Surface.headMap (controlMap i))) := by
  simp only [internalPreprocess,hr,Control.entry_map,Control.success_map]
  split
  · exact Surface.pendingPreprocess_map (controlMap i) blank
      (⟨(rep (p,v)).left,.pending,(rep (p,v)).right,(rep (p,v)).leftBoundary,(rep (p,v)).rightBoundary⟩ : Surface.Sector S Γ (Control.Head S Q))
  · split
    · simp only [List.map_cons,List.map_nil]
      congr 1
      exact Surface.cleanupPreprocess_map (controlMap i) blank
        (⟨(rep (p,v)).left,.cleanup,(rep (p,v)).right,(rep (p,v)).leftBoundary,(rep (p,v)).rightBoundary⟩ : Surface.Sector S Γ (Control.Head S Q))
    · rfl

omit [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable Q'] [Primcodable P] in
include hr in
theorem preprocess_map (p : P) (v : Surface.Sector S Γ (Control.Head S Q)) :
    preprocess blank rep' (p,Scan.mapHead (Surface.headMap (controlMap i)) v)=
      (preprocess blank rep (p,v)).map (Scan.mapHead (Surface.headMap (controlMap i))) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> simp only [preprocess,headMap,Scan.mapHead,List.map_cons,List.map_nil]
  case raw => congr 1; exact Surface.rawNormal_map (controlMap i) blank (⟨l,.raw,r,lb,rb⟩ : Surface.Sector S Γ (Control.Head S Q))
  case pending => exact Surface.pendingPreprocess_map (controlMap i) blank (⟨l,.pending,r,lb,rb⟩ : Surface.Sector S Γ (Control.Head S Q))
  case cleanup => congr 1; exact Surface.cleanupPreprocess_map (controlMap i) blank (⟨l,.cleanup,r,lb,rb⟩ : Surface.Sector S Γ (Control.Head S Q))
  case internal q => exact internalPreprocess_map i blank rep rep' hr p ⟨l,q,r,lb,rb⟩

end FiniteAlgebraicEnvelopes.Compiler.Surface.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
variable {H H' B T : Type*} (i : H → H')
theorem unliteral_map (v : Path.Sector (B×T) H) :
    unliteral (Path.mapSector i v)=mapHead i (unliteral v) := rfl
theorem literal_map (v : Sector H B T) :
    literal id (mapHead i v)=Path.mapSector i (literal id v) := rfl
end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Word
open HeadCodec
variable {S Γ Q Q' : Type*} (i : Q → Q') (blank : Γ)

def headMap : Surface.Head (Control.Head S Q) → Surface.Head (Control.Head S Q') :=
  Surface.headMap (controlMap i)
def letterMap : Letter S Γ Q → Letter S Γ Q' := Path.mapLetter (headMap i)

theorem headMap_injective (hi : Function.Injective i) : Function.Injective (headMap (S := S) i) :=
  Surface.headMap_injective (controlMap_injective hi)
theorem letterMap_injective (hi : Function.Injective i) :
    Function.Injective (letterMap (S := S) (Γ := Γ) i) :=
  Path.mapLetter_injective _ (headMap_injective i hi)

@[simp] theorem raw_map (w : List S) : (raw (Q := Q) blank w).map (letterMap i)=raw blank w := by
  simp only [raw,encode,letterMap,←Path.encode_map]
  rfl

@[simp] theorem rawLetters_map (w : List (Letter S Γ Q)) : rawLetters (w.map (letterMap i))=rawLetters w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a with
    | right c =>
      rcases c with ⟨b,t⟩
      cases b <;> simp_all only [List.map_cons,rawLetters,List.filterMap_cons,letterMap,Path.mapLetter]
    | _ => simp_all only [List.map_cons,rawLetters,List.filterMap_cons,letterMap,Path.mapLetter]

variable [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] [DecidableEq Q']
theorem readRaw_map (hi : Function.Injective i) (w : List (Letter S Γ Q)) :
    readRaw blank (w.map (letterMap i))=readRaw blank w := by
  have he : raw blank (rawLetters w)=w.map (letterMap i) ↔ raw blank (rawLetters w)=w := by
    rw [←raw_map i blank]
    exact List.map_injective_iff.mpr (letterMap_injective i hi) |>.eq_iff
  simp only [readRaw,rawLetters_map,he]

theorem classify_map (hi : Function.Injective i) (w : List (Letter S Γ Q)) :
    classify blank (w.map (letterMap i))=Sum.map (List.map (letterMap i)) id (classify blank w) := by
  simp only [classify,readRaw_map i blank hi]
  cases readRaw blank w <;> rfl

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] [DecidableEq Q'] in
theorem realize_map (a : Item S Γ Q) :
    realize blank (Sum.map (List.map (letterMap i)) id a)=(realize blank a).map (letterMap i) := by
  cases a <;> simp only [Sum.map_inl,Sum.map_inr,realize,raw_map,id_eq]
end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.Compiler.Word.Uniform
open HeadCodec
open scoped HeadCodec
variable {P S Γ Q Q' : Type*} [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable Q'] [Primcodable P]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] [DecidableEq Q']
variable (i : Q → Q') (blank : Γ)
  (rep : P × Control.Sector S Γ Q → Control.Sector S Γ Q)
  (rep' : P × Control.Sector S Γ Q' → Control.Sector S Γ Q')
  (hr : ∀ p v,rep' (p,Scan.mapHead (controlMap i) v)=Scan.mapHead (controlMap i) (rep (p,v)))

include hr in
omit [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable Q'] [Primcodable P] in
theorem sectorPreprocess_map (p : P) (v : Sector S Γ Q) :
    sectorPreprocess blank rep' (p,Path.mapSector (headMap i) v)=
      (sectorPreprocess blank rep (p,v)).map (Path.mapSector (headMap i)) := by
  simp only [sectorPreprocess,Scan.unliteral_map,headMap,
    Surface.Uniform.preprocess_map i blank rep rep' hr,List.map_map,Function.comp_def,Scan.literal_map]

include hr in
omit [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable Q'] [Primcodable P] in
theorem preprocess_map (hi : Function.Injective i) (p : P) (w : List (Letter S Γ Q)) :
    preprocess blank rep' (p,w.map (letterMap i))=
      (preprocess blank rep (p,w)).map (List.map (letterMap i)) :=
  Path.prepare_map (headMap i) _ _ (sectorPreprocess_map i blank rep rep' hr p)
    (headMap_injective i hi) w

include hr in
omit [Fintype S] [Fintype Γ] [Primcodable Q] [Primcodable Q'] [Primcodable P] in
theorem partialNormal_map (hi : Function.Injective i) (f : P × List S → Part (List S))
    (p : P) (w : List (Letter S Γ Q)) :
    partialNormal blank rep' f (p,w.map (letterMap i))=
      (partialNormal blank rep f (p,w)).map (List.map (letterMap i)) := by
  have hshape : Path.shape (w.map (letterMap i))=Path.shape w := Path.shape_map (headMap i) w
  simp only [partialNormal,hshape]
  split
  · rfl
  · rw [preprocess_map i blank rep rep' hr hi]
    simp only [List.map_map,Function.comp_def,classify_map i blank hi]
    have he := List.map_map (f := classify (Q := Q) (Γ := Γ) blank)
      (g := Sum.map (List.map (letterMap (S := S) (Γ := Γ) i)) (id : List S → List S))
      (l := preprocess blank rep (p,w))
    simp only [Function.comp_def] at he
    rw [←he,RawRuns.partialSource_map]
    simp only [Part.map_map]
    congr 1
    funext l
    simp only [List.flatMap_map,List.map_flatMap,Function.comp_def,realize_map]

end FiniteAlgebraicEnvelopes.Compiler.Word.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler
open HeadCodec
open scoped HeadCodec
variable {P S Γ Q : Type*} [Primcodable P] [Primcodable Q]
  [Fintype S] [Fintype Γ] [Fintype Q]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [LinearOrder (Control.Sector S Γ Q)]
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)

namespace Surface.Uniform
omit [Primcodable P] [Primcodable Q] in
theorem preprocess_specialize (p : P) (v : Surface.Sector S Γ (Control.Head S Q)) :
    preprocess A.blank (fun x : P × Control.Sector S Γ Q => Control.representative A M x.2) (p,v) =
      Surface.preprocess A M v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> rfl
end Surface.Uniform

namespace Word.Uniform
omit [Primcodable P] [Primcodable Q] in
theorem sectorPreprocess_specialize (p : P) (v : Word.Sector S Γ Q) :
    sectorPreprocess A.blank (fun x : P × Control.Sector S Γ Q => Control.representative A M x.2) (p,v) =
      Word.sectorPreprocess A M v := by
  simp only [sectorPreprocess,Surface.Uniform.preprocess_specialize,Word.sectorPreprocess]

omit [Primcodable P] [Primcodable Q] in
theorem preprocess_specialize (p : P) (w : List (Word.Letter S Γ Q)) :
    preprocess A.blank (fun x : P × Control.Sector S Γ Q => Control.representative A M x.2) (p,w) =
      Word.preprocess A M w := by
  simp only [preprocess,sectorPreprocess_specialize,Word.preprocess]

omit [Primcodable P] [Primcodable Q] in
theorem partialNormal_specialize (p : P) (f : List S → Part (List S)) (w : List (Word.Letter S Γ Q)) :
    partialNormal A.blank (fun x : P × Control.Sector S Γ Q => Control.representative A M x.2)
      (fun x => f x.2) (p,w)=Word.partialNormal A M f w := by
  simp only [partialNormal,Word.partialNormal,preprocess_specialize]
end Word.Uniform

end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

section
open Compiler Compiler.Simulator Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec
variable {S T Γ Q : Type*} [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable T] [Primcodable Γ] [Primcodable Q]
variable (A : Alphabet S Γ) (M : Machine Q Γ) (p : S) (B : Alphabet T (Bool×Γ))

noncomputable def codedNormal (f : ℕ × List T → Part (List T)) :
    ℕ × List (Compiler.Word.Letter T (Bool×Γ) (Control Q)) → Part (List (Compiler.Word.Letter T (Bool×Γ) (Control Q))) :=
  Compiler.Word.Uniform.partialNormal B.blank (codedRepresentative A M p B) f

theorem partrec_codedNormal {f : ℕ × List T → Part (List T)} (hf : Partrec f) :
    Partrec (codedNormal A M p B f) :=
  Compiler.Word.Uniform.partrec_partialNormal B.blank _ (primrec_codedRepresentative A M p B) hf

omit [Primcodable T] [Primcodable Γ] in
theorem codedNormal_map (n : ℕ) (f : ℕ × List T → Part (List T))
    (w : List (Compiler.Word.Letter T (Bool×Γ) (State Q n))) :
    letI := finiteOrder (T := T) (Γ := Γ) (Q := Q) n
    codedNormal A M p B f (n,w.map (Compiler.Word.letterMap (encode n)))=
      (Compiler.Word.partialNormal B (machine A M p n) (fun u => f (n,u)) w).map
        (List.map (Compiler.Word.letterMap (encode n))) := by
  let : Primcodable (State Q n) := Effect.finitePrimcodable _
  let := finiteOrder (T := T) (Γ := Γ) (Q := Q) n
  have h := Compiler.Word.Uniform.partialNormal_map (P := Unit) (encode n) B.blank
    (fun x => Compiler.Control.representative B (machine A M p n) x.2)
    (fun x => codedRepresentative A M p B (n,x.2))
    (fun _ v => codedRepresentative_map A M p B n v)
    (encode_injective n) (fun x => f (n,x.2)) () w
  rw [Compiler.Word.Uniform.partialNormal_specialize B (machine A M p n) () (fun u => f (n,u)) w] at h
  exact h

end

open Compiler Compiler.HeadCodec ParameterMachine
open scoped Compiler.HeadCodec
variable {T Γ Q : Type*} [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q] [Primcodable Q]

noncomputable def letters (n : ℕ) : List (Word.Letter T (Bool×Γ) (Control Q)) :=
  [.zero,.enter,.leave] ++
  (Scan.finiteList (Word.Cell T (Bool×Γ))).map Path.Letter.left ++
  (Scan.finiteList (Word.Cell T (Bool×Γ))).map Path.Letter.right ++
  (surfaces n).map Path.Letter.head

omit [DecidableEq T] [DecidableEq Q] in
theorem primrec_surfaces : Primrec (surfaces (T := T) (Q := Q)) :=
  Primrec.list_append.comp (Primrec.const _) (Primrec.list_map primrec_heads
    (primrec_internal.comp Primrec.snd).to₂)

omit [DecidableEq T] [DecidableEq Γ] [DecidableEq Q] in
theorem primrec_letters : Primrec (letters (T := T) (Γ := Γ) (Q := Q)) :=
  Primrec.list_append.comp (Primrec.const _)
    (Primrec.list_map primrec_surfaces (Path.Uniform.primrec_head.comp Primrec.snd).to₂)

omit [DecidableEq T] [DecidableEq Q] [Primcodable Q] in
theorem mem_surfaces_iff (n : ℕ) (h : Surface.Head (Compiler.Control.Head T (Control Q))) :
    h∈surfaces n ↔ ∃ a : Surface.Head (Compiler.Control.Head T (State Q n)),
      Surface.headMap (controlMap (encode n)) a=h := by
  cases h with
  | raw =>
    constructor
    · intro _; exact ⟨.raw,rfl⟩
    · intro _; simp [surfaces]
  | pending =>
    constructor
    · intro _; exact ⟨.pending,rfl⟩
    · intro _; simp [surfaces]
  | cleanup =>
    constructor
    · intro _; exact ⟨.cleanup,rfl⟩
    · intro _; simp [surfaces]
  | internal q =>
    simp only [surfaces,List.mem_append,List.mem_cons,List.mem_map,
      Surface.Head.internal.injEq,reduceCtorEq,List.not_mem_nil,false_or,exists_eq_right,mem_heads_iff]
    constructor
    · rintro ⟨a,ha⟩; exact ⟨.internal a,congrArg Surface.Head.internal ha⟩
    · rintro ⟨a,ha⟩
      cases a with
      | internal b => exact ⟨b,Surface.Head.internal.inj ha⟩
      | _ => cases ha

omit [DecidableEq T] [DecidableEq Γ] [DecidableEq Q] [Primcodable Q] in
theorem mem_letters_iff (n : ℕ) (h : Word.Letter T (Bool×Γ) (Control Q)) :
    h∈letters n ↔ ∃ a : Word.Letter T (Bool×Γ) (State Q n), Word.letterMap (encode n) a=h := by
  constructor
  · intro hh
    cases h with
    | zero => exact ⟨.zero,rfl⟩
    | enter => exact ⟨.enter,rfl⟩
    | leave => exact ⟨.leave,rfl⟩
    | left c => exact ⟨.left c,rfl⟩
    | right c => exact ⟨.right c,rfl⟩
    | head h =>
      have hm : h∈surfaces n := by simpa [letters] using hh
      obtain ⟨a,rfl⟩ := (mem_surfaces_iff n h).mp hm
      exact ⟨.head a,rfl⟩
  · rintro ⟨a,rfl⟩
    cases a with
    | head a =>
      have hm := (mem_surfaces_iff n (Surface.headMap (controlMap (encode n)) a)).mpr ⟨a,rfl⟩
      simpa [letters,Word.letterMap,Word.headMap,Path.mapLetter] using hm
    | _ => simp [letters,Word.letterMap,Path.mapLetter,Scan.mem_finiteList]

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

variable [Primcodable S]

/-- The alphabet and all non-initializer control are now fixed once for the whole
    partial-recursive family. The only variable finite control is the explicit
    unary counter `Fin (n+2)`, not a choice of an evaluator for each index. -/
theorem exists_parameter_machine {S : Type} [Fintype S] [Primcodable S]
    {f : ℕ → List S → Part (List S)} (hf : Partrec₂ f) :
    ∃ (Γ Q : Type) (_ : Fintype Γ) (_ : Fintype Q) (_ : DecidableEq Γ)
      (A : Alphabet (S ⊕ Unit) Γ) (M : Machine Q Γ),
      (∀ g a, A.output g=some a → g=A.input a) ∧
      ∀ n, Compiler.Word.Realizes (restrict (alphabet A)) (machine A M (.inr ()) n) (f n) := by
  classical
  obtain ⟨Γ,Q,hΓ,hQ,A,M,hA,hM⟩ := WordEvaluator.exists_machine (partrec_universal hf)
  let : Fintype Γ := hΓ
  let : Fintype Q := hQ
  refine ⟨Γ,Q,hΓ,hQ,inferInstance,A,M,hA,?_⟩
  intro n
  exact restrict_realizes (alphabet A) (machine A M (.inr ()) n)
    (ParameterMachine.realizes A M (.inr ()) n hM) (fun w => universal_input f w n)

end FiniteAlgebraicEnvelopes.MachineRealization.UniversalMachine

end OAI
end

section
-- module Solutions.OAIQ066_SO.BooneHigman_MonoidAlgebras
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite compiler monoids, zero products, both F₂ algebras, and selector constructions.
-/

namespace FiniteAlgebraicEnvelopes
namespace Compiler.Word
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]
@[simp] theorem partialNormal_nil (f : List S → Part (List S)) : partialNormal A M f []=Part.some [] := by
  simp [partialNormal,preprocess,Path.prepare,Path.prepareChunks,RawRuns.partialSource,RawRuns.plan,RawRuns.execute]
end Compiler.Word

end FiniteAlgebraicEnvelopes

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryDescend
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology
noncomputable section
open Set Function
open scoped unitInterval

namespace PresentationGeometry.Cells

open Metric
open scoped unitInterval

variable {k d : ℕ}

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable (f : C(boundary k d, X))

theorem radialDisk_continuous : Continuous (fun p : I × Shell d => radialDisk p.1 p.2) := by
  apply Continuous.subtype_mk
  have ht : Continuous (fun p : I × Shell d => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hv : Continuous (fun p : I × Shell d => p.2.1) :=
    continuous_subtype_val.comp continuous_snd
  exact ((continuous_const.sub ht).add (ht.mul (hv.norm.inv₀
    (fun p => (shell_norm_pos p.2).ne')))).smul hv

omit [T2Space X] [CompactSpace X] in
theorem shellSlide_continuous : Continuous (fun p : I × ClosedCollarSpace f => shellSlide f p.1 p.2) := by
  apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
  have h₁ : Continuous (fun p : I × X => Adjunction.old f p.2) :=
    (Adjunction.continuous_old f).comp continuous_snd
  have h₂ : Continuous (fun p : I × (Fin k × Shell d) =>
      Adjunction.disk f (p.2.1, radialDisk p.1 p.2.2)) :=
    (Adjunction.continuous_disk f).comp
      ((continuous_fst.comp continuous_snd).prodMk
        (radialDisk_continuous.comp (continuous_fst.prodMk
          (continuous_snd.comp continuous_snd))))
  convert (h₁.sumElim h₂).comp Homeomorph.prodSumDistrib.continuous using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  rcases p with ⟨t, x | y⟩ <;> rfl

end PresentationGeometry.Cells

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SimplexHomotopy
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
namespace SimplexHomotopy
open Set Topology Metric
open scoped unitInterval
open SimplexBoundary
universe u
variable {Y : Type u} [TopologicalSpace Y]

theorem exists_prescribed {n : ℕ}
    (hπ : ∀ y : Y, Subsingleton (HomotopyGroup (Fin n) Y y))
    (f₀ f₁ : C(Simplex n,Y)) (h : C(I × Boundary n,Y))
    (h₀ : ∀ b, h (0,b) = f₀ b.1) (h₁ : ∀ b, h (1,b) = f₁ b.1) :
    ∃ F : C(I × Simplex n,Y), (∀ s, F (0,s) = f₀ s) ∧
      (∀ s, F (1,s) = f₁ s) ∧ ∀ t b, F (t,b.1) = h (t,b) := by
  obtain ⟨K,hK₀,hK₁,hKs⟩ := exists_disk_cylinder hπ (diskMap f₀) (diskMap f₁)
    (sideMap h) (sideMap_time f₀ h 0 h₀) (sideMap_time f₁ h 1 h₁)
  let F : C(I × Simplex n,Y) := K.comp
    ⟨fun z => (z.1,SimplexDisk.diskEquiv n z.2),
      continuous_fst.prodMk ((SimplexDisk.diskEquiv n).continuous.comp continuous_snd)⟩
  refine ⟨F,?_,?_,?_⟩
  · intro s
    change K (0,SimplexDisk.diskEquiv n s) = _
    rw [hK₀]
    exact congrArg f₀ ((SimplexDisk.diskEquiv n).symm_apply_apply s)
  · intro s
    change K (1,SimplexDisk.diskEquiv n s) = _
    rw [hK₁]
    exact congrArg f₁ ((SimplexDisk.diskEquiv n).symm_apply_apply s)
  · intro t b
    change K (t,SimplexDisk.diskEquiv n b.1) = _
    rw [boundary_compat_forward]
    change K (t,CWCylinder.boundaryDisk n (boundaryEquiv n b)) = _
    rw [hKs]
    exact congrArg h (Prod.ext rfl ((boundaryEquiv n).symm_apply_apply b))

end SimplexHomotopy

namespace SingularTightening
open Set Topology Metric
open scoped unitInterval
open SimplexBoundary
universe u
variable {Y : Type u} [TopologicalSpace Y]

variable {k m : ℕ} {y₀ : Y}

theorem exists_next (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (f : C(Simplex (m+1),Y)) :
    ∃ F : C(I × Simplex (m+1),Y), (∀ s, F (0,s) = f s) ∧
      (∀ t b, F (t,b.1) = boundaryHom S f (t,b)) ∧
      (m+1 < k → ∀ s, F (1,s) = y₀) := by
  by_cases hmk : m+1 < k
  · obtain ⟨F,h₀,h₁,hb⟩ := SimplexHomotopy.exists_prescribed (hπ _ hmk) f
      (ContinuousMap.const _ y₀) (boundaryHom S f) (boundaryHom_zero S f)
      (boundaryHom_one S (Nat.lt_of_le_of_lt (Nat.le_succ m) hmk) f)
    exact ⟨F,h₀,hb,fun _ => h₁⟩
  · obtain ⟨F,h₀,hb⟩ := SimplexHomotopy.exists_extension f (boundaryHom S f) (boundaryHom_zero S f)
    exact ⟨F,h₀,hb,fun h => (hmk h).elim⟩

def next (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (f : C(Simplex (m+1),Y)) : C(I × Simplex (m+1),Y) :=
  (exists_next hπ S f).choose

lemma next_zero (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (f : C(Simplex (m+1),Y)) (s : Simplex (m+1)) :
    next hπ S f (0,s) = f s := (exists_next hπ S f).choose_spec.1 s

lemma next_face (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (f : C(Simplex (m+1),Y)) (i : Fin (m+2)) t s :
    next hπ S f (t,SimplexBoundary.face i s) =
      S.hom m le_rfl (f.comp (SimplexBoundary.face i)) (t,s) := by
  have h := (exists_next hπ S f).choose_spec.2.1 t (faceQuot m (i,s))
  change next hπ S f (t,SimplexBoundary.face i s) = boundaryHom S f (t,faceQuot m (i,s)) at h
  rw [boundaryHom,glueHomotopies_face] at h
  exact h

lemma next_top (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (h : m+1 < k) (f : C(Simplex (m+1),Y)) s :
    next hπ S f (1,s) = y₀ := (exists_next hπ S f).choose_spec.2.2 h s

def extendHom (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (p : ℕ) (hp : p ≤ m+1) : C(Simplex p,Y) → C(I × Simplex p,Y) := by
  by_cases h : p ≤ m
  · exact S.hom p h
  · have he : p = m+1 := by omega
    subst p
    exact next hπ S

lemma extendHom_old (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (p : ℕ) (hp : p ≤ m) :
    extendHom hπ S p (hp.trans (Nat.le_succ m)) = S.hom p hp := by
  simp [extendHom,hp]

lemma extendHom_new (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) : extendHom hπ S (m+1) le_rfl = next hπ S := by
  simp [extendHom]

def extend (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) : System k (m+1) y₀ where
  hom := extendHom hπ S
  zero p hp f s := by
    by_cases h : p ≤ m
    · rw [extendHom_old hπ S p h]
      exact S.zero p h f s
    · have he : p = m+1 := by omega
      subst p
      rw [extendHom_new]
      exact next_zero hπ S f s
  face p hp f i t s := by
    by_cases h : p+1 ≤ m
    · rw [extendHom_old hπ S (p+1) h,extendHom_old hπ S p (by omega)]
      exact S.face p h f i t s
    · have he : p = m := by omega
      subst p
      rw [extendHom_new,extendHom_old hπ S m le_rfl]
      exact next_face hπ S f i t s
  top p hp hk f s := by
    by_cases h : p ≤ m
    · rw [extendHom_old hπ S p h]
      exact S.top p h hk f s
    · have he : p = m+1 := by omega
      subst p
      rw [extendHom_new]
      exact next_top hπ S hk f s

theorem exists_baseHom (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) (f : C(Simplex 0,Y)) :
    ∃ F : C(I × Simplex 0,Y), (∀ s, F (0,s) = f s) ∧
      (0 < k → ∀ s, F (1,s) = y₀) := by
  by_cases hk : 0 < k
  · let h : C(I × Boundary 0,Y) := ⟨fun b => isEmptyElim b.2,continuous_of_discreteTopology⟩
    obtain ⟨F,h₀,h₁,_⟩ := SimplexHomotopy.exists_prescribed (hπ 0 hk) f
      (ContinuousMap.const _ y₀) h (fun b => isEmptyElim b) (fun b => isEmptyElim b)
    exact ⟨F,h₀,fun _ => h₁⟩
  · exact ⟨f.comp ContinuousMap.snd,fun _ => rfl,fun h => (hk h).elim⟩

def baseHom (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) (f : C(Simplex 0,Y)) : C(I × Simplex 0,Y) :=
  (exists_baseHom hπ y₀ f).choose

def base (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) : System k 0 y₀ where
  hom p hp := by
    have he : p = 0 := Nat.eq_zero_of_le_zero hp
    subst p
    exact baseHom hπ y₀
  zero p hp f s := by
    obtain rfl : p = 0 := Nat.eq_zero_of_le_zero hp
    exact (exists_baseHom hπ y₀ f).choose_spec.1 s
  face p hp := by omega
  top p hp hk f s := by
    obtain rfl : p = 0 := Nat.eq_zero_of_le_zero hp
    exact (exists_baseHom hπ y₀ f).choose_spec.2 hk s

def system (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) : ∀ m, System k m y₀
  | 0 => base hπ y₀
  | m+1 => extend hπ (system hπ y₀ m)

def hom (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) (n : ℕ) : C(Simplex n,Y) → C(I × Simplex n,Y) :=
  (system hπ y₀ n).hom n le_rfl

lemma hom_zero (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) (n : ℕ) (f : C(Simplex n,Y)) s : hom hπ y₀ n f (0,s) = f s :=
  (system hπ y₀ n).zero n le_rfl f s

lemma hom_top (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) (n : ℕ) (hn : n < k) (f : C(Simplex n,Y)) s : hom hπ y₀ n f (1,s) = y₀ :=
  (system hπ y₀ n).top n le_rfl hn f s

lemma hom_face (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) (n : ℕ) (f : C(Simplex (n+1),Y)) (i : Fin (n+2)) t s :
    hom hπ y₀ (n+1) f (t,SimplexBoundary.face i s) =
      hom hπ y₀ n (f.comp (SimplexBoundary.face i)) (t,s) := by
  change (system hπ y₀ (n+1)).hom (n+1) le_rfl f _ = _
  rw [(system hπ y₀ (n+1)).face]
  change extendHom hπ (system hπ y₀ n) n _ _ _ = _
  rw [extendHom_old hπ _ n le_rfl]
  rfl

end SingularTightening

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularPrism
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open _root_.CategoryTheory AlgebraicTopology Limits

namespace SingularNormalization
section
open Set Topology _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial unitInterval
open SingularChains
variable {X : Type} [TopologicalSpace X]

open Coherent
def tightening {k : ℕ}
    (hπ : ∀ p < k, ∀ x : X, Subsingleton (HomotopyGroup (Fin p) X x)) (x₀ : X) :
    Coherent X where
  H := SingularTightening.hom hπ x₀
  zero := SingularTightening.hom_zero hπ x₀
  face := SingularTightening.hom_face hπ x₀

lemma tightening_top {k : ℕ}
    (hπ : ∀ p < k, ∀ x : X, Subsingleton (HomotopyGroup (Fin p) X x)) (x₀ : X)
    (n : ℕ) (hn : n < k) (f : C(Std n,X)) :
    (tightening hπ x₀).top n f = ContinuousMap.const _ x₀ := by
  ext s
  exact SingularTightening.hom_top hπ x₀ n hn f s

end

open _root_.CategoryTheory AlgebraicTopology Limits HomologicalComplex
open SingularChains
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

lemma homologyMap_const (n : ℕ) (hn : n ≠ 0) (y : Y) :
    homologyMap (map (ContinuousMap.const X y)) n = 0 := by
  let F := (singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)
  have hz : CategoryTheory.Limits.IsZero (F.obj (TopCat.of PUnit)) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of PUnit) hn
  change F.map (TopCat.ofHom (ContinuousMap.const X y)) = 0
  have he : TopCat.ofHom (ContinuousMap.const X y) =
      TopCat.ofHom (ContinuousMap.const X PUnit.unit) ≫
        TopCat.ofHom (ContinuousMap.const PUnit y) := rfl
  rw [he,F.map_comp,hz.eq_of_src (F.map (TopCat.ofHom (ContinuousMap.const PUnit y))) 0,
    comp_zero]

end SingularNormalization

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSphereCycle
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open _root_.CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval

namespace HurewiczNormalized
section
open Set Topology _root_.CategoryTheory AlgebraicTopology Limits HomologicalComplex
open SingularChains
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {n : ℕ} {x : X}

variable {k : ℕ}

def normalizedSimplex
    (hπ : ∀ p < k+1, ∀ z : X, Subsingleton (HomotopyGroup (Fin p) X z))
    (x₀ : X) (f : C(Std (k+1),X)) : BasedSimplex.Space (k+1) X x₀ :=
  ⟨(SingularNormalization.tightening hπ x₀).top (k+1) f,by
    rintro s ⟨i,hi⟩
    rw [← SimplexBoundary.face_drop i s hi]
    change ((SingularNormalization.tightening hπ x₀).top (k+1) f).comp (face i) _ = _
    rw [SingularNormalization.Coherent.top_face,
      SingularNormalization.tightening_top hπ x₀ k (by omega)]
    rfl⟩

end

open Set Topology _root_.CategoryTheory AlgebraicTopology Limits HomologicalComplex
open SingularChains

end HurewiczNormalized

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_BasedHorn
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open _root_.CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval
open Set Topology
open scoped unitInterval

namespace DuffyHurewicz
open Set Topology _root_.CategoryTheory AlgebraicTopology Limits HomologicalComplex
open SingularChains HurewiczNormalized DuffyBased
variable {X : Type} [TopologicalSpace X] {n : ℕ} {x : X}

lemma range_canonical_le_range (x : X) :
    Set.range (HurewiczConstruction.canonical (n+1) (X:=X) (x:=x)) ⊆
      Set.range (hom n x) := by
  rintro z ⟨p,rfl⟩
  induction p using Quotient.inductionOn with
  | h p =>
    let f := BasedSimplex.ofLoop p
    have hf : BasedSimplex.homotopyClass f = Quotient.mk _ p :=
      congrArg (Quotient.mk _) (BasedSimplex.loop_ofLoop p)
    refine ⟨Additive.ofMul (homotopyClass f),?_⟩
    rw [hom_class,← canonical_simplex,hf]

end DuffyHurewicz

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_BoundaryValueBoundarySplit
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open _root_.CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval
open Set Topology
open scoped unitInterval

namespace FixedSingularTightening
attribute [local instance] Classical.propDecidable
open Set Topology Metric
open scoped unitInterval
open SimplexBoundary
universe u
variable {Y : Type u} [TopologicalSpace Y]

structure System (k m : ℕ) (y₀ : Y) where
  hom : ∀ p, p ≤ m → C(Simplex p,Y) → C(I × Simplex p,Y)
  zero : ∀ p hp f s, hom p hp f (0,s) = f s
  face : ∀ p (hp : p+1 ≤ m) (f : C(Simplex (p+1),Y)) (i : Fin (p+2)) t s,
    hom (p+1) hp f (t,SimplexBoundary.face i s) =
      hom p (Nat.le_trans (Nat.le_succ p) hp) (f.comp (SimplexBoundary.face i)) (t,s)
  top : ∀ p hp, p < k → ∀ f s, hom p hp f (1,s) = y₀
  fixed : ∀ p hp, hom p hp (ContinuousMap.const _ y₀) = ContinuousMap.const _ y₀

variable {k m : ℕ} {y₀ : Y}

lemma boundary_compatible (S : System k m y₀) (f : C(Simplex (m+1),Y)) :
    ∀ t i j a b, SimplexBoundary.face i a = SimplexBoundary.face j b →
      S.hom m le_rfl (f.comp (SimplexBoundary.face i)) (t,a) =
        S.hom m le_rfl (f.comp (SimplexBoundary.face j)) (t,b) := by
  intro t
  apply compatible_faces
  intro p hp i j s
  subst m
  change S.hom (p+1) _ _ (t,SimplexBoundary.face (j.predAbove i) s) =
    S.hom (p+1) _ _ (t,SimplexBoundary.face j s)
  rw [S.face p,S.face p]
  congr 2
  apply ContinuousMap.ext
  intro a
  exact congrArg f (face_face i j a)

def boundaryHom (S : System k m y₀) (f : C(Simplex (m+1),Y)) :
    C(I × Boundary (m+1),Y) :=
  glueHomotopies (fun i => S.hom m le_rfl (f.comp (SimplexBoundary.face i)))
    (boundary_compatible S f)

lemma boundaryHom_zero (S : System k m y₀) (f : C(Simplex (m+1),Y)) (b : Boundary (m+1)) :
    boundaryHom S f (0,b) = f b.1 := by
  obtain ⟨⟨i,s⟩,rfl⟩ := faceQuot_surjective m b
  rw [boundaryHom,glueHomotopies_face,S.zero]
  rfl

lemma boundaryHom_one (S : System k m y₀) (hmk : m < k) (f : C(Simplex (m+1),Y))
    (b : Boundary (m+1)) : boundaryHom S f (1,b) = y₀ := by
  obtain ⟨⟨i,s⟩,rfl⟩ := faceQuot_surjective m b
  rw [boundaryHom,glueHomotopies_face,S.top m le_rfl hmk]

theorem exists_next (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (f : C(Simplex (m+1),Y)) :
    ∃ F : C(I × Simplex (m+1),Y), (∀ s, F (0,s) = f s) ∧
      (∀ t b, F (t,b.1) = boundaryHom S f (t,b)) ∧
      (m+1 < k → ∀ s, F (1,s) = y₀) := by
  by_cases hmk : m+1 < k
  · obtain ⟨F,h₀,h₁,hb⟩ := SimplexHomotopy.exists_prescribed (hπ _ hmk) f
      (ContinuousMap.const _ y₀) (boundaryHom S f) (boundaryHom_zero S f)
      (boundaryHom_one S (Nat.lt_of_le_of_lt (Nat.le_succ m) hmk) f)
    exact ⟨F,h₀,hb,fun _ => h₁⟩
  · obtain ⟨F,h₀,hb⟩ := SimplexHomotopy.exists_extension f (boundaryHom S f) (boundaryHom_zero S f)
    exact ⟨F,h₀,hb,fun h => (hmk h).elim⟩

def next (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (f : C(Simplex (m+1),Y)) : C(I × Simplex (m+1),Y) :=
  if f = ContinuousMap.const _ y₀ then ContinuousMap.const _ y₀ else (exists_next hπ S f).choose

lemma next_zero (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (f : C(Simplex (m+1),Y)) (s : Simplex (m+1)) :
    next hπ S f (0,s) = f s := by
  by_cases hf : f = ContinuousMap.const _ y₀
  · simp [next,hf]
  · simpa only [next,ite_eq_right hf] using (exists_next hπ S f).choose_spec.1 s

lemma next_face (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (f : C(Simplex (m+1),Y)) (i : Fin (m+2)) t s :
    next hπ S f (t,SimplexBoundary.face i s) =
      S.hom m le_rfl (f.comp (SimplexBoundary.face i)) (t,s) := by
  by_cases hf : f = ContinuousMap.const _ y₀
  · subst f
    simpa only [next,ite_true,ContinuousMap.const_comp,ContinuousMap.const_apply] using
      (congrArg (fun a : C(I × Simplex m,Y) => a (t,s)) (S.fixed m le_rfl)).symm
  have h := (exists_next hπ S f).choose_spec.2.1 t (faceQuot m (i,s))
  rw [show next hπ S f = (exists_next hπ S f).choose by simp only [next,ite_eq_right hf]]
  change (exists_next hπ S f).choose (t,SimplexBoundary.face i s) = boundaryHom S f (t,faceQuot m (i,s)) at h
  rw [show boundaryHom S f (t,faceQuot m (i,s)) = S.hom m le_rfl (f.comp (SimplexBoundary.face i)) (t,s) from glueHomotopies_face _ _ _ _ _] at h
  exact h

lemma next_top (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (h : m+1 < k) (f : C(Simplex (m+1),Y)) s :
    next hπ S f (1,s) = y₀ := by
  by_cases hf : f = ContinuousMap.const _ y₀
  · simp [next,hf]
  · simpa only [next,ite_eq_right hf] using (exists_next hπ S f).choose_spec.2.2 h s

lemma next_fixed (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) : next hπ S (ContinuousMap.const _ y₀) = ContinuousMap.const _ y₀ := by
  simp [next]

def extendHom (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (p : ℕ) (hp : p ≤ m+1) : C(Simplex p,Y) → C(I × Simplex p,Y) := by
  by_cases h : p ≤ m
  · exact S.hom p h
  · have he : p = m+1 := by omega
    subst p
    exact next hπ S

lemma extendHom_old (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) (p : ℕ) (hp : p ≤ m) :
    extendHom hπ S p (hp.trans (Nat.le_succ m)) = S.hom p hp := by
  simp [extendHom,hp]

lemma extendHom_new (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) : extendHom hπ S (m+1) le_rfl = next hπ S := by
  simp [extendHom]

def extend (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (S : System k m y₀) : System k (m+1) y₀ where
  hom := extendHom hπ S
  zero p hp f s := by
    by_cases h : p ≤ m
    · rw [extendHom_old hπ S p h]
      exact S.zero p h f s
    · have he : p = m+1 := by omega
      subst p
      rw [extendHom_new]
      exact next_zero hπ S f s
  face p hp f i t s := by
    by_cases h : p+1 ≤ m
    · rw [extendHom_old hπ S (p+1) h,extendHom_old hπ S p (by omega)]
      exact S.face p h f i t s
    · have he : p = m := by omega
      subst p
      rw [extendHom_new,extendHom_old hπ S m le_rfl]
      exact next_face hπ S f i t s
  top p hp hk f s := by
    by_cases h : p ≤ m
    · rw [extendHom_old hπ S p h]
      exact S.top p h hk f s
    · have he : p = m+1 := by omega
      subst p
      rw [extendHom_new]
      exact next_top hπ S hk f s
  fixed p hp := by
    by_cases h : p ≤ m
    · rw [extendHom_old hπ S p h]
      exact S.fixed p h
    · have he : p = m+1 := by omega
      subst p
      rw [extendHom_new]
      exact next_fixed hπ S

theorem exists_baseHom (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) (f : C(Simplex 0,Y)) :
    ∃ F : C(I × Simplex 0,Y), (∀ s, F (0,s) = f s) ∧
      (0 < k → ∀ s, F (1,s) = y₀) := by
  by_cases hk : 0 < k
  · let h : C(I × Boundary 0,Y) := ⟨fun b => isEmptyElim b.2,continuous_of_discreteTopology⟩
    obtain ⟨F,h₀,h₁,_⟩ := SimplexHomotopy.exists_prescribed (hπ 0 hk) f
      (ContinuousMap.const _ y₀) h (fun b => isEmptyElim b) (fun b => isEmptyElim b)
    exact ⟨F,h₀,fun _ => h₁⟩
  · exact ⟨f.comp ContinuousMap.snd,fun _ => rfl,fun h => (hk h).elim⟩

def baseHom (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) (f : C(Simplex 0,Y)) : C(I × Simplex 0,Y) :=
  if f = ContinuousMap.const _ y₀ then ContinuousMap.const _ y₀ else (exists_baseHom hπ y₀ f).choose

def base (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) : System k 0 y₀ where
  hom p hp := by
    have he : p = 0 := Nat.eq_zero_of_le_zero hp
    subst p
    exact baseHom hπ y₀
  zero p hp f s := by
    obtain rfl : p = 0 := Nat.eq_zero_of_le_zero hp
    by_cases hf : f = ContinuousMap.const _ y₀
    · simp only [baseHom,hf,ite_true,ContinuousMap.const_apply]
    · simpa only [baseHom,ite_eq_right hf] using (exists_baseHom hπ y₀ f).choose_spec.1 s
  face p hp := by omega
  top p hp hk f s := by
    obtain rfl : p = 0 := Nat.eq_zero_of_le_zero hp
    by_cases hf : f = ContinuousMap.const _ y₀
    · simp only [baseHom,ite_eq_left hf,ContinuousMap.const_apply]
    · simpa only [baseHom,ite_eq_right hf] using (exists_baseHom hπ y₀ f).choose_spec.2 hk s
  fixed p hp := by
    obtain rfl : p = 0 := Nat.eq_zero_of_le_zero hp
    simp only [baseHom,ite_true]

def system (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) : ∀ m, System k m y₀
  | 0 => base hπ y₀
  | m+1 => extend hπ (system hπ y₀ m)

def hom (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) (n : ℕ) : C(Simplex n,Y) → C(I × Simplex n,Y) :=
  (system hπ y₀ n).hom n le_rfl

lemma hom_zero (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) (n : ℕ) (f : C(Simplex n,Y)) s : hom hπ y₀ n f (0,s) = f s :=
  (system hπ y₀ n).zero n le_rfl f s

lemma hom_top (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) (n : ℕ) (hn : n < k) (f : C(Simplex n,Y)) s : hom hπ y₀ n f (1,s) = y₀ :=
  (system hπ y₀ n).top n le_rfl hn f s

lemma hom_face (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) (n : ℕ) (f : C(Simplex (n+1),Y)) (i : Fin (n+2)) t s :
    hom hπ y₀ (n+1) f (t,SimplexBoundary.face i s) =
      hom hπ y₀ n (f.comp (SimplexBoundary.face i)) (t,s) := by
  change (system hπ y₀ (n+1)).hom (n+1) le_rfl f _ = _
  rw [(system hπ y₀ (n+1)).face]
  change extendHom hπ (system hπ y₀ n) n _ _ _ = _
  rw [extendHom_old hπ _ n le_rfl]
  rfl

lemma hom_fixed (hπ : ∀ p < k, ∀ y : Y, Subsingleton (HomotopyGroup (Fin p) Y y))
    (y₀ : Y) (n : ℕ) : hom hπ y₀ n (ContinuousMap.const _ y₀) = ContinuousMap.const _ y₀ :=
  (system hπ y₀ n).fixed n le_rfl

end FixedSingularTightening

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_HurewiczInverse
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open _root_.CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval
open Set Topology
open scoped unitInterval
namespace HurewiczInverse
open Set Topology _root_.CategoryTheory AlgebraicTopology Limits HomologicalComplex
open SingularChains SingularNormalization.Coherent
open scoped unitInterval
variable {X : Type} [TopologicalSpace X] {n : ℕ} {x : X}

variable (hπ : ∀ p < n+2, ∀ z : X, Subsingleton (HomotopyGroup (Fin p) X z)) (x : X)

def coherent : SingularNormalization.Coherent X where
  H := FixedSingularTightening.hom hπ x
  zero := FixedSingularTightening.hom_zero hπ x
  face := FixedSingularTightening.hom_face hπ x

lemma coherent_top (p : ℕ) (hp : p < n+2) (f : C(Std p,X)) :
    (coherent hπ x).top p f = ContinuousMap.const _ x := by
  ext s
  exact FixedSingularTightening.hom_top hπ x p hp f s

lemma coherent_fixed (p : ℕ) :
    (coherent hπ x).H p (ContinuousMap.const _ x) = ContinuousMap.const _ x :=
  FixedSingularTightening.hom_fixed hπ x p

def normalize (f : C(Std (n+2),X)) : BasedSimplex.Space (n+2) X x :=
  ⟨(coherent hπ x).top (n+2) f,by
    rintro s ⟨i,hi⟩
    rw [← SimplexBoundary.face_drop i s hi]
    change ((coherent hπ x).top (n+2) f).comp (face i) _ = _
    rw [top_face,coherent_top hπ x (n+1) (by omega)]
    rfl⟩

lemma normalize_const : normalize hπ x (ContinuousMap.const _ x) = BasedSimplex.const _ x := by
  apply Subtype.ext
  ext s
  change (coherent hπ x).H (n+2) (ContinuousMap.const _ x) (1,s) = x
  rw [coherent_fixed]
  rfl

lemma hom_relative (f : BasedSimplex.Space (n+2) X x) :
    Nonempty (f.1.HomotopyRel (normalize hπ x f.1).1 (BasedSimplex.Boundary (n+2))) := by
  refine ⟨{ toHomotopy := ?_, prop' := ?_ }⟩
  · exact { toContinuousMap := (coherent hπ x).H (n+2) f.1
            map_zero_left := (coherent hπ x).zero (n+2) f.1
            map_one_left := fun _ => rfl }
  · intro t s hs
    change (coherent hπ x).H (n+2) f.1 (t,s) = f.1 s
    rw [f.2 s hs]
    obtain ⟨i,hi⟩ := hs
    rw [← SimplexBoundary.face_drop i s hi]
    exact ((coherent hπ x).face (n+1) f.1 i t (SimplexBoundary.drop i s hi)).trans (by
      rw [HurewiczNormalized.based_face,coherent_fixed]
      rfl)

lemma normalize_class (f : BasedSimplex.Space (n+2) X x) :
    DuffyBased.homotopyClass (normalize hπ x f.1) = DuffyBased.homotopyClass f :=
  ((DuffyBased.class_eq_iff _ _).mpr (hom_relative hπ x f)).symm

lemma top_double (f : C(Std (n+3),X)) :
    ∀ s ∈ DuffyTriangle.DoubleBoundary (n+3), (coherent hπ x).top (n+3) f s = x := by
  rintro s ⟨i,j,hij,hi,hj⟩
  obtain ⟨j',hj'⟩ := Fin.exists_succAbove_eq hij.symm
  subst j
  let a := SimplexBoundary.drop i s hi
  have ha : a.1 j' = 0 := hj
  rw [← SimplexBoundary.face_drop i s hi]
  change ((coherent hπ x).top (n+3) f).comp (face i) a = x
  rw [top_face,← SimplexBoundary.face_drop j' a ha]
  change ((coherent hπ x).top (n+2) (f.comp (face i))).comp (face j') _ = x
  rw [top_face,coherent_top hπ x (n+1) (by omega)]
  rfl

lemma top_basedFace (f : C(Std (n+3),X)) (i : Fin (n+4)) :
    SimplexAddition.basedFace ((coherent hπ x).top (n+3) f) (top_double hπ x f) i =
      normalize hπ x (f.comp (face i)) := by
  apply Subtype.ext
  exact top_face (coherent hπ x) (n+2) f i

abbrev A := BoundaryValue.A n X x

def chainValue : (chains X).X (n+2) ⟶ ModuleCat.of ℤ (A (n:=n) (x:=x)) :=
  desc (fun f => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (BoundaryValue.value (normalize hπ x f))))

lemma generator_chainValue (f : C(Std (n+2),X)) :
    generator f ≫ chainValue hπ x =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (BoundaryValue.value (normalize hπ x f))) :=
  generator_desc _ _

lemma boundary_chainValue : (chains X).d (n+3) (n+2) ≫ chainValue hπ x = 0 := by
  apply SingularChains.hom_ext
  intro f
  rw [← Category.assoc,generator_boundary]
  simp only [Preadditive.sum_comp,Preadditive.zsmul_comp,generator_chainValue,comp_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  have h := BoundaryValue.boundary_zero ((coherent hπ x).top (n+3) f) (top_double hπ x f)
  simp only [BoundaryValue.boundary,top_basedFace] at h
  simpa using h

def inverse : (chains X).homology (n+2) ⟶ ModuleCat.of ℤ (A (n:=n) (x:=x)) :=
  ((chains X).sc (n+2)).descHomology (((chains X).sc (n+2)).iCycles ≫ chainValue hπ x) (by
    erw [← Category.assoc,ShortComplex.toCycles_i]
    change (chains X).d _ (n+2) ≫ chainValue hπ x = 0
    have hd (i : ℕ) : (chains X).d i (n+2) ≫ chainValue hπ x = 0 := by
      by_cases hi : i = n+3
      · subst i
        exact boundary_chainValue hπ x
      · rw [(chains X).shape i (n+2) (by change ¬ n+2+1 = i; omega)]
        exact zero_comp
    exact hd _)

lemma homologyπ_inverse : (chains X).homologyπ (n+2) ≫ inverse hπ x =
    (chains X).iCycles (n+2) ≫ chainValue hπ x :=
  ShortComplex.π_descHomology _ _ _

lemma cycleClassHom_inverse (f : BasedSimplex.Space (n+2) X x) :
    HurewiczNormalized.cycleClassHom (HurewiczNormalized.cycle f) (HurewiczNormalized.cycle_d f) ≫
      inverse hπ x = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (BoundaryValue.value f)) := by
  rw [HurewiczNormalized.cycleClassHom,Category.assoc,homologyπ_inverse,
    ← Category.assoc,liftCycles_i,HurewiczNormalized.cycle,Preadditive.sub_comp,
    generator_chainValue,generator_chainValue,normalize_const]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (1:ℤ) • BoundaryValue.value (normalize hπ x f.1) -
    (1:ℤ) • BoundaryValue.value (BasedSimplex.const (n+2) x) = (1:ℤ) • BoundaryValue.value f
  rw [one_smul,one_smul,one_smul,BoundaryValue.value_const,sub_zero]
  exact congrArg Additive.ofMul (normalize_class hπ x f)

lemma inverse_homologyClass (f : BasedSimplex.Space (n+2) X x) :
    inverse hπ x (HurewiczNormalized.homologyClass f) = BoundaryValue.value f := by
  have h := congrArg (fun z : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ (A (n:=n) (x:=x)) => z 1)
    (cycleClassHom_inverse hπ x f)
  change inverse hπ x (HurewiczNormalized.homologyClass f) = (1:ℤ) • BoundaryValue.value f at h
  simpa only [one_smul] using h

lemma leftInverse : Function.LeftInverse (inverse hπ x) (DuffyHurewicz.hom (n+1) x) := by
  intro p
  obtain ⟨q,hq⟩ := Quotient.exists_rep p.toMul
  let f := DuffyBased.ofLoop q
  have hf : DuffyBased.homotopyClass f = p.toMul := by
    exact (congrArg (Quotient.mk _) (DuffyBased.loop_ofLoop q)).trans hq
  have hp : Additive.ofMul (DuffyBased.homotopyClass f) = p := congrArg Additive.ofMul hf
  rw [← hp,DuffyHurewicz.hom_class,inverse_homologyClass]
  rfl

end HurewiczInverse

namespace DuffyHurewicz
open SingularChains
variable {X : Type} [TopologicalSpace X] {n : ℕ}

theorem injective
    (hπ : ∀ p < n+2, ∀ z : X, Subsingleton (HomotopyGroup (Fin p) X z)) (x : X) :
    Function.Injective (hom (n+1) x) :=
  (HurewiczInverse.leftInverse hπ x).injective

end DuffyHurewicz

namespace HurewiczConstruction
section
open SingularChains SphereQuotient _root_.CategoryTheory HomologicalComplex
variable {X : Type} [TopologicalSpace X] {n : ℕ}

variable {G : Type} [Group G] [MulAction G X] [ContinuousConstSMul G X]

def homologyRep (j : ℕ) : Representation ℤ G (integralHomology j X) where
  toFun g := pushforward j (actionMap g)
  map_one' := by
    rw [actionMap_one]
    exact congrArg ModuleCat.Hom.hom
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) j).obj (ModuleCat.of ℤ ℤ)).map_id _)
  map_mul' g h := by rw [actionMap_mul,pushforward_comp]; rfl

abbrev homologyModule (j : ℕ) := (homologyRep (G:=G) (X:=X) j).asModule

def sphereModuleClass (j : ℕ) (f : C(Boundary (j+1),X)) : homologyModule (G:=G) (X:=X) j :=
  (homologyRep (G:=G) (X:=X) j).asModuleEquiv.symm
    (pushforward j f (SingularSphereCycle.fundamentalClass j))

end

open CategoryTheory.Limits SingularChains
end HurewiczConstruction

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PartialResolutionPartialCyclesFg
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CWEquivariant
section
attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension CWCellular _root_.CategoryTheory HomologicalComplex ProductCriterion

attribute [instance] AddCommGroup.toIntModule
end

attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension CWCellular _root_.CategoryTheory HomologicalComplex ProductCriterion
variable {G X : Type} [Group G] [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
  [∀ n, MulAction G (RelCWComplex.cell (univ : Set X) n)]
variable (hc : ∀ (g : G) n (i : RelCWComplex.cell (univ : Set X) n) (v : Disk n),
  g • RelCWComplex.map n i v = RelCWComplex.map n (g • i) v)

def wholeRep (j : ℕ) : Rep ℤ G :=
  Rep.of ({ toFun := fun g => (homologyMap (SingularChains.map (onSpace (X:=X) g)) j).hom
            map_one' := by
              have he : onSpace (X:=X) (1:G) = ContinuousMap.id _ := by
                ext x; simp [onSpace]
              rw [he,SingularChains.map_id,homologyMap_id]
              rfl
            map_mul' := by
              intro g h
              have he : onSpace (X:=X) (g*h) = (onSpace g).comp (onSpace h) := by
                ext x; simp [onSpace,mul_smul]
              rw [he,SingularChains.map_comp,homologyMap_comp]
              rfl } : Representation ℤ G ((SingularChains.chains (univ : Set X)).homology j))

attribute [instance] AddCommGroup.toIntModule
end CWEquivariant

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularAction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
namespace SingularAction
attribute [-instance] AddCommGroup.toIntModule
open Set Topology _root_.CategoryTheory HomologicalComplex ProductCriterion
variable {G X : Type} [Group G] [TopologicalSpace X]
  [MulAction G X] [ContinuousConstSMul G X]

def rep (j : ℕ) : Rep ℤ G :=
  Rep.of ({ toFun := fun g => (homologyMap (SingularChains.map (actionMap (X:=X) g)) j).hom
            map_one' := by
              have he : actionMap (X:=X) (1:G) = ContinuousMap.id _ := by
                ext x; simp [actionMap]
              rw [he,SingularChains.map_id,homologyMap_id]
              rfl
            map_mul' := by
              intro g h
              have he : actionMap (X:=X) (g*h) = (actionMap g).comp (actionMap h) := by
                ext x; simp [actionMap,mul_smul]
              rw [he,SingularChains.map_comp,homologyMap_comp]
              rfl } : Representation ℤ G ((SingularChains.chains X).homology j))

lemma val_surjective (j : ℕ) :
    Function.Surjective (homologyMap (SingularChains.map (val (X:=X))) j) := by
  intro x
  refine ⟨homologyMap (SingularChains.map (ofVal (X:=X))) j x,?_⟩
  change (homologyMap (SingularChains.map (ofVal (X:=X))) j ≫
    homologyMap (SingularChains.map (val (X:=X))) j) x = x
  rw [← homologyMap_comp,← SingularChains.map_comp]
  have he : (val (X:=X)).comp ofVal = ContinuousMap.id X := rfl
  rw [he,SingularChains.map_id,homologyMap_id]
  rfl

def fromUniv (j : ℕ) : CWEquivariant.wholeRep (G:=G) (X:=X) j ⟶ rep (G:=G) (X:=X) j :=
  Rep.ofHom ((homologyMap (SingularChains.map (val (X:=X))) j).hom.intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g x
    change (homologyMap (SingularChains.map (CWEquivariant.onSpace g)) j ≫
      homologyMap (SingularChains.map val) j) x =
      (homologyMap (SingularChains.map val) j ≫ homologyMap (SingularChains.map (actionMap g)) j) x
    rw [← homologyMap_comp,← homologyMap_comp,← SingularChains.map_comp,← SingularChains.map_comp]
    rfl))

lemma finite_of_univ (j : ℕ)
    [Module.Finite (MonoidAlgebra ℤ G) (CWEquivariant.wholeRep (G:=G) (X:=X) j).ρ.asModule] :
    Module.Finite (MonoidAlgebra ℤ G) (rep (G:=G) (X:=X) j).ρ.asModule :=
  Module.Finite.of_surjective (moduleMap (fromUniv j)) (val_surjective j)

lemma univ_homology_zero (j : ℕ)
    (hz : CategoryTheory.Limits.IsZero ((SingularChains.chains X).homology j)) :
    CategoryTheory.Limits.IsZero ((SingularChains.chains (univ : Set X)).homology j) := by
  have hinj : Function.Injective (homologyMap (SingularChains.map (val (X:=X))) j) := by
    intro x y h
    have he : (ofVal (X:=X)).comp val = ContinuousMap.id _ := by ext x; rfl
    have hr : homologyMap (SingularChains.map (val (X:=X))) j ≫
      homologyMap (SingularChains.map ofVal) j = 𝟙 _ := by
      rw [← homologyMap_comp,← SingularChains.map_comp,he,SingularChains.map_id,homologyMap_id]
    have hh := congrArg (fun z => homologyMap (SingularChains.map (ofVal (X:=X))) j z) h
    change (homologyMap (SingularChains.map val) j ≫ homologyMap (SingularChains.map ofVal) j) x =
      (homologyMap (SingularChains.map val) j ≫ homologyMap (SingularChains.map ofVal) j) y at hh
    simpa only [hr,ConcreteCategory.id_apply] using hh
  let := ModuleCat.isZero_iff_subsingleton.mp hz
  let := hinj.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

attribute [instance] AddCommGroup.toIntModule
end SingularAction

end

namespace EquivariantCoverCells
attribute [-instance] AddCommGroup.toIntModule
open Set Topology _root_.CategoryTheory CWEquivariant CWExtension CoveringCW

attribute [instance] AddCommGroup.toIntModule
end EquivariantCoverCells

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CoreDeck
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoreDeck
attribute [-instance] AddCommGroup.toIntModule
open Set Topology _root_.CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [instance] AddCommGroup.toIntModule
end CoreDeck

namespace PresentationGeometry.Rose
section
open scoped unitInterval

variable {k : ℕ}

def edgeMap (i : Fin k) : C(Cells.Disk 1, Space k) :=
  ⟨fun v => Adjunction.disk (attaching k) (i,v),
    (Adjunction.continuous_disk (attaching k)).comp (continuous_const.prodMk continuous_id)⟩

def edgeLeft : Cells.Disk 1 := ⟨fun _ => -1, by simp [Metric.mem_closedBall]⟩
def edgeRight : Cells.Disk 1 := ⟨fun _ => 1, by simp [Metric.mem_closedBall]⟩

@[simp] theorem edgeMap_left (i : Fin k) : edgeMap i edgeLeft = basepoint k := by
  exact Adjunction.disk_boundary (attaching k) ⟨(i,edgeLeft), by simp [Cells.boundary, edgeLeft]⟩

@[simp] theorem edgeMap_right (i : Fin k) : edgeMap i edgeRight = basepoint k := by
  exact Adjunction.disk_boundary (attaching k) ⟨(i,edgeRight), by simp [Cells.boundary, edgeRight]⟩

instance disk_contractible (d : ℕ) : ContractibleSpace (Cells.Disk d) :=
  (convex_closedBall (0 : Fin d → ℝ) 1).contractibleSpace
    ⟨0, Metric.mem_closedBall_self (by norm_num)⟩

def edgeInterval (u v : Cells.Disk 1) : Path u v where
  toFun t := ⟨Path.segment u.1 v.1 t,
    (convex_closedBall (0 : Fin 1 → ℝ) 1).segment_subset u.property v.property
      ((Path.range_segment u.1 v.1) ▸ (show Path.segment u.1 v.1 t ∈ Set.range (Path.segment u.1 v.1) from ⟨t,rfl⟩))⟩
  continuous_toFun := (Path.segment u.1 v.1).continuous.subtype_mk _
  source' := Subtype.ext (Path.segment u.1 v.1).source
  target' := Subtype.ext (Path.segment u.1 v.1).target

def edgeSpoke (i : Fin k) (v : Cells.Disk 1) : Path (basepoint k) (edgeMap i v) :=
  ((edgeInterval edgeLeft v).map (edgeMap i).continuous).cast (edgeMap_left i).symm rfl

@[simp] theorem edgeSpoke_left (i : Fin k) :
    (edgeSpoke i edgeLeft).cast rfl (edgeMap_left i).symm = Path.refl (basepoint k) := by
  have h : edgeInterval edgeLeft edgeLeft = Path.refl edgeLeft := by
    ext t j
    simp [edgeInterval]
  ext t
  change edgeMap i (edgeInterval edgeLeft edgeLeft t) = basepoint k
  rw [h]
  exact edgeMap_left i

@[simp] theorem edgeSpoke_right (i : Fin k) :
    (edgeSpoke i edgeRight).cast rfl (edgeMap_right i).symm = generatorLoop i := by
  ext t
  change Adjunction.disk (attaching k)
    (i, ⟨Path.segment edgeLeft.1 edgeRight.1 t, _⟩) =
    Cells.characteristic (attaching k) i (Path.segment _ _ t)
  exact (Cells.characteristic_on_disk (attaching k) i _).symm

def pointCode (a : Space k) : Point ⊕ (Fin k × Cells.Disk 1) :=
  Quotient.lift (Adjunction.normalize (attaching k)) (fun _ _ h => h) a

@[simp] theorem pointCode_base : pointCode (basepoint k) = Sum.inl PUnit.unit := rfl

@[simp] theorem pointCode_edge (i : Fin k) (v : Cells.Disk 1)
    (hv : ‖v.1‖ < 1) : pointCode (edgeMap i v) = Sum.inr (i,v) := by
  exact Adjunction.normalize_inr_notMem (attaching k) (i,v)
    (by simpa [Cells.boundary, mem_sphere_zero_iff_norm] using (ne_of_lt hv))

theorem pointCode_cases (a : Space k) :
    (pointCode a = Sum.inl PUnit.unit ∧ a = basepoint k) ∨
    ∃ (i : Fin k) (v : Cells.Disk 1), ‖v.1‖ < 1 ∧
      pointCode a = Sum.inr (i,v) ∧ a = edgeMap i v := by
  obtain ⟨x | ⟨i,v⟩, rfl⟩ := Quotient.mk_surjective a
  · exact Or.inl ⟨rfl, rfl⟩
  · by_cases h : (i,v) ∈ Cells.boundary k 1
    · left
      have he := Adjunction.disk_boundary (attaching k) ⟨(i,v), h⟩
      change Adjunction.disk (attaching k) (i,v) = basepoint k at he
      rw [show Quotient.mk (Adjunction.relation (attaching k)) (Sum.inr (i,v)) =
        basepoint k from he]
      exact ⟨rfl,rfl⟩
    · have hv : ‖v.1‖ < 1 := lt_of_le_of_ne (mem_closedBall_zero_iff.mp v.property)
        (by simpa [Cells.boundary, mem_sphere_zero_iff_norm] using h)
      exact Or.inr ⟨i,v,hv,pointCode_edge i v hv,rfl⟩

def edgeData (a : {a : Space k // a ≠ basepoint k}) : Fin k × Cells.Disk 1 :=
  let h := (pointCode_cases a.1).resolve_left (fun h => a.2 h.2)
  (h.choose, h.choose_spec.choose)

theorem edgeData_spec (a : {a : Space k // a ≠ basepoint k}) :
    ‖(edgeData a).2.1‖ < 1 ∧ pointCode a.1 = Sum.inr (edgeData a) ∧
      a.1 = edgeMap (edgeData a).1 (edgeData a).2 := by
  exact ((pointCode_cases a.1).resolve_left (fun h => a.2 h.2)).choose_spec.choose_spec

def spoke (a : Space k) : Path (basepoint k) a := by
  classical
  exact if ha : a = basepoint k then (Path.refl (basepoint k)).cast rfl ha
    else (edgeSpoke (edgeData ⟨a,ha⟩).1 (edgeData ⟨a,ha⟩).2).cast rfl
      (edgeData_spec ⟨a,ha⟩).2.2

@[simp] theorem spoke_base : spoke (basepoint k) = Path.refl (basepoint k) := by
  simp [spoke]

theorem spoke_edge (i : Fin k) (v : Cells.Disk 1) (hv : ‖v.1‖ < 1) :
    spoke (edgeMap i v) = edgeSpoke i v := by
  classical
  have hn : edgeMap i v ≠ basepoint k := by
    intro he
    have := congrArg pointCode he
    rw [pointCode_edge i v hv, pointCode_base] at this
    cases this
  have he : edgeData ⟨edgeMap i v,hn⟩ = (i,v) := by
    have hc := (edgeData_spec ⟨edgeMap i v,hn⟩).2.1
    rw [pointCode_edge i v hv] at hc
    exact (Sum.inr.inj hc).symm
  simp only [spoke, dite_eq_right hn]
  ext t
  change edgeMap (edgeData ⟨edgeMap i v,hn⟩).1
    (edgeInterval edgeLeft (edgeData ⟨edgeMap i v,hn⟩).2 t) = edgeMap i (edgeInterval edgeLeft v t)
  rw [he]

end

open scoped unitInterval
open PresentationVanKampen

variable {k : ℕ}

theorem basedPathClass_edge {u v : Cells.Disk 1} (i : Fin k)
    (hu : ‖u.1‖ < 1) (hv : ‖v.1‖ < 1) (q : Path u v) :
    basedPathClass (basepoint k) spoke (q.map (edgeMap i).continuous) = 1 := by
  have h := (SimplyConnectedSpace.paths_homotopic
    ((edgeInterval edgeLeft u).trans q) (edgeInterval edgeLeft v)).map (edgeMap i)
  have h' : ((edgeSpoke i u).trans (q.map (edgeMap i).continuous)).Homotopic
      (edgeSpoke i v) := by
    simpa only [Path.map_trans, Path.cast_trans, Path.cast_rfl_rfl, edgeSpoke] using
      h.pathCast (edgeMap_left i).symm rfl
  have he : (Path.Homotopic.Quotient.mk ((edgeSpoke i u).trans
    (q.map (edgeMap i).continuous))) = Path.Homotopic.Quotient.mk (edgeSpoke i v) :=
      Quotient.sound h'
  simp only [basedPathClass, spoke_edge i u hu, spoke_edge i v hv,
    ← Path.Homotopic.Quotient.trans_assoc, ← Path.Homotopic.Quotient.mk_trans]
  rw [he, Path.Homotopic.Quotient.trans_symm]
  rfl

def openEdgeLift (i : Fin k) : C(Cells.cellInterior (attaching k) i, Cells.Disk 1) :=
  ⟨fun x => Cells.interiorInDisk
    ((Cells.characteristic_isOpenEmbedding (attaching k) i).isEmbedding.toHomeomorph.symm x),
    Cells.interiorInDisk_isOpenEmbedding.continuous.comp
      (Cells.characteristic_isOpenEmbedding (attaching k) i).isEmbedding.toHomeomorph.symm.continuous⟩

@[simp] theorem edgeMap_openEdgeLift (i : Fin k)
    (a : Cells.cellInterior (attaching k) i) : edgeMap i (openEdgeLift i a) = a.1 := by
  have h := congrArg Subtype.val
    ((Cells.characteristic_isOpenEmbedding (attaching k) i).isEmbedding.toHomeomorph.apply_symm_apply a)
  change Adjunction.disk (attaching k) (i, openEdgeLift i a) = a.1
  rw [← Cells.characteristic_on_disk (attaching k) i]
  exact h

theorem norm_openEdgeLift (i : Fin k) (a : Cells.cellInterior (attaching k) i) :
    ‖(openEdgeLift i a).1‖ < 1 :=
  mem_ball_zero_iff.mp
    ((Cells.characteristic_isOpenEmbedding (attaching k) i).isEmbedding.toHomeomorph.symm a).property

theorem basedPathClass_interior {a c : Space k} (p : Path a c) (i : Fin k)
    (hp : Set.range p ⊆ Cells.cellInterior (attaching k) i) :
    basedPathClass (basepoint k) spoke p = 1 := by
  let a' : Cells.cellInterior (attaching k) i := ⟨a, hp p.source_mem_range⟩
  let c' : Cells.cellInterior (attaching k) i := ⟨c, hp p.target_mem_range⟩
  let q := (pathIn p hp).map (openEdgeLift i).continuous
  have h := basedPathClass_edge i (norm_openEdgeLift i a') (norm_openEdgeLift i c') q
  have ha := edgeMap_openEdgeLift i a'
  have hc := edgeMap_openEdgeLift i c'
  have hcast : ∀ {a c a' c' : Space k} (q : Path a c) (ha : a' = a) (hc : c' = c),
      basedPathClass (basepoint k) spoke (q.cast ha hc) =
        basedPathClass (basepoint k) spoke q := by
    intro a c a' c' q ha hc
    subst a'; subst c'
    rfl
  rw [← hcast _ ha.symm hc.symm] at h
  have he : (q.map (edgeMap i).continuous).cast ha.symm hc.symm = p := by
    ext t
    exact edgeMap_openEdgeLift i ((pathIn p hp) t)
  rwa [he] at h

end PresentationGeometry.Rose

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationVanKampenRectanglePaths
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PresentationGeometry.Cells
open scoped unitInterval
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable {k d : ℕ} (f : C(boundary k d, X))

@[simp] theorem collarToShell_disk (i : Fin k) (v : Shell d)
    (hv : (1 / 2 : ℝ) < ‖v.1‖) :
    collarToShell f ⟨Adjunction.disk f (i,shellInDisk v),
      (mem_collar_disk_iff f i (shellInDisk v)).mpr hv⟩ =
        Adjunction.disk (shellAttach f) (i,v) := by
  apply shellInclude_injective f
  simp

end PresentationGeometry.Cells

namespace PresentationGeometry.Rose
section
open scoped unitInterval
open PresentationVanKampen
variable {k : ℕ}

def outward (a : Cells.collar (attaching k)) : Path a.1 (basepoint k) where
  toFun t := Cells.shellSlide (attaching k) t (Cells.collarToShell (attaching k) a)
  continuous_toFun := (Cells.shellSlide_continuous (attaching k)).comp
    (continuous_id.prodMk continuous_const)
  source' := by simp
  target' := by rw [Cells.shellSlide_one]; rfl

@[simp] theorem outward_base :
    outward ⟨basepoint k, Cells.mem_collar_old (attaching k) PUnit.unit⟩ =
      Path.refl (basepoint k) := by
  ext t
  change Cells.shellSlide (attaching k) t
    (Cells.collarToShell (attaching k) ⟨Adjunction.old (attaching k) PUnit.unit,_⟩) = _
  simp [basepoint, Path.refl]
  rfl

theorem collar_path_homotopic {a c : Space k} (p : Path a c)
    (hp : Set.range p ⊆ Cells.collar (attaching k)) :
    (p.trans (outward ⟨c,hp p.target_mem_range⟩)).Homotopic
      (outward ⟨a,hp p.source_mem_range⟩) := by
  let H : C(I × I, Space k) :=
    ⟨fun z => Cells.shellSlide (attaching k) z.1
      (Cells.collarToShell (attaching k) ((pathIn p hp) z.2)),
      (Cells.shellSlide_continuous (attaching k)).comp
        (continuous_fst.prodMk ((Cells.collarToShell (attaching k)).continuous.comp
          ((pathIn p hp).continuous.comp continuous_snd)))⟩
  have h := rectangle_paths p (outward ⟨c,hp p.target_mem_range⟩)
    (outward ⟨a,hp p.source_mem_range⟩) (Path.refl (basepoint k)) H
    (fun t => by simp [H, pathIn])
    (fun t => by
      change Cells.shellSlide (attaching k) t
        (Cells.collarToShell (attaching k) ((pathIn p hp) 1)) = _
      rw [(pathIn p hp).target]
      rfl)
    (fun t => by
      change Cells.shellSlide (attaching k) t
        (Cells.collarToShell (attaching k) ((pathIn p hp) 0)) = _
      rw [(pathIn p hp).source]
      rfl)
    (fun t => by
      change Cells.shellSlide (attaching k) 1 _ = _
      rw [Cells.shellSlide_one]
      rfl)
  exact h.trans (Path.Homotopic.trans_refl _)

theorem radialDisk_one_cases (v : Cells.Shell 1) :
    Cells.radialDisk 1 v = edgeLeft ∨ Cells.radialDisk 1 v = edgeRight := by
  have hn : ‖(Cells.radialDisk 1 v).1‖ = 1 := by
    change ‖Cells.radialVector 1 v‖ = 1
    rw [Cells.norm_radialVector]
    simp
  have he : |(Cells.radialDisk 1 v).1 0| = 1 := by
    have hv : (Cells.radialDisk 1 v).1 = fun _ : Fin 1 => (Cells.radialDisk 1 v).1 0 := by
      funext j
      rw [show j = 0 from Subsingleton.elim _ _]
    rw [hv] at hn
    simpa only [pi_norm_const, Real.norm_eq_abs] using hn
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp he with he | he
  · right
    apply Subtype.ext
    funext j
    fin_cases j
    exact he
  · left
    apply Subtype.ext
    funext j
    fin_cases j
    exact he

theorem spoke_outward_mem (a : Cells.collar (attaching k)) :
    Path.Homotopic.Quotient.mk ((spoke a.1).trans (outward a)) ∈
      (freeToFundamental k).range := by
  rcases pointCode_cases a.1 with ⟨_,he⟩ | ⟨i,v,hv,_,he⟩
  · have ha : a = ⟨basepoint k, Cells.mem_collar_old (attaching k) PUnit.unit⟩ :=
      Subtype.ext he
    subst a
    simp only [spoke_base, outward_base]
    have hh := (Path.Homotopic.refl_trans (Path.refl (basepoint k)))
    have hq : Path.Homotopic.Quotient.mk ((Path.refl (basepoint k)).trans (Path.refl _)) =
        Path.Homotopic.Quotient.refl (basepoint k) :=
      Quotient.sound hh
    rw [hq]
    exact (freeToFundamental k).range.one_mem
  · have hlow : (1 / 2 : ℝ) < ‖v.1‖ := by
      have := a.property
      rw [he] at this
      exact (Cells.mem_collar_disk_iff (attaching k) i v).mp this
    let v' : Cells.Shell 1 := ⟨v.1, le_of_lt hlow, mem_closedBall_zero_iff.mp v.property⟩
    let a' : Cells.collar (attaching k) := ⟨edgeMap i v,
      (Cells.mem_collar_disk_iff (attaching k) i v).mpr hlow⟩
    have ha : a = a' := Subtype.ext he
    subst a
    let q : Path v (Cells.radialDisk 1 v') :=
      ⟨⟨fun t => Cells.radialDisk t v',
        Cells.radialDisk_continuous.comp (continuous_id.prodMk continuous_const)⟩,
        Cells.radialDisk_zero v', rfl⟩
    have hend : edgeMap i (Cells.radialDisk 1 v') = basepoint k := by
      rcases radialDisk_one_cases v' with hr | hr <;> rw [hr] <;> simp
    have hout : (q.map (edgeMap i).continuous).cast rfl hend.symm = outward a' := by
      ext t
      change edgeMap i (Cells.radialDisk t v') =
        Cells.shellSlide (attaching k) t (Cells.collarToShell (attaching k) a')
      have hc : Cells.collarToShell (attaching k) a' =
          Adjunction.disk (Cells.shellAttach (attaching k)) (i,v') :=
        Cells.collarToShell_disk (attaching k) i v' hlow
      rw [hc, Cells.shellSlide_disk]
      rfl
    have h := (SimplyConnectedSpace.paths_homotopic
      ((edgeInterval edgeLeft v).trans q)
      (edgeInterval edgeLeft (Cells.radialDisk 1 v'))).map (edgeMap i) |>.pathCast
        (edgeMap_left i).symm hend.symm
    have h' : ((spoke a'.1).trans (outward a')).Homotopic
        ((edgeSpoke i (Cells.radialDisk 1 v')).cast rfl hend.symm) := by
      change ((spoke (edgeMap i v)).trans (outward a')).Homotopic
        (((edgeInterval edgeLeft (Cells.radialDisk 1 v')).map (edgeMap i).continuous).cast
          (edgeMap_left i).symm hend.symm)
      rw [spoke_edge i v hv]
      simpa only [Path.map_trans, Path.cast_trans, Path.cast_rfl_rfl, hout, edgeSpoke] using h
    have hh : Path.Homotopic.Quotient.mk ((spoke a'.1).trans (outward a')) =
        Path.Homotopic.Quotient.mk
          ((edgeSpoke i (Cells.radialDisk 1 v')).cast rfl hend.symm) := Quotient.sound h'
    rw [hh]
    rcases radialDisk_one_cases v' with hr | hr
    · have he : (edgeSpoke i (Cells.radialDisk 1 v')).cast rfl hend.symm =
          Path.refl (basepoint k) := by
        ext t
        change edgeMap i (edgeInterval edgeLeft (Cells.radialDisk 1 v') t) = basepoint k
        rw [hr]
        exact congrArg (fun p : Path (basepoint k) (basepoint k) => p t) (edgeSpoke_left i)
      rw [he]
      exact (freeToFundamental k).range.one_mem
    · have he : (edgeSpoke i (Cells.radialDisk 1 v')).cast rfl hend.symm =
          generatorLoop i := by
        ext t
        change edgeMap i (edgeInterval edgeLeft (Cells.radialDisk 1 v') t) = generatorLoop i t
        rw [hr]
        exact congrArg (fun p : Path (basepoint k) (basepoint k) => p t) (edgeSpoke_right i)
      rw [he]
      refine ⟨FreeGroup.of i, ?_⟩
      simp [freeToFundamental]

end

open scoped unitInterval
open PresentationVanKampen
variable {k : ℕ}

theorem basedPathClass_collar_mem {a c : Space k} (p : Path a c)
    (hp : Set.range p ⊆ Cells.collar (attaching k)) :
    basedPathClass (basepoint k) spoke p ∈ (freeToFundamental k).range := by
  have hout : ∀ x : Cells.collar (attaching k),
      basedPathClass (basepoint k) spoke (outward x) ∈ (freeToFundamental k).range := by
    intro x
    have he : basedPathClass (basepoint k) spoke (outward x) =
        Path.Homotopic.Quotient.mk ((spoke x.1).trans (outward x)) := by
      simp only [basedPathClass, spoke_base, Path.Homotopic.Quotient.mk_trans,
        Path.Homotopic.Quotient.mk_refl]
      have hr : (Path.Homotopic.Quotient.refl (basepoint k)).symm =
          Path.Homotopic.Quotient.refl (basepoint k) := rfl
      rw [hr, Path.Homotopic.Quotient.trans_refl]
    rw [he]
    exact spoke_outward_mem x
  have he := basedPathClass_homotopic (basepoint k) spoke _ _ (collar_path_homotopic p hp)
  rw [basedPathClass_trans] at he
  have hmem := (freeToFundamental k).range.mul_mem
    ((freeToFundamental k).range.inv_mem (hout ⟨c,hp p.target_mem_range⟩))
    (hout ⟨a,hp p.source_mem_range⟩)
  rwa [← he, inv_mul_cancel_left] at hmem

theorem freeToFundamental_surjective (k : ℕ) :
    Function.Surjective (freeToFundamental k) := by
  let U : Option (Fin k) → Set (Space k) := fun i =>
    match i with
    | none => Cells.collar (attaching k)
    | some i => Cells.cellInterior (attaching k) i
  have hU : ∀ i, IsOpen (U i) := by
    intro i
    cases i with
    | none => exact Cells.collar_isOpen (attaching k)
    | some i => exact Cells.cellInterior_isOpen (attaching k) i
  have hcover : Set.univ ⊆ ⋃ i, U i := by
    intro x hx
    have h : x ∈ Cells.collar (attaching k) ∪ ⋃ i, Cells.cellInterior (attaching k) i := by
      rw [Cells.collar_union_interiors]
      trivial
    rcases h with h | h
    · exact Set.mem_iUnion.mpr ⟨none,h⟩
    · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp h
      exact Set.mem_iUnion.mpr ⟨some i,hi⟩
  have htop := subgroup_eq_top_of_open_cover U hU hcover (basepoint k) spoke
    (by rw [spoke_base]) (freeToFundamental k).range (by
      intro a c p i hp
      cases i with
      | none => exact basedPathClass_collar_mem p hp
      | some i =>
        rw [basedPathClass_interior p i hp]
        exact (freeToFundamental k).range.one_mem)
  intro g
  have hg : g ∈ (freeToFundamental k).range := by rw [htop]; trivial
  exact hg

end PresentationGeometry.Rose

namespace PresentationGeometry.Rose
section
open scoped unitInterval
open Set
variable {k : ℕ}

def coverSet : Option (Fin k) → Set (Space k)
  | none => Cells.collar (attaching k)
  | some i => Cells.cellInterior (attaching k) i

theorem coverSet_isOpen (i : Option (Fin k)) : IsOpen (coverSet i) := by
  cases i with
  | none => exact Cells.collar_isOpen (attaching k)
  | some i => exact Cells.cellInterior_isOpen (attaching k) i

theorem mem_coverSet (x : Space k) : ∃ i, x ∈ coverSet i := by
  have hx : x ∈ Cells.collar (attaching k) ∪ ⋃ i, Cells.cellInterior (attaching k) i := by
    rw [Cells.collar_union_interiors]; trivial
  rcases hx with h | h
  · exact ⟨none,h⟩
  · obtain ⟨i,hi⟩ := mem_iUnion.mp h
    exact ⟨some i,hi⟩

theorem overlap_coord_ne_zero (i : Fin k)
    (x : (coverSet (none : Option (Fin k)) ∩ coverSet (some i) : Set (Space k))) :
    (openEdgeLift i ⟨x.1,x.property.2⟩).1 0 ≠ 0 := by
  let v := openEdgeLift i ⟨x.1,x.property.2⟩
  have hv : (1 / 2 : ℝ) < ‖v.1‖ := by
    apply (Cells.mem_collar_disk_iff (attaching k) i v).mp
    change edgeMap i v ∈ Cells.collar (attaching k)
    rw [edgeMap_openEdgeLift]
    exact x.property.1
  intro he
  have hz : v.1 = 0 := by
    funext j
    rw [show j = 0 from Subsingleton.elim _ _]
    exact he
  rw [hz, norm_zero] at hv
  norm_num at hv

variable {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]

noncomputable def potential (g : Fin k → Q) : Option (Fin k) → Space k → Q := by
  classical
  exact fun
    | none, _ => 1
    | some i, x => if h : x ∈ Cells.cellInterior (attaching k) i then
        if 0 < (openEdgeLift i ⟨x,h⟩).1 0 then (g i)⁻¹ else 1 else 1

omit [TopologicalSpace Q] [DiscreteTopology Q] in
@[simp] theorem potential_none (g : Fin k → Q) (x : Space k) :
    potential g none x = 1 := rfl

omit [DiscreteTopology Q] in
theorem potential_continuous_overlap (g : Fin k → Q) (i : Fin k) :
    Continuous fun x : (coverSet (none : Option (Fin k)) ∩ coverSet (some i) : Set (Space k)) =>
      potential g (some i) x.1 := by
  classical
  let c : (coverSet (none : Option (Fin k)) ∩ coverSet (some i) : Set (Space k)) → ℝ :=
    fun x => (openEdgeLift i ⟨x.1,x.property.2⟩).1 0
  have hc : Continuous c :=
    (continuous_apply 0).comp (continuous_subtype_val.comp ((openEdgeLift i).continuous.comp
      (continuous_subtype_val.subtype_mk (fun x => x.property.2))))
  have hset : {x | 0 < c x} = {x | 0 ≤ c x} := by
    ext x
    exact lt_iff_le_and_ne.trans
      ⟨fun h => h.1, fun h => ⟨h, (overlap_coord_ne_zero i x).symm⟩⟩
  have hcl : IsClopen {x | 0 < c x} := ⟨by rw [hset]; exact isClosed_le continuous_const hc,
    isOpen_lt continuous_const hc⟩
  have hh : Continuous fun x => if 0 < c x then (g i)⁻¹ else (1 : Q) :=
    Continuous.if (by intro x hx; rw [hcl.frontier_eq] at hx; exact hx.elim)
      continuous_const continuous_const
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  have hx : x.1 ∈ Cells.cellInterior (attaching k) i := x.property.2
  simp only [potential, dite_eq_left hx]
  rfl

noncomputable def transition (g : Fin k → Q) (i j : Option (Fin k))
    (x : Space k) (q : Q) : Q := potential g j x * (potential g i x)⁻¹ * q

theorem continuousOn_transition (g : Fin k → Q) (i j : Option (Fin k)) :
    ContinuousOn (fun p : Space k × Q => transition g i j p.1 p.2)
      ((coverSet i ∩ coverSet j) ×ˢ univ) := by
  classical
  by_cases hij : i = j
  · subst j
    simpa [transition] using (continuous_snd : Continuous (Prod.snd : Space k × Q → Q)).continuousOn
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j =>
      rw [continuousOn_iff_continuous_domRestrict]
      have hc : Continuous (fun p : (coverSet (none : Option (Fin k)) ∩ coverSet (some j)) ×ˢ
          (univ : Set Q) =>
          potential g (some j) p.1.1) :=
        (potential_continuous_overlap g j).comp
          ((continuous_fst.comp continuous_subtype_val).subtype_mk (fun p => p.property.1))
      convert hc.mul (continuous_snd.comp continuous_subtype_val) using 1
      all_goals try with_reducible_and_instances rfl
      funext p
      simp [transition, Set.domRestrict, potential_none]
  | some i =>
    cases j with
    | none =>
      rw [inter_comm]
      rw [continuousOn_iff_continuous_domRestrict]
      have hc : Continuous (fun p : (coverSet (none : Option (Fin k)) ∩ coverSet (some i)) ×ˢ
          (univ : Set Q) =>
          potential g (some i) p.1.1) :=
        (potential_continuous_overlap g i).comp
          ((continuous_fst.comp continuous_subtype_val).subtype_mk (fun p => p.property.1))
      convert hc.inv.mul (continuous_snd.comp continuous_subtype_val) using 1
      all_goals try with_reducible_and_instances rfl
      funext p
      simp [transition, Set.domRestrict, potential_none]
    | some j =>
      have hd := Cells.cellInterior_pairwiseDisjoint (attaching k) (by
        intro h; apply hij; exact congrArg some h : i ≠ j)
      have he : coverSet (some i) ∩ coverSet (some j) = ∅ := hd.inter_eq
      rw [he, empty_prod]
      exact continuousOn_empty _

noncomputable def coveringCore (g : Fin k → Q) : FiberBundleCore (Option (Fin k)) (Space k) Q where
  baseSet := coverSet
  isOpen_baseSet := coverSet_isOpen
  indexAt x := (mem_coverSet x).choose
  mem_baseSet_at x := (mem_coverSet x).choose_spec
  coordChange := transition g
  coordChange_self := by intros; simp [transition]
  continuousOn_coordChange := continuousOn_transition g
  coordChange_comp := by intros; simp only [transition]; group

end

open scoped unitInterval
open Set DiscreteCoverCharts
variable {k : ℕ}

theorem edgeMap_mem_interior (i : Fin k) (v : Cells.Disk 1) (hv : ‖v.1‖ < 1) :
    edgeMap i v ∈ Cells.cellInterior (attaching k) i := by
  refine ⟨⟨v.1,mem_ball_zero_iff.mpr hv⟩,?_⟩
  exact Cells.characteristic_on_disk (attaching k) i v

@[simp] theorem openEdgeLift_edgeMap (i : Fin k) (v : Cells.Disk 1) (hv : ‖v.1‖ < 1) :
    openEdgeLift i ⟨edgeMap i v, edgeMap_mem_interior i v hv⟩ = v := by
  have h := edgeMap_openEdgeLift i ⟨edgeMap i v, edgeMap_mem_interior i v hv⟩
  have hn : (i,v) ∉ Cells.boundary k 1 := by
    intro hm
    have he : ‖v.1‖ = 1 := by
      simpa only [Cells.boundary, mem_ofPred_eq, mem_sphere_zero_iff_norm] using hm
    linarith
  exact congrArg Prod.snd ((Adjunction.disk_eq_disk_of_notMem (attaching k) hn).mp h.symm) |>.symm

def edgeNegative : Cells.Disk 1 := ⟨fun _ => -(3/4 : ℝ), by norm_num [Metric.mem_closedBall, dist_pi_def]⟩
def edgePositive : Cells.Disk 1 := ⟨fun _ => (3/4 : ℝ), by norm_num [Metric.mem_closedBall, dist_pi_def]⟩

@[simp] theorem norm_edgeNegative : ‖(edgeNegative : Cells.Disk 1).1‖ = (3/4 : ℝ) := by
  norm_num [edgeNegative, pi_norm_const]
@[simp] theorem norm_edgePositive : ‖(edgePositive : Cells.Disk 1).1‖ = (3/4 : ℝ) := by
  norm_num [edgePositive, pi_norm_const]

def edgeFirst (i : Fin k) : Path (basepoint k) (edgeMap i edgeNegative) :=
  ((edgeInterval edgeLeft edgeNegative).map (edgeMap i).continuous).cast (edgeMap_left i).symm rfl

def edgeMiddle (i : Fin k) : Path (edgeMap i edgeNegative) (edgeMap i edgePositive) :=
  (edgeInterval edgeNegative edgePositive).map (edgeMap i).continuous

def edgeLast (i : Fin k) : Path (edgeMap i edgePositive) (basepoint k) :=
  ((edgeInterval edgePositive edgeRight).map (edgeMap i).continuous).cast rfl (edgeMap_right i).symm

theorem edgeFirst_collar (i : Fin k) : Set.range (edgeFirst i) ⊆ coverSet none := by
  rintro _ ⟨t,rfl⟩
  apply (Cells.mem_collar_disk_iff (attaching k) i (edgeInterval edgeLeft edgeNegative t)).mpr
  have hn : |(edgeInterval edgeLeft edgeNegative t).1 0| ≤
      ‖(edgeInterval edgeLeft edgeNegative t).1‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (edgeInterval edgeLeft edgeNegative t).1 0
  have hv : (edgeInterval edgeLeft edgeNegative t).1 0 = -(1 : ℝ) + (t : ℝ) / 4 := by
    change (Path.segment (fun _ : Fin 1 => (-1 : ℝ)) (fun _ => -(3/4 : ℝ)) t) 0 = _
    simp only [Path.segment_apply, AffineMap.lineMap_apply, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, vadd_eq_add, vsub_eq_sub, smul_eq_mul]
    ring
  rw [hv] at hn
  have ht := t.property
  have hn' := neg_le_abs (-(1 : ℝ) + (t : ℝ) / 4)
  linarith [t.property.1, t.property.2]

theorem edgeMiddle_interior (i : Fin k) : Set.range (edgeMiddle i) ⊆ coverSet (some i) := by
  rintro _ ⟨t,rfl⟩
  apply edgeMap_mem_interior
  have h := (convex_ball (0 : Fin 1 → ℝ) 1).segment_subset
    (mem_ball_zero_iff.mpr (show ‖(edgeNegative : Cells.Disk 1).1‖ < 1 by norm_num))
    (mem_ball_zero_iff.mpr (show ‖(edgePositive : Cells.Disk 1).1‖ < 1 by norm_num))
    ((Path.range_segment edgeNegative.1 edgePositive.1) ▸
      (show Path.segment edgeNegative.1 edgePositive.1 t ∈ Set.range (Path.segment edgeNegative.1 edgePositive.1) from ⟨t,rfl⟩))
  exact mem_ball_zero_iff.mp h

theorem edgeLast_collar (i : Fin k) : Set.range (edgeLast i) ⊆ coverSet none := by
  rintro _ ⟨t,rfl⟩
  apply (Cells.mem_collar_disk_iff (attaching k) i (edgeInterval edgePositive edgeRight t)).mpr
  have hn : |(edgeInterval edgePositive edgeRight t).1 0| ≤
      ‖(edgeInterval edgePositive edgeRight t).1‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (edgeInterval edgePositive edgeRight t).1 0
  have hv : (edgeInterval edgePositive edgeRight t).1 0 = (3/4 : ℝ) + (t : ℝ) / 4 := by
    change (Path.segment (fun _ : Fin 1 => (3/4 : ℝ)) (fun _ => (1 : ℝ)) t) 0 = _
    simp only [Path.segment_apply, AffineMap.lineMap_apply, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, vadd_eq_add, vsub_eq_sub, smul_eq_mul]
    ring
  rw [hv] at hn
  have ht := t.property
  have hn' := le_abs_self ((3/4 : ℝ) + (t : ℝ) / 4)
  linarith [t.property.1, t.property.2]

theorem edge_parts_homotopic (i : Fin k) :
    ((edgeFirst i).trans ((edgeMiddle i).trans (edgeLast i))).Homotopic (generatorLoop i) := by
  have h := (SimplyConnectedSpace.paths_homotopic
    ((edgeInterval edgeLeft edgeNegative).trans
      ((edgeInterval edgeNegative edgePositive).trans (edgeInterval edgePositive edgeRight)))
    (edgeInterval edgeLeft edgeRight)).map (edgeMap i) |>.pathCast
      (edgeMap_left i).symm (edgeMap_right i).symm
  have he : ((edgeInterval edgeLeft edgeRight).map (edgeMap i).continuous).cast
      (edgeMap_left i).symm (edgeMap_right i).symm = generatorLoop i := by
    calc
      _ = (edgeSpoke i edgeRight).cast rfl (edgeMap_right i).symm := by ext t; rfl
      _ = generatorLoop i := edgeSpoke_right i
  rw [he] at h
  simpa only [Path.map_trans, Path.cast_trans, Path.cast_rfl_rfl, edgeFirst, edgeMiddle,
    edgeLast] using h

variable {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]

omit [TopologicalSpace Q] [DiscreteTopology Q] in
@[simp] theorem potential_negative (g : Fin k → Q) (i : Fin k) :
    potential g (some i) (edgeMap i edgeNegative) = 1 := by
  have hv : ‖(edgeNegative : Cells.Disk 1).1‖ < 1 := by norm_num
  simp only [potential, dite_eq_left (edgeMap_mem_interior i edgeNegative hv)]
  norm_num [edgeNegative]

omit [TopologicalSpace Q] [DiscreteTopology Q] in
@[simp] theorem potential_positive (g : Fin k → Q) (i : Fin k) :
    potential g (some i) (edgeMap i edgePositive) = (g i)⁻¹ := by
  have hv : ‖(edgePositive : Cells.Disk 1).1‖ < 1 := by norm_num
  simp only [potential, dite_eq_left (edgeMap_mem_interior i edgePositive hv)]
  norm_num [edgePositive]

theorem monodromy_generator (g : Fin k → Q) (i : Fin k) (q : Q) :
    (covering (coveringCore g)).monodromy (Path.Homotopic.Quotient.mk (generatorLoop i))
      ⟨point (coveringCore g) none (basepoint k) q,rfl⟩ =
      ⟨point (coveringCore g) none (basepoint k) (g i * q),rfl⟩ := by
  let Z := coveringCore g
  have hn : point Z none (edgeMap i edgeNegative) q = point Z (some i) (edgeMap i edgeNegative) q := by
    have h := point_change Z none (some i)
      (edgeFirst_collar i (edgeFirst i).target_mem_range)
      (edgeMiddle_interior i (edgeMiddle i).source_mem_range) q
    simpa only [Z, coveringCore, transition, potential_none, potential_negative, inv_one,
      one_mul] using h
  have hp : point Z (some i) (edgeMap i edgePositive) q =
      point Z none (edgeMap i edgePositive) (g i * q) := by
    have h := point_change Z (some i) none
      (edgeMiddle_interior i (edgeMiddle i).target_mem_range)
      (edgeLast_collar i (edgeLast i).source_mem_range) q
    simpa only [Z, coveringCore, transition, potential_none, potential_positive, inv_inv,
      one_mul] using h
  have he : Path.Homotopic.Quotient.mk (generatorLoop i) =
      (Path.Homotopic.Quotient.mk (edgeFirst i)).trans
        ((Path.Homotopic.Quotient.mk (edgeMiddle i)).trans
          (Path.Homotopic.Quotient.mk (edgeLast i))) := by
    simp only [← Path.Homotopic.Quotient.mk_trans]
    exact Quotient.sound (edge_parts_homotopic i).symm
  rw [he]
  rw [IsCoveringMap.monodromy_trans_apply, monodromy_chartPath Z none _ (edgeFirst_collar i)]
  have hn' : (⟨point Z none (edgeMap i edgeNegative) q,rfl⟩ : Z.proj ⁻¹' {edgeMap i edgeNegative}) =
      ⟨point Z (some i) (edgeMap i edgeNegative) q,rfl⟩ := Subtype.ext hn
  rw [hn', IsCoveringMap.monodromy_trans_apply,
    monodromy_chartPath Z (some i) _ (edgeMiddle_interior i)]
  have hp' : (⟨point Z (some i) (edgeMap i edgePositive) q,rfl⟩ : Z.proj ⁻¹' {edgeMap i edgePositive}) =
      ⟨point Z none (edgeMap i edgePositive) (g i * q),rfl⟩ := Subtype.ext hp
  rw [hp', monodromy_chartPath Z none _ (edgeLast_collar i)]

end PresentationGeometry.Rose

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryRose
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PresentationGeometry.Rose
section
open Set DiscreteCoverCharts
variable {k : ℕ}
variable {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]

noncomputable def monodromyRepresentation (g : Fin k → Q) :
    FundamentalGroup (Space k) (basepoint k) →* Equiv.Perm Q :=
  ((fiberEquiv (coveringCore g) none (basepoint k)
    (Cells.mem_collar_old (attaching k) PUnit.unit)).symm.permCongrHom.toMonoidHom).comp
      ((covering (coveringCore g)).monodromyPerm (basepoint k))

@[simp] theorem monodromyRepresentation_generator (g : Fin k → Q) (i : Fin k) (q : Q) :
    monodromyRepresentation g (freeToFundamental k (FreeGroup.of i)) q = g i * q := by
  let e := fiberEquiv (coveringCore g) none (basepoint k)
    (Cells.mem_collar_old (attaching k) PUnit.unit)
  have hg : freeToFundamental k (FreeGroup.of i) =
      (Path.Homotopic.Quotient.mk (generatorLoop i) : FundamentalGroup (Space k) (basepoint k)) := by
    exact FreeGroup.lift_apply_of (β := FundamentalGroup (Space k) (basepoint k))
      (f := fun i : Fin k =>
      (Path.Homotopic.Quotient.mk (generatorLoop i) : FundamentalGroup (Space k) (basepoint k)))
  rw [hg]
  change e.symm ((covering (coveringCore g)).monodromy
    (Path.Homotopic.Quotient.mk (generatorLoop i)) (e q)) = _
  have h : (covering (coveringCore g)).monodromy
      (Path.Homotopic.Quotient.mk (generatorLoop i)) (e q) = e (g i * q) :=
    monodromy_generator g i q
  rw [h, e.symm_apply_apply]

theorem monodromyRepresentation_comp (g : Fin k → Q) :
    (monodromyRepresentation g).comp (freeToFundamental k) =
      (MulAction.toPermHom Q Q).comp (FreeGroup.lift g) := by
  apply FreeGroup.ext_hom
  intro i
  ext q
  simp only [MonoidHom.comp_apply, monodromyRepresentation_generator,
    FreeGroup.lift_apply_of, MulAction.toPermHom_apply]
  rfl

end

open DiscreteCoverCharts
variable {k : ℕ}
variable {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]

theorem monodromy_word (g : Fin k → Q) (w : List (Fin k × Bool)) (q : Q) :
    (covering (coveringCore g)).monodromy
      (Path.Homotopic.Quotient.mk (wordLoop w))
      ⟨point (coveringCore g) none (basepoint k) q,rfl⟩ =
      ⟨point (coveringCore g) none (basepoint k) (FreeGroup.lift g (FreeGroup.mk w) * q),rfl⟩ := by
  let e := fiberEquiv (coveringCore g) none (basepoint k)
    (Cells.mem_collar_old (attaching k) PUnit.unit)
  apply e.symm.injective
  have h := DFunLike.congr_fun (monodromyRepresentation_comp g) (FreeGroup.mk w)
  have h' := DFunLike.congr_fun h q
  change monodromyRepresentation g (freeToFundamental k (FreeGroup.mk w)) q =
    FreeGroup.lift g (FreeGroup.mk w) * q at h'
  rw [freeToFundamental_mk] at h'
  change e.symm ((covering (coveringCore g)).monodromy
    (Path.Homotopic.Quotient.mk (wordLoop w)) (e q)) = e.symm (e _)
  rw [e.symm_apply_apply]
  exact h'

def liftedRelator (g : Fin k → Q) (w : List (Fin k × Bool))
    (hw : FreeGroup.lift g (FreeGroup.mk w) = 1) :
    Path (point (coveringCore g) none (basepoint k) 1)
      (point (coveringCore g) none (basepoint k) 1) where
  toContinuousMap := (covering (coveringCore g)).liftPath (wordLoop w)
    (point (coveringCore g) none (basepoint k) 1) (wordLoop w).source
  source' := (covering (coveringCore g)).liftPath_zero _ _ _
  target' := by
    have h := congrArg Subtype.val (monodromy_word g w 1)
    rw [hw,one_mul] at h
    exact h

@[simp] theorem liftedRelator_proj (g : Fin k → Q) (w : List (Fin k × Bool))
    (hw : FreeGroup.lift g (FreeGroup.mk w) = 1) (t : unitInterval) :
    (coveringCore g).proj (liftedRelator g w hw t) = wordLoop w t :=
  congrFun ((covering (coveringCore g)).liftPath_lifts (wordLoop w)
    (point (coveringCore g) none (basepoint k) 1) (wordLoop w).source) t

end PresentationGeometry.Rose

namespace PresentationGeometry.AttachingLoops
open scoped unitInterval

variable {k r : ℕ} (w : Fin r → List (Fin k × Bool))
variable {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
variable (g : Fin k → Q) (hw : ∀ i, FreeGroup.lift g (FreeGroup.mk (w i)) = 1)

def boundaryCircle : C(Cells.boundary r 2, Fin r × AddCircle (1 : ℝ)) where
  toFun b := (b.1.1,boundaryParameter ⟨b.1.2.1,b.2⟩)
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).prodMk
    (boundaryParameter.continuous.comp
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _))

def liftedRelatorsOnCircle : C(Fin r × AddCircle (1 : ℝ), (Rose.coveringCore g).TotalSpace) where
  toFun p := onCircle (Rose.liftedRelator g (w p.1) (hw p.1)) p.2
  continuous_toFun := continuous_prod_of_discrete_left.mpr fun i =>
    (onCircle (Rose.liftedRelator g (w i) (hw i))).continuous

end PresentationGeometry.AttachingLoops

end

end OAI
end


