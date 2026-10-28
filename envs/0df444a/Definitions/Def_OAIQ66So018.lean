-- Prove2me | Definitions.Def_OAIQ66So018
-- name    : OAIQ66So018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:23:51.586561+00:00
-- url     : https://prove2.me/theorems/166c510b-ef35-4119-ba29-3a8db948b334
-- title:
--   Definitions bundle OAIQ66So018 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 350 declarations of OpenAI's Lean: 98 definitions, 2 inductive types or structures, 4 instances and 246 theorems. The definitions and types are `OAI.CoreDeck.leftFundamentalEquiv`, `OAI.EquivariantCoverCells.abelianEquiv`, `OAI.EquivariantCoverCells.cellularRepresentation`, `OAI.EquivariantCoverCells.freeIso`, `OAI.EquivariantCoverCells.representationEquiv`, `OAI.EquivariantOrderChains.action`, `OAI.EquivariantOrderChains.augmentation`, `OAI.EquivariantOrderChains.differential`, `OAI.EquivariantOrderChains.endpoints`, `OAI.EquivariantOrderChains.object`, `OAI.EquivariantOrderChains.permutationIso`, `OAI.EquivariantOrderChains.representation`, `OAI.EquivariantOrderChains.simplexAct`, `OAI.EquivariantOrderChains.tuple`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.commandMap`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.controlMap`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.leftCross`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.pathCode`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.pathPrimcodable`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.stateMap`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.staticBoundary`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.surfaceCode`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.surfacePrimcodable`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Path.Sector.code`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Path.mapLetter`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Path.mapSector`, `OAI.FiniteAlgebraicEnvelopes.Compiler.RawRuns.Action.partial`, `OAI.FiniteAlgebraicEnvelopes.Compiler.RawRuns.Action.total`, `OAI.FiniteAlgebraicEnvelopes.Compiler.RawRuns.execute`, `OAI.FiniteAlgebraicEnvelopes.Compiler.RawRuns.partialSource`, `OAI.FiniteAlgebraicEnvelopes.Compiler.RawRuns.plan`, `OAI.FiniteAlgebraicEnvelopes.Compiler.RawRuns.push`, `OAI.OrderChainComplex.aug`, `OAI.OrderChainComplex.basisIso`, `OAI.OrderChainComplex.chains`, `OAI.OrderChainComplex.d`, `OAI.OrderChainComplex.simplexSet`, `OAI.OrderChains.Descending`, `OAI.OrderChains.carrier`, `OAI.OrderChains.module` and 60 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `FiniteCompiler_Effectivity`, `FiniteCompiler_Normalization`, `FiniteCompiler_UniformControl`, `FiniteCompiler_UniformPaths`, `FiniteType_ChainShortExact`, `FiniteType_CoreDeckLeftQuotientCovering`, `FiniteType_CoveringCellGeometryHausdorff`, `FiniteType_CubeDisk`, `FiniteType_EquivariantOrderChains`, `FiniteType_FiniteIndexProducts`, `FiniteType_OrderChains`, `FiniteType_OrderListChains`, `FiniteType_OrderListChainsBased`, `FiniteType_PresentationGeometry`, `FiniteType_PresentationGeometryCellCoverExtension`, `FiniteType_PresentationGeometryCells`, `FiniteType_PresentationGeometryDescend`, `FiniteType_RegularCoverGeometry`, `FiniteType_RelativeChainsEmptyProjectionQuasiIso`, `FiniteType_SimplexHomotopy`, `FiniteType_SingularAction`, `FiniteType_SingularPrism`, `FiniteType_SingularSigma`, `FiniteType_TwistedBrinBasisCutBasis`.
--
--   **Imports.** It imports the bundles `OAIQ66So010`, `OAIQ66So011` and `OAIQ66So012` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So023`, `OAIQ66So024`, `OAIQ66So025` and `OAIQ66So026`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So010
import Definitions.Def_OAIQ66So011
import Definitions.Def_OAIQ66So012

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Normalization
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.RawRuns.instPrimcodableAction _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableInstruction _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Raw-run folds, full word compilation, partial budgets, and bounded normalization.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.RawRuns
variable {C S : Type*}

variable {f : List S → List S} {m : ℕ}

 theorem source_grade (g : C → ℕ) (h : Budget f m) (w : List (Item C S))
    (hm : grade g w ≤ m) : grade g (source f w) ≤ grade g w := by
  rw [source_eq_normalize g h w hm]
  exact normalize_grade g h w hm

end FiniteAlgebraicEnvelopes.Compiler.RawRuns

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
variable {H B T K : Type*}

namespace Literal
open _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path

 theorem rule_length (table : Table H B T) (m : H → K) {u v : List (Letter (B×T) K)}
    (h : Rule table m u v) : u.length = 2 ∧ v.length = 2 := by
  cases h with
  | cell q b t i h =>
    cases hd : table.direction q <;> cases hc : i.cross <;>
      simp [headed,inLeft,inRight,outLeft,outRight]
  | left => simp
  | right => simp

end Literal
end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.RawRuns
variable {C S : Type*}

def plan : List (Item C S) → List (Action C S)
  | [] => []
  | .inl c::w => .keep c::plan w
  | .inr x::w =>
    let p := splitRun w
    let z := match p.1 with
      | [] => Action.raw x
      | _::_ => Action.call (x++p.1.flatten)
    z :: plan p.2
termination_by w => w.length
decreasing_by
  · simp_wf
  · have := splitRun_length w
    simp_wf
    omega

def Action.total (f : List S → List S) : Action C S → Item C S
  | .keep c => .inl c
  | .raw x => .inr x
  | .call x => .inr (f x)

theorem plan_total (f : List S → List S) (w : List (Item C S)) :
    (plan w).map (Action.total f) = source f w := by
  cases w with
  | nil => simp [plan,source]
  | cons a w =>
    cases a with
    | inl c => simp only [plan,source,List.map_cons,Action.total,plan_total f w]
    | inr x =>
      have ht := splitRun_length w
      rw [plan,source,List.map_cons,plan_total f (splitRun w).2]
      cases (splitRun w).1 <;> rfl
termination_by w.length
decreasing_by all_goals simp_all only [List.length_cons]; omega

/-- Every program argument is bounded by the grade of the original item list,
    before any output from the program is computed. -/
theorem plan_call_bound (g : C → ℕ) (w : List (Item C S)) {x : List S}
    (hx : Action.call x ∈ plan w) : x.length ≤ grade g w := by
  cases w with
  | nil => simp [plan] at hx
  | cons a w =>
    cases a with
    | inl c =>
      simp only [plan,List.mem_cons] at hx
      rcases hx with he | hx
      · cases he
      ·
        exact (plan_call_bound g w hx).trans (by simp only [grade_cons,itemGrade]; omega)
    | inr y =>
      have ht := splitRun_length w
      have hj := splitRun_join w
      simp only [plan,List.mem_cons] at hx
      rcases hx with he | hx
      · cases hh : (splitRun w).1 with
        | nil => simp only [hh] at he; cases he
        | cons z zs =>
          simp only [hh] at he
          cases he
          rw [←hj]
          simp only [grade_cons,itemGrade,grade_append,grade_raws,hh]
          simp only [List.length_append]
          omega
      · have hp := plan_call_bound g (splitRun w).2 hx
        rw [←hj]
        simp only [grade_cons,itemGrade,grade_append]
        omega
termination_by w.length
decreasing_by all_goals simp_all only [List.length_cons]; omega

def Action.partial (f : List S → Part (List S)) : Action C S → Part (Item C S)
  | .keep c => Part.some (.inl c)
  | .raw x => Part.some (.inr x)
  | .call x => (f x).map Sum.inr

def execute (f : List S → Part (List S)) : List (Action C S) → Part (List (Item C S))
  | [] => Part.some []
  | a::w => (a.partial f).bind fun b => (execute f w).map (b::·)

theorem execute_total_mem {f : List S → Part (List S)} {t : List S → List S}
    (p : List (Action C S)) (h : ∀ x, Action.call x ∈ p → t x ∈ f x) :
    p.map (Action.total t) ∈ execute f p := by
  induction p with
  | nil => exact Part.mem_some []
  | cons a p ih =>
    have hp := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    have ha : Action.total t a ∈ Action.partial f a := by
      cases a with
      | keep c => exact Part.mem_some _
      | raw x => exact Part.mem_some _
      | call x => exact (Part.mem_map_iff _).mpr ⟨t x,h x (List.mem_cons_self),rfl⟩
    exact Part.mem_bind_iff.mpr ⟨_,ha,(Part.mem_map_iff _).mpr ⟨_,hp,rfl⟩⟩

def partialSource (f : List S → Part (List S)) (w : List (Item C S)) : Part (List (Item C S)) :=
  execute f (plan w)

theorem partialSource_total_mem (g : C → ℕ) {f : List S → Part (List S)} {t : List S → List S}
    (w : List (Item C S)) (h : ∀ x, x.length ≤ grade g w → t x ∈ f x) :
    source t w ∈ partialSource f w := by
  rw [←plan_total t]
  exact execute_total_mem _ (fun x hx => h x (plan_call_bound g w hx))

end FiniteAlgebraicEnvelopes.Compiler.RawRuns

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Effectivity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
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

namespace FiniteAlgebraicEnvelopes.Compiler.RawRuns
variable {C S : Type*}

def push : Item C S → List (Action C S) → List (Action C S)
  | .inl c,p => .keep c::p
  | .inr x,[] => [.raw x]
  | .inr x,.keep c::p => .raw x::.keep c::p
  | .inr x,.raw y::p => .call (x++y)::p
  | .inr x,.call y::p => .call (x++y)::p

theorem plan_cons (a : Item C S) (w : List (Item C S)) :
    plan (a::w) = push a (plan w) := by
  cases a with
  | inl c => simp only [plan,push]
  | inr x =>
    cases w with
    | nil => simp [plan,splitRun,push]
    | cons b w =>
      cases b with
      | inl c => simp [plan,splitRun,push]
      | inr y =>
        rw [plan,plan]
        simp only [splitRun]
        cases (splitRun w).1 <;> simp [push]

theorem plan_fold (w : List (Item C S)) : plan w = w.foldr push [] := by
  induction w with
  | nil => simp [plan]
  | cons a w ih => rw [plan_cons,ih]; rfl

variable [Primcodable C] [Primcodable S]

 theorem primrec_push : Primrec₂ (push (C := C) (S := S)) := by
  have hl : Primrec₂ (fun (p : Item C S × List (Action C S)) (c : C) => Action.keep c::p.2) :=
    (Primrec.list_cons.comp (Action.primrec_keep.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)).to₂
  have hr : Primrec₂ (fun (p : Item C S × List (Action C S)) (x : List S) =>
      match p.2 with
      | [] => [Action.raw x]
      | .keep c::l => Action.raw x::.keep c::l
      | .raw y::l => Action.call (x++y)::l
      | .call y::l => Action.call (x++y)::l) := by
    have hc : Primrec₂ (fun (p : (Item C S × List (Action C S)) × List S)
        (q : Action C S × List (Action C S)) =>
        match q.1 with
        | .keep c => Action.raw p.2::.keep c::q.2
        | .raw y => Action.call (p.2++y)::q.2
        | .call y => Action.call (p.2++y)::q.2) := by
      exact (Action.primrec_cases (Primrec.fst.comp Primrec.snd)
        (Primrec.list_cons.comp
          (Action.primrec_raw.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.list_cons.comp (Action.primrec_keep.comp Primrec.snd)
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).to₂
        (Primrec.list_cons.comp
          (Action.primrec_call.comp (Primrec.list_append.comp
            (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to₂
        (Primrec.list_cons.comp
          (Action.primrec_call.comp (Primrec.list_append.comp
            (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to₂).to₂
    exact (Primrec.list_casesOn (Primrec.snd.comp Primrec.fst)
      (Primrec.list_cons.comp (Action.primrec_raw.comp Primrec.snd) (Primrec.const [])) hc).to₂.of_eq
      (by intro p x; cases p.2 with
        | nil => rfl
        | cons a l => cases a <;> rfl)
  exact (Primrec.sumCasesOn Primrec.fst hl hr).to₂.of_eq fun a p => by
    cases a with
    | inl c => rfl
    | inr x => cases p with
      | nil => rfl
      | cons a p => cases a <;> rfl

 theorem primrec_plan : Primrec (plan (C := C) (S := S)) :=
  (Primrec.list_foldr Primrec.id (Primrec.const [])
    (primrec_push.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    (fun w => (plan_fold w).symm)

end FiniteAlgebraicEnvelopes.Compiler.RawRuns

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {H B T : Type*}

variable [Primcodable H] [Primcodable B] [Primcodable T]

theorem Sector.primrec_decode : Primrec (Sector.code (H := H) (B := B) (T := T)).symm :=
  Primrec.of_equiv_symm

theorem Sector.primrec_left : Primrec (Sector.left (Head := H) (Base := B) (Tag := T)) :=
  Primrec.fst.comp Sector.primrec_code

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Path
open FiniteAlgebraicEnvelopes.Effect
variable {C H : Type*}

def Sector.code : Sector C H ≃ List C × (H × (List C × (Bool × Bool))) where
  toFun v := (v.left,v.head,v.right,v.leftBoundary,v.rightBoundary)
  invFun p := ⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instPrimcodableSector [Primcodable C] [Primcodable H] : Primcodable (Sector C H) :=
  Primcodable.ofEquiv _ Sector.code

variable [Primcodable C] [Primcodable H]

theorem Sector.primrec_code : Primrec (Sector.code (C := C) (H := H)) := Primrec.of_equiv
theorem Sector.primrec_decode : Primrec (Sector.code (C := C) (H := H)).symm :=
  Primrec.of_equiv_symm

theorem Sector.primrec_left : Primrec (Sector.left (C := C) (H := H)) :=
  Primrec.fst.comp Sector.primrec_code
theorem Sector.primrec_head : Primrec (Sector.head (C := C) (H := H)) :=
  Primrec.fst.comp (Primrec.snd.comp Sector.primrec_code)
theorem Sector.primrec_right : Primrec (Sector.right (C := C) (H := H)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Sector.primrec_code))
theorem Sector.primrec_lb : Primrec (Sector.leftBoundary (C := C) (H := H)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Sector.primrec_code)))
theorem Sector.primrec_rb : Primrec (Sector.rightBoundary (C := C) (H := H)) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Sector.primrec_code)))

theorem Sector.primrec_mk {α : Type*} [Primcodable α]
    {l r : α → List C} {q : α → H} {a b : α → Bool}
    (hl : Primrec l) (hq : Primrec q) (hr : Primrec r) (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => (⟨l x,q x,r x,a x,b x⟩ : Sector C H)) :=
  Sector.primrec_decode.comp (hl.pair (hq.pair (hr.pair (ha.pair hb))))

variable [Fintype C] [Fintype H] [DecidableEq C] [DecidableEq H]
noncomputable instance instPrimcodableLetter : Primcodable (Letter C H) := finitePrimcodable _

end FiniteAlgebraicEnvelopes.Compiler.Path

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_UniformControl
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
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

variable [Fintype B] [Fintype T]

variable [DecidableEq H] [DecidableEq B] [DecidableEq T]

omit [DecidableEq H] [DecidableEq T] in
omit [Primcodable H] [Primcodable B] [Primcodable T] in
@[simp] theorem mem_universeList (heads : List H) (v w : Sector H B T) :
    w ∈ universeList heads v ↔ w.head ∈ heads ∧ baseSkeleton w=baseSkeleton v := by
  simp only [universeList,List.mem_filter,mem_sectorList,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h,_,_⟩,he⟩; exact ⟨h,he⟩
  · rintro ⟨h,he⟩
    have hl := skeleton_length he
    exact ⟨⟨h,by omega,by omega⟩,he⟩

end FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open Simulator

variable {S Q Q' H C : Type*}

def surfaceCode : Surface.Head H ≃ Fin 3 ⊕ H where
  toFun | .raw => .inl 0 | .pending => .inl 1 | .cleanup => .inl 2 | .internal q => .inr q
  invFun | .inl k => if k=0 then .raw else if k=1 then .pending else .cleanup
         | .inr q => .internal q
  left_inv q := by cases q <;> rfl
  right_inv q := by cases q with
    | inl k => fin_cases k <;> rfl
    | inr q => rfl

def pathCode : Path.Letter C H ≃ Fin 3 ⊕ (C ⊕ (C ⊕ H)) where
  toFun | .zero => .inl 0 | .enter => .inl 1 | .leave => .inl 2
        | .left c => .inr (.inl c) | .right c => .inr (.inr (.inl c))
        | .head q => .inr (.inr (.inr q))
  invFun | .inl k => if k=0 then .zero else if k=1 then .enter else .leave
         | .inr (.inl c) => .left c | .inr (.inr (.inl c)) => .right c
         | .inr (.inr (.inr q)) => .head q
  left_inv q := by cases q <;> rfl
  right_inv q := by
    cases q with
    | inl k => fin_cases k <;> rfl
    | inr q => cases q with
      | inl c => rfl
      | inr q => cases q <;> rfl

scoped instance surfacePrimcodable [Primcodable H] : Primcodable (Surface.Head H) :=
  Primcodable.ofEquiv _ surfaceCode
scoped instance pathPrimcodable [Primcodable C] [Primcodable H] : Primcodable (Path.Letter C H) :=
  Primcodable.ofEquiv _ pathCode

variable [Fintype S] [Primcodable Q]
theorem primrec_simDecode : Primrec (simCode (S := S) (Q := Q)).symm := Primrec.of_equiv_symm
theorem primrec_ofStatic : Primrec (ofStatic (S := S) (Q := Q)) :=
  primrec_simDecode.comp Primrec.sumInl
theorem primrec_dynamic : Primrec (dynamic (S := S) (Q := Q)) :=
  primrec_simDecode.comp Primrec.sumInr

theorem primrec_controlCode : Primrec (controlCode (S := S) (Q := Q)) := Primrec.of_equiv
theorem primrec_controlDecode : Primrec (controlCode (S := S) (Q := Q)).symm := Primrec.of_equiv_symm
theorem primrec_machine : Primrec (Control.Head.machine (S := S) (Q := Q)) :=
  primrec_controlDecode.comp Primrec.sumInr

theorem primrec_surfaceCode [Primcodable H] : Primrec (surfaceCode (H := H)) := Primrec.of_equiv
theorem primrec_surfaceDecode [Primcodable H] : Primrec (surfaceCode (H := H)).symm := Primrec.of_equiv_symm
theorem primrec_internal [Primcodable H] : Primrec (Surface.Head.internal (H := H)) :=
  primrec_surfaceDecode.comp Primrec.sumInr

theorem primrec_pathCode [Primcodable C] [Primcodable H] : Primrec (pathCode (C := C) (H := H)) :=
  Primrec.of_equiv
theorem primrec_pathDecode [Primcodable C] [Primcodable H] : Primrec (pathCode (C := C) (H := H)).symm :=
  Primrec.of_equiv_symm

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open Simulator
open scoped HeadCodec
variable {S Γ Q Q' P : Type*}

def stateMap (f : Q → Q') : Simulator.Head S Q → Simulator.Head S Q'
  | .start => .start | .rewind r => .rewind r | .scan r => .scan r
  | .run q => .run (f q) | .left q => .left (f q) | .finish => .finish | .ok => .ok

def controlMap (f : Q → Q') : Control.Head S Q → Control.Head S Q'
  | .initial => .initial | .left => .left | .right => .right
  | .workspace => .workspace | .suffix => .suffix | .machine q => .machine (stateMap f q)

def commandMap (f : Q → Q') (c : Command Q Γ) : Command Q' Γ := ⟨f c.state,c.write,c.move⟩

theorem primrec_commandCode [Primcodable Q] [Primcodable Γ] : Primrec (commandCode (Q := Q) (Γ := Γ)) :=
  Primrec.of_equiv

theorem primrec_commandState [Primcodable Q] [Primcodable Γ] : Primrec (Command.state (Q := Q) (Γ := Γ)) :=
  Primrec.fst.comp primrec_commandCode

theorem primrec_commandWrite [Primcodable Q] [Primcodable Γ] : Primrec (Command.write (Q := Q) (Γ := Γ)) :=
  Primrec.fst.comp (Primrec.snd.comp primrec_commandCode)

theorem primrec_commandMove [Primcodable Q] [Primcodable Γ] : Primrec (Command.move (Q := Q) (Γ := Γ)) :=
  Primrec.snd.comp (Primrec.snd.comp primrec_commandCode)

theorem primrec_commandMk [Primcodable P] [Primcodable Q] [Primcodable Γ]
    {q : P → Q} {a : P → Γ} {d : P → Move} (hq : Primrec q) (ha : Primrec a) (hd : Primrec d) :
    Primrec (fun p => (⟨q p,a p,d p⟩ : Command Q Γ)) :=
  Primrec.of_equiv_symm.comp (hq.pair (ha.pair hd))

variable [Fintype S] [Primcodable P] [Primcodable Q] [Primcodable Q']

theorem primrec_instruction [Primcodable Γ] {q : P → Q} {t : P → Γ} {b : P → Bool}
    (hq : Primrec q) (ht : Primrec t) (hb : Primrec b) :
    Primrec (fun p => (⟨q p,t p,b p⟩ : Instruction Q Γ)) :=
  Primrec.of_equiv_symm.comp (hq.pair (ht.pair hb))

omit [Fintype S] [Primcodable P] [Primcodable Q] [Primcodable Q'] in
theorem stateMap_injective {f : Q → Q'} (hf : Function.Injective f) :
    Function.Injective (stateMap (S := S) f) := by
  intro a b h
  cases a <;> cases b <;> simp_all [stateMap]
  all_goals exact hf h

omit [Fintype S] [Primcodable P] [Primcodable Q] [Primcodable Q'] in
theorem controlMap_injective {f : Q → Q'} (hf : Function.Injective f) :
    Function.Injective (controlMap (S := S) f) := by
  intro a b h
  cases a <;> cases b <;> simp_all [controlMap]
  exact stateMap_injective hf h

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

namespace FiniteAlgebraicEnvelopes.Compiler.Simulator
open HeadCodec
variable {S Γ Q Q' : Type*} [DecidableEq Γ]
variable (A : Alphabet S Γ) (M : Machine Q Γ) (N : Machine Q' Γ) (i : Q → Q')
  (hi : N.initial=i M.initial)
  (ht : ∀ q a,N.transition (i q) a=(M.transition q a).map (commandMap i))

theorem table_direction_map (q : Head S Q) :
    (table A N).direction (stateMap i q)=(table A M).direction q := by
  cases q <;> rfl

theorem table_boundary_map (q : Head S Q) :
    (table A N).boundary (stateMap i q)=((table A M).boundary q).map (stateMap i) := by
  cases q <;> try rfl
  case scan r => cases r <;> rfl

include hi ht in
theorem table_cell_map (q : Head S Q) (b : Base S) (a : Tag S Γ) :
    (table A N).cell (stateMap i q) b a=
      ((table A M).cell q b a).map (Scan.mapInstruction (stateMap i)) := by
  cases q with
  | start | ok => rfl
  | rewind r => rfl
  | finish => rfl
  | left q => cases b <;> rfl
  | scan r =>
    cases r <;> cases b <;>
      simp [table,cell,stateMap,Scan.mapInstruction,hi]
    all_goals split <;> simp_all [Scan.mapInstruction,stateMap]
    all_goals split <;> simp_all [Scan.mapInstruction,stateMap,Option.map_map,Function.comp_def]
  | run q =>
    cases b <;> try rfl
    case workspace =>
      simp only [table,cell,stateMap,ht]
      cases h : M.transition q a.work with
      | none => rfl
      | some c =>
        rcases c with ⟨q,g,m⟩
        cases m <;> rfl

end FiniteAlgebraicEnvelopes.Compiler.Simulator

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open Simulator
open scoped HeadCodec
variable {S Γ Q P : Type*} [Fintype S] [Fintype Γ] [DecidableEq S] [DecidableEq Γ]
  [Primcodable Γ] [Primcodable Q] [Primcodable P]
variable (A : Alphabet S Γ) (M : P → Machine Q Γ)
  (hinit : Primrec (fun p => (M p).initial))
  (htrans : Primrec (fun x : P × Q × Γ => (M x.1).transition x.2.1 x.2.2))

omit [Fintype S] [Fintype Γ] [DecidableEq S] [Primcodable Γ] [Primcodable Q] [Primcodable P] in
theorem static_cell (p : P) (s : Static S) (b : Base S) (t : Tag S Γ) :
    cell A (M p) (ofStatic s) b t=
      (cell A dummy (ofStatic s) b t).map
        (Scan.mapInstruction (stateMap (fun _ : Unit => (M p).initial))) := by
  cases s with
  | start | rewind | finish | ok => rfl
  | scan r =>
    cases r <;> cases b <;>
      simp [cell,ofStatic,stateMap,Scan.mapInstruction,dummy]
    all_goals split <;> simp_all [Scan.mapInstruction,stateMap]
    all_goals split <;> simp_all [Scan.mapInstruction,stateMap,Option.map_map,Function.comp_def]

def leftCross : Base S → Option Bool
  | .workspace => some true | .cutC => some false | _ => none

omit [DecidableEq S] [Primcodable Γ] in
theorem primrec_leftCell : Primrec (fun x : P × Q × Base S × Tag S Γ =>
    cell A (M x.1) (.left x.2.1) x.2.2.1 x.2.2.2) := by
  have hc : Primrec (fun x : P × Q × Base S × Tag S Γ => leftCross x.2.2.1) :=
    (Primrec.dom_finite (leftCross (S := S))).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hs : Primrec₂ (fun (x : P × Q × Base S × Tag S Γ) (b : Bool) =>
      (⟨.run x.2.1,x.2.2.2,b⟩ : Instruction (Simulator.Head S Q) (Tag S Γ))) :=
    (primrec_instruction
      (primrec_dynamic.comp ((Primrec.const false).pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd).to₂
  exact (Primrec.option_map hc hs).of_eq fun x => by cases x.2.2.1 <;> rfl

include htrans in
omit [DecidableEq S] in
theorem primrec_runWorkspace : Primrec (fun x : P × Q × Tag S Γ =>
    cell A (M x.1) (.run x.2.1) .workspace x.2.2) := by
  have ht : Primrec (fun x : P × Q × Tag S Γ => x.2.2) := Primrec.snd.comp Primrec.snd
  have hw : Primrec (fun x : Tag S Γ => x.work) := Primrec.dom_finite _
  have hc := htrans.comp (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair (hw.comp ht)))
  have hz : Primrec (fun x : P × Q × Tag S Γ =>
      some (⟨.rewind .readout,x.2.2,false⟩ : Instruction (Simulator.Head S Q) (Tag S Γ))) :=
    Primrec.option_some.comp (primrec_instruction (Primrec.const _) ht (Primrec.const false))
  have hd : Primrec₂ (fun (x : P × Q × Tag S Γ) (c : Command Q Γ) =>
      some (⟨(if c.move = .left then .left c.state else .run c.state),
        {x.2.2 with work := c.write}, c.move == .right⟩ : Instruction (Simulator.Head S Q) (Tag S Γ))) := by
    unfold Primrec₂
    apply Primrec.option_some.comp
    apply primrec_instruction
    · exact (primrec_dynamic.comp
        (((Primrec.dom_finite (fun d : Move => decide (d=.left))).comp
          ((primrec_commandMove (Q := Q) (Γ := Γ)).comp Primrec.snd)).pair
            (primrec_commandState.comp Primrec.snd))).of_eq fun x => by
              simp only [dynamic, decide_eq_true_eq]
    · exact (Primrec.dom_finite (fun p : Tag S Γ × Γ => {p.1 with work := p.2})).comp
        ((ht.comp Primrec.fst).pair ((primrec_commandWrite (Q := Q) (Γ := Γ)).comp Primrec.snd))
    · exact (Primrec.dom_finite (fun d : Move => d == .right)).comp
        ((primrec_commandMove (Q := Q) (Γ := Γ)).comp Primrec.snd)
  exact (Primrec.option_casesOn hc hz hd).of_eq fun x => by
    simp only [cell]
    cases (M x.1).transition x.2.1 x.2.2.work <;> rfl

include htrans in
theorem primrec_runCell : Primrec (fun x : P × Q × Base S × Tag S Γ =>
    cell A (M x.1) (.run x.2.1) x.2.2.1 x.2.2.2) := by
  have hb : Primrec (fun x : P × Q × Base S × Tag S Γ => decide (x.2.2.1=.workspace)) :=
    (Primrec.dom_finite (fun b : Base S => decide (b=.workspace))).comp
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  exact (Primrec.cond hb
    ((primrec_runWorkspace A M htrans).comp (Primrec.fst.pair
      ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
    (Primrec.const none)).of_eq fun x => by cases x.2.2.1 <;> rfl

def staticBoundary : Static S → Option (Static S)
  | .start => some (.rewind .input) | .rewind r => some (.scan r)
  | .scan .input => some (.rewind .spare) | .finish => some .ok | _ => none

omit [Fintype S] [DecidableEq S] [Primcodable Q] in
theorem validatorHead_map {Q' : Type*} (f : Q → Q') (h : Validator.Head) :
    controlMap (S := S) f (Control.validatorHead h)=Control.validatorHead h := by
  cases h <;> rfl

omit [Fintype S] [Fintype Γ] [Primcodable Γ] [Primcodable Q] [Primcodable P] in
theorem staticControl_cell (p : P) (k : Fin 5) (b : Base S) (t : Tag S Γ) :
    (Control.table A (M p)).cell (staticControl k) b t =
      ((Control.table A dummy).cell (staticControl k) b t).map
        (Scan.mapInstruction (controlMap (fun _ : Unit => (M p).initial))) := by
  have hm :
      Scan.mapInstruction (T := Tag S Γ) (controlMap (fun _ : Unit => (M p).initial)) ∘
        Scan.mapInstruction (Control.validatorHead (S := S)) =
          Scan.mapInstruction (Control.validatorHead (S := S) (Q := Q)) := by
    funext c
    cases c with | mk q t b => simp [Scan.mapInstruction,validatorHead_map]
  fin_cases k <;>
    simp [staticControl,controlCode,Control.table,Control.toValidator,Option.map_map,hm]

omit [Fintype S] [Fintype Γ] [Primcodable Γ] [Primcodable Q] [Primcodable P] in
theorem staticControl_boundary (p : P) (k : Fin 5) :
    (Control.table A (M p)).boundary (staticControl k) =
      ((Control.table A dummy).boundary (staticControl k)).map
        (controlMap (fun _ : Unit => (M p).initial)) := by
  have hm : controlMap (fun _ : Unit => (M p).initial) ∘
      Control.validatorHead (S := S) = Control.validatorHead (S := S) (Q := Q) := by
    funext q; exact validatorHead_map _ q
  fin_cases k <;>
    simp [staticControl,controlCode,Control.table,Control.toValidator,Option.map_map,hm]

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

namespace FiniteAlgebraicEnvelopes.Compiler.Control
open HeadCodec
variable {S Γ Q Q' : Type*} [DecidableEq S] [DecidableEq Γ] [Fintype S]
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ) (N : Simulator.Machine Q' Γ)
  (i : Q → Q') (hi : N.initial=i M.initial)
  (ht : ∀ q a,N.transition (i q) a=(M.transition q a).map (commandMap i))

omit [Fintype S] in
theorem table_direction_map (q : Head S Q) :
    (table A N).direction (controlMap i q)=(table A M).direction q := by
  cases q <;> try rfl
  exact Simulator.table_direction_map A M N i _

omit [Fintype S] in
theorem table_boundary_map (q : Head S Q) :
    (table A N).boundary (controlMap i q)=((table A M).boundary q).map (controlMap i) := by
  have hm : controlMap i ∘ validatorHead (S := S)=validatorHead (S := S) := by
    funext q; cases q <;> rfl
  cases q <;> simp only [table,controlMap,toValidator,Option.map_map]
  all_goals try { simp only [hm] }
  case machine q =>
    rw [Simulator.table_boundary_map A M N i]
    simp only [Option.map_map]
    rfl

include hi ht in
omit [Fintype S] in
theorem table_cell_map (q : Head S Q) (b : Base S) (a : Tag S Γ) :
    (table A N).cell (controlMap i q) b a=
      ((table A M).cell q b a).map (Scan.mapInstruction (controlMap i)) := by
  have hm : Scan.mapInstruction (T := Tag S Γ) (controlMap i) ∘
      Scan.mapInstruction (validatorHead (S := S))=Scan.mapInstruction (validatorHead (S := S)) := by
    funext c
    cases c with | mk h t b => cases h <;> rfl
  cases q <;> simp only [table,controlMap,toValidator,Option.map_map]
  all_goals try { simp only [hm] }
  case machine q =>
    rw [Simulator.table_cell_map A M N i hi ht]
    simp only [Option.map_map]
    rfl

omit [DecidableEq S] [DecidableEq Γ] [Fintype S] in
theorem entry_map (blank : Γ) (v : Sector S Γ Q) :
    Entry blank (Scan.mapHead (controlMap i) v) ↔ Entry blank v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> simp [Entry,Scan.mapHead,controlMap]

omit [DecidableEq S] [DecidableEq Γ] [Fintype S] in
theorem success_map (v : Sector S Γ Q) :
    Success (Scan.mapHead (controlMap i) v) ↔ Success v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> simp [Success,Scan.mapHead,controlMap]
  case machine q => cases q <;> simp [stateMap]
end FiniteAlgebraicEnvelopes.Compiler.Control

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open FiniteAlgebraicEnvelopes.Effect
open scoped HeadCodec
variable {S Q : Type*} [Fintype S]

variable [Primcodable Q]
theorem primrec_simSupport : Primrec (simSupport (S := S) (Q := Q)) := by
  have hr : Primrec (Simulator.Head.run (S := S) (Q := Q)) :=
    primrec_dynamic.comp ((Primrec.const false).pair Primrec.id)
  have hl : Primrec (Simulator.Head.left (S := S) (Q := Q)) :=
    primrec_dynamic.comp ((Primrec.const true).pair Primrec.id)
  exact Primrec.list_append.comp (Primrec.const _)
    (Primrec.list_flatMap Primrec.id ((Primrec.list_cons.comp hr
      (Primrec.list_cons.comp hl (Primrec.const []))).comp Primrec.snd).to₂)

theorem primrec_controlSupport : Primrec (controlSupport (S := S) (Q := Q)) :=
  Primrec.list_append.comp (Primrec.const _)
    (Primrec.list_map primrec_simSupport (primrec_machine.comp Primrec.snd).to₂)

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_UniformPaths
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform surface and path normalization with recursive compiler interfaces.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Path.Uniform
open FiniteAlgebraicEnvelopes.Compiler.Path HeadCodec FiniteAlgebraicEnvelopes.Effect
open scoped HeadCodec
variable {C H : Type*} [Primcodable C] [Primcodable H]

theorem primrec_left : Primrec (Letter.left (C := C) (H := H)) :=
  primrec_pathDecode.comp (Primrec.sumInr.comp Primrec.sumInl)
theorem primrec_right : Primrec (Letter.right (C := C) (H := H)) :=
  primrec_pathDecode.comp (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.sumInl))
theorem primrec_head : Primrec (Letter.head (C := C) (H := H)) :=
  primrec_pathDecode.comp (Primrec.sumInr.comp (Primrec.sumInr.comp Primrec.sumInr))

theorem primrec_typeOf : Primrec (typeOf (C := C) (H := H)) := by
  let f : Fin 3 → Shape := fun k => if k=0 then .zero else if k=1 then .path .outer .left else .path .right .outer
  exact ((primrec_sumElim (Primrec.dom_finite f)
    (primrec_sumElim (Primrec.const (Shape.path .left .left))
      (primrec_sumElim (Primrec.const (Shape.path .right .right)) (Primrec.const (Shape.path .left .right))))).comp
        primrec_pathCode).of_eq fun a => by cases a <;> rfl

theorem primrec_shape : Primrec (shape (C := C) (H := H)) := by
  have hp : Primrec (fun p : Letter C H × Shape => typeOf p.1 * p.2) :=
    (Primrec.dom_finite (fun p : Shape × Shape => p.1*p.2)).comp
      ((primrec_typeOf.comp Primrec.fst).pair Primrec.snd)
  exact (Primrec.list_foldr Primrec.id (Primrec.const Shape.unit)
    (hp.comp Primrec.snd).to₂).of_eq fun w => by
      induction w with
      | nil => rfl
      | cons a w ih => simpa only [id_eq,List.foldr_cons,shape_cons] using congrArg (typeOf a * ·) ih

theorem primrec_head? : Primrec (fun a : Letter C H => match a with | .head q => some q | _ => none) := by
  exact ((primrec_sumElim (Primrec.const none)
    (primrec_sumElim (Primrec.const none)
      (primrec_sumElim (Primrec.const none) Primrec.option_some))).comp primrec_pathCode).of_eq
        fun a => by cases a <;> rfl

theorem primrec_left? : Primrec (fun a : Letter C H => match a with | .left c => some c | _ => none) := by
  exact ((primrec_sumElim (Primrec.const none)
    (primrec_sumElim Primrec.option_some (Primrec.const none))).comp primrec_pathCode).of_eq
        fun a => by cases a <;> rfl

theorem primrec_right? : Primrec (fun a : Letter C H => match a with | .right c => some c | _ => none) := by
  exact ((primrec_sumElim (Primrec.const none)
    (primrec_sumElim (Primrec.const none)
      (primrec_sumElim Primrec.option_some (Primrec.const none)))).comp primrec_pathCode).of_eq
        fun a => by cases a <;> rfl

theorem primrec_heads : Primrec (heads (C := C) (H := H)) :=
  Primrec.listFilterMap Primrec.id (primrec_head?.comp Primrec.snd).to₂
theorem primrec_lefts : Primrec (lefts (C := C) (H := H)) :=
  Primrec.listFilterMap Primrec.id (primrec_left?.comp Primrec.snd).to₂
theorem primrec_rights : Primrec (rights (C := C) (H := H)) :=
  Primrec.listFilterMap Primrec.id (primrec_right?.comp Primrec.snd).to₂
 theorem primrec_encode : Primrec (encode (C := C) (H := H)) := by
  have hl : Primrec (fun v : Sector C H => v.left.reverse.map (Letter.left : C → Letter C H)) :=
    Primrec.list_map (Primrec.list_reverse.comp Sector.primrec_left)
      (primrec_left.comp Primrec.snd).to₂
  have hr : Primrec (fun v : Sector C H => v.right.map (Letter.right : C → Letter C H)) :=
    Primrec.list_map Sector.primrec_right (primrec_right.comp Primrec.snd).to₂
  exact Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp
    (Primrec.list_append.comp
      ((Primrec.dom_finite (fun b : Bool => if b then ([.enter] : List (Letter C H)) else [])).comp
        Sector.primrec_lb) hl)
      (Primrec.list_cons.comp (primrec_head.comp Sector.primrec_head) (Primrec.const []))) hr)
    ((Primrec.dom_finite (fun b : Bool => if b then ([.leave] : List (Letter C H)) else [])).comp
      Sector.primrec_rb)

 theorem primrec_glue : Primrec₂ (glue (C := C) (H := H)) := by
  have hn : Primrec (fun p : List (Letter C H) × List (List (Letter C H)) =>
      if p.1 = [] then [] else [p.1]) :=
    Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const [])) (Primrec.const [])
      (Primrec.list_cons.comp Primrec.fst (Primrec.const []))
  have hc : Primrec₂ (fun (p : List (Letter C H) × List (List (Letter C H)))
      (ct : List (Letter C H) × List (List (Letter C H))) => (p.1++ct.1)::ct.2) :=
    (Primrec.list_cons.comp (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_casesOn Primrec.snd hn hc).to₂.of_eq fun u w => by
    cases w <;> cases u <;> rfl

variable [DecidableEq C] [DecidableEq H]

omit [Primcodable C] [Primcodable H] in
 theorem cuts_fold (w : List (Letter C H)) :
    cuts w = w.foldr (fun a cs => if a = .leave then [.leave]::cs else glue [a] cs) [] := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [cuts,ih]

 theorem primrec_cuts : Primrec (cuts (C := C) (H := H)) := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const [])
    (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const Letter.leave))
      (Primrec.list_cons.comp (Primrec.const [Letter.leave]) (Primrec.snd.comp Primrec.snd))
      (primrec_glue.comp (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.const []))
        (Primrec.snd.comp Primrec.snd))).to₂).of_eq fun w => (cuts_fold w).symm

omit [DecidableEq C] [DecidableEq H] in
 theorem primrec_mem (a : Letter C H) : PrimrecPred (fun w : List (Letter C H) => a ∈ w) := by
  exact ((Primrec.eq.comp Primrec.id (Primrec.const a)).exists_mem_list).of_eq fun w => by simp

 theorem primrec_decode : Primrec (decode (C := C) (H := H)) := by
  let make : List (Letter C H) × H → Sector C H := fun p =>
    ⟨(lefts p.1).reverse,p.2,rights p.1,decide (.enter ∈ p.1),decide (.leave ∈ p.1)⟩
  have hm : Primrec make := Sector.primrec_mk
    (Primrec.list_reverse.comp (primrec_lefts.comp Primrec.fst)) Primrec.snd
    (primrec_rights.comp Primrec.fst) ((primrec_mem .enter).decide.comp Primrec.fst)
    ((primrec_mem .leave).decide.comp Primrec.fst)
  have ht : Primrec (fun p : List (Letter C H) × H =>
      if encode (make p) = p.1 then some (make p) else none) :=
    Primrec.ite (Primrec.eq.comp (primrec_encode.comp hm) Primrec.fst)
      (Primrec.option_some.comp hm) (Primrec.const none)
  have hh : Primrec (fun w : List (Letter C H) => if (heads w).length = 1 then
      (heads w).head?.bind (fun q => if encode (make (w,q)) = w then some (make (w,q)) else none)
      else none) :=
    Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp primrec_heads) (Primrec.const 1))
      (Primrec.option_bind (Primrec.list_head?.comp primrec_heads) ht.to₂) (Primrec.const none)
  exact hh.of_eq fun w => by
    unfold decode
    cases h : heads w with
    | nil => simp
    | cons q t => cases t with
      | nil => simp only [List.length_singleton,↓reduceIte,List.head?_cons,Option.bind_some]; rfl
      | cons q' t => simp

end FiniteAlgebraicEnvelopes.Compiler.Path.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler
open HeadCodec FiniteAlgebraicEnvelopes.Effect
open scoped HeadCodec

namespace Control.Uniform
variable {S Γ Q : Type*} [Fintype S] [Fintype Γ] [Primcodable Q]
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] in
theorem primrec_entry (blank : Γ) : PrimrecPred (Entry (S := S) (Q := Q) blank) :=
  (Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const Head.initial)).and
    (Primrec.eq.comp (Primrec.list_head?.comp Scan.Sector.primrec_right)
      (Primrec.const (some (Validator.cell blank .cutD))))

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] in
theorem primrec_success : PrimrecPred (Success (S := S) (Γ := Γ) (Q := Q)) :=
  (Primrec.eq.comp Scan.Sector.primrec_head (Primrec.const (Head.machine .ok))).and
    ((Primrec.eq.comp Scan.Sector.primrec_right (Primrec.const [])).and
      (Primrec.eq.comp Scan.Sector.primrec_rb (Primrec.const true)))
end Control.Uniform

namespace Path.Uniform
variable {P C H : Type*} [Primcodable P] [Primcodable C] [Primcodable H]
  [DecidableEq C] [DecidableEq H]

theorem primrec_prepareChunk_family {norm : P × Sector C H → List (Sector C H)}
    (hn : Primrec norm) : Primrec (fun x : P × List (Letter C H) =>
      prepareChunk (fun v => norm (x.1,v)) x.2) := by
  exact (Primrec.option_casesOn (primrec_decode.comp Primrec.snd)
    (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
    (Primrec.list_map (hn.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))
      (primrec_encode.comp Primrec.snd).to₂).to₂).of_eq
        fun x => by cases h : decode x.2 <;> simp [prepareChunk,h]

theorem primrec_prepareChunks_family {norm : P × Sector C H → List (Sector C H)}
    (hn : Primrec norm) : Primrec (fun x : P × List (List (Letter C H)) =>
      prepareChunks (fun v => norm (x.1,v)) x.2) :=
  Primrec.list_flatMap Primrec.snd ((primrec_prepareChunk_family hn).comp
    ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂

theorem primrec_prepare_family {norm : P × Sector C H → List (Sector C H)}
    (hn : Primrec norm) : Primrec (fun x : P × List (Letter C H) =>
      prepare (fun v => norm (x.1,v)) x.2) :=
  (primrec_prepareChunks_family hn).comp (Primrec.fst.pair (primrec_cuts.comp Primrec.snd))
end Path.Uniform

end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Compiler.RawRuns.Uniform
variable {P C S : Type*} [Primcodable P] [Primcodable C] [Primcodable S]

theorem partrec_action {f : P × List S → Part (List S)} (hf : Partrec f) :
    Partrec (fun x : P × Action C S => Action.partial (fun w => f (x.1,w)) x.2) := by
  have hh : Partrec₂ (fun (x : P × Action C S) (b : List S ⊕ List S) =>
      b.elim (fun w => Part.some (Sum.inr w : Item C S))
        (fun w => (f (x.1,w)).map (Sum.inr (α := C)))) := by
    exact (Partrec.sumCasesOn_right Computable.snd
      (Computable.sumInr.comp Computable.snd).to₂
      (((hf.comp ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair Computable.snd)).map
        (Computable.sumInr.comp Computable.snd).to₂).to₂)).to₂
  exact (Partrec.sumCasesOn_right (Action.primrec_code.to_comp.comp Computable.snd)
    (Computable.sumInl.comp Computable.snd).to₂ hh).of_eq fun x => by cases x.2 <;> rfl

theorem partrec_execute {f : P × List S → Part (List S)} (hf : Partrec f) :
    Partrec (fun x : P × List (Action C S) => execute (fun w => f (x.1,w)) x.2) := by
  apply (Effect.partrec_traverse_family (partrec_action (C := C) hf)).of_eq
  intro x
  induction x.2 with
  | nil => rfl
  | cons a l ih => simp only [Effect.traverse,execute,ih]

theorem partrec_partialSource {f : P × List S → Part (List S)} (hf : Partrec f) :
    Partrec (fun x : P × List (Item C S) => partialSource (fun w => f (x.1,w)) x.2) :=
  (partrec_execute hf).comp (Computable.fst.pair (primrec_plan.to_comp.comp Computable.snd))
end FiniteAlgebraicEnvelopes.Compiler.RawRuns.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler.Path
variable {C H H' : Type*}

def mapLetter (i : H → H') : Letter C H → Letter C H'
  | .zero => .zero
  | .enter => .enter
  | .leave => .leave
  | .left c => .left c
  | .right c => .right c
  | .head q => .head (i q)

def mapSector (i : H → H') (v : Sector C H) : Sector C H' :=
  ⟨v.left,i v.head,v.right,v.leftBoundary,v.rightBoundary⟩

variable (i : H → H')
@[simp] theorem typeOf_mapLetter (a : Letter C H) : typeOf (mapLetter i a)=typeOf a := by
  cases a <;> rfl
@[simp] theorem shape_map (w : List (Letter C H)) : shape (w.map (mapLetter i))=shape w := by
  simp [shape,List.map_map,Function.comp_def]

theorem mapLetter_injective (hi : Function.Injective i) : Function.Injective (mapLetter (C := C) i) := by
  intro a b h
  cases a <;> cases b <;> simp_all [mapLetter]
  exact hi h

@[simp] theorem headed_map (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    (headed l q r lb rb).map (mapLetter i)=headed l (i q) r lb rb := by
  cases lb <;> cases rb <;> simp [headed,List.map_map,Function.comp_def,mapLetter]
@[simp] theorem encode_map (v : Sector C H) :
    encode (mapSector i v)=(encode v).map (mapLetter i) := (headed_map i _ _ _ _ _).symm

@[simp] theorem heads_map (w : List (Letter C H)) :
    heads (w.map (mapLetter i))=(heads w).map i := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp only [heads,List.map_cons,List.filterMap_cons,mapLetter] at * <;> simp_all
@[simp] theorem lefts_map (w : List (Letter C H)) : lefts (w.map (mapLetter i))=lefts w := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp only [lefts,List.map_cons,List.filterMap_cons,mapLetter] at * <;> simp_all
@[simp] theorem rights_map (w : List (Letter C H)) : rights (w.map (mapLetter i))=rights w := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp only [rights,List.map_cons,List.filterMap_cons,mapLetter] at * <;> simp_all
@[simp] theorem enter_mem_map (w : List (Letter C H)) :
    .enter ∈ w.map (mapLetter i) ↔ .enter ∈ w := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨a,ha,he⟩; cases a <;> simp [mapLetter] at he; exact ha
  · intro h; exact ⟨.enter,h,rfl⟩
@[simp] theorem leave_mem_map (w : List (Letter C H)) :
    .leave ∈ w.map (mapLetter i) ↔ .leave ∈ w := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨a,ha,he⟩; cases a <;> simp [mapLetter] at he; exact ha
  · intro h; exact ⟨.leave,h,rfl⟩

variable [DecidableEq C] [DecidableEq H] [DecidableEq H']
theorem decode_map (hi : Function.Injective i) (w : List (Letter C H)) :
    decode (w.map (mapLetter i))=(decode w).map (mapSector i) := by
  have he (v : Sector C H) : encode (mapSector i v)=w.map (mapLetter i) ↔ encode v=w := by
    rw [encode_map]
    exact List.map_injective_iff.mpr (mapLetter_injective i hi) |>.eq_iff
  unfold decode
  rw [heads_map]
  cases h : heads w with
  | nil => rfl
  | cons q qs =>
    cases qs with
    | cons q' qs => rfl
    | nil =>
      simp only [List.map_cons,List.map_nil,lefts_map,rights_map,enter_mem_map,leave_mem_map]
      let v : Sector C H := ⟨(lefts w).reverse,q,rights w,decide (.enter∈w),decide (.leave∈w)⟩
      change (if encode (mapSector i v) = w.map (mapLetter i) then some (mapSector i v) else none) = _
      simp only [he]
      split <;> rfl

omit [DecidableEq C] [DecidableEq H] [DecidableEq H'] in
theorem glue_map (w : List (Letter C H)) (ws : List (List (Letter C H))) :
    glue (w.map (mapLetter i)) (ws.map (List.map (mapLetter i)))=
      (glue w ws).map (List.map (mapLetter i)) := by
  cases ws <;> cases w <;> simp [glue]
omit [DecidableEq C] [DecidableEq H] [DecidableEq H'] in
@[simp] theorem cuts_map (w : List (Letter C H)) :
    cuts (w.map (mapLetter i))=(cuts w).map (List.map (mapLetter i)) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have hh := glue_map i [a] (cuts w)
    cases a <;> simp only [List.map_cons,List.map_nil,mapLetter,cuts,ih] at hh ⊢ <;> exact hh

variable (p : Sector C H → List (Sector C H)) (p' : Sector C H' → List (Sector C H'))
  (hp : ∀ v,p' (mapSector i v)=(p v).map (mapSector i))
include hp in
theorem prepareChunk_map (hi : Function.Injective i) (w : List (Letter C H)) :
    prepareChunk p' (w.map (mapLetter i))=(prepareChunk p w).map (List.map (mapLetter i)) := by
  unfold prepareChunk
  rw [decode_map i hi]
  cases h : decode w with
  | none => rfl
  | some v => simp only [Option.map_some,hp,List.map_map,Function.comp_def,encode_map]
include hp in
theorem prepare_map (hi : Function.Injective i) (w : List (Letter C H)) :
    prepare p' (w.map (mapLetter i))=(prepare p w).map (List.map (mapLetter i)) := by
  simp only [prepare,prepareChunks,cuts_map,List.flatMap_map,List.map_flatMap]
  congr 1
  funext a
  exact prepareChunk_map i p p' hp hi a

end FiniteAlgebraicEnvelopes.Compiler.Path

namespace FiniteAlgebraicEnvelopes.Compiler.RawRuns
variable {C D S : Type*} (i : C → D)

theorem splitRun_map (w : List (Item C S)) :
    splitRun (w.map (Sum.map i id))=((splitRun w).1,(splitRun w).2.map (Sum.map i id)) := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp only [List.map_cons,Sum.map_inl,Sum.map_inr,id_eq,splitRun,ih]

theorem plan_map (w : List (Item C S)) :
    plan (w.map (Sum.map i id))=(plan w).map (Action.mapKeep i) := by
  cases w with
  | nil => simp only [List.map_nil,plan]
  | cons a w =>
    cases a with
    | inl c => simp only [List.map_cons,Sum.map_inl,plan,Action.mapKeep,plan_map w]
    | inr x =>
      rw [List.map_cons]
      simp only [Sum.map_inr,id_eq,plan,splitRun_map,List.map_cons,plan_map (splitRun w).2]
      cases (splitRun w).1 <;> rfl
termination_by w.length
decreasing_by all_goals have := splitRun_length w; simp_all only [List.length_cons]; omega

theorem Action.partial_map (f : List S → Part (List S)) (a : Action C S) :
    (a.mapKeep i).partial f=(a.partial f).map (Sum.map i id) := by
  cases a <;> simp only [Action.mapKeep,Action.partial,Part.map_some,Part.map_map,
    Function.comp_def,Sum.map_inl,Sum.map_inr,id_eq]

theorem execute_map (f : List S → Part (List S)) (p : List (Action C S)) :
    execute f (p.map (Action.mapKeep i))=(execute f p).map (List.map (Sum.map i id)) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.map_cons,execute,Action.partial_map,ih,Part.bind_map,Part.map_bind,Part.map_map]
    congr 1

theorem partialSource_map (f : List S → Part (List S)) (w : List (Item C S)) :
    partialSource f (w.map (Sum.map i id))=(partialSource f w).map (List.map (Sum.map i id)) := by
  simp only [partialSource,plan_map,execute_map]

end FiniteAlgebraicEnvelopes.Compiler.RawRuns

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometry
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology

noncomputable section

namespace PresentationGeometry

namespace AttachingLoops

open scoped unitInterval

theorem complexVector_continuous : Continuous complexVector := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact Complex.continuous_re
  · exact Complex.continuous_im

theorem complexVector_ne_zero (z : Circle) : complexVector z ≠ 0 := by
  intro h
  have hh := congrArg vectorComplex h
  simp only [vectorComplex_complexVector] at hh
  have hzero : vectorComplex 0 = 0 := by simp [vectorComplex]
  exact z.coe_ne_zero (hh.trans hzero)

def squareOfCircle : C(Circle, SquareBoundary) where
  toFun z := ((homeomorphUnitSphereProd (Fin 2 → ℝ))
    ⟨complexVector z, by simpa using complexVector_ne_zero z⟩).1
  continuous_toFun := continuous_fst.comp
    ((homeomorphUnitSphereProd (Fin 2 → ℝ)).continuous.comp
      ((complexVector_continuous.comp continuous_subtype_val).subtype_mk
        (fun z => by simpa using complexVector_ne_zero z)))

theorem boundaryAngle_squareOfCircle (z : Circle) :
    boundaryAngle (squareOfCircle z) = (Complex.arg z : Real.Angle) := by
  simp only [boundaryAngle, ContinuousMap.coe_mk, squareOfCircle,
    homeomorphUnitSphereProd_apply_fst_coe]
  change (Complex.arg (vectorComplex (‖complexVector z‖⁻¹ • complexVector z)) :
    Real.Angle) = _
  have hlin : ∀ (a : ℝ) (v : Fin 2 → ℝ),
      vectorComplex (a • v) = (a : ℂ) * vectorComplex v := by
    intro a v
    simp [vectorComplex, mul_add, mul_assoc]
  rw [hlin, vectorComplex_complexVector, Complex.arg_real_mul]
  exact inv_pos.mpr (norm_pos_iff.mpr (complexVector_ne_zero z))

def boundaryLift : C(AddCircle (1 : ℝ), SquareBoundary) :=
  let e := AddCircle.homeomorphAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero
  squareOfCircle.comp ((⟨AddCircle.homeomorphCircle',
    AddCircle.homeomorphCircle'.continuous⟩ : C(Real.Angle, Circle)).comp
      ⟨e.symm, e.symm.continuous⟩)

@[simp] theorem boundaryParameter_boundaryLift (z : AddCircle (1 : ℝ)) :
    boundaryParameter (boundaryLift z) = z := by
  change AddCircle.homeomorphAddCircle (2 * Real.pi) 1 _ _
    (boundaryAngle (squareOfCircle (AddCircle.homeomorphCircle'
      ((AddCircle.homeomorphAddCircle (2 * Real.pi) 1 _ _).symm z)))) = z
  rw [boundaryAngle_squareOfCircle]
  change AddCircle.homeomorphAddCircle (2 * Real.pi) 1 _ _
    (AddCircle.homeomorphCircle'.symm (AddCircle.homeomorphCircle' _)) = z
  simp only [Homeomorph.symm_apply_apply, Homeomorph.apply_symm_apply]

def boundaryLoop : Path (boundaryLift 0) (boundaryLift 0) where
  toFun t := boundaryLift ((t : ℝ) : AddCircle (1 : ℝ))
  continuous_toFun := boundaryLift.continuous.comp
    (continuous_quotient_mk'.comp continuous_subtype_val)
  source' := by simp
  target' := by
    change boundaryLift ((1 : ℝ) : AddCircle (1 : ℝ)) = boundaryLift 0
    rw [AddCircle.coe_period]

def relators {k r : ℕ} (w : Fin r → List (Fin k × Bool)) :
    C(Cells.boundary r 2, Rose.Space k) where
  toFun b := onCircle (Rose.wordLoop (w b.1.1)) (boundaryParameter ⟨b.1.2.1, b.2⟩)
  continuous_toFun := by
    have hf : Continuous (fun p : Fin r × AddCircle (1 : ℝ) =>
        onCircle (Rose.wordLoop (w p.1)) p.2) :=
      continuous_prod_of_discrete_left.mpr fun i => (onCircle (Rose.wordLoop (w i))).continuous
    have hp : Continuous (fun b : Cells.boundary r 2 =>
        boundaryParameter ⟨b.1.2.1, b.2⟩) :=
      boundaryParameter.continuous.comp
        ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _)
    exact hf.comp ((continuous_fst.comp continuous_subtype_val).prodMk hp)

end AttachingLoops

namespace PresentationComplex

variable {k r : ℕ} (w : Fin r → List (Fin k × Bool))

abbrev Space := Cells.Space (AttachingLoops.relators w)

def basepoint : Space w := Adjunction.old (AttachingLoops.relators w) (Rose.basepoint k)

def includeRose : C(Rose.Space k, Space w) :=
  ⟨Adjunction.old (AttachingLoops.relators w), Adjunction.continuous_old _⟩

def freeToFundamental : FreeGroup (Fin k) →* FundamentalGroup (Space w) (basepoint w) :=
  (FundamentalGroup.map (includeRose w) (Rose.basepoint k)).comp (Rose.freeToFundamental k)

def diskMap (i : Fin r) : C(Cells.Disk 2, Space w) :=
  ⟨fun v => Adjunction.disk (AttachingLoops.relators w) (i, v),
    (Adjunction.continuous_disk _).comp (continuous_const.prodMk continuous_id)⟩

def boundaryInDisk : C(AttachingLoops.SquareBoundary, Cells.Disk 2) :=
  ⟨fun b => ⟨b.1, Metric.sphere_subset_closedBall b.2⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem diskMap_boundary (i : Fin r) (b : AttachingLoops.SquareBoundary) :
    diskMap w i (boundaryInDisk b) = includeRose w
      (AttachingLoops.onCircle (Rose.wordLoop (w i)) (AttachingLoops.boundaryParameter b)) :=
  Adjunction.disk_boundary (AttachingLoops.relators w)
    ⟨(i, boundaryInDisk b), b.2⟩

theorem diskMap_boundary_basepoint (i : Fin r) :
    diskMap w i (boundaryInDisk (AttachingLoops.boundaryLift 0)) = basepoint w := by
  rw [diskMap_boundary, AttachingLoops.boundaryParameter_boundaryLift]
  have hh := AttachingLoops.onCircle_coe (Rose.wordLoop (w i)) 0
  change includeRose w _ = includeRose w (Rose.basepoint k)
  simpa using congrArg (includeRose w) hh

def filledRelatorLoop (i : Fin r) : Path (basepoint w) (basepoint w) :=
  (((AttachingLoops.boundaryLoop).map boundaryInDisk.continuous).map
    (diskMap w i).continuous).cast
      (diskMap_boundary_basepoint w i).symm (diskMap_boundary_basepoint w i).symm

theorem filledRelatorLoop_eq (i : Fin r) :
    filledRelatorLoop w i = (Rose.wordLoop (w i)).map (includeRose w).continuous := by
  ext t
  change diskMap w i (boundaryInDisk (AttachingLoops.boundaryLift
    ((t : ℝ) : AddCircle (1 : ℝ)))) = includeRose w (Rose.wordLoop (w i) t)
  rw [diskMap_boundary, AttachingLoops.boundaryParameter_boundaryLift,
    AttachingLoops.onCircle_coe]

theorem relator_nullhomotopic (i : Fin r) :
    ((Rose.wordLoop (w i)).map (includeRose w).continuous).Homotopic
      (Path.refl (basepoint w)) := by
  let : ContractibleSpace (Cells.Disk 2) := Metric.contractibleSpace_closedBall (by norm_num)
  have h := SimplyConnectedSpace.paths_homotopic
    (AttachingLoops.boundaryLoop.map boundaryInDisk.continuous)
    (Path.refl (boundaryInDisk (AttachingLoops.boundaryLift 0)))
  have hh := (h.map (diskMap w i)).pathCast
    (diskMap_boundary_basepoint w i).symm (diskMap_boundary_basepoint w i).symm
  change (filledRelatorLoop w i).Homotopic _ at hh
  rw [filledRelatorLoop_eq] at hh
  have href : ((Path.refl (boundaryInDisk (AttachingLoops.boundaryLift 0))).map
      (diskMap w i).continuous).cast
      (diskMap_boundary_basepoint w i).symm (diskMap_boundary_basepoint w i).symm =
      Path.refl (basepoint w) := by
    ext t
    exact diskMap_boundary_basepoint w i
  rw [href] at hh
  exact hh

theorem freeToFundamental_relator (i : Fin r) :
    freeToFundamental w (FreeGroup.mk (w i)) = 1 := by
  change FundamentalGroup.map (includeRose w) (Rose.basepoint k)
    (Rose.freeToFundamental k (FreeGroup.mk (w i))) = _
  rw [Rose.freeToFundamental_mk]
  exact Quotient.sound (relator_nullhomotopic w i)

def presentedToFundamental : PresentedGroup (relatorSet w) →*
    FundamentalGroup (Space w) (basepoint w) :=
  QuotientGroup.lift (Subgroup.normalClosure (relatorSet w)) (freeToFundamental w)
    (Subgroup.normalClosure_le_normal (by
      rintro _ ⟨i, rfl⟩
      exact freeToFundamental_relator w i))

@[simp]
theorem presentedToFundamental_mk (g : FreeGroup (Fin k)) :
    presentedToFundamental w (PresentedGroup.mk (relatorSet w) g) =
      freeToFundamental w g := rfl

end PresentationComplex

end PresentationGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryDescend
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology
noncomputable section
open Set Function
open scoped unitInterval
namespace PresentationGeometry
namespace Adjunction

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {A : Set Y} (f : C(A, X))

def descend (g : X → Z) (h : Y → Z) (he : ∀ a : A, h a.1 = g (f a)) :
    Space f → Z := by
  classical
  refine Quotient.lift (Sum.elim g h) ?_
  have hn : ∀ a, Sum.elim g h (normalize f a) = Sum.elim g h a := by
    intro a
    cases a with
    | inl x => rfl
    | inr y =>
      by_cases hy : y ∈ A
      · simpa only [normalize_inr_mem f ⟨y, hy⟩, Sum.elim_inl, Sum.elim_inr] using
          (he ⟨y, hy⟩).symm
      · rw [normalize_inr_notMem f y hy]
  intro a b hab
  exact (hn a).symm.trans ((congrArg (Sum.elim g h) hab).trans (hn b))

omit [TopologicalSpace Z] in
@[simp] theorem descend_old (g : X → Z) (h : Y → Z)
    (he : ∀ a : A, h a.1 = g (f a)) (x : X) :
    descend f g h he (old f x) = g x := rfl

omit [TopologicalSpace Z] in
@[simp] theorem descend_disk (g : X → Z) (h : Y → Z)
    (he : ∀ a : A, h a.1 = g (f a)) (y : Y) :
    descend f g h he (disk f y) = h y := rfl

theorem continuous_descend (g : C(X, Z)) (h : C(Y, Z))
    (he : ∀ a : A, h a.1 = g (f a)) : Continuous (descend f g h he) :=
  (g.continuous.sumElim h.continuous).quotient_lift _

end Adjunction
namespace Cells

open Metric

def innerClosed {X : Type*} [TopologicalSpace X] {k d : ℕ}
    (f : C(boundary k d, X)) : Set (Space f) :=
  Adjunction.disk f '' {p : Fin k × Disk d | ‖p.2.1‖ ≤ (1 / 2 : ℝ)}

def collar {X : Type*} [TopologicalSpace X] {k d : ℕ}
    (f : C(boundary k d, X)) : Set (Space f) := (innerClosed f)ᶜ

def cellInterior {X : Type*} [TopologicalSpace X] {k d : ℕ}
    (f : C(boundary k d, X)) (i : Fin k) : Set (Space f) :=
  range ((OpenDisk d).domRestrict (characteristic f i))

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable {k d : ℕ} (f : C(boundary k d, X))

theorem collar_isOpen : IsOpen (collar f) := by
  have hc : IsClosed (innerClosed f) := ((isClosed_le (continuous_norm.comp (continuous_subtype_val.comp continuous_snd))
    continuous_const).isCompact.image (Adjunction.continuous_disk f)).isClosed
  exact hc.isOpen_compl

omit [T2Space X] [CompactSpace X] in
theorem cellInterior_isOpen (i : Fin k) : IsOpen (cellInterior f i) :=
  (characteristic_isOpenEmbedding f i).isOpen_range

omit [T2Space X] [CompactSpace X] in
theorem mem_collar_old (x : X) : Adjunction.old f x ∈ collar f := by
  rintro ⟨p, hp, he⟩
  have hpn : p ∉ boundary k d := by
    intro hh
    have hh' : ‖p.2.1‖ = 1 := by simpa only [boundary, mem_ofPred_eq, mem_sphere_zero_iff_norm] using hh
    change ‖p.2.1‖ ≤ (1 / 2 : ℝ) at hp
    linarith
  exact Adjunction.old_ne_disk_of_notMem f x hpn he.symm

omit [T2Space X] [CompactSpace X] in
theorem mem_collar_disk_iff (i : Fin k) (v : Disk d) :
    Adjunction.disk f (i, v) ∈ collar f ↔ (1 / 2 : ℝ) < ‖v.1‖ := by
  change (¬ ∃ p, ‖p.2.1‖ ≤ (1 / 2 : ℝ) ∧ Adjunction.disk f p = _) ↔ _
  constructor
  · intro h
    by_contra hn
    exact h ⟨(i, v), le_of_not_gt hn, rfl⟩
  · intro hv ⟨p, hp, he⟩
    have hpn : p ∉ boundary k d := by
      intro hh
      have hh' : ‖p.2.1‖ = 1 := by
        simpa only [boundary, mem_ofPred_eq, mem_sphere_zero_iff_norm] using hh
      linarith
    have he' := (Adjunction.disk_eq_disk_of_notMem f hpn).mp he
    cases he'
    exact (not_le.mpr hv) hp

omit [T2Space X] [CompactSpace X] in
theorem characteristic_on_openDisk (i : Fin k) (v : OpenDisk d) :
    characteristic f i v.1 = Adjunction.disk f (i, interiorInDisk v) :=
  characteristic_on_disk f i (interiorInDisk v)

omit [T2Space X] [CompactSpace X] in
theorem cellInterior_pairwiseDisjoint : Pairwise (Disjoint on cellInterior f) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro z ⟨u, rfl⟩ ⟨v, hv⟩
  change characteristic f j v.1 = characteristic f i u.1 at hv
  rw [characteristic_on_openDisk f i u, characteristic_on_openDisk f j v] at hv
  have he : (j, interiorInDisk v) = (i, interiorInDisk u) :=
    (Adjunction.disk_eq_disk_of_notMem f (interiorInFamily j v).property).mp hv
  exact hij (congrArg Prod.fst he).symm

omit [T2Space X] [CompactSpace X] in
theorem collar_union_interiors : collar f ∪ ⋃ i, cellInterior f i = univ := by
  apply eq_univ_of_forall
  intro z
  by_cases hz : z ∈ collar f
  · exact Or.inl hz
  · have hz' : z ∈ innerClosed f := not_not.mp hz
    obtain ⟨⟨i, v⟩, hv, rfl⟩ := hz'
    right
    apply mem_iUnion.mpr
    refine ⟨i, ⟨⟨v.1, ?_⟩, ?_⟩⟩
    · rw [mem_ball_zero_iff]
      change ‖v.1‖ ≤ (1 / 2 : ℝ) at hv
      linarith
    · exact characteristic_on_disk f i v

end Cells
end PresentationGeometry

namespace PresentationGeometry.Cells
section

open Metric

def shellInDisk {d : ℕ} (v : Shell d) : Disk d :=
  ⟨v.1, mem_closedBall_zero_iff.mpr v.2.2⟩

@[fun_prop] theorem shellInDisk_continuous {dimension : ℕ} :
    Continuous (shellInDisk (d := dimension)) :=
  continuous_subtype_val.subtype_mk _

def shellBoundary (k d : ℕ) : Set (Fin k × Shell d) := {p | ‖p.2.1‖ = 1}

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable {k d : ℕ} (f : C(boundary k d, X))

def shellAttach : C(shellBoundary k d, X) where
  toFun p := f ⟨(p.1.1, shellInDisk p.1.2), mem_sphere_zero_iff_norm.mpr p.2⟩
  continuous_toFun := f.continuous.comp (by fun_prop)

abbrev ClosedCollarSpace := Adjunction.Space (shellAttach f)

def shellInclude : ClosedCollarSpace f → Space f :=
  Adjunction.descend (shellAttach f) (Adjunction.old f)
    (fun p => Adjunction.disk f (p.1, shellInDisk p.2))
    (fun p => Adjunction.disk_boundary f
      ⟨(p.1.1, shellInDisk p.1.2), mem_sphere_zero_iff_norm.mpr p.2⟩)

omit [T2Space X] [CompactSpace X] in
@[simp] theorem shellInclude_old (x : X) :
    shellInclude f (Adjunction.old (shellAttach f) x) = Adjunction.old f x := rfl

omit [T2Space X] [CompactSpace X] in
@[simp] theorem shellInclude_disk (p : Fin k × Shell d) :
    shellInclude f (Adjunction.disk (shellAttach f) p) =
      Adjunction.disk f (p.1, shellInDisk p.2) := rfl

omit [T2Space X] [CompactSpace X] in
theorem shellInclude_continuous : Continuous (shellInclude f) := by
  apply Adjunction.continuous_descend (shellAttach f)
    ⟨_, Adjunction.continuous_old f⟩
    ⟨_, (Adjunction.continuous_disk f).comp (by fun_prop)⟩

omit [T2Space X] [CompactSpace X] in
theorem shellInclude_injective : Injective (shellInclude f) := by
  let m : X ⊕ (Fin k × Shell d) → X ⊕ (Fin k × Disk d) :=
    Sum.map id (fun p => (p.1, shellInDisk p.2))
  have hm : Injective m := by
    apply Function.Injective.sumMap (fun _ _ h => h)
    intro a b h
    apply Prod.ext
    · exact congrArg (fun p : Fin k × Disk d => p.1) h
    · apply Subtype.ext
      exact congrArg (fun p => p.2.1) h
  have hn : ∀ a, Adjunction.normalize f (m a) = m (Adjunction.normalize (shellAttach f) a) := by
    intro a
    cases a with
    | inl x => rfl
    | inr p =>
      by_cases hp : p ∈ shellBoundary k d
      · have hp' : (p.1, shellInDisk p.2) ∈ boundary k d :=
          mem_sphere_zero_iff_norm.mpr hp
        change Adjunction.normalize f (Sum.inr (p.1, shellInDisk p.2)) = _
        rw [Adjunction.normalize_inr_mem f ⟨_, hp'⟩,
          Adjunction.normalize_inr_mem (shellAttach f) ⟨p, hp⟩]
        rfl
      · have hp' : (p.1, shellInDisk p.2) ∉ boundary k d := by
          intro hh
          apply hp
          exact mem_sphere_zero_iff_norm.mp hh
        change Adjunction.normalize f (Sum.inr (p.1, shellInDisk p.2)) = _
        rw [Adjunction.normalize_inr_notMem f _ hp',
          Adjunction.normalize_inr_notMem (shellAttach f) p hp]
        rfl
  intro a b hab
  induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
      apply Quotient.sound
      apply hm
      rw [← hn a, ← hn b]
      have hq : ∀ z, shellInclude f (Quotient.mk (Adjunction.relation (shellAttach f)) z) =
          Quotient.mk (Adjunction.relation f) (m z) := by
        intro z; cases z <;> rfl
      rw [hq, hq] at hab
      exact Quotient.exact hab

theorem shellInclude_isClosedEmbedding : IsClosedEmbedding (shellInclude f) :=
  (shellInclude_continuous f).isClosedEmbedding (shellInclude_injective f)

omit [T2Space X] [CompactSpace X] in
theorem collar_subset_range_shellInclude : collar f ⊆ range (shellInclude f) := by
  intro z hz
  obtain ⟨x | p, rfl⟩ := Quotient.mk_surjective z
  · exact ⟨Adjunction.old (shellAttach f) x, rfl⟩
  · have hp : (1 / 2 : ℝ) < ‖p.2.1‖ := (mem_collar_disk_iff f p.1 p.2).mp hz
    refine ⟨Adjunction.disk (shellAttach f)
      (p.1, ⟨p.2.1, hp.le, mem_closedBall_zero_iff.mp p.2.2⟩), ?_⟩
    rfl

def collarToShell : C(collar f, ClosedCollarSpace f) where
  toFun z := (shellInclude_isClosedEmbedding f).isEmbedding.toHomeomorph.symm
    ⟨z.1, collar_subset_range_shellInclude f z.2⟩
  continuous_toFun :=
    (shellInclude_isClosedEmbedding f).isEmbedding.toHomeomorph.symm.continuous.comp
      (continuous_subtype_val.subtype_mk _)

@[simp] theorem shellInclude_collarToShell (z : collar f) :
    shellInclude f (collarToShell f z) = z.1 :=
  congrArg Subtype.val ((shellInclude_isClosedEmbedding f).isEmbedding.toHomeomorph.apply_symm_apply _)

end

open Metric
open scoped unitInterval

variable {k d : ℕ}

theorem shell_norm_pos (v : Shell d) : 0 < ‖v.1‖ := by
  linarith [v.2.1]

def shellUnit (p : Fin k × Shell d) : boundary k d := by
  have hn : ‖p.2.1‖ ≠ 0 := (shell_norm_pos p.2).ne'
  have hunit : ‖‖p.2.1‖⁻¹ • p.2.1‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  exact ⟨(p.1, ⟨‖p.2.1‖⁻¹ • p.2.1, mem_closedBall_zero_iff.mpr hunit.le⟩),
    mem_sphere_zero_iff_norm.mpr hunit⟩

theorem shellUnit_continuous : Continuous (shellUnit (k := k) (d := d)) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk continuous_fst
  apply Continuous.subtype_mk
  exact ((continuous_norm.comp (continuous_subtype_val.comp continuous_snd)).inv₀
    (fun p => (shell_norm_pos p.2).ne')).smul (continuous_subtype_val.comp continuous_snd)

theorem shellUnit_boundary (p : shellBoundary k d) :
    shellUnit p.1 = ⟨(p.1.1, shellInDisk p.1.2), mem_sphere_zero_iff_norm.mpr p.2⟩ := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change ‖p.1.2.1‖⁻¹ • p.1.2.1 = p.1.2.1
    rw [show ‖p.1.2.1‖ = 1 from p.2, inv_one, one_smul]

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable (f : C(boundary k d, X))

def shellRetraction : C(ClosedCollarSpace f, X) where
  toFun := Adjunction.descend (shellAttach f) id (f ∘ shellUnit)
    (fun p => congrArg f (shellUnit_boundary p))
  continuous_toFun := Adjunction.continuous_descend (shellAttach f)
    (ContinuousMap.id X) ⟨f ∘ shellUnit, f.continuous.comp shellUnit_continuous⟩ _

omit [T2Space X] [CompactSpace X] in
@[simp] theorem shellRetraction_old (x : X) :
    shellRetraction f (Adjunction.old (shellAttach f) x) = x := rfl

omit [T2Space X] [CompactSpace X] in
@[simp] theorem shellRetraction_disk (p : Fin k × Shell d) :
    shellRetraction f (Adjunction.disk (shellAttach f) p) = f (shellUnit p) := rfl

def radialVector (t : I) (v : Shell d) : Fin d → ℝ :=
  ((1 - (t : ℝ)) + (t : ℝ) * ‖v.1‖⁻¹) • v.1

theorem norm_radialVector (t : I) (v : Shell d) :
    ‖radialVector t v‖ = (1 - (t : ℝ)) * ‖v.1‖ + (t : ℝ) := by
  have hn : ‖v.1‖ ≠ 0 := (shell_norm_pos v).ne'
  have hc : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) * ‖v.1‖⁻¹ :=
    add_nonneg (sub_nonneg.mpr t.2.2) (mul_nonneg t.2.1 (inv_nonneg.mpr (norm_nonneg _)))
  rw [radialVector, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, add_mul,
    mul_assoc, inv_mul_cancel₀ hn, mul_one]

def radialDisk (t : I) (v : Shell d) : Disk d :=
  ⟨radialVector t v, mem_closedBall_zero_iff.mpr (by
    rw [norm_radialVector]
    nlinarith [v.2.2, mul_nonneg (sub_nonneg.mpr t.2.2) (sub_nonneg.mpr v.2.2)])⟩

@[simp] theorem radialDisk_zero (v : Shell d) : radialDisk 0 v = shellInDisk v := by
  apply Subtype.ext
  simp [radialDisk, radialVector, shellInDisk]

@[simp] theorem radialDisk_boundary (t : I) (p : shellBoundary k d) :
    radialDisk t p.1.2 = shellInDisk p.1.2 := by
  apply Subtype.ext
  change ((1 - (t : ℝ)) + (t : ℝ) * ‖p.1.2.1‖⁻¹) • p.1.2.1 = p.1.2.1
  rw [show ‖p.1.2.1‖ = 1 from p.2, inv_one, mul_one, sub_add_cancel, one_smul]

def shellSlide (t : I) : ClosedCollarSpace f → Space f :=
  Adjunction.descend (shellAttach f) (Adjunction.old f)
    (fun p => Adjunction.disk f (p.1, radialDisk t p.2)) (fun p => by
      rw [radialDisk_boundary t p]
      exact Adjunction.disk_boundary f
        ⟨(p.1.1, shellInDisk p.1.2), mem_sphere_zero_iff_norm.mpr p.2⟩)

omit [T2Space X] [CompactSpace X] in
@[simp] theorem shellSlide_old (t : I) (x : X) :
    shellSlide f t (Adjunction.old (shellAttach f) x) = Adjunction.old f x := rfl

omit [T2Space X] [CompactSpace X] in
@[simp] theorem shellSlide_disk (t : I) (p : Fin k × Shell d) :
    shellSlide f t (Adjunction.disk (shellAttach f) p) =
      Adjunction.disk f (p.1, radialDisk t p.2) := rfl

omit [T2Space X] [CompactSpace X] in
@[simp] theorem shellSlide_zero (z : ClosedCollarSpace f) :
    shellSlide f 0 z = shellInclude f z := by
  induction z using Quotient.inductionOn with | h z =>
    cases z with
    | inl x => rfl
    | inr p => exact congrArg (fun v => Adjunction.disk f (p.1, v)) (radialDisk_zero p.2)

omit [T2Space X] [CompactSpace X] in
@[simp] theorem shellSlide_one (z : ClosedCollarSpace f) :
    shellSlide f 1 z = Adjunction.old f (shellRetraction f z) := by
  induction z using Quotient.inductionOn with | h z =>
    cases z with
    | inl x => rfl
    | inr p =>
      change Adjunction.disk f (p.1, radialDisk 1 p.2) = Adjunction.old f (f (shellUnit p))
      have hv : (p.1, radialDisk 1 p.2) = (shellUnit p).1 := by
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          simp [radialDisk, radialVector, shellUnit]
      rw [hv]
      exact Adjunction.disk_boundary f (shellUnit p)

@[simp] theorem collarToShell_old (x : X) :
    collarToShell f ⟨Adjunction.old f x, mem_collar_old f x⟩ =
      Adjunction.old (shellAttach f) x := by
  apply shellInclude_injective f
  rw [shellInclude_collarToShell, shellInclude_old]

end PresentationGeometry.Cells

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryCells
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
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

open Set Metric
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable {k d : ℕ} (f : C(boundary k d, X))

def collarRetraction : C(collar f, X) := (shellRetraction f).comp (collarToShell f)

@[simp] theorem collarRetraction_old (x : X) :
    collarRetraction f ⟨Adjunction.old f x, mem_collar_old f x⟩ = x := by
  simp [collarRetraction]

def interiorLift (i : Fin k) : C(cellInterior f i, OpenDisk d) :=
  ⟨(characteristic_isOpenEmbedding f i).isEmbedding.toHomeomorph.symm,
    (characteristic_isOpenEmbedding f i).isEmbedding.toHomeomorph.symm.continuous⟩

omit [T2Space X] [CompactSpace X] in
@[simp] theorem interiorLift_disk (i : Fin k) (z : cellInterior f i) :
    Adjunction.disk f (i,interiorInDisk (interiorLift f i z)) = z.1 := by
  rw [← characteristic_on_openDisk]
  exact congrArg Subtype.val
    ((characteristic_isOpenEmbedding f i).isEmbedding.toHomeomorph.apply_symm_apply z)

omit [T2Space X] [CompactSpace X] in
theorem overlapLift_half (i : Fin k) (z : (collar f ∩ cellInterior f i : Set (Space f))) :
    (1/2 : ℝ) < ‖(interiorLift f i ⟨z.1,z.2.2⟩).1‖ := by
  apply (mem_collar_disk_iff f i (interiorInDisk (interiorLift f i ⟨z.1,z.2.2⟩))).mp
  rw [interiorLift_disk]
  exact z.2.1

def overlapShell (i : Fin k) (z : (collar f ∩ cellInterior f i : Set (Space f))) : Shell d :=
  ⟨(interiorLift f i ⟨z.1,z.2.2⟩).1, (overlapLift_half f i z).le,
    (mem_ball_zero_iff.mp (interiorLift f i ⟨z.1,z.2.2⟩).2).le⟩

omit [T2Space X] [CompactSpace X] in
theorem overlapShell_continuous (i : Fin k) : Continuous (overlapShell f i) :=
  (continuous_subtype_val.comp ((interiorLift f i).continuous.comp
    (continuous_subtype_val.subtype_mk (fun z => z.2.2)))).subtype_mk _

def overlapBoundary (i : Fin k) : C((collar f ∩ cellInterior f i : Set (Space f)), boundary k d) :=
  ⟨fun z => shellUnit (i,overlapShell f i z),
    shellUnit_continuous.comp (continuous_const.prodMk (overlapShell_continuous f i))⟩

theorem collarToShell_overlap (i : Fin k) (z : (collar f ∩ cellInterior f i : Set (Space f))) :
    collarToShell f ⟨z.1,z.2.1⟩ = Adjunction.disk (shellAttach f) (i,overlapShell f i z) := by
  apply shellInclude_injective f
  rw [shellInclude_collarToShell,shellInclude_disk]
  exact (interiorLift_disk f i ⟨z.1,z.2.2⟩).symm

@[simp] theorem collarRetraction_overlap (i : Fin k)
    (z : (collar f ∩ cellInterior f i : Set (Space f))) :
    collarRetraction f ⟨z.1,z.2.1⟩ = f (overlapBoundary f i z) := by
  change shellRetraction f (collarToShell f _) = _
  rw [collarToShell_overlap, shellRetraction_disk]
  rfl

end PresentationGeometry.Cells

namespace PresentationGeometry.CellCoverExtension
open Set Cells
variable {X ι Q : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
variable {k d : ℕ} (f : C(boundary k d, X)) (b : X) (Z : FiberBundleCore ι X Q)

def baseSet : ι ⊕ Fin k → Set (Cells.Space f)
  | .inl j => Subtype.val '' ((collarRetraction f) ⁻¹' Z.baseSet j)
  | .inr i => cellInterior f i

omit [Group Q] [DiscreteTopology Q] in
@[simp] theorem mem_baseSet_old (j : ι) (x : Cells.Space f) :
    x ∈ baseSet f Z (.inl j) ↔ ∃ h : x ∈ collar f, collarRetraction f ⟨x,h⟩ ∈ Z.baseSet j := by
  constructor
  · rintro ⟨⟨x,hx⟩,h,rfl⟩
    exact ⟨hx,h⟩
  · rintro ⟨hx,h⟩
    exact ⟨⟨x,hx⟩,h,rfl⟩

omit [Group Q] [DiscreteTopology Q] in
theorem baseSet_isOpen (a : ι ⊕ Fin k) : IsOpen (baseSet f Z a) := by
  cases a with
  | inl j =>
    exact (collar_isOpen f).isOpenMap_subtype_val _
      ((Z.isOpen_baseSet j).preimage (collarRetraction f).continuous)
  | inr i => exact cellInterior_isOpen f i

omit [Group Q] [DiscreteTopology Q] in
theorem mem_baseSet (x : Cells.Space f) : ∃ a, x ∈ baseSet f Z a := by
  have hx : x ∈ collar f ∪ ⋃ i, cellInterior f i := by rw [collar_union_interiors]; trivial
  rcases hx with hx | hx
  · exact ⟨.inl (Z.indexAt (collarRetraction f ⟨x,hx⟩)),
      (mem_baseSet_old f Z _ x).mpr ⟨hx,Z.mem_baseSet_at _⟩⟩
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact ⟨.inr i,hi⟩

noncomputable def retractAt (x : Cells.Space f) : X := by
  classical
  exact if hx : x ∈ collar f then collarRetraction f ⟨x,hx⟩ else b

@[simp] theorem retractAt_collar (x : collar f) : retractAt f b x.1 = collarRetraction f x := by
  classical
  simp only [retractAt,dite_eq_left x.2]

@[simp] theorem retractAt_old (x : X) : retractAt f b (Adjunction.old f x) = x := by
  exact (retractAt_collar f b ⟨Adjunction.old f x,mem_collar_old f x⟩).trans
    (collarRetraction_old f x)

variable (pot : ι → X → Q)
variable (s : C(boundary k d,Z.TotalSpace))
variable (hs : ∀ c, Z.proj (s c) = f c)

def overlapSection (i : Fin k) : C((collar f ∩ cellInterior f i : Set (Cells.Space f)),Z.TotalSpace) :=
  s.comp (overlapBoundary f i)

include hs in
omit [Group Q] [DiscreteTopology Q] in
@[simp] theorem overlapSection_proj (i : Fin k)
    (x : (collar f ∩ cellInterior f i : Set (Cells.Space f))) :
    Z.proj (overlapSection f Z s i x) = collarRetraction f ⟨x.1,x.2.1⟩ := by
  rw [collarRetraction_overlap]
  exact hs _

noncomputable def potential : ι ⊕ Fin k → Cells.Space f → Q := by
  classical
  exact fun
    | .inl j,x => pot j (retractAt f b x)
    | .inr i,x => if hx : x ∈ collar f ∩ cellInterior f i then
        ((pot (Z.indexAt (retractAt f b x)) (retractAt f b x))⁻¹ *
          (show Q from (overlapSection f Z s i ⟨x,hx⟩).2))⁻¹ else 1

noncomputable def transition (i j : ι ⊕ Fin k) (x : Cells.Space f) (q : Q) : Q :=
  potential f b Z pot s j x * (potential f b Z pot s i x)⁻¹ * q

def mixedCoordinate (j : ι) (i : Fin k) :
    C((baseSet f Z (.inl j) ∩ baseSet f Z (.inr i) : Set (Cells.Space f)),Q) := by
  let lift : C((baseSet f Z (.inl j) ∩ baseSet f Z (.inr i) : Set (Cells.Space f)),Z.TotalSpace) :=
    (overlapSection f Z s i).comp
      ⟨fun x => ⟨x.1,(mem_baseSet_old f Z j x.1).mp x.2.1 |>.choose,x.2.2⟩,
        continuous_subtype_val.subtype_mk _⟩
  refine ⟨fun x => ((Z.localTriv j) (lift x)).2, ?_⟩
  apply continuous_snd.comp
  apply (Z.localTriv j).continuousOn.comp_continuous lift.continuous
  intro x
  change (lift x).1 ∈ Z.baseSet j
  rw [show (lift x).1 = collarRetraction f
      ⟨x.1, (mem_baseSet_old f Z j x.1).mp x.2.1 |>.choose⟩ from
        overlapSection_proj f Z s hs i _]
  exact (mem_baseSet_old f Z j x.1).mp x.2.1 |>.choose_spec

variable (hpot : ∀ i j x q, Z.coordChange i j x q = pot j x * (pot i x)⁻¹ * q)

include hpot in
omit [DiscreteTopology Q] in
theorem mixedCoordinate_formula (j : ι) (i : Fin k)
    (x : (baseSet f Z (.inl j) ∩ baseSet f Z (.inr i) : Set (Cells.Space f))) :
    mixedCoordinate f Z s hs j i x =
      potential f b Z pot s (.inl j) x.1 * (potential f b Z pot s (.inr i) x.1)⁻¹ := by
  classical
  have hx : x.1 ∈ collar f ∩ cellInterior f i :=
    ⟨((mem_baseSet_old f Z j x.1).mp x.2.1).choose,x.2.2⟩
  change Z.coordChange (Z.indexAt (overlapSection f Z s i ⟨x.1,hx⟩).1) j
    (overlapSection f Z s i ⟨x.1,hx⟩).1 (overlapSection f Z s i ⟨x.1,hx⟩).2 = _
  have he : (overlapSection f Z s i ⟨x.1,hx⟩).1 = retractAt f b x.1 := by
    exact (overlapSection_proj f Z s hs i ⟨x.1,hx⟩).trans
      (retractAt_collar f b ⟨x.1,hx.1⟩).symm
  erw [hpot,he]
  simp only [potential,dite_eq_left hx,inv_inv]
  exact mul_assoc _ _ _

include hpot in
omit [DiscreteTopology Q] in
theorem transition_old_new (j : ι) (i : Fin k)
    (x : (baseSet f Z (.inl j) ∩ baseSet f Z (.inr i) : Set (Cells.Space f))) (q : Q) :
    transition f b Z pot s (.inl j) (.inr i) x.1 q =
      (mixedCoordinate f Z s hs j i x)⁻¹ * q := by
  rw [mixedCoordinate_formula f b Z pot s hs hpot]
  simp only [transition,mul_inv_rev,inv_inv]

include hpot in
omit [DiscreteTopology Q] in
theorem transition_new_old (j : ι) (i : Fin k)
    (x : (baseSet f Z (.inl j) ∩ baseSet f Z (.inr i) : Set (Cells.Space f))) (q : Q) :
    transition f b Z pot s (.inr i) (.inl j) x.1 q =
      mixedCoordinate f Z s hs j i x * q := by
  rw [mixedCoordinate_formula f b Z pot s hs hpot]
  rfl

include hs hpot in
theorem continuousOn_transition (i j : ι ⊕ Fin k) :
    ContinuousOn (fun p : Cells.Space f × Q => transition f b Z pot s i j p.1 p.2)
      ((baseSet f Z i ∩ baseSet f Z j) ×ˢ univ) := by
  classical
  by_cases hij : i = j
  · subst j
    simpa [transition] using (continuous_snd : Continuous (Prod.snd : Cells.Space f × Q → Q)).continuousOn
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      rw [continuousOn_iff_continuous_domRestrict]
      let D := ((baseSet f Z (.inl i) ∩ baseSet f Z (.inl j)) ×ˢ (univ : Set Q))
      let c : C(D, collar f) := ⟨fun p => ⟨p.1.1,
        ((mem_baseSet_old f Z i p.1.1).mp p.2.1.1).choose⟩,
        (continuous_fst.comp continuous_subtype_val).subtype_mk _⟩
      have hr : Continuous (fun p : D => (collarRetraction f (c p),p.1.2)) :=
        ((collarRetraction f).continuous.comp c.continuous).prodMk
          (continuous_snd.comp continuous_subtype_val)
      have hc := (Z.continuousOn_coordChange i j).comp_continuous hr (fun p =>
        (show (collarRetraction f (c p),p.1.2) ∈ (Z.baseSet i ∩ Z.baseSet j) ×ˢ univ from
          ⟨⟨((mem_baseSet_old f Z i p.1.1).mp p.2.1.1).choose_spec,
            ((mem_baseSet_old f Z j p.1.1).mp p.2.1.2).choose_spec⟩,mem_univ _⟩))
      convert hc using 1
      all_goals try with_reducible_and_instances rfl
      funext p
      change transition f b Z pot s (.inl i) (.inl j) p.1.1 p.1.2 =
        Z.coordChange i j (collarRetraction f (c p)) p.1.2
      rw [hpot]
      simp only [transition,potential]
      rw [show retractAt f b p.1.1 = collarRetraction f (c p) from retractAt_collar f b (c p)]
    | inr j =>
      rw [continuousOn_iff_continuous_domRestrict]
      have hc : Continuous (fun p : (baseSet f Z (.inl i) ∩ baseSet f Z (.inr j)) ×ˢ (univ : Set Q) =>
          mixedCoordinate f Z s hs i j ⟨p.1.1,p.2.1⟩) :=
        (mixedCoordinate f Z s hs i j).continuous.comp
          ((continuous_fst.comp continuous_subtype_val).subtype_mk _)
      convert hc.inv.mul (continuous_snd.comp continuous_subtype_val) using 1
      all_goals try with_reducible_and_instances rfl
      funext p
      exact transition_old_new f b Z pot s hs hpot i j ⟨p.1.1,p.2.1⟩ p.1.2
  | inr i =>
    cases j with
    | inl j =>
      rw [inter_comm,continuousOn_iff_continuous_domRestrict]
      have hc : Continuous (fun p : (baseSet f Z (.inl j) ∩ baseSet f Z (.inr i)) ×ˢ (univ : Set Q) =>
          mixedCoordinate f Z s hs j i ⟨p.1.1,p.2.1⟩) :=
        (mixedCoordinate f Z s hs j i).continuous.comp
          ((continuous_fst.comp continuous_subtype_val).subtype_mk _)
      convert hc.mul (continuous_snd.comp continuous_subtype_val) using 1
      all_goals try with_reducible_and_instances rfl
      funext p
      exact transition_new_old f b Z pot s hs hpot j i ⟨p.1.1,p.2.1⟩ p.1.2
    | inr j =>
      have hd := cellInterior_pairwiseDisjoint f (by
        intro h; apply hij; exact congrArg Sum.inr h : i ≠ j)
      have he : baseSet f Z (.inr i) ∩ baseSet f Z (.inr j) = ∅ := hd.inter_eq
      rw [he,empty_prod]
      exact continuousOn_empty _

noncomputable def coveringCore : FiberBundleCore (ι ⊕ Fin k) (Cells.Space f) Q where
  baseSet := baseSet f Z
  isOpen_baseSet := baseSet_isOpen f Z
  indexAt x := (mem_baseSet f Z x).choose
  mem_baseSet_at x := (mem_baseSet f Z x).choose_spec
  coordChange := transition f b Z pot s
  coordChange_self := by intros; simp [transition]
  continuousOn_coordChange := continuousOn_transition f b Z pot s hs hpot
  coordChange_comp := by intros; simp only [transition]; group

@[simp] theorem coveringCore_old_coordChange (i j : ι) (x : X) (q : Q) :
    (coveringCore f b Z pot s hs hpot).coordChange (.inl i) (.inl j) (Adjunction.old f x) q =
      Z.coordChange i j x q := by
  rw [hpot]
  simp only [coveringCore,transition,potential,retractAt_old]

@[simp] theorem mem_coveringCore_old (i : ι) (x : X) :
    Adjunction.old f x ∈ (coveringCore f b Z pot s hs hpot).baseSet (.inl i) ↔ x ∈ Z.baseSet i := by
  change Adjunction.old f x ∈ baseSet f Z (.inl i) ↔ _
  rw [mem_baseSet_old]
  constructor
  · rintro ⟨hx,h⟩
    simpa only [collarRetraction_old] using h
  · intro hx
    exact ⟨mem_collar_old f x,by simpa only [collarRetraction_old] using hx⟩

end PresentationGeometry.CellCoverExtension

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_RegularCoverGeometry
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology
noncomputable section
open Set Function
open scoped unitInterval
open scoped unitInterval
open Set

namespace PresentationGeometry.CellCoverExtension
open Set Cells
variable {X ι Q : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
  {k d : ℕ} (f : C(boundary k d,X)) (b : X) (Z : FiberBundleCore ι X Q)
  (pot : ι → X → Q) (s : C(boundary k d,Z.TotalSpace))
  (hs : ∀ c, Z.proj (s c) = f c)
  (hpot : ∀ i j x q, Z.coordChange i j x q = pot j x * (pot i x)⁻¹ * q)

def oldLift : C(Z.TotalSpace,(coveringCore f b Z pot s hs hpot).TotalSpace) :=
  FiberCoreMap.continuousMap Z (coveringCore f b Z pot s hs hpot)
    ⟨Adjunction.old f,Adjunction.continuous_old f⟩ Sum.inl
    (fun i x hx => (mem_coveringCore_old f b Z pot s hs hpot i x).mpr hx)
    (fun i j x _ q => coveringCore_old_coordChange f b Z pot s hs hpot i j x q)

@[simp] lemma oldLift_proj (e : Z.TotalSpace) :
    (coveringCore f b Z pot s hs hpot).proj (oldLift f b Z pot s hs hpot e) =
      Adjunction.old f (Z.proj e) := rfl

end PresentationGeometry.CellCoverExtension

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryCellCoverExtension
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Function Topology
open Set Function
open scoped unitInterval
open scoped unitInterval
open Set
open Set Topology unitInterval
namespace PresentationGeometry.CellCoverExtension
open Set Cells Metric
variable {X ι Q : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
  {k d : ℕ} (f : C(boundary k d,X)) (b : X) (Z : FiberBundleCore ι X Q)
  (pot : ι → X → Q) (s : C(boundary k d,Z.TotalSpace))
  (hs : ∀ c, Z.proj (s c) = f c)
  (hpot : ∀ i j x q, Z.coordChange i j x q = pot j x * (pot i x)⁻¹ * q)

def boundarySlice (i : Fin k) : C(SphereCover.Sphere (Fin d → ℝ),boundary k d) :=
  ⟨fun v => ⟨(i,⟨v.1,sphere_subset_closedBall v.2⟩),v.2⟩,
    (continuous_const.prodMk (continuous_subtype_val.subtype_mk _)).subtype_mk _⟩

def sphereInDisk : C(SphereCover.Sphere (Fin d → ℝ),Disk d) :=
  ⟨fun v => ⟨v.1,sphere_subset_closedBall v.2⟩,continuous_subtype_val.subtype_mk _⟩

def attachedDisk (i : Fin k) : C(Disk d,Cells.Space f) :=
  ⟨fun v => Adjunction.disk f (i,v),
    (Adjunction.continuous_disk f).comp (continuous_const.prodMk continuous_id)⟩

omit [T2Space X] [CompactSpace X] in
@[simp] lemma attachedDisk_boundary (i : Fin k) (v : SphereCover.Sphere (Fin d → ℝ)) :
    attachedDisk f i (sphereInDisk v) = Adjunction.old f (f (boundarySlice i v)) :=
  Adjunction.disk_boundary f (boundarySlice i v)

end PresentationGeometry.CellCoverExtension

end

open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ChainShortExact
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric

namespace RelativeChains

open Set _root_.CategoryTheory HomologicalComplex SingularChains
variable {X : Type} [TopologicalSpace X]

lemma preimage_singleton_inclusion {D : Set X} (x : D) :
    (SingularSubspace.inclusionMap D) ⁻¹' ({x.1} : Set X) = {x} := by
  ext z
  simp only [mem_preimage,mem_singleton_iff]
  exact Subtype.ext_iff.symm

end RelativeChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CubeDisk
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
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

namespace WeakSphere
open Set Topology Metric
open scoped unitInterval
universe u
variable {Y : Type u} [TopologicalSpace Y]
open SphereQuotient

theorem exists_disk_path {n : ℕ} (f : C(Boundary (n+1),Y))
    [Subsingleton (HomotopyGroup (Fin n) Y (f (pole n)))] :
    ∃ P : C(Disk n,C(I,Y)),
      (∀ v,P v 0 = f (quotient n v)) ∧
      (∀ v,P v 1 = f (pole n)) ∧
      ∀ v : Disk n, ‖v.1‖ = 1 → P v = .const I (f (pole n)) := by
  have he : (⟦loop f⟧ : HomotopyGroup (Fin n) Y (f (pole n))) = ⟦GenLoop.const⟧ :=
    @Subsingleton.elim (HomotopyGroup (Fin n) Y (f (pole n))) ‹Subsingleton _› _ _
  obtain ⟨H⟩ := Quotient.exact he
  let P : C(Disk n,C(I,Y)) := (H.toHomotopy.toContinuousMap.comp
    ⟨fun z : Disk n × I => (z.2,CubeDisk.toCube n z.1),
      continuous_snd.prodMk ((CubeDisk.toCube n).continuous.comp continuous_fst)⟩).curry
  refine ⟨P,?_,?_,?_⟩
  · intro v
    change H (0,CubeDisk.toCube n v) = _
    refine (H.map_zero_left (CubeDisk.toCube n v)).trans ?_
    change f (quotient n (CubeDisk.toDisk n (CubeDisk.toCube n v))) = _
    rw [CubeDisk.toDisk_toCube]
  · intro v
    exact H.map_one_left (CubeDisk.toCube n v)
  · intro v hv
    ext t
    exact H.eq_snd t (CubeDisk.boundary_of_norm_eq_one v hv)

theorem pathData_factors {n : ℕ} (y : Y) (P : C(Disk n,C(I,Y)))
    (hP : ∀ v : Disk n,‖v.1‖ = 1 → P v = .const I y) :
    Function.FactorsThrough (pathData y P) (sphereQuot n) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      rcases quotient_eq hab with h | ⟨ha,hb⟩
      · exact congrArg P h
      · exact (hP a ha).trans (hP b hb).symm
    | inr b => exact hP a (quotient_eq_pole hab)
  | inr a =>
    cases b with
    | inl b => exact (hP b (quotient_eq_pole hab.symm)).symm
    | inr b => rfl

theorem sphere_nullhomotopic (n : ℕ) (f : C(Boundary (n+1),Y))
    [Subsingleton (HomotopyGroup (Fin n) Y (f (pole n)))] : f.Nullhomotopic := by
  obtain ⟨P,hP₀,hP₁,hPb⟩ := exists_disk_path f
  let K : C(Boundary (n+1),C(I,Y)) :=
    (sphereQuot_isQuotientMap n).lift (pathData (f (pole n)) P) (pathData_factors (f (pole n)) P hPb)
  have hK (a : Disk n ⊕ Unit) : K (sphereQuot n a) = pathData (f (pole n)) P a :=
    DFunLike.congr_fun ((sphereQuot_isQuotientMap n).lift_comp
      (pathData (f (pole n)) P) (pathData_factors (f (pole n)) P hPb)) a
  have h₀ : ∀ z,K z 0 = f z := by
    intro z
    obtain ⟨a,rfl⟩ := sphereQuot_surjective n z
    rw [hK]
    rcases a with v | a
    · exact hP₀ v
    · rfl
  have h₁ : ∀ z,K z 1 = f (pole n) := by
    intro z
    obtain ⟨a,rfl⟩ := sphereQuot_surjective n z
    rw [hK]
    rcases a with v | a
    · exact hP₁ v
    · rfl
  refine ⟨f (pole n),⟨?_⟩⟩
  exact { toFun := fun z => K z.2 z.1
          continuous_toFun := (K.continuous.comp continuous_snd).eval continuous_fst
          map_zero_left := h₀
          map_one_left := h₁ }

end WeakSphere

open Set Topology Metric
open scoped unitInterval

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_RelativeChainsEmptyProjectionQuasiIso
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric

namespace SphereCover
section
open Set Metric _root_.CategoryTheory
variable {E : Type} [NormedAddCommGroup E]

lemma val_ne_zero (v : Sphere E) : (v : E) ≠ 0 := by
  intro h
  have hv := norm_eq_of_mem_sphere v
  simp [h] at hv

variable [InnerProductSpace ℝ E]

lemma eq_or_neg_of_finrank_one [FiniteDimensional ℝ E] (hd : Module.finrank ℝ E = 1)
    (v w : Sphere E) : w = v ∨ w = -v := by
  have ht : (ℝ ∙ (v : E)) = ⊤ := Submodule.eq_top_of_finrank_eq ((finrank_span_singleton (val_ne_zero v)).trans hd.symm)
  have hw : (w : E) ∈ ℝ ∙ (v : E) := by rw [ht]; trivial
  obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp hw
  have hn : |t| = 1 := by
    have h := congrArg norm ht
    simpa only [norm_smul,Real.norm_eq_abs,norm_eq_of_mem_sphere v,norm_eq_of_mem_sphere w,mul_one] using h
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hn with rfl | rfl
  · left; apply Subtype.ext; simpa using ht.symm
  · right; apply Subtype.ext; simpa using ht.symm

lemma finite_of_finrank_one [FiniteDimensional ℝ E] (hd : Module.finrank ℝ E = 1) (v : Sphere E) :
    Finite (Sphere E) := by
  apply Finite.of_surjective (fun b : Bool => if b then v else -v)
  intro w
  rcases eq_or_neg_of_finrank_one hd v w with rfl | rfl
  · exact ⟨true,rfl⟩
  · exact ⟨false,rfl⟩

end

open Set Metric _root_.CategoryTheory

end SphereCover

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSigma
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric
namespace SingularSigma
open Set _root_.CategoryTheory HomologicalComplex SingularChains
attribute [-instance] AddCommGroup.toIntModule
variable {ι X : Type} [TopologicalSpace X]
def index {n : ℕ} (f : C(Std n,Space ι X)) : ι := (f (Convexity.StdSimplex.single 0)).1
lemma index_eq {n : ℕ} (f : C(Std n,Space ι X)) (s : Std n) : (f s).1 = index f := by
  let : TopologicalSpace ι := ⊥
  let : DiscreteTopology ι := ⟨rfl⟩
  exact PreconnectedSpace.constant (inferInstance : PreconnectedSpace (Std n))
    (f := fun s => (f s).1) ((continuous_sigma fun _ => continuous_const).comp f.continuous)
lemma incl_snd {n : ℕ} (f : C(Std n,Space ι X)) : (incl (index f)).comp (snd.comp f) = f := by
  apply ContinuousMap.ext
  intro s
  change Sigma.mk (index f) (f s).2 = f s
  have h := index_eq f s
  cases hf : f s with | mk i x => simp only [hf] at h ⊢; exact congrArg (fun i => Sigma.mk i x) h.symm
lemma index_incl {n : ℕ} (i : ι) (f : C(Std n,X)) : index ((incl i).comp f) = i := rfl
lemma snd_incl {n : ℕ} (i : ι) (f : C(Std n,X)) : snd.comp ((incl i).comp f) = f := rfl

attribute [instance] AddCommGroup.toIntModule
end SingularSigma

namespace CWSkeletalHomology
attribute [-instance] AddCommGroup.toIntModule
open Set Topology Metric CWExtension _root_.CategoryTheory HomologicalComplex

attribute [instance] AddCommGroup.toIntModule
end CWSkeletalHomology

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CoveringCellGeometryHausdorff
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoveringCW
open Set Topology Metric CoveringCellGeometry
variable {X E : Type} [TopologicalSpace X] [TopologicalSpace E] [T2Space X] [T2Space E]
  [CWComplex (univ : Set X)] {p : E → X} (cov : IsCoveringMap p)

lemma skeleton_preimage (n : ℕ) :
    letI := cwComplex_general cov
    (RelCWComplex.skeletonLT (univ : Set E) n : Set E) =
      p ⁻¹' (RelCWComplex.skeletonLT (univ : Set X) n : Set X) := by
  let := cwComplex_general cov
  ext e
  constructor
  · intro he
    obtain ⟨m,hm,c,v,hv,rfl⟩ := CWComplex.mem_skeletonLT_iff.mp he
    exact CWComplex.mem_skeletonLT_iff.mpr
      ⟨m,hm,c.1,v,hv,(chart_proj cov m c (ball_subset_closedBall hv)).symm⟩
  · intro he
    obtain ⟨m,hm,i,v,hv,hve⟩ := CWComplex.mem_skeletonLT_iff.mp he
    let z : Pullback (p := p) (baseChar m i) :=
      ⟨(⟨v,ball_subset_closedBall hv⟩,e),hve.symm⟩
    refine CWComplex.mem_skeletonLT_iff.mpr
      ⟨m,hm,⟨i,sheet cov (baseChar m i) z⟩,v,hv,?_⟩
    exact (characteristic_on_disk cov m _ ⟨v,ball_subset_closedBall hv⟩).trans
      (characteristicLift_sheet cov (baseChar m i) z)
end CoveringCW

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SimplexHomotopy
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
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

theorem exists_disk_cylinder {n : ℕ}
    (hπ : ∀ y : Y, Subsingleton (HomotopyGroup (Fin n) Y y))
    (f₀ f₁ : C(CWCylinder.Disk n,Y)) (h : C(I × CWCylinder.Boundary n,Y))
    (h₀ : ∀ v, h (0,v) = f₀ (CWCylinder.boundaryDisk n v))
    (h₁ : ∀ v, h (1,v) = f₁ (CWCylinder.boundaryDisk n v)) :
    ∃ F : C(I × CWCylinder.Disk n,Y),
      (∀ v, F (0,v) = f₀ v) ∧ (∀ v, F (1,v) = f₁ v) ∧
      ∀ t v, F (t,CWCylinder.boundaryDisk n v) = h (t,v) := by
  let b := CWCylinder.boundaryMap f₀ f₁ h h₀ h₁
  let := hπ (b (SphereQuotient.pole n))
  obtain ⟨g,hg⟩ := SphereExtension.exists_extension b (WeakSphere.sphere_nullhomotopic n b)
  have hg' (v : CWCylinder.Boundary (n+1)) : g (CWCylinder.boundaryDisk (n+1) v) = b v := hg v
  refine ⟨g.comp (CWCylinder.encode n),?_,?_,?_⟩
  · intro v
    change g (CWCylinder.encode n (0,v)) = _
    rw [show (0,v) = CWCylinder.faceCylinder n (Sum.inl v) from rfl,CWCylinder.face_encode,hg']
    exact CWCylinder.boundaryMap_face f₀ f₁ h h₀ h₁ (Sum.inl v)
  · intro v
    change g (CWCylinder.encode n (1,v)) = _
    rw [show (1,v) = CWCylinder.faceCylinder n (Sum.inr (Sum.inl v)) from rfl,CWCylinder.face_encode,hg']
    exact CWCylinder.boundaryMap_face f₀ f₁ h h₀ h₁ (Sum.inr (Sum.inl v))
  · intro t v
    change g (CWCylinder.encode n (t,CWCylinder.boundaryDisk n v)) = _
    rw [show (t,CWCylinder.boundaryDisk n v) = CWCylinder.faceCylinder n (Sum.inr (Sum.inr (t,v))) from rfl,
      CWCylinder.face_encode,hg']
    exact CWCylinder.boundaryMap_face f₀ f₁ h h₀ h₁ (Sum.inr (Sum.inr (t,v)))

end SimplexHomotopy

namespace SimplexBoundary
open Set Topology Metric
open scoped unitInterval

instance boundary_zero_isEmpty : IsEmpty (Boundary 0) := by
  constructor
  intro s
  obtain ⟨i,hi⟩ := s.2
  have hs := s.1.total_of_fintype
  have hi0 : i = 0 := Fin.ext (by omega)
  rw [hi0] at hi
  have hs' : s.1.weights 0 = 1 := (Fin.sum_univ_one _).symm.trans hs
  exact zero_ne_one (hi.symm.trans hs')

universe u
variable {Y : Type u} [TopologicalSpace Y]

omit [TopologicalSpace Y] in
theorem compatible_faces {n : ℕ} (h : Fin (n+2) → Simplex n → Y)
    (hh : ∀ (m : ℕ) (hm : n = m+1) (i : Fin (m+3)) (j : Fin (m+2)) (s : Simplex m),
      h (hm ▸ i.succAbove j) (hm ▸ face (j.predAbove i) s) =
        h (hm ▸ i) (hm ▸ face j s)) :
    ∀ i j a b, face i a = face j b → h i a = h j b := by
  intro i j a b hab
  by_cases hij : i = j
  · subst j
    exact congrArg (h i) (face_injective i hab)
  cases n with
  | zero =>
    have hx : (face i a).weights j = 0 := by rw [hab]; exact face_zero _ _
    obtain ⟨k,hk⟩ : ∃ k, j = i.succAbove k := by
      rcases Fin.eq_self_or_eq_succAbove i j with h' | h'
      · exact False.elim (hij h'.symm)
      · exact h'
    rw [hk,face_succAbove] at hx
    have hs := a.total_of_fintype
    have hk0 : k = 0 := Subsingleton.elim _ _
    have hs' : a.weights 0 = 1 := (Fin.sum_univ_one _).symm.trans hs
    rw [hk0] at hx
    exact False.elim (zero_ne_one (hx.symm.trans hs'))
  | succ n =>
    obtain ⟨k,s,rfl,rfl,rfl⟩ := face_overlap hij hab
    exact (hh n rfl i k s).symm

end SimplexBoundary

namespace SingularTightening
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

end SingularTightening

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularPrism
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
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

structure Coherent (X : Type) [TopologicalSpace X] where
  H : ∀ n, C(Std n,X) → C(I × Std n,X)
  zero : ∀ n f s, H n f (0,s) = f s
  face : ∀ n (f : C(Std (n+1),X)) (i : Fin (n+2)) t s,
    H (n+1) f (t,SingularChains.face i s) = H n (f.comp (SingularChains.face i)) (t,s)

namespace Coherent
variable (S : Coherent X)

def top (n : ℕ) (f : C(Std n,X)) : C(Std n,X) := finish (S.H n f)

lemma start_eq (n : ℕ) (f : C(Std n,X)) : start (S.H n f) = f := by
  ext s
  exact S.zero n f s

lemma top_face (n : ℕ) (f : C(Std (n+1),X)) (i : Fin (n+2)) :
    (S.top (n+1) f).comp (SingularChains.face i) = S.top n (f.comp (SingularChains.face i)) := by
  ext s
  exact S.face n f i 1 s

lemma hom_face (n : ℕ) (f : C(Std (n+1),X)) (i : Fin (n+2)) :
    precompCylinder (S.H (n+1) f) (SingularChains.face i) = S.H n (f.comp (SingularChains.face i)) := by
  ext s
  exact S.face n f i s.1 s.2

end Coherent

open Coherent

end

open _root_.CategoryTheory AlgebraicTopology Limits HomologicalComplex
open SingularChains

end SingularNormalization

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularAction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
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

attribute [instance] AddCommGroup.toIntModule
end SingularAction

namespace CoveringCellGeometry
open Set Topology unitInterval
variable {X E A : Type*} [TopologicalSpace X] [TopologicalSpace E]
  [TopologicalSpace A] {p : E → X} (cov : IsCoveringMap p)
variable (d : E ≃ₜ E) (hd : p ∘ d = p)

variable [ContractibleSpace A] (f : C(A,X))

theorem characteristicLift_deck (j : p ⁻¹' {f (contractionPoint A)}) (a : A) :
    characteristicLift cov f ⟨d j,(congrFun hd j).trans j.2⟩ a =
      d (characteristicLift cov f j a) := by
  let H := contractionImage f
  let z : Pullback (p := p) (endpoint H 0) :=
    pullbackCongr (contractionImage_zero f).symm (constantPullback (p := p) _ (a,j))
  have hpoint : z.1 = (a,(j : E)) := by
    simp only [z,pullbackCongr_val]
    rfl
  have hpoint' : (pullbackCongr (contractionImage_zero f).symm
      (constantPullback (p := p) (f (contractionPoint A))
        (a,⟨d j,(congrFun hd j).trans j.2⟩))) = deckPullback d hd (endpoint H 0) z := by
    apply Subtype.ext
    simp only [pullbackCongr_val,deckPullback,hpoint]
    rfl
  change (pullbackCongr (contractionImage_one f)
    (transportHomeomorph cov H
      (pullbackCongr (contractionImage_zero f).symm
        (constantPullback (p := p) (f (contractionPoint A))
          (a,⟨d j,(congrFun hd j).trans j.2⟩))))).1.2 =
    d ((pullbackCongr (contractionImage_one f)
      (transportHomeomorph cov H z)).1.2)
  simp only [pullbackCongr_val,hpoint']
  exact familyLift_deck cov d hd H z 1

end CoveringCellGeometry

namespace EquivariantCoverCells
open Set Topology _root_.CategoryTheory
open CoveringCW
open scoped MonoidAlgebra
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
    [T2Space X] [T2Space E] [CWComplex (univ : Set X)]
    {G : Type u} [Group G] [MulAction G E] [ContinuousConstSMul G E]
    {p : E → X} [hproj : Fact (∀ (g : G) x, p (g • x) = p x)]
    (hfree : ∀ (g h : G) (x : E), g • x = h • x → g = h)
    (htrans : ∀ (a b : E), p a = p b → ∃ g : G, g • a = b)
    (surj : Function.Surjective p)

omit [TopologicalSpace E] [T2Space X] [T2Space E] [ContinuousConstSMul G E] in
@[simp] theorem cellEquiv_smul (n : ℕ) (d g : G) (i : BaseCell (X := X) n) :
    cellEquiv hfree htrans surj n (i,d*g) = d • cellEquiv hfree htrans surj n (i,g) := by
  change ((d*g) • (⟨i,seed surj n i⟩ : Cell (p := p) n)) = _
  exact mul_smul d g _

noncomputable abbrev cellularRepresentation (n : ℕ) :=
  Representation.ofMulAction ℤ G (Cell (p := p) n)

noncomputable def abelianEquiv (n : ℕ) :
    (BaseCell (X := X) n →₀ MonoidAlgebra ℤ G) ≃ₗ[ℤ]
      MonoidAlgebra ℤ (Cell (p := p) n) :=
  ((Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv ℤ)).trans
    ((Finsupp.curryLinearEquiv ℤ).symm.trans
      (Finsupp.domLCongr (cellEquiv hfree htrans surj n)))).trans
    (MonoidAlgebra.coeffLinearEquiv ℤ).symm

omit [TopologicalSpace E] [T2Space X] [T2Space E] [ContinuousConstSMul G E] in
@[simp] theorem abelianEquiv_single (n : ℕ) (i : BaseCell (X := X) n)
    (d : G) (a : ℤ) :
    abelianEquiv hfree htrans surj n (Finsupp.single i (MonoidAlgebra.single d a)) =
      MonoidAlgebra.single (cellEquiv hfree htrans surj n (i,d)) a := by
  simp [abelianEquiv, Finsupp.curryLinearEquiv]

noncomputable def representationEquiv (n : ℕ) :
    (Representation.free ℤ G (BaseCell (X := X) n)).Equiv
      (cellularRepresentation (p:=p) (G:=G) n) :=
  Representation.Equiv.mk (abelianEquiv hfree htrans surj n) (by
    intro d
    apply Finsupp.lhom_ext'
    intro i
    apply MonoidAlgebra.lhom_ext'
    intro g
    ext a
    simp only [LinearMap.comp_apply,Finsupp.lsingle_apply,MonoidAlgebra.lsingle_apply,LinearEquiv.coe_coe,Representation.free_single_single,
      abelianEquiv_single,Representation.ofMulAction_single,cellEquiv_smul])

noncomputable def freeIso (n : ℕ) : Rep.of (cellularRepresentation (p:=p) (G:=G) n) ≅
    Rep.free ℤ G (BaseCell (X:=X) n) :=
  (Rep.mkIso (representationEquiv hfree htrans surj n)).symm

omit [T2Space X] [T2Space E] in
lemma chart_smul (cov : IsCoveringMap p) (g : G) (n : ℕ)
    (c : Cell (p:=p) n) (v : Disk n) :
    g • chart cov n c v = chart cov n (g • c) v := by
  change g • characteristic cov n c v = characteristic cov n (g • c) v
  rw [characteristic_on_disk,characteristic_on_disk]
  exact (CoveringCellGeometry.characteristicLift_deck cov (actionHomeo g)
    (funext (hproj.out g)) (baseChar n c.1) c.2 v).symm

end EquivariantCoverCells

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
-- module Solutions.OAIQ066_SO.FiniteType_CoreDeckLeftQuotientCovering
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CoreDeck
open Set Topology
variable {ι X Q : Type} [TopologicalSpace X] [Group Q] [TopologicalSpace Q]
  [DiscreteTopology Q] (Z : FiberBundleCore ι X Q)
  (hZ : ∀ i j x a q, Z.coordChange i j x (a*q) = Z.coordChange i j x a * q)

include hZ in
theorem leftQuotientCovering :
    letI := leftAction Z
    IsQuotientCoveringMap Z.proj Q := by
  let := leftAction Z
  let := continuousLeftAction Z hZ
  let cov := DiscreteCoverCharts.covering Z
  exact {
    toIsQuotientMap := cov.isQuotientMap (fun x => ⟨⟨x,(1:Q)⟩,rfl⟩)
    continuous_const_smul := continuous_const_smul
    apply_eq_iff_mem_orbit := by
      intro a b
      constructor
      · intro h
        obtain ⟨q,hq⟩ := left_transitive Z b a h.symm
        exact ⟨q,hq⟩
      · rintro ⟨q,rfl⟩
        rfl
    disjoint := by
      intro x
      obtain ⟨t,hxt,hpt⟩ := cov.isLocalHomeomorph x
      refine ⟨t.source,t.open_source.mem_nhds hxt,?_⟩
      intro q hq
      rcases hq with ⟨z,⟨y,hy,rfl⟩,hqy⟩
      have he : q • y = y := t.injOn hqy hy (by rw [← hpt]; rfl)
      exact left_free Z q 1 y (he.trans (one_smul Q y).symm) }

def leftFundamentalEquiv [SimplyConnectedSpace Z.TotalSpace] (x : X) :
    Q ≃* FundamentalGroup X x := by
  letI := leftAction Z
  exact (MulEquiv.inv' Q).trans
    ((leftQuotientCovering Z hZ).fundamentalGroupEquiv ⟨⟨x,(1:Q)⟩,rfl⟩).symm
end CoreDeck

namespace PresentationGeometry.FiniteStage
attribute [-instance] AddCommGroup.toIntModule
open Set Topology Metric _root_.CategoryTheory CategoryTheory.Limits Cells CWExtension CellCoverExtension
open HurewiczConstruction

attribute [instance] AddCommGroup.toIntModule
end PresentationGeometry.FiniteStage

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderListChains
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderListChains
section

variable (G : Type*)

def vertex (a : G) : Chain G := Finsupp.single (simplexVertex G a) 1

def cone (a : G) : Chain G →ₗ[ℤ] Chain G :=
  Finsupp.lmapDomain ℤ ℤ (simplexCone G a)

@[simp] lemma cone_single (a : G) (s : Simplex G) (r : ℤ) :
    cone G a (Finsupp.single s r) = Finsupp.single (simplexCone G a s) r := by
  simp [cone]

lemma single_cons (a b : G) (l : List G) (r : ℤ) :
    Finsupp.single (a,b::l) r = cone G a (Finsupp.single (b,l) r) :=
  (cone_single G a (b,l) r).symm

def augmentation : Chain G →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun s : Simplex G => if s.2 = [] then 1 else 0)

@[simp] lemma augmentation_single (s : Simplex G) (r : ℤ) :
    augmentation G (Finsupp.single s r) = if s.2 = [] then r else 0 := by
  simp only [augmentation, Finsupp.linearCombination_single, smul_eq_mul]
  split_ifs <;> simp

@[simp] lemma augmentation_vertex (a : G) : augmentation G (vertex G a) = 1 := by
  simp [vertex, simplexVertex]

@[simp] lemma augmentation_cone (a : G) (c : Chain G) :
    augmentation G (cone G a c) = 0 := by
  have h : augmentation G ∘ₗ cone G a = 0 := by
    apply Finsupp.lhom_ext
    intro s r
    simp [simplexCone]
  exact LinearMap.congr_fun h c

def K (a : G) : Chain G →ₗ[ℤ] Chain G :=
  Finsupp.lsingle (simplexVertex G a) ∘ₗ augmentation G

@[simp] lemma K_apply (a : G) (c : Chain G) : K G a c = augmentation G c • vertex G a := by
  simp [K, vertex]

@[simp] lemma augmentation_K (a : G) (c : Chain G) :
    augmentation G (K G a c) = augmentation G c := by
  simp

def boundaryAux (a : G) : List G → Chain G
  | [] => 0
  | b :: l => Finsupp.single (b,l) 1 - cone G a (boundaryAux b l) -
    (if l = [] then vertex G a else 0)

def boundary : Chain G →ₗ[ℤ] Chain G :=
  Finsupp.linearCombination ℤ (fun s => boundaryAux G s.1 s.2)

@[simp] lemma boundary_single (s : Simplex G) (r : ℤ) :
    boundary G (Finsupp.single s r) = r • boundaryAux G s.1 s.2 := by
  simp [boundary]

@[simp] lemma boundary_vertex (a : G) : boundary G (vertex G a) = 0 := by
  simp [vertex, simplexVertex, boundaryAux]

@[simp] lemma boundary_K (a : G) (c : Chain G) : boundary G (K G a c) = 0 := by
  simp

lemma boundary_cone (a : G) (c : Chain G) :
    boundary G (cone G a c) = c - cone G a (boundary G c) - K G a c := by
  have h : boundary G ∘ₗ cone G a = LinearMap.id - cone G a ∘ₗ boundary G - K G a := by
    apply Finsupp.lhom_ext
    rintro ⟨b,l⟩ r
    simp only [LinearMap.comp_apply, cone_single, boundary_single, simplexCone, boundaryAux,
      LinearMap.sub_apply, LinearMap.id_apply, K_apply, augmentation_single, map_smul]
    split_ifs <;> simp [smul_sub, Finsupp.smul_single]
  exact LinearMap.congr_fun h c

@[simp] lemma augmentation_boundary (c : Chain G) : augmentation G (boundary G c) = 0 := by
  have h : augmentation G ∘ₗ boundary G = 0 := by
    apply Finsupp.lhom_ext
    rintro ⟨a,l⟩ r
    cases l with
    | nil => simp [boundaryAux]
    | cons b l =>
      change augmentation G (boundary G (Finsupp.single (a,b::l) r)) = 0
      rw [single_cons]
      rw [boundary_cone]
      simp only [map_sub, augmentation_cone, augmentation_K, sub_zero, sub_self]
  exact LinearMap.congr_fun h c

@[simp] lemma K_boundary (a : G) (c : Chain G) : K G a (boundary G c) = 0 := by
  simp

@[simp] lemma boundary_boundary (c : Chain G) : boundary G (boundary G c) = 0 := by
  have hb (l : List G) (a : G) :
      boundary G (boundary G (Finsupp.single (a,l) 1)) = 0 := by
    induction l generalizing a with
    | nil =>
      change boundary G (boundary G (vertex G a)) = 0
      rw [boundary_vertex, map_zero]
    | cons b l ih =>
      rw [single_cons]
      rw [boundary_cone, map_sub, map_sub, boundary_cone, ih b]
      simp only [map_zero, K_boundary, boundary_K, sub_zero, sub_self]
  have h : boundary G ∘ₗ boundary G = 0 := by
    apply Finsupp.lhom_ext
    intro s r
    have hr : Finsupp.single s r = r • Finsupp.single s 1 := by simp
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, hr, map_smul, hb s.2 s.1,
      smul_zero]
  exact LinearMap.congr_fun h c

def degree (s : Simplex G) : ℕ := s.2.length

def Homogeneous (n : ℕ) (c : Chain G) : Prop :=
  ∀ s ∈ c.support, degree G s = n

def mapChain {H : Type*} (f : G → H) : Chain G →ₗ[ℤ] Chain H :=
  Finsupp.lmapDomain ℤ ℤ (fun s => (f s.1, s.2.map f))

@[simp] lemma mapChain_single {H : Type*} (f : G → H) (s : Simplex G) (r : ℤ) :
    mapChain G f (Finsupp.single s r) = Finsupp.single (f s.1, s.2.map f) r := by
  simp [mapChain]

@[simp] lemma mapChain_vertex {H : Type*} (f : G → H) (a : G) :
    mapChain G f (vertex G a) = vertex H (f a) := by
  simp [vertex, simplexVertex]

lemma mapChain_cone {H : Type*} (f : G → H) (a : G) (c : Chain G) :
    mapChain G f (cone G a c) = cone H (f a) (mapChain G f c) := by
  have h : mapChain G f ∘ₗ cone G a = cone H (f a) ∘ₗ mapChain G f := by
    apply Finsupp.lhom_ext
    intro s r
    simp [simplexCone]
  exact LinearMap.congr_fun h c

@[simp] lemma augmentation_mapChain {H : Type*} (f : G → H) (c : Chain G) :
    augmentation H (mapChain G f c) = augmentation G c := by
  have h : augmentation H ∘ₗ mapChain G f = augmentation G := by
    apply Finsupp.lhom_ext
    intro s r
    simp
  exact LinearMap.congr_fun h c

lemma mapChain_K {H : Type*} (f : G → H) (a : G) (c : Chain G) :
    mapChain G f (K G a c) = K H (f a) (mapChain G f c) := by
  simp

lemma boundary_mapChain {H : Type*} (f : G → H) (c : Chain G) :
    boundary H (mapChain G f c) = mapChain G f (boundary G c) := by
  have hb (l : List G) (a : G) :
      boundary H (mapChain G f (Finsupp.single (a,l) 1)) =
        mapChain G f (boundary G (Finsupp.single (a,l) 1)) := by
    induction l generalizing a with
    | nil =>
      change boundary H (mapChain G f (vertex G a)) = mapChain G f (boundary G (vertex G a))
      rw [mapChain_vertex, boundary_vertex, boundary_vertex, map_zero]
    | cons b l ih =>
      rw [single_cons]
      rw [mapChain_cone, boundary_cone, boundary_cone, map_sub, map_sub,
        mapChain_cone, mapChain_K, ih b]
  have he : boundary H ∘ₗ mapChain G f = mapChain G f ∘ₗ boundary G := by
    apply Finsupp.lhom_ext
    intro s r
    have hr : Finsupp.single s r = r • Finsupp.single s 1 := by simp
    simp only [LinearMap.comp_apply, hr, map_smul, hb s.2 s.1]
  exact LinearMap.congr_fun he c

def Supported (P : Simplex G → Prop) (c : Chain G) : Prop := ∀ s ∈ c.support, P s

lemma supported_zero (P : Simplex G → Prop) : Supported G P 0 := by simp [Supported]

lemma supported_add {P : Simplex G → Prop} {c d : Chain G}
    (hc : Supported G P c) (hd : Supported G P d) : Supported G P (c+d) := by
  classical
  intro s hs
  obtain hs | hs := Finset.mem_union.mp (Finsupp.support_add hs)
  · exact hc s hs
  · exact hd s hs

lemma supported_neg {P : Simplex G → Prop} {c : Chain G}
    (hc : Supported G P c) : Supported G P (-c) := by
  simpa only [Supported, Finsupp.support_neg] using hc

lemma supported_sub {P : Simplex G → Prop} {c d : Chain G}
    (hc : Supported G P c) (hd : Supported G P d) : Supported G P (c-d) := by
  rw [sub_eq_add_neg]
  exact supported_add G hc (supported_neg G hd)

lemma supported_smul {P : Simplex G → Prop} {c : Chain G}
    (r : ℤ) (hc : Supported G P c) : Supported G P (r • c) :=
  fun s hs => hc s (Finsupp.support_smul hs)

lemma supported_single {P : Simplex G → Prop} {s : Simplex G} (hs : P s) (r : ℤ) :
    Supported G P (Finsupp.single s r) := by
  classical
  intro t ht
  have h : t = s := Finset.mem_singleton.mp (Finsupp.support_single_subset ht)
  simpa only [h] using hs

lemma supported_sum {ι : Type*} (t : Finset ι) {P : Simplex G → Prop}
    (c : ι → Chain G) (hc : ∀ i ∈ t, Supported G P (c i)) :
    Supported G P (∑ i ∈ t, c i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using supported_zero G P
  | @insert i t hit ih =>
    rw [Finset.sum_insert hit]
    exact supported_add G (hc i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hc j (Finset.mem_insert_of_mem hj)))

lemma supported_linearMap {H : Type*} {P : Simplex G → Prop} {Q : Simplex H → Prop}
    (T : Chain G →ₗ[ℤ] Chain H)
    (hT : ∀ s, P s → Supported H Q (T (Finsupp.single s 1)))
    {c : Chain G} (hc : Supported G P c) : Supported H Q (T c) := by
  classical
  have he : T c = ∑ s ∈ c.support, (c s) • T (Finsupp.single s 1) := by
    conv_lhs => rw [← Finsupp.sum_single c]
    rw [Finsupp.sum, map_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [he]
  exact supported_sum H c.support _ (fun s hs => supported_smul H _ (hT s (hc s hs)))

end

variable (G : Type*)

def vertices (s : Simplex G) : Set G := {a | a = s.1 ∨ a ∈ s.2}

@[simp] lemma mem_vertices (s : Simplex G) (a : G) :
    a ∈ vertices G s ↔ a = s.1 ∨ a ∈ s.2 := Iff.rfl

lemma vertices_vertex (a : G) : vertices G (simplexVertex G a) = {a} := by
  ext x
  simp [vertices, simplexVertex]

lemma vertices_cone (a : G) (s : Simplex G) :
    vertices G (simplexCone G a s) = insert a (vertices G s) := by
  ext x
  simp [vertices, simplexCone]

lemma supported_cone {P Q : Simplex G → Prop} (a : G)
    (h : ∀ s, P s → Q (simplexCone G a s)) {c : Chain G}
    (hc : Supported G P c) : Supported G Q (cone G a c) := by
  refine supported_linearMap G (Q := Q) (cone G a) ?_ hc
  intro s hs
  rw [cone_single]
  exact supported_single G (h s hs) 1

theorem boundary_faces (s : Simplex G) :
    Supported G (fun t => degree G t + 1 = degree G s ∧ vertices G t ⊆ vertices G s)
      (boundary G (Finsupp.single s 1)) := by
  rcases s with ⟨a,l⟩
  induction l generalizing a with
  | nil =>
    change Supported G _ (boundary G (vertex G a))
    rw [boundary_vertex]
    exact supported_zero G _
  | cons b l ih =>
    rw [single_cons, boundary_cone]
    apply supported_sub
    · apply supported_sub
      · apply supported_single
        constructor
        · rfl
        · intro x hx
          exact Or.inr (by simpa only [vertices, Set.mem_ofPred_eq, List.mem_cons] using hx)
      · refine supported_cone G
          (Q := fun t => degree G t + 1 = degree G (a, b::l) ∧
            vertices G t ⊆ vertices G (a, b::l)) a ?_ (ih b)
        intro t ht
        constructor
        · change degree G t + 1 + 1 = l.length + 1
          exact congrArg (· + 1) ht.1
        · rw [vertices_cone]
          intro x hx
          rcases hx with rfl | hx
          · exact Or.inl rfl
          · exact Or.inr (by simpa only [vertices, Set.mem_ofPred_eq, List.mem_cons] using ht.2 hx)
    · rw [K_apply, augmentation_single]
      by_cases hl : l = []
      · subst l
        rw [ite_eq_left rfl, one_smul]
        apply supported_single
        constructor
        · rfl
        · intro x hx
          exact Or.inl (by simpa only [vertices_vertex, Set.mem_singleton_iff] using hx)
      · rw [ite_eq_right hl, zero_smul]
        exact supported_zero G _

lemma boundary_lowers (s t : Simplex G)
    (ht : t ∈ (boundary G (Finsupp.single s 1)).support) :
    degree G t + 1 = degree G s := (boundary_faces G s t ht).1

def degreeModule (n : ℕ) : Submodule ℤ (Chain G) :=
  Finsupp.supported ℤ ℤ {s | degree G s = n}

lemma boundary_mem_degreeModule {n : ℕ} {c : Chain G}
    (hc : c ∈ degreeModule G (n+1)) : boundary G c ∈ degreeModule G n := by
  refine supported_linearMap G (Q := fun s => degree G s = n) (boundary G) ?_ hc
  intro s hs t ht
  have hl := boundary_lowers G s t ht
  exact Nat.add_right_cancel (hl.trans hs)

end OrderListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderListChainsBased
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise

namespace OrderListChains
variable (V : Type*)

def list (s : Simplex V) : List V := s.1 :: s.2
@[simp] lemma list_vertex (v : V) : list V (simplexVertex V v) = [v] := rfl
@[simp] lemma list_cone (v : V) (s : Simplex V) :
    list V (simplexCone V v s) = v :: list V s := rfl

lemma boundary_sublist (s : Simplex V) :
    Supported V (fun t => List.Sublist (list V t) (list V s)) (boundary V (Finsupp.single s 1)) := by
  rcases s with ⟨a,l⟩
  induction l generalizing a with
  | nil =>
    change Supported V _ (boundary V (vertex V a))
    rw [boundary_vertex]
    exact supported_zero V _
  | cons b l ih =>
    rw [single_cons,boundary_cone]
    apply supported_sub
    · apply supported_sub
      · apply supported_single
        exact List.Sublist.cons _ (List.Sublist.refl _)
      · refine supported_cone V (Q := fun t => List.Sublist (list V t) (list V (a,b::l))) a ?_ (ih b)
        intro t ht
        exact List.Sublist.cons_cons _ ht
    · rw [K_apply,augmentation_single]
      by_cases hl : l = []
      · subst l
        rw [ite_eq_left rfl,one_smul]
        apply supported_single
        exact List.Sublist.cons_cons _ (List.nil_sublist _)
      · rw [ite_eq_right hl,zero_smul]
        exact supported_zero V _

end OrderListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderChains
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderChains
section
open OrderListChains
variable (P : Type*) [Preorder P]
def Descending (s : Simplex P) : Prop := (list P s).Pairwise (fun a b => b ≤ a)
def module : Submodule ℤ (Chain P) := Finsupp.supported ℤ ℤ {s | Descending P s}
def carrier (x : P) : Submodule ℤ (Chain P) :=
  Finsupp.supported ℤ ℤ {s | Descending P s ∧ ∀ v ∈ vertices P s, v ≤ x}
lemma Descending.le_head {s : Simplex P} (hs : Descending P s) {v : P}
    (hv : v ∈ vertices P s) : v ≤ s.1 := by
  rcases hv with rfl | hv
  · exact le_rfl
  · exact (List.pairwise_cons.mp hs).1 v hv
lemma Descending.boundary {s t : Simplex P} (hs : Descending P s)
    (ht : t ∈ (boundary P (Finsupp.single s 1)).support) : Descending P t :=
  hs.sublist (boundary_sublist P s t ht)
lemma carrier_le_module (x : P) : carrier P x ≤ module P := fun _ hc _ hs => (hc hs).1
lemma boundary_mem {c : Chain P} (hc : c ∈ module P) : boundary P c ∈ module P := by
  apply OrderBasedComplex.map_mem_of_support
  intro s hs t ht
  exact (hc hs).boundary P ht

variable {Q : Type*} [Preorder Q]
lemma Descending.map (f : P →o Q) {s : Simplex P} (hs : Descending P s) :
    Descending Q (f s.1,s.2.map f) := by
  change ((list P s).map f).Pairwise _
  exact List.Pairwise.map f (fun a b h => f.monotone h) hs
lemma Descending.map_carrier (f g : P →o Q) (hfg : ∀ x, f x ≤ g x)
    {s : Simplex P} (hs : Descending P s) :
    mapChain P f (Finsupp.single s 1) ∈ carrier Q (g s.1) := by
  rw [mapChain_single]
  apply supported_single
  refine ⟨hs.map P f,?_⟩
  intro v hv
  rcases hv with rfl | hv
  · exact hfg s.1
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
    exact (f.monotone (hs.le_head P (Or.inr hw))).trans (hfg _)
lemma map_mem (f : P →o Q) {c : Chain P} (hc : c ∈ module P) :
    mapChain P f c ∈ module Q := by
  apply OrderBasedComplex.map_mem_of_support
  intro s hs
  exact carrier_le_module Q _ ((hc hs).map_carrier P f f (fun _ => le_rfl))
lemma map_degree (P : Type*) [Preorder P] {Q : Type*} [Preorder Q]
    (f : P → Q) {n : ℕ} {c : Chain P} (hc : Homogeneous P n c) :
    Homogeneous Q n (mapChain P f c) := by
  refine supported_linearMap P (P := fun s => degree P s = n)
    (Q := fun s => degree Q s = n) (mapChain P f) ?_ hc
  intro s hs
  rw [mapChain_single]
  apply supported_single
  simpa [degree] using hs

end

open OrderListChains
end OrderChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisCutBasis
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace OrderChainComplex
open OrderListChains
variable (P : Type) [Preorder P]
def simplexSet (n : ℕ) : Set (Simplex P) := {s | OrderChains.Descending P s ∧ degree P s = n}
def chains (n : ℕ) := Finsupp.supported ℤ ℤ (simplexSet P n)

lemma mem_chains {n : ℕ} {c : Chain P} : c ∈ chains P n ↔
    c ∈ OrderChains.module P ∧ Homogeneous P n c := by
  constructor
  · intro h
    exact ⟨fun s hs => (h hs).1,fun s hs => (h hs).2⟩
  · rintro ⟨h,h'⟩ s hs
    exact ⟨h hs,h' s hs⟩

def basisIso (n : ℕ) : chains P n ≃ₗ[ℤ] (simplexSet P n →₀ ℤ) :=
  Finsupp.supportedEquivFinsupp _

lemma boundary_internal (n : ℕ) (c : chains P (n+1)) : boundary P c ∈ chains P n := by
  exact (mem_chains P).mpr ⟨OrderChains.boundary_mem P ((mem_chains P).mp c.property).1,
    boundary_mem_degreeModule P ((mem_chains P).mp c.property).2⟩

def d (n : ℕ) : chains P (n+1) →ₗ[ℤ] chains P n :=
  LinearMap.codRestrict _ ((boundary P).comp (chains P (n+1)).subtype) (boundary_internal P n)
def aug : chains P 0 →ₗ[ℤ] ℤ := (augmentation P).comp (chains P 0).subtype
lemma d_d (n : ℕ) : (d P n).comp (d P (n+1)) = 0 := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  exact boundary_boundary P c.val
lemma d_aug : (aug P).comp (d P 0) = 0 := by
  ext c
  exact augmentation_boundary P c.val

end OrderChainComplex

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_EquivariantOrderChains
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace EquivariantOrderChains
open OrderListChains OrderChainComplex
variable {G P : Type} [Group G] [Preorder P] [MulAction G P]
  [CovariantClass G P HSMul.hSMul LE.le]

def simplexAct (n : ℕ) (g : G) (s : simplexSet P n) : simplexSet P n :=
  ⟨(g • s.val.1,s.val.2.map (g • ·)),s.property.1.map P (orderMap g),by
    simpa [degree] using s.property.2⟩

instance simplexAction (n : ℕ) : MulAction G (simplexSet P n) where
  smul := simplexAct n
  one_smul s := by
    apply Subtype.ext
    change ((1:G) • s.val.1,s.val.2.map ((1:G) • ·)) = s.val
    simp
  mul_smul g h s := by
    apply Subtype.ext
    change ((g*h) • s.val.1,s.val.2.map ((g*h) • ·)) =
      (g • (h • s.val.1),(s.val.2.map (h • ·)).map (g • ·))
    simp [mul_smul,List.map_map,Function.comp_def]

omit [Preorder P] in
lemma mapChain_id [Preorder P] (c : Chain P) : mapChain P id c = c := by
  have hh : mapChain P (id : P → P) = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro s r
    simp
  rw [hh,LinearMap.id_apply]
omit [Preorder P] in
lemma mapChain_comp [Preorder P] (f g : P → P) (c : Chain P) :
    mapChain P (f ∘ g) c = mapChain P f (mapChain P g c) := by
  have hh : mapChain P (f ∘ g) = (mapChain P f).comp (mapChain P g) := by
    apply Finsupp.lhom_ext
    intro s r
    simp [List.map_map]
  exact LinearMap.congr_fun hh c

def action (n : ℕ) (g : G) : chains P n →ₗ[ℤ] chains P n :=
  LinearMap.codRestrict _ ((mapChain P (g • ·)).comp (chains P n).subtype) (by
    intro c
    exact (mem_chains P).mpr ⟨OrderChains.map_mem P (orderMap g)
      ((mem_chains P).mp c.property).1,
      OrderChains.map_degree P (g • ·) ((mem_chains P).mp c.property).2⟩)

lemma action_val (n : ℕ) (g : G) (c : chains P n) :
    (action n g c).val = mapChain P (g • ·) c := rfl

def representation (n : ℕ) : Representation ℤ G (chains P n) where
  toFun := action n
  map_one' := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    simp only [action_val,one_smul,Module.End.one_apply]
    exact mapChain_id c.val
  map_mul' := by
    intro g h
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    change mapChain P ((g*h) • ·) c.val = mapChain P (g • ·) (mapChain P (h • ·) c.val)
    simpa only [mul_smul,Function.comp_def] using mapChain_comp (g • ·) (h • ·) c.val

def object (n : ℕ) : Rep ℤ G := Rep.of (representation (G := G) (P := P) n)

def differential (n : ℕ) : object (G := G) (P := P) (n+1) ⟶ object (G := G) (P := P) n :=
  Rep.ofHom ⟨d P n,by
    intro g
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact boundary_mapChain P (g • ·) c.val⟩

def augmentation : object (G := G) (P := P) 0 ⟶ Rep.trivial ℤ G ℤ :=
  Rep.ofHom ⟨aug P,by
    intro g
    apply LinearMap.ext
    intro c
    exact augmentation_mapChain P (g • ·) c.val⟩

lemma differential_squared (n : ℕ) :
    differential (G := G) (P := P) (n+1) ≫ differential n = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact d_d P n
lemma differential_aug : differential (G := G) (P := P) 0 ≫ augmentation = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact d_aug P

attribute [-instance] AddCommGroup.toIntModule
attribute [instance] AddCommGroup.toIntModule

lemma basisIso_single (n : ℕ) (s : simplexSet P n) (r : ℤ) :
    basisIso P n ⟨Finsupp.single s.val r,Finsupp.single_mem_supported ℤ r s.property⟩ =
      Finsupp.single s r := by
  apply (basisIso P n).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  exact (Finsupp.supportedEquivFinsupp_symm_single _ s r).symm

lemma basisIso_action (n : ℕ) (g : G) (c : chains P n) :
    basisIso P n (action n g c) =
      Finsupp.lmapDomain ℤ ℤ (fun s : simplexSet P n => g • s) (basisIso P n c) := by
  classical
  obtain ⟨z,rfl⟩ := (basisIso P n).symm.surjective c
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | single s r =>
    have he : (basisIso P n).symm (Finsupp.single s r) =
        ⟨Finsupp.single s.val r,Finsupp.single_mem_supported ℤ r s.property⟩ := by
      apply (basisIso P n).injective
      rw [LinearEquiv.apply_symm_apply,basisIso_single]
    rw [he,basisIso_single]
    have ha : action n g ⟨Finsupp.single s.val r,Finsupp.single_mem_supported ℤ r s.property⟩ =
        ⟨Finsupp.single (g • s).val r,Finsupp.single_mem_supported ℤ r (g • s).property⟩ := by
      apply Subtype.ext
      exact mapChain_single P (g • ·) s.val r
    rw [ha,basisIso_single]
    simp

def permutationIso (n : ℕ) : object (G := G) (P := P) n ≅
    permutationObject G (simplexSet P n) :=
  Rep.mkIso (Representation.Equiv.mk (basisIso P n) (fun g => by
    apply LinearMap.ext
    intro c
    exact basisIso_action n g c))
end EquivariantOrderChains

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
namespace OrderBrown
attribute [-instance] AddCommGroup.toIntModule
open OrderChainComplex EquivariantOrderChains
end OrderBrown

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_FiniteIndexProducts
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace EquivariantOrderChains
open OrderListChains OrderChainComplex
variable {G P : Type} [Group G] [Preorder P] [MulAction G P]
  [CovariantClass G P HSMul.hSMul LE.le] {n : ℕ}

def tuple (s : simplexSet P n) (i : Fin (n+1)) : P :=
  (s.val.1 :: s.val.2).get ⟨i.val,by
    have hn : s.val.2.length = n := s.property.2
    simp only [List.length_cons]
    omega⟩

lemma tuple_antitone (s : simplexSet P n) : Antitone (tuple s) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hlt | rfl
  · exact (List.pairwise_iff_get.mp s.property.1) _ _ hlt
  · exact le_rfl

def endpoints (s : simplexSet P n) : ActionTransport.Edge P :=
  ⟨(tuple s (Fin.last n),tuple s 0),tuple_antitone s (Fin.zero_le _)⟩

end EquivariantOrderChains

end

end OAI
end


