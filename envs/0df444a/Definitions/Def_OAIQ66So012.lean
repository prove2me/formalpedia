-- Prove2me | Definitions.Def_OAIQ66So012
-- name    : OAIQ66So012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:17:05.44859+00:00
-- url     : https://prove2.me/theorems/135ec103-69b8-4114-b4b5-5ccba84debed
-- title:
--   Definitions bundle OAIQ66So012 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 523 declarations of OpenAI's Lean: 136 definitions, 11 inductive types or structures, 7 instances and 369 theorems. The definitions and types are `OAI.CosetEndpoint.shapiroParentHomotopy`, `OAI.CosetEndpoint.shiftChain`, `OAI.CosetInduction.indCosetIso`, `OAI.DiscreteCoverCharts.fiberEquiv`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Quotient.normalCon`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Quotient.rawMap`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Cleanup.Sector`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Cleanup.Step`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Cleanup.cellsGrade`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Cleanup.emit`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Cleanup.grade`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Cleanup.letter`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Cleanup.normal`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Cleanup.output`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Cleanup.step`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Compiled.Cfg`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Compiled.MachineRel`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Compiled.MachineSector`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Compiled.Step`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Compiled.bases`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Compiled.cleanEntry`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Compiled.embed`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Compiled.handoff`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Compiled.project`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Control.Entry`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Control.Head`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Control.Sector`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Control.Success`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Control.machine`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Control.ofCfg`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Control.representative`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Control.table`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Control.toCfg`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Control.toValidator`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Control.validator`, `OAI.FiniteAlgebraicEnvelopes.Compiler.Control.validatorHead`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.Static`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.commandCode`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.commandPrimcodable`, `OAI.FiniteAlgebraicEnvelopes.Compiler.HeadCodec.controlCode` and 107 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `FiniteCompiler_Control`, `FiniteCompiler_Effectivity`, `FiniteCompiler_Normalization`, `FiniteCompiler_Quotients`, `FiniteCompiler_Selectors`, `FiniteCompiler_Simulator`, `FiniteCompiler_Surface`, `FiniteCompiler_UniformControl`, `FiniteType_CosetInduction`, `FiniteType_FiberCoreMap`, `FiniteType_FiniteIndexProducts`, `FiniteType_OrderListChains`, `FiniteType_RegularCoverGeometry`, `FiniteType_SemilinearCoinvariants`, `FiniteType_SphereCover`, `FiniteType_StandardShapiro`.
--
--   **Imports.** It imports the bundles `OAIQ66So000`, `OAIQ66So001`, `OAIQ66So002`, `OAIQ66So004` and `OAIQ66So005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So017`, `OAIQ66So018`, `OAIQ66So019` and `OAIQ66So020`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So000
import Definitions.Def_OAIQ66So001
import Definitions.Def_OAIQ66So002
import Definitions.Def_OAIQ66So004
import Definitions.Def_OAIQ66So005

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Simulator
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Scan.fixedFintype _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Scan.fixedStepDecidable _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableInstruction _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Literal finite-quota machine simulation and readout correctness.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Simulator

instance instFintypeMove : Fintype Move := ⟨{.stay, .left, .right}, by intro x; cases x <;> simp⟩

structure Command (Q Γ : Type*) where
  state : Q
  write : Γ
  move : Move
  deriving DecidableEq, Fintype

/-- A deterministic left-ended one-tape machine. `none` is halt, recognized
    only while the head is at a workspace cell. -/
structure Machine (Q Γ : Type*) where
  initial : Q
  transition : Q → Γ → Option (Command Q Γ)

variable {S Γ Q : Type*}

/-- The cell table is finite when the alphabets and state set are finite. All
    tests and assignments are precisely the source's scan expansion. -/
def cell (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]
    (q : Head S Q) (b : Base S) (t : Tag S Γ) :
    Option (Instruction (Head S Q) (Tag S Γ)) :=
  match q with
  | .start | .ok => none
  | .rewind s => some ⟨.rewind s,t,true⟩
  | .scan .input => match b with
    | .anchor a => if t.anchorRead then some ⟨q,t,true⟩
      else some ⟨.rewind (.fill a),{t with anchorRead := true},false⟩
    | _ => some ⟨q,t,true⟩
  | .scan (.fill a) => match b with
    | .workspace => if t.workspaceFilled then some ⟨q,t,true⟩
      else some ⟨.rewind .input,{t with workspaceFilled := true, work := A.input a},false⟩
    | _ => some ⟨q,t,true⟩
  | .scan .spare => match b with
    | .workspace => if t.workspaceFilled then some ⟨q,t,true⟩
      else some ⟨.rewind .first,t,false⟩
    | _ => some ⟨q,t,true⟩
  | .scan .first => match b with
    | .workspace => some ⟨.run M.initial,t,false⟩
    | _ => some ⟨q,t,true⟩
  | .run c => match b with
    | .workspace => match M.transition c t.work with
      | none => some ⟨.rewind .readout,t,false⟩
      | some d => some ⟨(if d.move = .left then .left d.state else .run d.state),
          {t with work := d.write}, d.move == .right⟩
    | _ => none
  | .left c => match b with
    | .workspace => some ⟨.run c,t,true⟩
    | .cutC => some ⟨.run c,t,false⟩
    | _ => none
  | .scan .readout => match b with
    | .workspace => if t.outputRead then some ⟨q,t,true⟩
      else if t.work = A.blank then some ⟨.finish,t,false⟩
      else (A.output t.work).map fun a => ⟨.rewind (.put a),{t with outputRead := true},false⟩
    | _ => some ⟨q,t,true⟩
  | .scan (.put a) => match b with
    | .anchor _ => match t.output with
      | none => some ⟨.rewind .readout,{t with output := some a},false⟩
      | some _ => some ⟨q,t,true⟩
    | _ => some ⟨q,t,true⟩
  | .finish => some ⟨q,t,true⟩

def table (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ] :
    Table (Head S Q) (Base S) (Tag S Γ) where
  direction
    | .rewind _ | .left _ => .left
    | _ => .right
  cell := cell A M
  boundary
    | .start => some (.rewind .input)
    | .rewind s => some (.scan s)
    | .scan .input => some (.rewind .spare)
    | .finish => some .ok
    | _ => none

theorem ok_terminal (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]
    (v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)) (hv : v.head = .ok) :
    Scan.step (table A M) v = none := by
  simp only [Scan.step, hv, table]
  split
  · simp [cell]
  · split <;> rfl

/-- Rewinding crosses all left cells unchanged and then changes phase at alpha.
    This lemma holds on dirty data as well as the intended clean simulation. -/
theorem rewind (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]
    (s : Resume S) (l r : List (Base S × Tag S Γ)) (rb : Bool) :
    Relation.ReflTransGen (Scan.Step (table A M))
      ⟨l,.rewind s,r,true,rb⟩ ⟨[],.scan s,l.reverse ++ r,true,rb⟩ := by
  induction l generalizing r with
  | nil =>
      apply Relation.ReflTransGen.single
      simp [Scan.Step, Scan.step, table]
  | cons a l ih =>
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        (Relation.ReflTransGen.head (by simp [Scan.Step, Scan.step, table, cell]) (ih (a::r)))

/-- Going to the right boundary also preserves every cell. -/
theorem finish (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]
    (l r : List (Base S × Tag S Γ)) (lb : Bool) :
    Relation.ReflTransGen (Scan.Step (table A M))
      ⟨l,.finish,r,lb,true⟩ ⟨r.reverse ++ l,.ok,[],lb,true⟩ := by
  induction r generalizing l with
  | nil =>
      apply Relation.ReflTransGen.single
      simp [Scan.Step, Scan.step, table]
  | cons a r ih =>
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        (Relation.ReflTransGen.head (by simp [Scan.Step, Scan.step, table, cell]) (ih (a::l)))

end FiniteAlgebraicEnvelopes.Compiler.Simulator

namespace FiniteAlgebraicEnvelopes.Compiler.Simulator

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

/-- One complete find/update/rewind invocation acts on the first matching
    cell. No higher-level operation is used in the actual finite table. -/
theorem scan_update (s s' : Resume S) (p r : Cells S Γ) (b : Base S) (t t' : Tag S Γ)
    (hp : ∀ c ∈ p, cell A M (.scan s) c.1 c.2 = some ⟨.scan s,c.2,true⟩)
    (hc : cell A M (.scan s) b t = some ⟨.rewind s',t',false⟩) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan s,p ++ (b,t)::r,true,true⟩
      ⟨[],.scan s',p ++ (b,t')::r,true,true⟩ := by
  have h₀ := Scan.cross_right (table A M) (.scan s) rfl p [] ((b,t)::r) true true hp
  simp only [List.append_nil] at h₀
  have h₁ : Scan.Step (table A M)
      ⟨p.reverse,.scan s,(b,t)::r,true,true⟩
      ⟨p.reverse,.rewind s',(b,t')::r,true,true⟩ := by
    simp [Scan.Step, Scan.step, table, hc]
  have h₂ := rewind A M s' p.reverse ((b,t')::r) true
  simpa using (h₀.trans ((ReflTransGen.single h₁).trans h₂))

def Pass (s : Resume S) (c : Base S × Tag S Γ) : Prop :=
  cell A M (.scan s) c.1 c.2 = some ⟨.scan s,c.2,true⟩

@[simp] theorem pass_read (a : S) : Pass A M .input (readAnchor A a true) := by
  rfl
@[simp] theorem pass_input_bareC : Pass A M .input (bare A .cutC) := by rfl
@[simp] theorem pass_input_bareD : Pass A M .input (bare A .cutD) := by rfl
@[simp] theorem pass_input_bareW : Pass A M .input (bare A .workspace) := by rfl
@[simp] theorem pass_input_filled (a : S) : Pass A M .input (filledWork A a) := by rfl
@[simp] theorem pass_fill_anchor (a b : S) (r : Bool) :
    Pass A M (.fill a) (readAnchor A b r) := by rfl
@[simp] theorem pass_fill_bareC (a : S) : Pass A M (.fill a) (bare A .cutC) := by rfl
@[simp] theorem pass_fill_filled (a b : S) : Pass A M (.fill a) (filledWork A b) := by rfl

/-- A loaded input letter is transferred to the next free workspace cell,
    expanding the prefix and shrinking the finite quota by one. -/
theorem copy_left_one (xp xs yp ys w : List S) (a : S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .input,body A xp (a::xs) yp ys w (n+1),true,true⟩
      ⟨[],.scan .input,body A (xp++[a]) xs yp ys (w++[a]) n,true,true⟩ := by
  let p := xp.map (readAnchor A · true)
  let r := xs.map (readAnchor A · false) ++ [bare A .cutC] ++
    w.map (filledWork A) ++ List.replicate (n+1) (bare A .workspace) ++
    [bare A .cutD] ++ yp.map (readAnchor A · true) ++ ys.map (readAnchor A · false)
  have h₁ := scan_update A M .input (.fill a) p r (.anchor a)
    (readAnchor A a false).2 (readAnchor A a true).2
    (by change ∀ c ∈ p, Pass A M .input c; simp [p]) (by rfl)
  let p' := (xp ++ [a]).map (readAnchor A · true) ++ xs.map (readAnchor A · false) ++
    [bare A .cutC] ++ w.map (filledWork A)
  let r' := List.replicate n (bare A .workspace) ++ [bare A .cutD] ++
    yp.map (readAnchor A · true) ++ ys.map (readAnchor A · false)
  have h₂ := scan_update A M (.fill a) .input p' r' .workspace
    (clean A.blank) (filledWork A a).2
    (by
      change ∀ c ∈ p', Pass A M (.fill a) c
      intro c hc
      simp only [p', List.mem_append, List.mem_map, List.mem_singleton] at hc
      rcases hc with ((⟨b,_,rfl⟩ | ⟨b,_,rfl⟩) | rfl) | ⟨b,_,rfl⟩ <;> simp) (by rfl)
  have heq : (⟨[],Head.scan (.fill a),p ++ (.anchor a,(readAnchor A a true).2)::r,
      true,true⟩ : Scan.Sector (Head S Q) (Base S) (Tag S Γ)) =
      ⟨[],.scan (.fill a),p' ++ (.workspace,clean A.blank)::r',true,true⟩ := by
    simp [p, r, p', r', List.replicate_succ, readAnchor, bare, List.append_assoc]
  rw [heq] at h₁
  simpa [body, p, r, p', r', List.replicate_succ, readAnchor, bare, filledWork,
    List.append_assoc] using h₁.trans h₂

theorem copy_right_one (xp yp ys w : List S) (a : S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .input,body A xp [] yp (a::ys) w (n+1),true,true⟩
      ⟨[],.scan .input,body A xp [] (yp++[a]) ys (w++[a]) n,true,true⟩ := by
  let p := xp.map (readAnchor A · true) ++ [bare A .cutC] ++ w.map (filledWork A) ++
    List.replicate (n+1) (bare A .workspace) ++ [bare A .cutD] ++
    yp.map (readAnchor A · true)
  let r := ys.map (readAnchor A · false)
  have h₁ := scan_update A M .input (.fill a) p r (.anchor a)
    (readAnchor A a false).2 (readAnchor A a true).2
    (by
      change ∀ c ∈ p, Pass A M .input c
      intro c hc
      simp only [p, List.mem_append, List.mem_map, List.mem_singleton,
        List.mem_replicate] at hc
      rcases hc with ((((⟨b,_,rfl⟩ | rfl) | ⟨b,_,rfl⟩) | ⟨_,rfl⟩) | rfl) | ⟨b,_,rfl⟩ <;>
        simp) (by rfl)
  let p' := xp.map (readAnchor A · true) ++ [bare A .cutC] ++ w.map (filledWork A)
  let r' := List.replicate n (bare A .workspace) ++ [bare A .cutD] ++
    (yp++[a]).map (readAnchor A · true) ++ ys.map (readAnchor A · false)
  have h₂ := scan_update A M (.fill a) .input p' r' .workspace
    (clean A.blank) (filledWork A a).2
    (by
      change ∀ c ∈ p', Pass A M (.fill a) c
      intro c hc
      simp only [p', List.mem_append, List.mem_map, List.mem_singleton] at hc
      rcases hc with (⟨b,_,rfl⟩ | rfl) | ⟨b,_,rfl⟩ <;> simp) (by rfl)
  have heq : (⟨[],Head.scan (.fill a),p ++ (.anchor a,(readAnchor A a true).2)::r,
      true,true⟩ : Scan.Sector (Head S Q) (Base S) (Tag S Γ)) =
      ⟨[],.scan (.fill a),p' ++ (.workspace,clean A.blank)::r',true,true⟩ := by
    simp [p, r, p', r', List.replicate_succ, readAnchor, bare, List.append_assoc]
  rw [heq] at h₁
  simpa [body, p, r, p', r', List.replicate_succ, readAnchor, bare, filledWork,
    List.append_assoc] using h₁.trans h₂

theorem copy_left (xp xs yp ys w : List S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .input,body A xp xs yp ys w (xs.length+n),true,true⟩
      ⟨[],.scan .input,body A (xp++xs) [] yp ys (w++xs) n,true,true⟩ := by
  induction xs generalizing xp w with
  | nil => simp; exact .refl
  | cons a xs ih =>
    have h := copy_left_one A M xp xs yp ys w a (xs.length+n)
    simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.append_assoc] using h.trans (ih (xp++[a]) (w++[a]))

theorem copy_right (xp yp ys w : List S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .input,body A xp [] yp ys w (ys.length+n),true,true⟩
      ⟨[],.scan .input,body A xp [] (yp++ys) [] (w++ys) n,true,true⟩ := by
  induction ys generalizing yp w with
  | nil => simp; exact .refl
  | cons a ys ih =>
    have h := copy_right_one A M xp yp ys w a (ys.length+n)
    simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.append_assoc] using h.trans (ih (yp++[a]) (w++[a]))

/-- Both anchor blocks are copied in their order, not in zipper order. -/
theorem copy_all (x y : List S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .input,body A [] x [] y [] (x.length+y.length+n),true,true⟩
      ⟨[],.scan .input,body A x [] y [] (x++y) n,true,true⟩ := by
  have h₁ := copy_left A M [] x [] y [] (y.length+n)
  have h₂ := copy_right A M x [] y x n
  simp only [List.nil_append] at h₁ h₂
  simpa only [Nat.add_assoc] using h₁.trans h₂

@[simp] theorem pass_spare_anchor (a : S) (r : Bool) :
    Pass A M .spare (readAnchor A a r) := by rfl
@[simp] theorem pass_spare_C : Pass A M .spare (bare A .cutC) := by rfl
@[simp] theorem pass_spare_filled (a : S) : Pass A M .spare (filledWork A a) := by rfl
@[simp] theorem pass_first_anchor (a : S) (r : Bool) :
    Pass A M .first (readAnchor A a r) := by rfl
@[simp] theorem pass_first_C : Pass A M .first (bare A .cutC) := by rfl

/-- The two final copy scans check a spare blank and position the machine at
    the first workspace cell. In particular the quota is not treated as tape
    that may silently grow during internal transitions. -/
theorem copy_enter_run (x y w : List S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .input,body A x [] y [] w (n+1),true,true⟩
      ⟨(x.map (readAnchor A · true) ++ [bare A .cutC]).reverse,.run M.initial,
        w.map (filledWork A) ++ List.replicate (n+1) (bare A .workspace) ++
          [bare A .cutD] ++ y.map (readAnchor A · true),true,true⟩ := by
  let cells := body A x [] y [] w (n+1)
  have hall : ∀ c ∈ cells, Pass A M .input c := by
    simp only [cells, body, List.map_nil, List.append_nil, List.forall_mem_append,
      List.forall_mem_map, List.forall_mem_singleton, List.forall_mem_replicate]
    simp
  have h₀ := Scan.cross_right (table A M) (.scan .input) rfl cells [] [] true true hall
  have h₁ : Scan.Step (table A M) ⟨cells.reverse,.scan .input,[],true,true⟩
      ⟨cells.reverse,.rewind .spare,[],true,true⟩ := by
    simp [Scan.Step, Scan.step, table]
  have h₂ := rewind A M .spare cells.reverse [] true
  simp only [List.reverse_reverse, List.append_nil] at h₀ h₂
  have hpre := h₀.trans ((ReflTransGen.single h₁).trans h₂)
  let p := x.map (readAnchor A · true) ++ [bare A .cutC] ++ w.map (filledWork A)
  let r := List.replicate n (bare A .workspace) ++ [bare A .cutD] ++
    y.map (readAnchor A · true)
  have hs := scan_update A M .spare .first p r .workspace (clean A.blank) (clean A.blank)
    (by
      change ∀ c ∈ p, Pass A M .spare c
      simp only [p, List.forall_mem_append, List.forall_mem_map, List.forall_mem_singleton]
      simp) (by rfl)
  have heq : cells = p ++ (.workspace,clean A.blank)::r := by
    simp [cells, body, p, r, bare, List.replicate_succ, List.append_assoc]
  rw [← heq] at hs
  let p' := x.map (readAnchor A · true) ++ [bare A .cutC]
  let r' := w.map (filledWork A) ++ List.replicate (n+1) (bare A .workspace) ++
    [bare A .cutD] ++ y.map (readAnchor A · true)
  have hp' : ∀ c ∈ p', Pass A M .first c := by
    simp only [p', List.forall_mem_append, List.forall_mem_map, List.forall_mem_singleton]
    simp
  have hf := Scan.cross_right (table A M) (.scan .first) rfl p' [] r' true true hp'
  have hnonempty : ∃ t tail, r' = (.workspace,t)::tail := by
    cases w with
    | nil => exact ⟨clean A.blank,r,by simp [r', r, bare, List.replicate_succ, List.append_assoc]⟩
    | cons a w =>
      exact ⟨(filledWork A a).2,
        w.map (filledWork A) ++ List.replicate (n+1) (bare A .workspace) ++
          [bare A .cutD] ++ y.map (readAnchor A · true),
        by simp [r', filledWork, List.append_assoc]⟩
  have hlast : Scan.Step (table A M) ⟨p'.reverse,.scan .first,r',true,true⟩
      ⟨p'.reverse,.run M.initial,r',true,true⟩ := by
    obtain ⟨tag,tail,hr⟩ := hnonempty
    simp [Scan.Step, Scan.step, table, cell, hr]
  have heq' : cells = p' ++ r' := by simp [cells, body, p', r', List.append_assoc]
  rw [← heq'] at hf
  simp only [List.append_nil] at hf
  exact hpre.trans (hs.trans (hf.tail hlast))

/-- The fresh post-validator handoff starts copying from the left boundary. -/
theorem start_copy (cells : Cells S Γ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨cells.reverse,.start,[],true,true⟩ ⟨[],.scan .input,cells,true,true⟩ := by
  have h₀ : Scan.Step (table A M) ⟨cells.reverse,.start,[],true,true⟩
      ⟨cells.reverse,.rewind .input,[],true,true⟩ := by
    simp [Scan.Step, Scan.step, table]
  simpa using (ReflTransGen.head h₀ (rewind A M .input cells.reverse [] true))

/-- Literal correctness of the complete copy/init program with any sufficient
    finite quota. Every table operation is one of the listed compiled equations. -/
theorem copy_correct (x y : List S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨(body A [] x [] y [] (x.length+y.length+n+1)).reverse,.start,[],true,true⟩
      ⟨(x.map (readAnchor A · true) ++ [bare A .cutC]).reverse,.run M.initial,
        (x++y).map (filledWork A) ++ List.replicate (n+1) (bare A .workspace) ++
          [bare A .cutD] ++ y.map (readAnchor A · true),true,true⟩ := by
  have h₀ := start_copy A M (body A [] x [] y [] (x.length+y.length+(n+1)))
  have h₁ := copy_all A M x y (n+1)
  have h₂ := copy_enter_run A M x y (x++y) n
  simpa only [Nat.add_assoc] using h₀.trans (h₁.trans h₂)

end

section
open Relation
variable {S Γ Q : Type*}

/-- The intended finite-quota operations of the finite compiler. These are
    defined from the given machine table, not postulated accepting transitions. -/
inductive TapeStep (M : Machine Q Γ) : Tape (S := S) (Γ := Γ) (Q := Q) → Tape → Prop
  | stay {q l t r d} (h : M.transition q t.work = some d) (hm : d.move = .stay) :
      TapeStep M ⟨q,l,t::r⟩ ⟨d.state,l,writeWork t d.write::r⟩
  | right {q l t r d} (h : M.transition q t.work = some d) (hm : d.move = .right) :
      TapeStep M ⟨q,l,t::r⟩ ⟨d.state,writeWork t d.write::l,r⟩
  | leftEdge {q t r d} (h : M.transition q t.work = some d) (hm : d.move = .left) :
      TapeStep M ⟨q,[],t::r⟩ ⟨d.state,[],writeWork t d.write::r⟩
  | left {q v l t r d} (h : M.transition q t.work = some d) (hm : d.move = .left) :
      TapeStep M ⟨q,v::l,t::r⟩ ⟨d.state,l,v::writeWork t d.write::r⟩

def workCells (l : List (Tag S Γ)) : Cells S Γ := l.map fun t => (.workspace,t)

/-- Workspace in its fixed surrounding anchor/cut sector. `x` is the cells
    before C in their ordinary order, `y` the cells following D. -/
def runSector (A : Alphabet S Γ) (x y : Cells S Γ) (c : Tape (S := S) (Γ := Γ) (Q := Q)) :
    Scan.Sector (Head S Q) (Base S) (Tag S Γ) :=
  ⟨workCells c.left ++ bare A .cutC :: x.reverse, .run c.state,
    workCells c.right ++ bare A .cutD :: y, true, true⟩

variable (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

/-- Every bounded machine transition is implemented by one or two actual
    finite scan instructions. Both the stationary left edge and true left
    movement are proved, and no quota insertion occurs during simulation. -/
theorem tapeStep_simulates (x y : Cells S Γ) {c d : Tape (S := S) (Γ := Γ) (Q := Q)}
    (h : TapeStep M c d) :
    ReflTransGen (Scan.Step (table A M)) (runSector A x y c) (runSector A x y d) := by
  cases h with
  | stay h hm =>
      apply ReflTransGen.single
      simp [Scan.Step, Scan.step, table, cell, runSector, workCells, h, hm, writeWork]
  | right h hm =>
      apply ReflTransGen.single
      simp [Scan.Step, Scan.step, table, cell, runSector, workCells, h, hm, writeWork]
  | @leftEdge q t r d h hm =>
      apply ReflTransGen.trans (b :=
        ⟨bare A .cutC :: x.reverse, .left d.state,
          (.workspace, writeWork t d.write) :: (workCells r ++ bare A .cutD :: y), true,true⟩)
      · apply ReflTransGen.single
        simp [Scan.Step, Scan.step, table, cell, runSector, workCells, h, hm, writeWork]
      · apply ReflTransGen.single
        simp [Scan.Step, Scan.step, table, cell, runSector, workCells, bare]
  | @left q v l t r d h hm =>
      apply ReflTransGen.trans (b :=
        ⟨(.workspace,v) :: (workCells l ++ bare A .cutC :: x.reverse), .left d.state,
          (.workspace, writeWork t d.write) :: (workCells r ++ bare A .cutD :: y),true,true⟩)
      · apply ReflTransGen.single
        simp [Scan.Step, Scan.step, table, cell, runSector, workCells, h, hm, writeWork]
      · apply ReflTransGen.single
        simp [Scan.Step, Scan.step, table, cell, runSector, workCells]

/-- Simulation respects literal finite traces, without a running-time bound. -/
theorem tapeRun_simulates (x y : Cells S Γ) {c d : Tape (S := S) (Γ := Γ) (Q := Q)}
    (h : ReflTransGen (TapeStep M) c d) :
    ReflTransGen (Scan.Step (table A M)) (runSector A x y c) (runSector A x y d) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.trans (tapeStep_simulates A M x y hs)

/-- Exhaustion is stuck even if the machine's current state would be halting:
    a halt must be observed at an actual workspace cell. -/
theorem quota_exhausted (x y : Cells S Γ) (q : Q) (l : List (Tag S Γ)) :
    Scan.step (table A M) (runSector A x y ⟨q,l,[]⟩) = none := by
  simp [Scan.step, table, cell, runSector, workCells, bare]

/-- A genuine in-bounds halt triggers precisely the readout rewind. -/
theorem halt_readout (x y : Cells S Γ) (q : Q) (l : List (Tag S Γ))
    (t : Tag S Γ) (r : List (Tag S Γ)) (h : M.transition q t.work = none) :
    ReflTransGen (Scan.Step (table A M))
      (runSector A x y ⟨q,l,t::r⟩)
      ⟨[],.scan .readout,
        x ++ [bare A .cutC] ++ workCells (l.reverse ++ t::r) ++ bare A .cutD :: y,
        true,true⟩ := by
  have hs : Scan.Step (table A M) (runSector A x y ⟨q,l,t::r⟩)
      ⟨workCells l ++ bare A .cutC :: x.reverse, .rewind .readout,
        workCells (t::r) ++ bare A .cutD :: y, true,true⟩ := by
    simp [Scan.Step, Scan.step, table, cell, runSector, workCells, h]
  have hr := rewind A M .readout (workCells l ++ bare A .cutC :: x.reverse)
    (workCells (t::r) ++ bare A .cutD :: y) true
  simpa [workCells, List.reverse_append, List.reverse_cons, List.map_reverse,
    List.append_assoc] using ((ReflTransGen.single hs).trans hr)

end

section
open Relation
variable {S Γ Q : Type*}

def workView (l : Cells S Γ) : List (Bool × Γ) :=
  l.filterMap fun c => match c.1 with
    | .workspace => some (c.2.outputRead,c.2.work)
    | _ => none

def anchorView (l : Cells S Γ) : List (Option S) :=
  l.filterMap fun c => match c.1 with
    | .anchor _ => some c.2.output
    | _ => none

@[simp] theorem workView_append (l r : Cells S Γ) :
    workView (l ++ r) = workView l ++ workView r := List.filterMap_append
@[simp] theorem anchorView_append (l r : Cells S Γ) :
    anchorView (l ++ r) = anchorView l ++ anchorView r := List.filterMap_append

variable (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

theorem readout_pass (l : Cells S Γ) (done : List Γ)
    (h : workView l = done.map (true,·)) :
    ∀ c ∈ l, cell A M (.scan .readout) c.1 c.2 = some ⟨.scan .readout,c.2,true⟩ := by
  rintro ⟨b,t⟩ hc
  cases b <;> try rfl
  have ht : (t.outputRead,t.work) ∈ workView l :=
    List.mem_filterMap.mpr ⟨(.workspace,t),hc,rfl⟩
  rw [h] at ht
  obtain ⟨v,_,hv⟩ := List.mem_map.mp ht
  have hr : t.outputRead = true := (congrArg Prod.fst hv).symm
  simp [cell, hr]

theorem put_pass (a : S) (l : Cells S Γ) (done : List S)
    (h : anchorView l = done.map some) :
    ∀ c ∈ l, cell A M (.scan (.put a)) c.1 c.2 = some ⟨.scan (.put a),c.2,true⟩ := by
  rintro ⟨b,t⟩ hc
  cases b <;> try rfl
  rename_i b
  have ht : t.output ∈ anchorView l := List.mem_filterMap.mpr ⟨(.anchor b,t),hc,rfl⟩
  rw [h] at ht
  obtain ⟨v,_,hv⟩ := List.mem_map.mp ht
  simp [cell, ← hv]

/-- One output letter is read from the first unread workspace cell and written
    to the first unmarked anchor. The projected views certify both orders. -/
theorem readout_one (cells : Cells S Γ) (done remaining : List Γ)
    (out : List S) (a : S) (g : Γ) (n : ℕ)
    (hw : workView cells = done.map (true,·) ++ (false,g)::remaining.map (false,·))
    (ha : anchorView cells = out.map some ++ none :: List.replicate n none)
    (hg : g ≠ A.blank) (hg' : A.output g = some a) :
    ∃ cells', ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .readout,cells,true,true⟩ ⟨[],.scan .readout,cells',true,true⟩ ∧
      workView cells' = (done ++ [g]).map (true,·) ++ remaining.map (false,·) ∧
      anchorView cells' = (out ++ [a]).map some ++ List.replicate n none := by
  obtain ⟨p,⟨b,t⟩,r,hc,hp,hb,hr⟩ := split_filterMap
    (fun c : Base S × Tag S Γ => match c.1 with
      | .workspace => some (c.2.outputRead,c.2.work) | _ => none)
    cells (done.map (true,·)) (false,g) (remaining.map (false,·)) hw
  cases b <;> simp only at hb
  all_goals try contradiction
  have ht : t.outputRead = false ∧ t.work = g := by simpa using hb
  let t' : Tag S Γ := {t with outputRead := true}
  let mid := p ++ (.workspace,t')::r
  have hs := scan_update A M .readout (.put a) p r .workspace t t'
    (readout_pass A M p done hp) (by simp [cell, ht.1, ht.2, hg, hg', t'])
  rw [← hc] at hs
  have hwm : workView mid = (done ++ [g]).map (true,·) ++ remaining.map (false,·) := by
    simp only [mid, workView_append]
    change workView p ++ (true,t.work)::workView r = _
    change workView p = _ at hp
    change workView r = _ at hr
    simp [hp, hr, ht.2, List.append_assoc]
  have ham : anchorView mid = anchorView cells := by
    rw [hc]
    simp [mid, anchorView, List.filterMap_append]
  obtain ⟨p₂,⟨b₂,t₂⟩,r₂,hc₂,hp₂,hb₂,hr₂⟩ := split_filterMap
    (fun c : Base S × Tag S Γ => match c.1 with
      | .anchor _ => some c.2.output | _ => none)
    mid (out.map some) none (List.replicate n none) (ham.trans ha)
  cases b₂ <;> simp only at hb₂
  all_goals try contradiction
  rename_i a₂
  have ht₂ : t₂.output = none := Option.some.inj hb₂
  let t₂' : Tag S Γ := {t₂ with output := some a}
  let result := p₂ ++ (.anchor a₂,t₂')::r₂
  have hs₂ := scan_update A M (.put a) .readout p₂ r₂ (.anchor a₂) t₂ t₂'
    (put_pass A M a p₂ out hp₂) (by simp [cell, ht₂, t₂'])
  rw [← hc₂] at hs₂
  refine ⟨result,hs.trans hs₂,?_,?_⟩
  · have heq : workView result = workView mid := by
      rw [hc₂]
      simp [result, workView, List.filterMap_append]
    exact heq.trans hwm
  · simp only [result, anchorView_append]
    change anchorView p₂ ++ some a :: anchorView r₂ = _
    change anchorView p₂ = _ at hp₂
    change anchorView r₂ = _ at hr₂
    simp [hp₂,hr₂,List.append_assoc]

/-- The first unread blank ends output. No cell is changed by the final sweep. -/
theorem readout_blank (cells : Cells S Γ) (done : List Γ) (rest : List (Bool × Γ))
    (hw : workView cells = done.map (true,·) ++ (false,A.blank)::rest) :
    ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .readout,cells,true,true⟩ ⟨cells.reverse,.ok,[],true,true⟩ := by
  obtain ⟨p,⟨b,t⟩,r,hc,hp,hb,_⟩ := split_filterMap
    (fun c : Base S × Tag S Γ => match c.1 with
      | .workspace => some (c.2.outputRead,c.2.work) | _ => none)
    cells (done.map (true,·)) (false,A.blank) rest hw
  cases b <;> simp only at hb
  all_goals try contradiction
  have ht : t.outputRead = false ∧ t.work = A.blank := by simpa using hb
  have h₀ := Scan.cross_right (table A M) (.scan .readout) rfl p [] ((.workspace,t)::r)
    true true (readout_pass A M p done hp)
  simp only [List.append_nil] at h₀
  have h₁ : Scan.Step (table A M) ⟨p.reverse,.scan .readout,(.workspace,t)::r,true,true⟩
      ⟨p.reverse,.finish,(.workspace,t)::r,true,true⟩ := by
    simp [Scan.Step, Scan.step, table, cell, ht.1, ht.2]
  have h₂ := finish A M p.reverse ((.workspace,t)::r) true
  simpa [hc, List.reverse_append] using h₀.trans ((ReflTransGen.single h₁).trans h₂)

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

omit [DecidableEq Γ] in
theorem input_ne_blank (a : S) : A.input a ≠ A.blank := by
  intro h
  have := A.output_input a
  rw [h, A.output_blank] at this
  contradiction

/-- Complete readout of a finite, blank-delimited returned string. The spare
    anchor count drops by exactly one for each letter, including when that
    letter's anchor is on the other side of the workspace. -/
theorem readout_complete (out : List S) (cells : Cells S Γ) (done tail : List Γ)
    (old : List S) (n : ℕ)
    (hw : workView cells = done.map (true,·) ++
      (out.map A.input ++ A.blank::tail).map (false,·))
    (ha : anchorView cells = old.map some ++ List.replicate (out.length+n) none) :
    ∃ cells', ReflTransGen (Scan.Step (table A M))
      ⟨[],.scan .readout,cells,true,true⟩ ⟨cells'.reverse,.ok,[],true,true⟩ ∧
      anchorView cells' = (old ++ out).map some ++ List.replicate n none := by
  induction out generalizing cells done old with
  | nil =>
      refine ⟨cells,readout_blank A M cells done (tail.map (false,·)) ?_,?_⟩
      · simpa using hw
      · simpa using ha
  | cons a out ih =>
      have hw' : workView cells = done.map (true,·) ++ (false,A.input a)::
          (out.map A.input ++ A.blank::tail).map (false,·) := by simpa using hw
      have ha' : anchorView cells = old.map some ++ none::
          List.replicate (out.length+n) none := by
        have hn : (a :: out).length + n = (out.length + n) + 1 := by simp; omega
        rw [hn, List.replicate_succ] at ha
        exact ha
      obtain ⟨mid,hs,hmw,hma⟩ := readout_one A M cells done
        (out.map A.input ++ A.blank::tail) old a (A.input a) (out.length+n)
        hw' ha' (input_ne_blank A a) (A.output_input a)
      obtain ⟨result,hr,hra⟩ := ih mid (done ++ [A.input a]) (old ++ [a]) hmw hma
      refine ⟨result,hs.trans hr,?_⟩
      simpa [List.append_assoc] using hra

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

/-- Rejection here means the actual finite table has no forward accepting
    trace; it is stronger than merely failing a chosen simulation trace. -/
def Rejects (v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)) : Prop :=
  ∀ w, ReflTransGen (Scan.Step (table A M)) v w → w.head ≠ .ok

theorem terminal_of_none {v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (h : Scan.step (table A M) v = none) : Terminal (Scan.Step (table A M)) v := by
  intro w hw
  rw [Scan.Step, h] at hw
  contradiction

theorem rejects_of_stuck {v s : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (hvs : ReflTransGen (Scan.Step (table A M)) v s)
    (hs : Scan.step (table A M) s = none) (hq : s.head ≠ .ok) : Rejects A M v := by
  intro w hw hq'
  rcases ReflTransGen.total_of_right_unique (Scan.deterministic (table A M)) hvs hw with h | h
  · exact hq ((congrArg Scan.Sector.head (terminal_eq_of_reaches (terminal_of_none A M hs) h)).trans hq')
  · have he := terminal_eq_of_reaches (terminal_of_none A M (ok_terminal A M w hq')) h
    exact hq ((congrArg Scan.Sector.head he).symm.trans hq')

theorem rejects_before {v s : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (hvs : ReflTransGen (Scan.Step (table A M)) v s) (hs : Rejects A M s) : Rejects A M v := by
  intro w hw hq
  rcases ReflTransGen.total_of_right_unique (Scan.deterministic (table A M)) hvs hw with h | h
  · exact hs w h hq
  · have he := terminal_eq_of_reaches (terminal_of_none A M (ok_terminal A M w hq)) h
    exact hs s .refl ((congrArg Scan.Sector.head he).symm.trans hq)

/-- No unread cell, in particular no blank delimiter, means that readout stops
    at omega without entering the finish phase. -/
theorem readout_no_unread (cells : Cells S Γ) (done : List Γ)
    (h : workView cells = done.map (true,·)) :
    Rejects A M ⟨[],.scan .readout,cells,true,true⟩ := by
  have hr := Scan.cross_right (table A M) (.scan .readout) rfl cells [] [] true true
    (readout_pass A M cells done h)
  simp only [List.append_nil] at hr
  exact rejects_of_stuck A M hr (by simp [Scan.step,table]) (by simp)

/-- Filled anchors cannot be overwritten. Exhausting them rejects even if a
    workspace character was successfully decoded. -/
theorem put_no_anchor (cells : Cells S Γ) (old : List S) (a : S)
    (h : anchorView cells = old.map some) :
    Rejects A M ⟨[],.scan (.put a),cells,true,true⟩ := by
  have hr := Scan.cross_right (table A M) (.scan (.put a)) rfl cells [] [] true true
    (put_pass A M a cells old h)
  simp only [List.append_nil] at hr
  exact rejects_of_stuck A M hr (by simp [Scan.step,table]) (by simp)

/-- Metasymbols that are neither blank nor returned letters block output. -/
theorem readout_invalid (cells : Cells S Γ) (done : List Γ) (g : Γ)
    (rest : List (Bool × Γ))
    (h : workView cells = done.map (true,·) ++ (false,g)::rest)
    (hg : g ≠ A.blank) (hdecode : A.output g = none) :
    Rejects A M ⟨[],.scan .readout,cells,true,true⟩ := by
  obtain ⟨p,⟨b,t⟩,r,hc,hp,hb,_⟩ := split_filterMap
    (fun c : Base S × Tag S Γ => match c.1 with
      | .workspace => some (c.2.outputRead,c.2.work) | _ => none)
    cells (done.map (true,·)) (false,g) rest h
  cases b <;> simp only at hb
  all_goals try contradiction
  have ht : t.outputRead = false ∧ t.work = g := by simpa using hb
  have hr := Scan.cross_right (table A M) (.scan .readout) rfl p [] ((.workspace,t)::r)
    true true (readout_pass A M p done hp)
  simp only [List.append_nil] at hr
  rw [← hc] at hr
  exact rejects_of_stuck A M hr
    (by simp [Scan.step,table,cell,ht.1,ht.2,hg,hdecode]) (by simp)

/-- The first nonblank output symbol cannot succeed when all anchors are full. -/
theorem readout_no_anchor (cells : Cells S Γ) (done : List Γ) (rest : List (Bool × Γ))
    (old : List S) (a : S) (g : Γ)
    (hw : workView cells = done.map (true,·) ++ (false,g)::rest)
    (ha : anchorView cells = old.map some)
    (hg : g ≠ A.blank) (hdecode : A.output g = some a) :
    Rejects A M ⟨[],.scan .readout,cells,true,true⟩ := by
  obtain ⟨p,⟨b,t⟩,r,hc,hp,hb,_⟩ := split_filterMap
    (fun c : Base S × Tag S Γ => match c.1 with
      | .workspace => some (c.2.outputRead,c.2.work) | _ => none)
    cells (done.map (true,·)) (false,g) rest hw
  cases b <;> simp only at hb
  all_goals try contradiction
  have ht : t.outputRead = false ∧ t.work = g := by simpa using hb
  let t' : Tag S Γ := {t with outputRead := true}
  have hr := scan_update A M .readout (.put a) p r .workspace t t'
    (readout_pass A M p done hp) (by simp [cell,ht.1,ht.2,hg,hdecode,t'])
  rw [← hc] at hr
  apply rejects_before A M hr
  apply put_no_anchor A M (p ++ (.workspace,t')::r) old a
  rw [hc] at ha
  simpa [anchorView,List.filterMap_append] using ha

end

section
open Relation
variable {S Γ Q : Type*}

/-- Appending untouched blank cells reserves quota without altering any already
    represented tape position. -/
def pad (A : Alphabet S Γ) (c : Tape (S := S) (Γ := Γ) (Q := Q)) (n : ℕ) : Tape (S := S) (Γ := Γ) (Q := Q) :=
  { c with right := c.right ++ List.replicate n (clean A.blank) }

/-- Unbounded left-ended tape semantics. A cell beyond the finite represented
    region is blank; it is materialized only when reached. No output fact or
    acceptance relation is built into these transition constructors. -/
inductive UnboundedStep (A : Alphabet S Γ) (M : Machine Q Γ) :
    Tape (S := S) (Γ := Γ) (Q := Q) → Tape (S := S) (Γ := Γ) (Q := Q) → Prop
  | within {c d} (h : TapeStep M c d) : UnboundedStep A M c d
  | extend {q l d} (h : TapeStep M ⟨q,l,[clean A.blank]⟩ d) :
      UnboundedStep A M ⟨q,l,[]⟩ d

variable (A : Alphabet S Γ) (M : Machine Q Γ)

/-- A bounded operation never inspects cells beyond its current head and is
    therefore preserved by appending arbitrary extra blank quota. -/
theorem tapeStep_pad {c d : Tape (S := S) (Γ := Γ) (Q := Q)}
    (h : TapeStep M c d) (n : ℕ) : TapeStep M (pad A c n) (pad A d n) := by
  cases h with
  | stay h hm => exact .stay h hm
  | right h hm => exact .right h hm
  | leftEdge h hm => exact .leftEdge h hm
  | left h hm => exact .left h hm

/-- Every finite unbounded trace uses a finite quota. The terminal padding can
    be prescribed in advance, in particular ensuring an explicit spare blank. -/
theorem finite_quota {c d : Tape (S := S) (Γ := Γ) (Q := Q)}
    (h : ReflTransGen (UnboundedStep A M) c d) :
    ∀ n, ∃ k, n ≤ k ∧ ReflTransGen (TapeStep M) (pad A c k) (pad A d n) := by
  induction h with
  | refl => exact fun n => ⟨n,le_rfl,.refl⟩
  | @tail d e _ hs ih =>
      intro n
      cases hs with
      | within hh =>
          obtain ⟨k,hkn,hk⟩ := ih n
          exact ⟨k,hkn,hk.tail (tapeStep_pad A M hh n)⟩
      | @extend q l e hh =>
          obtain ⟨k,hkn,hk⟩ := ih (n+1)
          refine ⟨k,by omega,hk.tail ?_⟩
          simpa [pad,List.replicate_succ] using tapeStep_pad A M hh n

/-- A predicate on full tags insensitive to changes of the work symbol is an
    invariant of every bounded run, not just of a chosen clean execution. -/
theorem tapeStep_tags (P : Tag S Γ → Prop)
    (hwrite : ∀ t a, P t → P (writeWork t a))
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : TapeStep M c d)
    (hc : ∀ t ∈ c.left ++ c.right, P t) : ∀ t ∈ d.left ++ d.right, P t := by
  cases h <;> simp only [List.mem_append,List.mem_cons] at hc ⊢
  all_goals
    intro t ht
    rcases ht with (ht | ht)
    · try {exact hc t (Or.inl ht)}
      try {rcases ht with rfl | ht
           · exact hwrite _ _ (hc _ (Or.inr (Or.inl rfl)))
           · exact hc t (Or.inl ht)}
      try {exact hc t (Or.inl (Or.inr ht))}
    · try {rcases ht with rfl | ht
           · exact hwrite _ _ (hc _ (Or.inr (Or.inl rfl)))
           · exact hc t (Or.inr (Or.inr ht))}
      try {exact hc t (Or.inr (Or.inr ht))}
      try {rcases ht with rfl | rfl | ht
           · exact hc _ (Or.inl (Or.inl rfl))
           · exact hwrite _ _ (hc _ (Or.inr (Or.inl rfl)))
           · exact hc t (Or.inr (Or.inr ht))}

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ)

theorem unboundedStep_tags (P : Tag S Γ → Prop)
    (hblank : P (clean A.blank)) (hwrite : ∀ t a, P t → P (writeWork t a))
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : UnboundedStep A M c d)
    (hc : ∀ t ∈ c.left ++ c.right, P t) : ∀ t ∈ d.left ++ d.right, P t := by
  cases h with
  | within h => exact tapeStep_tags M P hwrite h hc
  | extend h =>
      apply tapeStep_tags M P hwrite h
      simpa using (show ∀ t, t ∈ _ ∨ t = clean A.blank → P t from
        fun t ht => ht.elim (fun ht => hc t (by simpa using ht)) (fun ht => ht ▸ hblank))

theorem unboundedRun_tags (P : Tag S Γ → Prop)
    (hblank : P (clean A.blank)) (hwrite : ∀ t a, P t → P (writeWork t a))
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : ReflTransGen (UnboundedStep A M) c d)
    (hc : ∀ t ∈ c.left ++ c.right, P t) : ∀ t ∈ d.left ++ d.right, P t := by
  induction h with
  | refl => exact hc
  | tail _ hs ih => exact unboundedStep_tags A M P hblank hwrite hs ih

/-- Initial finite representation after copying, before adding blank quota. -/
def initialTape (w : List S) : Tape (S := S) (Γ := Γ) (Q := Q) :=
  ⟨M.initial,[],w.map fun a => (filledWork A a).2⟩

/-- The halt test includes the implicit blank at the first unrepresented cell. -/
def Halted (c : Tape (S := S) (Γ := Γ) (Q := Q)) : Prop :=
  M.transition c.state (c.right.headD (clean A.blank)).work = none

/-- The returned string begins at position zero and is delimited by its first
    blank. Extra blanks may lie outside the finite represented portion. -/
def Returns (c : Tape (S := S) (Γ := Γ) (Q := Q)) (out : List S) : Prop :=
  ∃ n tail, (c.left.reverse ++ c.right).map Tag.work ++ List.replicate n A.blank =
    out.map A.input ++ A.blank::tail

@[simp] theorem pad_left (c : Tape (S := S) (Γ := Γ) (Q := Q)) (n : ℕ) :
    (pad A c n).left = c.left := rfl

@[simp] theorem pad_right (c : Tape (S := S) (Γ := Γ) (Q := Q)) (n : ℕ) :
    (pad A c n).right = c.right ++ List.replicate n (clean A.blank) := rfl

theorem halt_pad {c : Tape (S := S) (Γ := Γ) (Q := Q)} (hc : Halted A M c) (n : ℕ) :
    ∃ t r, (pad A c (n+1)).right = t::r ∧ M.transition c.state t.work = none := by
  rcases c with ⟨q,l,r⟩
  cases r with
  | nil => exact ⟨clean A.blank,List.replicate n (clean A.blank),rfl,hc⟩
  | cons t r => exact ⟨t,r ++ List.replicate (n+1) (clean A.blank),rfl,hc⟩

@[simp] theorem anchorView_workCells (ts : List (Tag S Γ)) :
    anchorView (workCells ts) = [] := by simp [workCells,anchorView,List.filterMap_map]

/-- Full cell list at readout, with the copied anchors on either side. -/
def finalCells (x y : List S) (c : Tape (S := S) (Γ := Γ) (Q := Q)) : Cells S Γ :=
  x.map (readAnchor A · true) ++ [bare A .cutC] ++
    workCells (c.left.reverse ++ c.right) ++ bare A .cutD :: y.map (readAnchor A · true)

@[simp] theorem anchorView_readAnchors (xs : List S) (r : Bool) :
    anchorView (xs.map (readAnchor A · r)) = List.replicate xs.length none := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      change none :: anchorView (xs.map (readAnchor A · r)) = _
      rw [ih]
      rfl

@[simp] theorem workView_readAnchors (xs : List S) (r : Bool) :
    workView (xs.map (readAnchor A · r)) = [] := by
  simp [workView,readAnchor,List.filterMap_map]

theorem finalCells_anchors (x y : List S) (c : Tape (S := S) (Γ := Γ) (Q := Q)) :
    anchorView (finalCells A x y c) = List.replicate (x.length+y.length) none := by
  have hC : anchorView [bare A .cutC] = [] := rfl
  have hD : anchorView (bare A .cutD :: y.map (readAnchor A · true)) =
      List.replicate y.length none := anchorView_readAnchors A y true
  simp only [finalCells,anchorView_append,anchorView_readAnchors,anchorView_workCells,hC,hD]
  simp

theorem finalCells_work (x y : List S) (c : Tape (S := S) (Γ := Γ) (Q := Q))
    (hc : ∀ t ∈ c.left ++ c.right, t.outputRead = false) :
    workView (finalCells A x y c) = ((c.left.reverse ++ c.right).map Tag.work).map (false,·) := by
  have hm : (c.left.reverse ++ c.right).map (fun t => (t.outputRead,t.work)) =
      (c.left.reverse ++ c.right).map (fun t => (false,t.work)) := by
    apply List.map_congr_left
    intro t ht
    have : t.outputRead = false := hc t (by simpa using ht)
    rw [this]
  simpa [finalCells,workView_append,workView,bare,List.filterMap_append,List.filterMap_map,
    workCells,readAnchor,List.map_map,Function.comp_def] using hm

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

theorem copy_correct_pad (x y : List S) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      ⟨(body A [] x [] y [] (x.length+y.length+n+1)).reverse,.start,[],true,true⟩
      (runSector A (x.map (readAnchor A · true)) (y.map (readAnchor A · true))
        (pad A (initialTape A M (x++y)) (n+1))) := by
  convert copy_correct A M x y n using 1
  all_goals try with_reducible_and_instances rfl
  simp [runSector,initialTape,pad,workCells,filledWork,bare,List.map_map,
      Function.comp_def,List.append_assoc]
  rfl

theorem halt_readout_pad (x y : List S) (c : Tape (S := S) (Γ := Γ) (Q := Q))
    (hc : Halted A M c) (n : ℕ) :
    ReflTransGen (Scan.Step (table A M))
      (runSector A (x.map (readAnchor A · true)) (y.map (readAnchor A · true)) (pad A c (n+1)))
      ⟨[],.scan .readout,finalCells A x y (pad A c (n+1)),true,true⟩ := by
  obtain ⟨t,r,hr,hh⟩ := halt_pad A M hc n
  have he : pad A c (n+1) = ⟨c.state,c.left,t::r⟩ := by
    cases c
    simp only [pad] at hr ⊢
    rw [hr]
  rw [he]
  exact halt_readout A M _ _ _ _ _ _ hh

omit [DecidableEq Γ] in
theorem unread_pad (c : Tape (S := S) (Γ := Γ) (Q := Q)) (n : ℕ)
    (hc : ∀ t ∈ c.left ++ c.right, t.outputRead = false) :
    ∀ t ∈ (pad A c n).left ++ (pad A c n).right, t.outputRead = false := by
  intro t ht
  simp only [pad_left,pad_right,List.mem_append,List.mem_replicate] at ht
  rcases ht with ht | ht | ⟨_,rfl⟩
  · exact hc t (List.mem_append_left _ ht)
  · exact hc t (List.mem_append_right _ ht)
  · rfl

/-- Adequate quota for every genuinely halting, length-bounded output. This
    connects the actual copy/run/readout table, including empty inputs, without
    assuming a bound on the machine's running time or workspace beforehand. -/
theorem simulation_complete (x y out : List S)
    (c : Tape (S := S) (Γ := Γ) (Q := Q))
    (hrun : ReflTransGen (UnboundedStep A M) (initialTape A M (x++y)) c)
    (hhalt : Halted A M c) (hout : Returns A c out)
    (hlen : out.length ≤ x.length+y.length) :
    ∃ s cells', ReflTransGen (Scan.Step (table A M))
      ⟨(body A [] x [] y [] s).reverse,.start,[],true,true⟩
      ⟨cells'.reverse,.ok,[],true,true⟩ ∧
      anchorView cells' = out.map some ++ List.replicate (x.length+y.length-out.length) none := by
  obtain ⟨n,tail,ho⟩ := hout
  obtain ⟨k,hk,hb⟩ := finite_quota A M hrun (n+1)
  cases k with
  | zero => omega
  | succ k =>
    have hi : ∀ t ∈ (initialTape A M (x++y)).left ++ (initialTape A M (x++y)).right,
        t.outputRead = false := by
      intro t ht
      simp only [initialTape,List.nil_append,List.mem_map] at ht
      obtain ⟨a,_,rfl⟩ := ht
      rfl
    have hc := unboundedRun_tags A M (fun t => t.outputRead = false) rfl
      (fun _ _ ht => ht) hrun hi
    have hwork := finalCells_work A x y (pad A c (n+1)) (unread_pad A c (n+1) hc)
    have he : ((pad A c (n+1)).left.reverse ++ (pad A c (n+1)).right).map Tag.work =
        out.map A.input ++ A.blank::(tail ++ [A.blank]) := by
      simpa [pad,List.map_append,List.map_replicate,clean,List.replicate_succ',
        List.append_assoc] using congrArg (· ++ [A.blank]) ho
    rw [he] at hwork
    have ha : anchorView (finalCells A x y (pad A c (n+1))) =
        ([] : List S).map some ++ List.replicate
          (out.length + (x.length+y.length-out.length)) none := by
      have hn : out.length + (x.length+y.length-out.length) = x.length+y.length := by omega
      simpa [hn] using finalCells_anchors A x y (pad A c (n+1))
    obtain ⟨cells',hr,ha'⟩ := readout_complete A M out (finalCells A x y (pad A c (n+1)))
      [] (tail ++ [A.blank]) [] (x.length+y.length-out.length) (by simpa using hwork) ha
    refine ⟨x.length+y.length+k+1,cells',?_,by simpa using ha'⟩
    exact (copy_correct_pad A M x y k).trans
      ((tapeRun_simulates A M _ _ hb).trans ((halt_readout_pad A M x y c hhalt n).trans hr))

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

/-- The first readout-rewind configuration, before any tape cell is moved. -/
def haltSector (x y : Cells S Γ) (c : Tape (S := S) (Γ := Γ) (Q := Q)) :
    Scan.Sector (Head S Q) (Base S) (Tag S Γ) :=
  ⟨workCells c.left ++ bare A .cutC :: x.reverse, .rewind .readout,
    workCells c.right ++ bare A .cutD :: y,true,true⟩

/-- Exact classification of a simulator step made in a workspace run phase.
    The only intermediate phase is the deterministic half of a left move. -/
theorem run_step_cases (x y : Cells S Γ)
    (c : Tape (S := S) (Γ := Γ) (Q := Q))
    {v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (h : Scan.Step (table A M) (runSector A x y c) v) :
    (∃ d, TapeStep M c d ∧ (v = runSector A x y d ∨
      ((∃ q, v.head = .left q) ∧ Scan.Step (table A M) v (runSector A x y d)))) ∨
    (Halted A M c ∧ v = haltSector A x y c) := by
  rcases c with ⟨q,l,r⟩
  cases r with
  | nil => simp [Scan.Step,quota_exhausted] at h
  | cons t r =>
      cases hc : M.transition q t.work with
      | none =>
          right
          constructor
          · exact hc
          · simpa [Scan.Step,Scan.step,table,cell,runSector,workCells,hc,haltSector] using h.symm
      | some d =>
          left
          cases hm : d.move with
          | stay =>
              refine ⟨⟨d.state,l,writeWork t d.write::r⟩,.stay hc hm,Or.inl ?_⟩
              simpa [Scan.Step,Scan.step,table,cell,runSector,workCells,hc,hm,writeWork] using h.symm
          | right =>
              refine ⟨⟨d.state,writeWork t d.write::l,r⟩,.right hc hm,Or.inl ?_⟩
              simpa [Scan.Step,Scan.step,table,cell,runSector,workCells,hc,hm,writeWork] using h.symm
          | left =>
              have hv : v =
                  ⟨workCells l ++ bare A .cutC :: x.reverse, .left d.state,
                    (.workspace,writeWork t d.write) :: (workCells r ++ bare A .cutD :: y),
                    true,true⟩ := by
                simpa [Scan.Step,Scan.step,table,cell,runSector,workCells,hc,hm,writeWork] using h.symm
              subst v
              cases l with
              | nil =>
                  refine ⟨⟨d.state,[],writeWork t d.write::r⟩,.leftEdge hc hm,
                    Or.inr ⟨⟨d.state,rfl⟩,?_⟩⟩
                  simp [Scan.Step,Scan.step,table,cell,runSector,workCells,bare]
              | cons a l =>
                  refine ⟨⟨d.state,l,a::writeWork t d.write::r⟩,.left hc hm,
                    Or.inr ⟨⟨d.state,rfl⟩,?_⟩⟩
                  simp [Scan.Step,Scan.step,table,cell,runSector,workCells]

/-- Arbitrary accepting paths, not just chosen forward simulations, must have
    exited the run phases through a genuine in-bounds machine halt. -/
theorem simulation_halt_sound (x y : Cells S Γ)
    {c : Tape (S := S) (Γ := Γ) (Q := Q)}
    {v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (h : ReflTransGen (Scan.Step (table A M)) (runSector A x y c) v)
    (hv : v.head = .ok) :
    ∃ d, ReflTransGen (TapeStep M) c d ∧ Halted A M d ∧
      ReflTransGen (Scan.Step (table A M)) (haltSector A x y d) v := by
  have hi :
      (∃ d, ReflTransGen (TapeStep M) c d ∧ v = runSector A x y d) ∨
      (∃ d, ReflTransGen (TapeStep M) c d ∧ (∃ q, v.head = .left q) ∧
        Scan.Step (table A M) v (runSector A x y d)) ∨
      (∃ d, ReflTransGen (TapeStep M) c d ∧ Halted A M d ∧
        ReflTransGen (Scan.Step (table A M)) (haltSector A x y d) v) := by
    clear hv
    induction h with
    | refl => exact Or.inl ⟨c,.refl,rfl⟩
    | @tail v w hpre hs ih =>
        rcases ih with ⟨d,hd,rfl⟩ | ⟨d,hd,_,hf⟩ | ⟨d,hd,hh,hr⟩
        · rcases run_step_cases A M x y d hs with ⟨e,hde,he | ⟨hq,he⟩⟩ | ⟨hh,he⟩
          · exact Or.inl ⟨e,hd.tail hde,he⟩
          · exact Or.inr (Or.inl ⟨e,hd.tail hde,hq,he⟩)
          · exact Or.inr (Or.inr ⟨d,hd,hh,he ▸ ReflTransGen.refl⟩)
        · exact Or.inl ⟨d,hd,Scan.deterministic _ hs hf⟩
        · exact Or.inr (Or.inr ⟨d,hd,hh,hr.tail hs⟩)
  rcases hi with ⟨d,_,hd⟩ | ⟨d,_,⟨q,hq⟩,_⟩ | hgood
  · simp [hd,runSector] at hv
  · simp [hq] at hv
  · exact hgood

end

section
open Relation
variable {S Γ Q : Type*}

/-- The literal machine command interpreted on an infinite right-hand tape. -/
def semanticStep (M : Machine Q Γ) (c : SemanticTape Γ Q) : Option (SemanticTape Γ Q) :=
  (M.transition c.state c.right.head).map fun d =>
    match d.move with
    | .stay => ⟨d.state,c.left,Stream'.cons d.write c.right.tail⟩
    | .right => ⟨d.state,d.write::c.left,c.right.tail⟩
    | .left => match c.left with
      | [] => ⟨d.state,[],Stream'.cons d.write c.right.tail⟩
      | a::l => ⟨d.state,l,Stream'.cons a (Stream'.cons d.write c.right.tail)⟩

def SemanticStep (M : Machine Q Γ) (c d : SemanticTape Γ Q) : Prop :=
  semanticStep M c = some d

def interpret (A : Alphabet S Γ) (c : Tape (S := S) (Γ := Γ) (Q := Q)) : SemanticTape Γ Q :=
  ⟨c.state,c.left.map Tag.work,
    Stream'.appendStream' (c.right.map Tag.work) (Stream'.const A.blank)⟩

@[simp] theorem interpret_pad (A : Alphabet S Γ)
    (c : Tape (S := S) (Γ := Γ) (Q := Q)) (n : ℕ) :
    interpret A (pad A c n) = interpret A c := by
  rcases c with ⟨q,l,r⟩
  simp [interpret,pad,List.map_append,List.map_replicate,clean,replicate_append_const]

/-- Each bounded transition is exactly one transition of the semantic machine. -/
theorem tapeStep_interpret (A : Alphabet S Γ) (M : Machine Q Γ)
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : TapeStep M c d) :
    SemanticStep M (interpret A c) (interpret A d) := by
  cases h <;>
    simp_all [SemanticStep,semanticStep,interpret,Stream'.appendStream',writeWork]

/-- Materializing an implicit blank never changes the semantic tape. -/
theorem unboundedStep_interpret (A : Alphabet S Γ) (M : Machine Q Γ)
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : UnboundedStep A M c d) :
    SemanticStep M (interpret A c) (interpret A d) := by
  cases h with
  | within h => exact tapeStep_interpret A M h
  | @extend q l d h =>
      have hi : interpret A (⟨q,l,[clean A.blank]⟩ : Tape (S := S) (Γ := Γ) (Q := Q)) =
          interpret A (⟨q,l,[]⟩ : Tape (S := S) (Γ := Γ) (Q := Q)) := by
        exact interpret_pad A ⟨q,l,[]⟩ 1
      rw [← hi]
      exact tapeStep_interpret A M h

theorem tapeRun_interpret (A : Alphabet S Γ) (M : Machine Q Γ)
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : ReflTransGen (TapeStep M) c d) :
    ReflTransGen (SemanticStep M) (interpret A c) (interpret A d) :=
  h.lift (interpret A) (fun _ _ => tapeStep_interpret A M)

theorem unboundedRun_interpret (A : Alphabet S Γ) (M : Machine Q Γ)
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : ReflTransGen (UnboundedStep A M) c d) :
    ReflTransGen (SemanticStep M) (interpret A c) (interpret A d) :=
  h.lift (interpret A) (fun _ _ => unboundedStep_interpret A M)

theorem semantic_deterministic (M : Machine Q Γ) : Relator.RightUnique (SemanticStep M) := by
  intro a b c hab hac
  exact Option.some.inj (hab.symm.trans hac)

theorem halted_interpret (A : Alphabet S Γ) (M : Machine Q Γ)
    {c : Tape (S := S) (Γ := Γ) (Q := Q)} (h : Halted A M c) :
    Terminal (SemanticStep M) (interpret A c) := by
  intro d hd
  rcases c with ⟨q,l,r⟩
  cases r <;> simp_all [Halted,SemanticStep,semanticStep,interpret,
    Stream'.appendStream',clean,Stream'.head,Stream'.get,Stream'.const,Stream'.cons]

/-- Halts with different finite quotas represent the same semantic output.
    In particular a workspace edge can neither invent a halt nor alter one. -/
theorem halted_quota_unique (A : Alphabet S Γ) (M : Machine Q Γ)
    {start c d : Tape (S := S) (Γ := Γ) (Q := Q)} (n : ℕ)
    (hc : ReflTransGen (TapeStep M) (pad A start n) c)
    (hd : ReflTransGen (UnboundedStep A M) start d)
    (hhc : Halted A M c) (hhd : Halted A M d) : interpret A c = interpret A d := by
  have hci := tapeRun_interpret A M hc
  rw [interpret_pad] at hci
  have hdi := unboundedRun_interpret A M hd
  rcases ReflTransGen.total_of_right_unique (semantic_deterministic M) hci hdi with h | h
  · exact terminal_eq_of_reaches (halted_interpret A M hhc) h
  · exact (terminal_eq_of_reaches (halted_interpret A M hhd) h).symm

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

/-- An accepting terminal cannot be bypassed by any other finite forward path. -/
theorem accepting_after
    {v s w : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (hs : ReflTransGen (Scan.Step (table A M)) v s)
    (hw : ReflTransGen (Scan.Step (table A M)) v w) (hq : w.head = .ok) :
    ReflTransGen (Scan.Step (table A M)) s w := by
  rcases ReflTransGen.total_of_right_unique (Scan.deterministic _) hs hw with h | h
  · exact h
  · have he := terminal_eq_of_reaches (terminal_of_none A M (ok_terminal A M w hq)) h
    exact he ▸ ReflTransGen.refl

/-- Soundness of the output scans, under the literal decoding convention of
    the compiled alphabet. Both the first blank and the anchor quota are forced;
    the result is not an arbitrary truncation of a workspace string. -/
theorem readout_sound
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    (remaining : List Γ) (cells : Cells S Γ) (done : List Γ) (old : List S) (n : ℕ)
    (hw : workView cells = done.map (true,·) ++ remaining.map (false,·))
    (ha : anchorView cells = old.map some ++ List.replicate n none)
    {v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (hv : ReflTransGen (Scan.Step (table A M)) ⟨[],.scan .readout,cells,true,true⟩ v)
    (hq : v.head = .ok) :
    ∃ out tail result, remaining = out.map A.input ++ A.blank::tail ∧ out.length ≤ n ∧
      v = ⟨result.reverse,.ok,[],true,true⟩ ∧
      anchorView result = (old ++ out).map some ++ List.replicate (n-out.length) none := by
  induction remaining generalizing cells done old n with
  | nil =>
      have hr := readout_no_unread A M cells done (by simpa using hw)
      exact False.elim (hr v hv hq)
  | cons g remaining ih =>
      by_cases hg : g = A.blank
      · subst g
        have hr := readout_blank A M cells done (remaining.map (false,·)) (by simpa using hw)
        have he := terminal_eq_of_reaches (terminal_of_none A M
          (ok_terminal A M ⟨cells.reverse,.ok,[],true,true⟩ rfl))
          (accepting_after A M hr hv hq)
        exact ⟨[],remaining,cells,rfl,Nat.zero_le _,he.symm,by simpa using ha⟩
      · cases hg' : A.output g with
        | none =>
            exact False.elim ((readout_invalid A M cells done g (remaining.map (false,·))
              (by simpa using hw) hg hg') v hv hq)
        | some a =>
            cases n with
            | zero =>
                exact False.elim ((readout_no_anchor A M cells done (remaining.map (false,·)) old a g
                  (by simpa using hw) (by simpa using ha) hg hg') v hv hq)
            | succ n =>
                obtain ⟨cells',hr,hw',ha'⟩ := readout_one A M cells done remaining old a g n
                  (by simpa using hw) (by simpa only [List.replicate_succ] using ha) hg hg'
                obtain ⟨out,tail,result,hout,hlen,he,haout⟩ := ih cells' (done ++ [g])
                  (old ++ [a]) n hw' ha' (accepting_after A M hr hv hq)
                refine ⟨a::out,tail,result,?_,by simpa using Nat.succ_le_succ hlen,he,?_⟩
                · simp [hdecode g a hg',hout]
                · simpa [List.append_assoc] using haout

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ)

/-- The whole semantic tape, read in physical order starting at cell zero. -/
def semanticContent (c : SemanticTape Γ Q) : Stream' Γ :=
  Stream'.appendStream' c.left.reverse c.right

/-- Standard literal, first-blank-delimited machine output. -/
def SemanticReturns (c : SemanticTape Γ Q) (w : List S) : Prop :=
  ∃ tail, semanticContent c = Stream'.appendStream' (w.map A.input) (Stream'.cons A.blank tail)

theorem returns_interpret {c : Tape (S := S) (Γ := Γ) (Q := Q)} {w : List S}
    (h : Returns A c w) : SemanticReturns A (interpret A c) w := by
  obtain ⟨n,tail,h⟩ := h
  refine ⟨Stream'.appendStream' tail (Stream'.const A.blank),?_⟩
  have hi := congrArg (fun l => Stream'.appendStream' l (Stream'.const A.blank)) h
  simpa [semanticContent,interpret,List.map_append,List.map_reverse,
    Stream'.append_append_stream,replicate_append_const,Stream'.appendStream'] using hi

theorem input_injective : Function.Injective A.input := by
  intro a b h
  have hi := congrArg A.output h
  simpa only [A.output_input,Option.some.injEq] using hi

/-- The input alphabet excludes the delimiter, so two literal returned prefixes
    of the same infinite tape must be the same list, including empty output. -/
theorem delimited_prefix_unique (x y : List S) (r s : Stream' Γ)
    (h : Stream'.appendStream' (x.map A.input) (Stream'.cons A.blank r) =
      Stream'.appendStream' (y.map A.input) (Stream'.cons A.blank s)) : x = y := by
  induction x generalizing y with
  | nil =>
      cases y with
      | nil => rfl
      | cons b y =>
          have hi := congrArg Stream'.head h
          simp only [List.map_nil,List.map_cons,Stream'.appendStream',Stream'.head_cons] at hi
          exact False.elim (input_ne_blank A b hi.symm)
  | cons a x ih =>
      cases y with
      | nil =>
          have hi := congrArg Stream'.head h
          simp only [List.map_nil,List.map_cons,Stream'.appendStream',Stream'.head_cons] at hi
          exact False.elim (input_ne_blank A a hi)
      | cons b y =>
          have hi := congrArg Stream'.head h
          have ht := congrArg Stream'.tail h
          simp only [List.map_cons,Stream'.appendStream',Stream'.head_cons] at hi
          simp only [List.map_cons,Stream'.appendStream',Stream'.tail_cons] at ht
          exact congrArg₂ List.cons (input_injective A hi) (ih y ht)

theorem semanticReturns_unique {c : SemanticTape Γ Q} {x y : List S}
    (hx : SemanticReturns A c x) (hy : SemanticReturns A c y) : x = y := by
  obtain ⟨r,hr⟩ := hx
  obtain ⟨s,hs⟩ := hy
  exact delimited_prefix_unique A x y r s (hr.symm.trans hs)

/-- The output of any bounded accepting computation agrees with the output of
    a genuine unbounded halt, whenever both are expressed in the literal input
    alphabet. This compares different quotas without comparing their padding. -/
theorem returned_quota_unique (M : Machine Q Γ)
    {start c d : Tape (S := S) (Γ := Γ) (Q := Q)} (n : ℕ)
    (hc : ReflTransGen (TapeStep M) (pad A start n) c)
    (hd : ReflTransGen (UnboundedStep A M) start d)
    (hhc : Halted A M c) (hhd : Halted A M d) {x y : List S}
    (hx : Returns A c x) (hy : Returns A d y) : x = y := by
  have he := halted_quota_unique A M n hc hd hhc hhd
  apply semanticReturns_unique A (returns_interpret A hx)
  rw [he]
  exact returns_interpret A hy

end

section
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

theorem haltSector_readout (x y : List S) (c : Tape (S := S) (Γ := Γ) (Q := Q)) :
    ReflTransGen (Scan.Step (table A M))
      (haltSector A (x.map (readAnchor A · true)) (y.map (readAnchor A · true)) c)
      ⟨[],.scan .readout,finalCells A x y c,true,true⟩ := by
  simpa [haltSector,finalCells,workCells,List.reverse_append,List.reverse_cons,
    List.map_reverse,List.append_assoc] using
    (rewind A M .readout
      (workCells c.left ++ bare A .cutC :: (x.map (readAnchor A · true)).reverse)
      (workCells c.right ++ bare A .cutD :: y.map (readAnchor A · true)) true)

omit [DecidableEq Γ] in
theorem tapeRun_tags (P : Tag S Γ → Prop)
    (hwrite : ∀ t a, P t → P (writeWork t a))
    {c d : Tape (S := S) (Γ := Γ) (Q := Q)} (h : ReflTransGen (TapeStep M) c d)
    (hc : ∀ t ∈ c.left ++ c.right, P t) : ∀ t ∈ d.left ++ d.right, P t := by
  induction h with
  | refl => exact hc
  | tail _ hs ih => exact tapeStep_tags M P hwrite hs ih

/-- Exact soundness from the fresh validated handoff, with a positive spare
    workspace quota. Arbitrary successes are actual halts returning exactly the
    output marks that cleanup will retain. -/
theorem simulation_sound_sufficient
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    (x y : List S) (n : ℕ)
    {v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (hv : ReflTransGen (Scan.Step (table A M))
      ⟨(body A [] x [] y [] (x.length+y.length+n+1)).reverse,.start,[],true,true⟩ v)
    (hq : v.head = .ok) :
    ∃ c out result,
      ReflTransGen (TapeStep M) (pad A (initialTape A M (x++y)) (n+1)) c ∧
      Halted A M c ∧ Returns A c out ∧ out.length ≤ x.length+y.length ∧
      v = ⟨result.reverse,.ok,[],true,true⟩ ∧
      anchorView result = out.map some ++ List.replicate (x.length+y.length-out.length) none := by
  have hrun := accepting_after A M (copy_correct_pad A M x y n) hv hq
  obtain ⟨c,hc,hh,hr⟩ := simulation_halt_sound A M _ _ hrun hq
  have hi : ∀ t ∈ (initialTape A M (x++y)).left ++ (initialTape A M (x++y)).right,
      t.outputRead = false := by
    intro t ht
    simp only [initialTape,List.nil_append,List.mem_map] at ht
    obtain ⟨a,_,rfl⟩ := ht
    rfl
  have hunread := tapeRun_tags M (fun t => t.outputRead = false) (fun _ _ ht => ht)
    hc (unread_pad A _ (n+1) hi)
  have hr' := accepting_after A M (haltSector_readout A M x y c) hr hq
  obtain ⟨out,tail,result,hout,hlen,he,ha⟩ := readout_sound A M hdecode
    ((c.left.reverse ++ c.right).map Tag.work) (finalCells A x y c) [] []
    (x.length+y.length) (by simpa using finalCells_work A x y c hunread)
    (by simpa using finalCells_anchors A x y c) hr' hq
  exact ⟨c,out,result,hc,hh,⟨0,tail,by simpa using hout⟩,hlen,he,by simpa using ha⟩

end

open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ) (M : Machine Q Γ) [DecidableEq Γ]

@[simp] theorem pass_fill_bareD (a : S) : Pass A M (.fill a) (bare A .cutD) := by rfl
@[simp] theorem pass_spare_D : Pass A M .spare (bare A .cutD) := by rfl

theorem scan_exhausted (s : Resume S) (cells : Cells S Γ)
    (hp : ∀ c ∈ cells, Pass A M s c) (hb : (table A M).boundary (.scan s) = none) :
    Rejects A M ⟨[],.scan s,cells,true,true⟩ := by
  have hr := Scan.cross_right (table A M) (.scan s) rfl cells [] [] true true hp
  simp only [List.append_nil] at hr
  exact rejects_of_stuck A M hr (by
    change ((table A M).boundary (.scan s)).map _ = none
    rw [hb]; rfl) (by simp)

theorem fill_no_space (xp xs yp ys w : List S) (a : S) :
    Rejects A M ⟨[],.scan (.fill a),body A xp xs yp ys w 0,true,true⟩ := by
  apply scan_exhausted A M _ _ _ rfl
  simp only [body,List.replicate_zero,List.append_nil,List.forall_mem_append,
    List.forall_mem_map,List.forall_mem_singleton]
  simp

/-- Zero spare workspace is a genuine rejection even for empty input. -/
theorem copy_no_space (xp xs yp ys w : List S) :
    Rejects A M ⟨[],.scan .input,body A xp xs yp ys w 0,true,true⟩ := by
  cases xs with
  | cons a xs =>
      let p := xp.map (readAnchor A · true)
      let r := xs.map (readAnchor A · false) ++ [bare A .cutC] ++ w.map (filledWork A) ++
        [bare A .cutD] ++ yp.map (readAnchor A · true) ++ ys.map (readAnchor A · false)
      have h₁ := scan_update A M .input (.fill a) p r (.anchor a)
        (readAnchor A a false).2 (readAnchor A a true).2
        (by change ∀ c ∈ p, Pass A M .input c; simp [p]) (by rfl)
      have hr : ReflTransGen (Scan.Step (table A M))
          ⟨[],.scan .input,body A xp (a::xs) yp ys w 0,true,true⟩
          ⟨[],.scan (.fill a),body A (xp++[a]) xs yp ys w 0,true,true⟩ := by
        simpa [body,p,r,readAnchor,List.append_assoc] using h₁
      exact rejects_before A M hr (fill_no_space A M _ _ _ _ _ a)
  | nil =>
      cases ys with
      | cons a ys =>
          let p := xp.map (readAnchor A · true) ++ [bare A .cutC] ++ w.map (filledWork A) ++
            [bare A .cutD] ++ yp.map (readAnchor A · true)
          let r := ys.map (readAnchor A · false)
          have h₁ := scan_update A M .input (.fill a) p r (.anchor a)
            (readAnchor A a false).2 (readAnchor A a true).2
            (by
              change ∀ c ∈ p, Pass A M .input c
              simp only [p,List.forall_mem_append,List.forall_mem_map,List.forall_mem_singleton]
              simp) (by rfl)
          have hr : ReflTransGen (Scan.Step (table A M))
              ⟨[],.scan .input,body A xp [] yp (a::ys) w 0,true,true⟩
              ⟨[],.scan (.fill a),body A xp [] (yp++[a]) ys w 0,true,true⟩ := by
            simpa [body,p,r,readAnchor,List.append_assoc] using h₁
          exact rejects_before A M hr (fill_no_space A M _ _ _ _ _ a)
      | nil =>
          let cells := body A xp [] yp [] w 0
          have hp : ∀ c ∈ cells, Pass A M .input c := by
            simp only [cells,body,List.map_nil,List.replicate_zero,List.append_nil,
              List.forall_mem_append,List.forall_mem_map,List.forall_mem_singleton]
            simp
          have h₀ := Scan.cross_right (table A M) (.scan .input) rfl cells [] [] true true hp
          have h₁ : Scan.Step (table A M) ⟨cells.reverse,.scan .input,[],true,true⟩
              ⟨cells.reverse,.rewind .spare,[],true,true⟩ := by
            simp [Scan.Step,Scan.step,table]
          have h₂ := rewind A M .spare cells.reverse [] true
          simp only [List.reverse_reverse,List.append_nil] at h₀ h₂
          apply rejects_before A M (h₀.trans ((ReflTransGen.single h₁).trans h₂))
          apply scan_exhausted A M _ _ _ rfl
          simp only [cells,body,List.map_nil,List.replicate_zero,List.append_nil,
            List.forall_mem_append,List.forall_mem_map,List.forall_mem_singleton]
          simp

/-- A quota no larger than the unread input rejects: there must be space for
    every copied letter and also the spare blank tested before running. -/
theorem copy_insufficient (xp xs yp ys w : List S) (n : ℕ)
    (hn : n ≤ xs.length+ys.length) :
    Rejects A M ⟨[],.scan .input,body A xp xs yp ys w n,true,true⟩ := by
  induction n generalizing xp xs yp ys w with
  | zero => exact copy_no_space A M xp xs yp ys w
  | succ n ih =>
      cases xs with
      | cons a xs =>
          apply rejects_before A M (copy_left_one A M xp xs yp ys w a n)
          exact ih _ _ _ _ _ (by simp only [List.length_cons] at hn ⊢; omega)
      | nil =>
          cases ys with
          | nil => simp at hn
          | cons a ys =>
              apply rejects_before A M (copy_right_one A M xp yp ys w a n)
              exact ih _ _ _ _ _ (by simp only [List.length_cons, List.length_nil] at hn ⊢; omega)

/-- Insufficient quota cannot give an accepting computation from a clean
    post-validator handoff, including the zero-workspace and empty-input cases. -/
theorem simulation_insufficient (x y : List S) (s : ℕ) (hs : s ≤ x.length+y.length) :
    Rejects A M ⟨(body A [] x [] y [] s).reverse,.start,[],true,true⟩ :=
  rejects_before A M (start_copy A M _) (copy_insufficient A M [] x [] y [] s hs)

/-- Soundness for *every* clean quota, without a promise that enough was
    inserted. All accepting paths return the genuine first-blank-delimited
    machine output, in input order and within the anchor length bound. -/
theorem simulation_sound
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    (x y : List S) (s : ℕ)
    {v : Scan.Sector (Head S Q) (Base S) (Tag S Γ)}
    (hv : ReflTransGen (Scan.Step (table A M))
      ⟨(body A [] x [] y [] s).reverse,.start,[],true,true⟩ v)
    (hq : v.head = .ok) :
    ∃ n c out result, s = x.length+y.length+n+1 ∧
      ReflTransGen (TapeStep M) (pad A (initialTape A M (x++y)) (n+1)) c ∧
      Halted A M c ∧ Returns A c out ∧ out.length ≤ x.length+y.length ∧
      v = ⟨result.reverse,.ok,[],true,true⟩ ∧
      anchorView result = out.map some ++ List.replicate (x.length+y.length-out.length) none := by
  by_cases hs : s ≤ x.length+y.length
  · exact False.elim (simulation_insufficient A M x y s hs v hv hq)
  · let n := s - (x.length+y.length+1)
    have he : s = x.length+y.length+n+1 := by dsimp [n]; omega
    rw [he] at hv
    obtain ⟨c,out,result,h⟩ := simulation_sound_sufficient A M hdecode x y n hv hq
    exact ⟨n,c,out,result,he,h⟩

end FiniteAlgebraicEnvelopes.Compiler.Simulator

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Control
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableInstruction _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite control and bounded compiler orbit normalization.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Cleanup
open Relation
variable {S Γ : Type*}

abbrev Sector (S Γ : Type*) := Scan.Sector Head (Base S) (Tag S Γ)

/-- Exactly the cleanup letter prescribed in the finite compiler. Output marks
    on nonanchors are deliberately ignored even on dirty configurations. -/
def emit (c : Base S × Tag S Γ) : Option S :=
  match c.1 with
  | .anchor _ => c.2.output
  | _ => none

def letter (blank : Γ) (a : S) : Base S × Tag S Γ := (.anchor a,clean blank)

def output (blank : Γ) (l : List (Base S × Tag S Γ)) : List (Base S × Tag S Γ) :=
  (l.filterMap emit).map (letter blank)

/-- The left sweep deletes every consumed tagged cell, and only marks on
    anchors produce a clean right-hand anchor. The boundary test is literal. -/
def step (blank : Γ) (v : Sector S Γ) : Option (Sector S Γ) :=
  match v.head with
  | .raw => none
  | .cleanup => match v.left with
    | c::l => some { v with left := l, right := (emit c).toList.map (letter blank) ++ v.right }
    | [] => if v.leftBoundary then some {v with head := .raw} else none

def Step (blank : Γ) (v w : Sector S Γ) : Prop := step blank v = some w

theorem deterministic (blank : Γ) : Relator.RightUnique (Step (S := S) blank) := by
  intro a b c hab hac
  exact Option.some.inj (hab.symm.trans hac)

@[simp] theorem output_nil (blank : Γ) : output (S := S) blank [] = [] := rfl

@[simp] theorem output_append (blank : Γ) (l r : List (Base S × Tag S Γ)) :
    output blank (l++r) = output blank l ++ output blank r := by
  simp [output,List.filterMap_append]

@[simp] theorem output_singleton (blank : Γ) (c : Base S × Tag S Γ) :
    output blank [c] = (emit c).toList.map (letter blank) := by
  cases h : emit c <;> simp [output,h]

/-- Each consumed cell is emitted before all previously emitted cells. This
    proves the leftward cleanup's order on arbitrary—not only clean—data. -/
theorem sweep (blank : Γ) (l r : List (Base S × Tag S Γ)) (a b : Bool) :
    ReflTransGen (Step blank) ⟨l,.cleanup,r,a,b⟩
      ⟨[],.cleanup,output blank l.reverse ++ r,a,b⟩ := by
  induction l generalizing r with
  | nil => exact .refl
  | cons c l ih =>
      have h : Step blank ⟨c::l,.cleanup,r,a,b⟩
          ⟨l,.cleanup,(emit c).toList.map (letter blank) ++ r,a,b⟩ := rfl
      simpa [List.reverse_cons,List.append_assoc] using
        (ReflTransGen.single h).trans (ih ((emit c).toList.map (letter blank) ++ r))

/-- Normalization of a cleanup head, with or without a left boundary. -/
def normal (blank : Γ) (v : Sector S Γ) : Sector S Γ :=
  match v.head with
  | .raw => v
  | .cleanup => ⟨[],if v.leftBoundary then .raw else .cleanup,
      output blank v.left.reverse ++ v.right,v.leftBoundary,v.rightBoundary⟩

theorem normal_reached (blank : Γ) (v : Sector S Γ) :
    ReflTransGen (Step blank) v (normal blank v) := by
  rcases v with ⟨l,h,r,a,b⟩
  cases h with
  | raw => exact .refl
  | cleanup =>
      have hr := sweep blank l r a b
      cases a with
      | false => exact hr
      | true => exact hr.tail rfl

theorem normal_terminal (blank : Γ) (v : Sector S Γ) :
    step blank (normal blank v) = none := by
  rcases v with ⟨l,h,r,a,b⟩
  cases h <;> cases a <;> rfl

/-- Cleanup normal forms are invariant under either direction of any local
    cleanup equation, including in dirty sectors with missing boundaries. -/
theorem normal_invariant (blank : Γ) {v w : Sector S Γ}
    (h : EqvGen (Step blank) v w) : normal blank v = normal blank w := by
  have tv : ∀ z, ¬Step blank (normal blank v) z := by
    intro z hz
    change step blank (normal blank v) = some z at hz
    rw [normal_terminal] at hz
    cases hz
  have tw : ∀ z, ¬Step blank (normal blank w) z := by
    intro z hz
    change step blank (normal blank w) = some z at hz
    rw [normal_terminal] at hz
    cases hz
  apply terminal_unique (deterministic blank) tv tw
  exact EqvGen.trans _ _ _
    (EqvGen.symm _ _ (EqvGen.reflTransGen_le_eqvGen _ _ _ (normal_reached blank v)))
    (EqvGen.trans _ _ _ h (EqvGen.reflTransGen_le_eqvGen _ _ _ (normal_reached blank w)))

/-- Cleanup forgets empty marks, not anchor order. -/
theorem emit_anchorView (l : List (Base S × Tag S Γ)) :
    l.filterMap emit = (Simulator.anchorView l).filterMap id := by
  rw [Simulator.anchorView,List.filterMap_filterMap]
  congr 1
  funext c
  rcases c with ⟨b,t⟩
  cases b <;> rfl

theorem emit_returned (l : List (Base S × Tag S Γ)) (out : List S) (n : ℕ)
    (h : Simulator.anchorView l = out.map some ++ List.replicate n none) :
    l.filterMap emit = out := by
  rw [emit_anchorView,h,List.filterMap_append]
  simp

/-- Exact successful cleanup, including empty returned strings. -/
theorem success (blank : Γ) (l : List (Base S × Tag S Γ)) (out : List S) (n : ℕ)
    (h : Simulator.anchorView l = out.map some ++ List.replicate n none) :
    ReflTransGen (Step blank) ⟨l.reverse,.cleanup,[],true,true⟩
      ⟨[],.raw,out.map (letter blank),true,true⟩ := by
  have hr := normal_reached blank (⟨l.reverse,.cleanup,[],true,true⟩ : Sector S Γ)
  simpa [normal,output,emit_returned l out n h] using hr

def grade : Base S → ℕ
  | .cutC => 2
  | .workspace => 0
  | _ => 1

def cellsGrade (l : List (Base S × Tag S Γ)) : ℕ := (l.map (grade ∘ Prod.fst)).sum

@[simp] theorem cellsGrade_append (l r : List (Base S × Tag S Γ)) :
    cellsGrade (l++r) = cellsGrade l + cellsGrade r := by simp [cellsGrade]

@[simp] theorem cellsGrade_reverse (l : List (Base S × Tag S Γ)) :
    cellsGrade l.reverse = cellsGrade l := by simp [cellsGrade,List.map_reverse]

/-- Grade is nonincreasing for EVERY tagged cleanup cell. Workspace marks do
    not emit letters, so grade-zero workspace can never create positive grade. -/
theorem output_grade_le (blank : Γ) (l : List (Base S × Tag S Γ)) :
    cellsGrade (output blank l) ≤ cellsGrade l := by
  induction l with
  | nil => simp [cellsGrade]
  | cons c l ih =>
      rcases c with ⟨b,t⟩
      cases b <;> simp only [output,List.filterMap_cons,emit]
      · cases t.output <;> simp_all [output,cellsGrade,letter,grade]
        omega
      all_goals simp_all [output,cellsGrade,grade]
      all_goals omega

end FiniteAlgebraicEnvelopes.Compiler.Cleanup

namespace FiniteAlgebraicEnvelopes.Compiler.Compiled

section
open Relation
variable {S Γ Q : Type*}
abbrev MachineSector (S Γ Q : Type*) := Scan.Sector (Simulator.Head S Q) (Base S) (Tag S Γ)
abbrev Cfg (S Γ Q : Type*) := Validator.Extended.Cfg S Γ (MachineSector S Γ Q)

/-- The fresh handoff is one state, not two copies joined by an artificial edge. -/
def embed (v : MachineSector S Γ Q) : Cfg S Γ Q :=
  match v.head with
  | .start => .inl ⟨.start,v.left,v.right,v.leftBoundary,v.rightBoundary⟩
  | _ => .inr v

def project : Cfg S Γ Q → MachineSector S Γ Q
  | .inl v => ⟨v.left,.start,v.right,v.leftBoundary,v.rightBoundary⟩
  | .inr v => v

@[simp] theorem project_embed (v : MachineSector S Γ Q) : project (embed v) = v := by
  rcases v with ⟨l,q,r,a,b⟩
  cases q <;> rfl

theorem embed_injective : Function.Injective (@embed S Γ Q) := by
  intro a b h
  simpa only [project_embed] using congrArg project h

@[simp] theorem embed_active (v : MachineSector S Γ Q) : Validator.Extended.Active (embed v) := by
  unfold embed
  split <;> trivial

@[simp] theorem embed_project {v : Cfg S Γ Q} (hv : Validator.Extended.Active v)
    (hc : ∀ u, v = .inr u → u.head ≠ .start) : embed (project v) = v := by
  cases v with
  | inl v => simp only [Validator.Extended.Active] at hv; cases v; cases hv; rfl
  | inr v =>
      have h := hc v rfl
      simp only [project,embed]

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ) [DecidableEq Γ]

def MachineRel (a b : Cfg S Γ Q) : Prop :=
  ∃ u v, a = embed u ∧ b = embed v ∧ Scan.Step (Simulator.table A M) u v

def Step : Cfg S Γ Q → Cfg S Γ Q → Prop :=
  Validator.Extended.Step A.blank (MachineRel A M)

theorem machine_deterministic : Relator.RightUnique (MachineRel A M) := by
  rintro a b c ⟨u,v,rfl,rfl,h⟩ ⟨u',v',he,rfl,h'⟩
  cases embed_injective he
  exact congrArg embed (Scan.deterministic _ h h')

theorem deterministic : Relator.RightUnique (Step A M) :=
  Validator.Extended.deterministic A.blank (machine_deterministic A M)

abbrev bases : Cfg S Γ Q → List (Base S) × Bool × Bool :=
  Validator.Extended.baseSkeleton Scan.baseSkeleton

omit [DecidableEq Γ] in
@[simp] theorem embed_bases (v : MachineSector S Γ Q) : bases (embed v) = Scan.baseSkeleton v := by
  unfold embed
  split <;> rfl

theorem machine_bases (a b : Cfg S Γ Q) (h : MachineRel A M a b) : bases a = bases b := by
  obtain ⟨u,v,rfl,rfl,h⟩ := h
  simpa only [embed_bases] using Scan.step_skeleton _ h

/-- The manuscript's uniqueness of entries, now for the concrete copy/run/read
    table, not for an unspecified simulated relation. -/
theorem entries_unique {a b : Validator.Sector S Γ}
    (ha : Validator.Entry A.blank a) (hb : Validator.Entry A.blank b)
    (h : EqvGen (Step A M) (.inl a) (.inl b)) : a = b :=
  Validator.Extended.entries_unique A.blank Scan.baseSkeleton
    (machine_deterministic A M) (machine_bases A M) ha hb h

theorem embed_step {u v : MachineSector S Γ Q}
    (h : Scan.Step (Simulator.table A M) u v) : Step A M (embed u) (embed v) :=
  .machine (embed_active u) (embed_active v) ⟨u,v,rfl,rfl,h⟩

theorem embed_run {u v : MachineSector S Γ Q}
    (h : ReflTransGen (Scan.Step (Simulator.table A M)) u v) :
    ReflTransGen (Step A M) (embed u) (embed v) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (embed_step A M hs)

theorem validator_run {u v : Validator.Sector S Γ}
    (h : ReflTransGen (Validator.Step A.blank) u v) :
    ReflTransGen (Step A M) (.inl u) (.inl v) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (.validator hs)

theorem active_step {a b : Cfg S Γ Q} (ha : Validator.Extended.Active a)
    (h : Step A M a b) : MachineRel A M a b := by
  cases h with
  | validator h => exact False.elim (Validator.Extended.validator_not_start A.blank h ha)
  | machine _ _ h => exact h

/-- A path retains its actual simulator suffix after the unique validation
    handoff. This rules out a dirty intermediate state being treated as input. -/
theorem path_decomposition {a : Validator.Sector S Γ} {b : Cfg S Γ Q}
    (h : ReflTransGen (Step A M) (.inl a) b) :
    (∃ v, b = .inl v ∧ ReflTransGen (Validator.Step A.blank) a v) ∨
    ∃ v u, ReflTransGen (Validator.Step A.blank) a v ∧ v.head = .start ∧
      b = embed u ∧ ReflTransGen (Scan.Step (Simulator.table A M)) (project (.inl v)) u := by
  induction h with
  | refl => exact Or.inl ⟨a,rfl,.refl⟩
  | @tail b c _ hs ih =>
      rcases ih with ⟨v,rfl,hv⟩ | ⟨v,u,hv,hq,rfl,hr⟩
      · cases hs with
        | validator hs => exact Or.inl ⟨_,rfl,hv.tail hs⟩
        | machine ha _ hs =>
            obtain ⟨u,w,hu,rfl,hw⟩ := hs
            have he : project (.inl v) = u := by rw [hu,project_embed]
            exact Or.inr ⟨v,w,hv,ha,rfl,by rw [he]; exact .single hw⟩
      · obtain ⟨u',w,he,rfl,hw⟩ := active_step A M (embed_active u) hs
        cases embed_injective he
        exact Or.inr ⟨v,w,hv,hq,rfl,hr.tail hw⟩

theorem ok_terminal {v : MachineSector S Γ Q} (hv : v.head = .ok) :
    Terminal (Step A M) (embed v) := by
  intro u h
  have he : embed v = .inr v := by simp [embed,hv]
  rw [he] at h
  cases h with
  | machine _ _ h =>
      obtain ⟨v',w,hv',_,h⟩ := h
      have hsame : v = v' := embed_injective (he.trans hv')
      subst v'
      rw [Scan.Step,Simulator.ok_terminal A M v hv] at h
      contradiction

/-- Arbitrary dirty accepting sectors are unique within a weak component. -/
theorem ok_unique {u v : MachineSector S Γ Q} (hu : u.head = .ok) (hv : v.head = .ok)
    (h : EqvGen (Step A M) (embed u) (embed v)) : u = v :=
  embed_injective (terminal_unique (deterministic A M) (ok_terminal A M hu) (ok_terminal A M hv) h)

end

open Relation
variable {S Γ Q : Type*}

/-- The literal entry and handoff of compiler-clean-entry. -/
def cleanEntry (blank : Γ) (x y : List S) (s : ℕ) : Validator.Sector S Γ :=
  ⟨.initial,List.replicate s (Validator.cell blank .workspace) ++
    Validator.cell blank .cutC :: (x.map (fun a => Validator.cell blank (.anchor a))).reverse,
    Validator.cell blank .cutD :: y.map (fun a => Validator.cell blank (.anchor a)),true,true⟩

def handoff (blank : Γ) (x y : List S) (s : ℕ) : Validator.Sector S Γ :=
  ⟨.start,(y.map (fun a => Validator.cell blank (.anchor a))).reverse ++
    Validator.cell blank .cutD :: (List.replicate s (Validator.cell blank .workspace) ++
    Validator.cell blank .cutC :: (x.map (fun a => Validator.cell blank (.anchor a))).reverse),
    [],true,true⟩

@[simp] theorem cleanEntry_entry (blank : Γ) (x y : List S) (s : ℕ) :
    Validator.Entry blank (cleanEntry blank x y s) := ⟨rfl,_,rfl⟩

theorem cleanEntry_reaches (blank : Γ) (x y : List S) (s : ℕ) :
    ReflTransGen (Validator.Step blank) (cleanEntry blank x y s) (handoff blank x y s) :=
  Validator.clean_entry_reaches blank x y s

theorem validator_start_terminal (blank : Γ) {v : Validator.Sector S Γ}
    (hv : v.head = .start) : Terminal (Validator.Step blank) v := by
  intro w h
  exact Validator.Extended.validator_not_start blank h hv

theorem handoff_unique (blank : Γ) (x y : List S) (s : ℕ) {v : Validator.Sector S Γ}
    (h : ReflTransGen (Validator.Step blank) (cleanEntry blank x y s) v)
    (hv : v.head = .start) : v = handoff blank x y s := by
  apply terminal_unique (Validator.step_deterministic blank)
    (validator_start_terminal blank hv) (validator_start_terminal blank rfl)
  exact EqvGen.trans _ _ _
    (EqvGen.symm _ _ (EqvGen.reflTransGen_le_eqvGen _ _ _ h))
    (EqvGen.reflTransGen_le_eqvGen _ _ _ (cleanEntry_reaches blank x y s))

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ) [DecidableEq Γ]

omit [DecidableEq Γ] in
@[simp] theorem project_handoff (x y : List S) (s : ℕ) :
    (project (.inl (handoff A.blank x y s)) : MachineSector S Γ Q) =
      ⟨(Simulator.body A [] x [] y [] s).reverse,.start,[],true,true⟩ := by
  simp [project,handoff,Simulator.body,Simulator.readAnchor,Simulator.bare,Validator.cell,
    clean,List.append_assoc]

/-- Clean entries that meet an accepting internal sector really passed the
    validator and then ran this very machine. No cleanliness is assumed of the
    sector used for finding its weak component. -/
theorem accepting_entry_runs {a : Validator.Sector S Γ} {b : MachineSector S Γ Q}
    (ha : Validator.Entry A.blank a) (hb : b.head = .ok)
    (h : EqvGen (Step A M) (.inl a) (embed b)) :
    ∃ x y s, a = cleanEntry A.blank x y s ∧
      ReflTransGen (Scan.Step (Simulator.table A M))
        ⟨(Simulator.body A [] x [] y [] s).reverse,.start,[],true,true⟩ b := by
  have hr := reaches_terminal (deterministic A M) (ok_terminal A M hb) h
  rcases path_decomposition A M hr with ⟨v,hv,_⟩ | ⟨v,u,hv,hq,hu,hr⟩
  · simp [embed,hb] at hv
  · have hub : b = u := embed_injective hu
    subst u
    obtain ⟨x,y,s,he⟩ := Validator.passing_entry A.blank ha hv hq
    change a = cleanEntry A.blank x y s at he
    subst a
    have he := handoff_unique A.blank x y s hv hq
    subst v
    exact ⟨x,y,s,rfl,by simpa only [project_handoff] using hr⟩

/-- Concrete soundness part of Lemma compiler-components: true halted output,
    the exact length bound, AND the mandated literal cleanup word. Quota
    insufficiency is ruled out by the previously proved rejection theorem. -/
theorem accepting_entry_sound
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {a : Validator.Sector S Γ} {b : MachineSector S Γ Q}
    (ha : Validator.Entry A.blank a) (hb : b.head = .ok)
    (h : EqvGen (Step A M) (.inl a) (embed b)) :
    ∃ x y s n c out, ∃ (result : List (Base S × Tag S Γ)),
      a = cleanEntry A.blank x y s ∧ s = x.length+y.length+n+1 ∧
      ReflTransGen (Simulator.TapeStep M)
        (Simulator.pad A (Simulator.initialTape A M (x++y)) (n+1)) c ∧
      Simulator.Halted A M c ∧ Simulator.Returns A c out ∧
      out.length ≤ x.length+y.length ∧ b = ⟨result.reverse,.ok,[],true,true⟩ ∧
      ReflTransGen (Cleanup.Step A.blank) ⟨result.reverse,.cleanup,[],true,true⟩
        ⟨[],.raw,out.map (Cleanup.letter A.blank),true,true⟩ := by
  obtain ⟨x,y,s,he,hr⟩ := accepting_entry_runs A M ha hb h
  obtain ⟨n,c,out,result,hs,hc,hhalt,hout,hlen,hb,hres⟩ :=
    Simulator.simulation_sound A M hdecode x y s hr hb
  exact ⟨x,y,s,n,c,out,result,he,hs,hc,hhalt,hout,hlen,hb,
    Cleanup.success A.blank result out _ hres⟩

/-- Conversely an actual finite halted computation with the required output
    bound has some quota and gives entry-to-ok reachability and exact cleanup. -/
theorem clean_success (x y out : List S)
    (c : Simulator.Tape (S := S) (Γ := Γ) (Q := Q))
    (hrun : ReflTransGen (Simulator.UnboundedStep A M) (Simulator.initialTape A M (x++y)) c)
    (hhalt : Simulator.Halted A M c) (hout : Simulator.Returns A c out)
    (hlen : out.length ≤ x.length+y.length) :
    ∃ s, ∃ (result : List (Base S × Tag S Γ)), ReflTransGen (Step A M) (.inl (cleanEntry A.blank x y s))
      (embed ⟨result.reverse,.ok,[],true,true⟩) ∧
      ReflTransGen (Cleanup.Step A.blank) ⟨result.reverse,.cleanup,[],true,true⟩
        ⟨[],.raw,out.map (Cleanup.letter A.blank),true,true⟩ := by
  obtain ⟨s,result,hr,hres⟩ := Simulator.simulation_complete A M x y out c hrun hhalt hout hlen
  refine ⟨s,result,?_,Cleanup.success A.blank result out _ hres⟩
  have hv := validator_run A M (cleanEntry_reaches A.blank x y s)
  have he : (.inl (handoff A.blank x y s) : Cfg S Γ Q) =
      embed ⟨(Simulator.body A [] x [] y [] s).reverse,.start,[],true,true⟩ := by
    rw [← project_handoff]
    rfl
  rw [he] at hv
  exact hv.trans (embed_run A M hr)

end FiniteAlgebraicEnvelopes.Compiler.Compiled

namespace FiniteAlgebraicEnvelopes.Compiler.Validator
variable {S Γ : Type*}

def toScan (v : Sector S Γ) : Scan.Sector Head (Base S) (Tag S Γ) :=
  ⟨v.left,v.head,v.right,v.leftBoundary,v.rightBoundary⟩

def ofScan (v : Scan.Sector Head (Base S) (Tag S Γ)) : Sector S Γ :=
  ⟨v.head,v.left,v.right,v.leftBoundary,v.rightBoundary⟩

@[simp] theorem toScan_ofScan (v : Scan.Sector Head (Base S) (Tag S Γ)) :
    toScan (ofScan v) = v := rfl
@[simp] theorem ofScan_toScan (v : Sector S Γ) : ofScan (toScan v) = v := rfl

variable (blank : Γ) [DecidableEq S] [DecidableEq Γ]

/-- The displayed validator equations as an executable finite scan table. -/
def table : Table Head (Base S) (Tag S Γ) where
  direction
    | .initial | .left => .left
    | _ => .right
  cell q b t := if t = clean blank then
    match q,b with
    | .initial,.workspace => some ⟨.initial,t,true⟩
    | .initial,.cutC => some ⟨.left,t,true⟩
    | .left,.anchor _ => some ⟨.left,t,true⟩
    | .right,.anchor _ => some ⟨.right,t,true⟩
    | .right,.cutC => some ⟨.workspace,t,true⟩
    | .workspace,.workspace => some ⟨.workspace,t,true⟩
    | .workspace,.cutD => some ⟨.suffix,t,true⟩
    | .suffix,.anchor _ => some ⟨.suffix,t,true⟩
    | _,_ => none
    else none
  boundary
    | .left => some .right
    | .suffix => some .start
    | _ => none

theorem step_toScan {v w : Sector S Γ} (h : Step blank v w) :
    Scan.Step (table blank) (toScan v) (toScan w) := by
  cases h <;> simp [Scan.Step,Scan.step,toScan,table,cell]

theorem step_ofScan {v w : Scan.Sector Head (Base S) (Tag S Γ)}
    (h : Scan.Step (table blank) v w) : Step blank (ofScan v) (ofScan w) := by
  rcases v with ⟨l,q,r,a,b⟩
  cases q with
  | initial =>
      cases l with
      | nil => cases a <;> simp [Scan.Step,Scan.step,table] at h
      | cons c l =>
          rcases c with ⟨base,t⟩
          by_cases ht : t = clean blank
          · subst t
            cases base <;> simp [Scan.Step,Scan.step,table] at h
            all_goals subst w; first | exact .initial_cut _ _ _ _ | exact .initial_workspace _ _ _ _
          · simp [Scan.Step,Scan.step,table,ht] at h
  | left =>
      cases l with
      | nil =>
          cases a <;> simp [Scan.Step,Scan.step,table] at h
          subst w; exact .left_boundary _ _
      | cons c l =>
          rcases c with ⟨base,t⟩
          by_cases ht : t = clean blank
          · subst t
            cases base <;> simp [Scan.Step,Scan.step,table] at h
            subst w; exact .left_anchor _ _ _ _ _
          · simp [Scan.Step,Scan.step,table,ht] at h
  | right =>
      cases r with
      | nil => cases b <;> simp [Scan.Step,Scan.step,table] at h
      | cons c r =>
          rcases c with ⟨base,t⟩
          by_cases ht : t = clean blank
          · subst t
            cases base <;> simp [Scan.Step,Scan.step,table] at h
            all_goals subst w; first | exact .right_anchor _ _ _ _ _ | exact .right_cut _ _ _ _
          · simp [Scan.Step,Scan.step,table,ht] at h
  | workspace =>
      cases r with
      | nil => cases b <;> simp [Scan.Step,Scan.step,table] at h
      | cons c r =>
          rcases c with ⟨base,t⟩
          by_cases ht : t = clean blank
          · subst t
            cases base <;> simp [Scan.Step,Scan.step,table] at h
            all_goals subst w; first | exact .workspace _ _ _ _ | exact .workspace_cut _ _ _ _
          · simp [Scan.Step,Scan.step,table,ht] at h
  | suffix =>
      cases r with
      | nil =>
          cases b <;> simp [Scan.Step,Scan.step,table] at h
          subst w; exact .suffix_boundary _ _
      | cons c r =>
          rcases c with ⟨base,t⟩
          by_cases ht : t = clean blank
          · subst t
            cases base <;> simp [Scan.Step,Scan.step,table] at h
            subst w; exact .suffix_anchor _ _ _ _ _
          · simp [Scan.Step,Scan.step,table,ht] at h
  | start =>
      cases r with
      | nil => cases b <;> simp [Scan.Step,Scan.step,table] at h
      | cons c r =>
          rcases c with ⟨base,t⟩
          by_cases ht : t = clean blank <;> simp [Scan.Step,Scan.step,table,ht] at h

@[simp] theorem step_iff_scan (v w : Sector S Γ) :
    Step blank v w ↔ Scan.Step (table blank) (toScan v) (toScan w) :=
  ⟨step_toScan blank,step_ofScan blank⟩

end FiniteAlgebraicEnvelopes.Compiler.Validator

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
variable {H H' B T : Type*}

def mapHead (f : H → H') (v : Sector H B T) : Sector H' B T :=
  ⟨v.left,f v.head,v.right,v.leftBoundary,v.rightBoundary⟩

@[simp] theorem skeleton_mapHead (f : H → H') (v : Sector H B T) :
    baseSkeleton (mapHead f v) = baseSkeleton v := rfl

/-- A literal relabeling of finite control commutes with one scan step. Only
    agreement at the current head is needed, permitting fused control tables. -/
theorem step_mapHead (f : H → H') (t : Table H B T) (t' : Table H' B T)
    (v : Sector H B T)
    (hd : t'.direction (f v.head) = t.direction v.head)
    (hc : ∀ b a, t'.cell (f v.head) b a = (t.cell v.head b a).map (mapInstruction f))
    (hb : t'.boundary (f v.head) = (t.boundary v.head).map f) :
    step t' (mapHead f v) = (step t v).map (mapHead f) := by
  rcases v with ⟨l,q,r,a,b⟩
  simp only [mapHead] at hd hc hb ⊢
  unfold step
  simp only [hd]
  cases hdir : t.direction q <;> dsimp only
  · cases l with
    | nil => cases a <;> simp [hb,mapHead,Option.map_map,Function.comp_def]
    | cons c l =>
        rcases c with ⟨base,tag⟩
        dsimp only
        rw [hc]
        cases hcell : t.cell q base tag with
        | none => rfl
        | some ins => rcases ins with ⟨iq,it,ic⟩; cases ic <;> rfl
  · cases r with
    | nil => cases b <;> simp [hb,mapHead,Option.map_map,Function.comp_def]
    | cons c r =>
        rcases c with ⟨base,tag⟩
        dsimp only
        rw [hc]
        cases hcell : t.cell q base tag with
        | none => rfl
        | some ins => rcases ins with ⟨iq,it,ic⟩; cases ic <;> rfl

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Control

section
open Relation
variable {S Γ Q : Type*}

/-- Finite internal-head alphabet, with a single fresh handoff/start state. -/
inductive Head (S Q : Type*)
  | initial | left | right | workspace | suffix
  | machine : Simulator.Head S Q → Head S Q
  deriving DecidableEq, Fintype

def validatorHead : Validator.Head → Head S Q
  | .initial => .initial
  | .left => .left
  | .right => .right
  | .workspace => .workspace
  | .suffix => .suffix
  | .start => .machine .start

def toValidator : Head S Q → Option Validator.Head
  | .initial => some .initial
  | .left => some .left
  | .right => some .right
  | .workspace => some .workspace
  | .suffix => some .suffix
  | .machine _ => none

abbrev Sector (S Γ Q : Type*) := Scan.Sector (Head S Q) (Base S) (Tag S Γ)

def validator (v : Validator.Sector S Γ) : Sector S Γ Q :=
  Scan.mapHead validatorHead (Validator.toScan v)

def machine (v : Compiled.MachineSector S Γ Q) : Sector S Γ Q :=
  Scan.mapHead Head.machine v

def toCfg (v : Sector S Γ Q) : Compiled.Cfg S Γ Q :=
  match v.head with
  | .initial => .inl ⟨.initial,v.left,v.right,v.leftBoundary,v.rightBoundary⟩
  | .left => .inl ⟨.left,v.left,v.right,v.leftBoundary,v.rightBoundary⟩
  | .right => .inl ⟨.right,v.left,v.right,v.leftBoundary,v.rightBoundary⟩
  | .workspace => .inl ⟨.workspace,v.left,v.right,v.leftBoundary,v.rightBoundary⟩
  | .suffix => .inl ⟨.suffix,v.left,v.right,v.leftBoundary,v.rightBoundary⟩
  | .machine q => Compiled.embed ⟨v.left,q,v.right,v.leftBoundary,v.rightBoundary⟩

@[simp] theorem cfg_validator (v : Validator.Sector S Γ) : toCfg (validator (Q := Q) v) = .inl v := by
  cases v with | mk q l r a b => cases q <;> rfl

@[simp] theorem cfg_machine (v : Compiled.MachineSector S Γ Q) :
    toCfg (machine v) = Compiled.embed v := rfl

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

/-- The literal finite union of validation and simulation equations. -/
def table : Table (Head S Q) (Base S) (Tag S Γ) where
  direction q := match toValidator q with
    | some v => (Validator.table (S := S) A.blank).direction v
    | none => match q with
      | .machine v => (Simulator.table A M).direction v
      | _ => .right
  cell q b t := match toValidator q with
    | some v => ((Validator.table (S := S) A.blank).cell v b t).map (Scan.mapInstruction validatorHead)
    | none => match q with
      | .machine v => ((Simulator.table A M).cell v b t).map (Scan.mapInstruction Head.machine)
      | _ => none
  boundary q := match toValidator q with
    | some v => ((Validator.table (S := S) A.blank).boundary v).map validatorHead
    | none => match q with
      | .machine v => ((Simulator.table A M).boundary v).map Head.machine
      | _ => none

theorem step_machine (v : Compiled.MachineSector S Γ Q) :
    Scan.step (table A M) (machine v) = (Scan.step (Simulator.table A M) v).map machine := by
  apply Scan.step_mapHead
  · rfl
  · intro b a; rfl
  · rfl

theorem step_validator (v : Validator.Sector S Γ) (hv : v.head ≠ .start) :
    Scan.step (table A M) (validator v) =
      (Scan.step (Validator.table (S := S) A.blank) (Validator.toScan v)).map (Scan.mapHead validatorHead) := by
  apply Scan.step_mapHead
  · cases v with | mk q l r a b => cases q <;> rfl
  · intro b a
    cases v with | mk q l r ls rs => cases q <;> first | rfl | exact False.elim (hv rfl)
  · cases v with | mk q l r a b => cases q <;> first | rfl | exact False.elim (hv rfl)

end

open Relation
variable {S Γ Q : Type*}

def ofCfg : Compiled.Cfg S Γ Q → Sector S Γ Q
  | .inl v => validator v
  | .inr v => machine v

@[simp] theorem ofCfg_embed (v : Compiled.MachineSector S Γ Q) :
    ofCfg (Compiled.embed v) = machine v := by
  rcases v with ⟨l,q,r,a,b⟩
  cases q <;> rfl

@[simp] theorem ofCfg_toCfg (v : Sector S Γ Q) : ofCfg (toCfg v) = v := by
  rcases v with ⟨l,q,r,a,b⟩
  cases q <;> first | rfl | exact ofCfg_embed _

theorem sector_cases (v : Sector S Γ Q) :
    (∃ w : Validator.Sector S Γ, w.head ≠ .start ∧ v = validator w) ∨
    ∃ w : Compiled.MachineSector S Γ Q, v = machine w := by
  rcases v with ⟨l,q,r,a,b⟩
  cases q with
  | machine q => exact Or.inr ⟨⟨l,q,r,a,b⟩,rfl⟩
  | initial => exact Or.inl ⟨⟨.initial,l,r,a,b⟩,by simp,rfl⟩
  | left => exact Or.inl ⟨⟨.left,l,r,a,b⟩,by simp,rfl⟩
  | right => exact Or.inl ⟨⟨.right,l,r,a,b⟩,by simp,rfl⟩
  | workspace => exact Or.inl ⟨⟨.workspace,l,r,a,b⟩,by simp,rfl⟩
  | suffix => exact Or.inl ⟨⟨.suffix,l,r,a,b⟩,by simp,rfl⟩

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

theorem validator_step {v w : Validator.Sector S Γ} (h : Validator.Step A.blank v w) :
    Scan.Step (table A M) (validator v) (validator w) := by
  rw [Scan.Step,step_validator A M v (Validator.Extended.validator_not_start A.blank h),
    Validator.step_toScan A.blank h]
  rfl

theorem machine_step {v w : Compiled.MachineSector S Γ Q}
    (h : Scan.Step (Simulator.table A M) v w) :
    Scan.Step (table A M) (machine v) (machine w) := by
  rw [Scan.Step,step_machine A M,h]
  rfl

theorem cfg_step {v w : Sector S Γ Q} (h : Scan.Step (table A M) v w) :
    Compiled.Step A M (toCfg v) (toCfg w) := by
  rcases sector_cases v with ⟨v,hv,rfl⟩ | ⟨v,rfl⟩
  · rw [Scan.Step,step_validator A M v hv] at h
    obtain ⟨u,hu,rfl⟩ := Option.map_eq_some_iff.mp h
    have he : Scan.mapHead (validatorHead (S := S) (Q := Q)) u =
        validator (Validator.ofScan u) := rfl
    rw [he,cfg_validator,cfg_validator]
    exact .validator (Validator.step_ofScan A.blank hu)
  · rw [Scan.Step,step_machine A M] at h
    obtain ⟨u,hu,rfl⟩ := Option.map_eq_some_iff.mp h
    rw [cfg_machine,cfg_machine]
    exact Compiled.embed_step A M hu

theorem ofCfg_step {v w : Compiled.Cfg S Γ Q} (h : Compiled.Step A M v w) :
    Scan.Step (table A M) (ofCfg v) (ofCfg w) := by
  cases h with
  | validator h => exact validator_step A M h
  | machine _ _ h =>
      obtain ⟨u,v,rfl,rfl,h⟩ := h
      rw [ofCfg_embed,ofCfg_embed]
      exact machine_step A M h

theorem cfg_connected {v w : Sector S Γ Q} (h : EqvGen (Scan.Step (table A M)) v w) :
    EqvGen (Compiled.Step A M) (toCfg v) (toCfg w) := by
  induction h with
  | rel _ _ h => exact .rel _ _ (cfg_step A M h)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

theorem ofCfg_runs {v w : Compiled.Cfg S Γ Q} (h : ReflTransGen (Compiled.Step A M) v w) :
    ReflTransGen (Scan.Step (table A M)) (ofCfg v) (ofCfg w) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (ofCfg_step A M h)

end FiniteAlgebraicEnvelopes.Compiler.Control

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open Relation
variable {H B T : Type*} [Fintype H] [Fintype B] [Fintype T]
  [DecidableEq H] [DecidableEq B] [DecidableEq T]

/-- Literal configurations, rather than an oracle for connectivity, returned
    by exhaustive search on the fixed finite base skeleton. -/
def literalComponent (table : Table H B T) (v : Sector H B T) : Finset (Sector H B T) :=
  (component (fixedStep table v) (fixedSelf v)).image Subtype.val

@[simp] theorem mem_literalComponent (table : Table H B T) (v w : Sector H B T) :
    w ∈ literalComponent table v ↔ EqvGen (Step table) v w := by
  constructor
  · intro h
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp h
    exact (fixedConnected_iff table v _ _).mp ((mem_component_iff _ _ _).mp hu)
  · intro h
    let u : Fixed v := ⟨w,(connected_skeleton table h).symm⟩
    apply Finset.mem_image.mpr
    refine ⟨u,?_,rfl⟩
    exact (mem_component_iff _ _ _).mpr ((fixedConnected_iff table v _ _).mpr h)

theorem literalComponent_nonempty (table : Table H B T) (v : Sector H B T) :
    (literalComponent table v).Nonempty :=
  ⟨v,(mem_literalComponent table v v).mpr (.refl v)⟩

theorem literalComponent_eq (table : Table H B T) {v w : Sector H B T}
    (h : EqvGen (Step table) v w) : literalComponent table v = literalComponent table w := by
  ext u
  simp only [mem_literalComponent]
  exact ⟨fun hv => .trans _ _ _ (.symm _ _ h) hv,fun hw => .trans _ _ _ h hw⟩

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler
variable {α : Type*}

theorem prioritySet_first (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    {s : Finset α} (hs : ∃ a ∈ s, P a) {b : α} (hb : b ∈ prioritySet P Q s) : P b := by
  have hn : (s.filter P).Nonempty := by
    obtain ⟨a,ha,hp⟩ := hs
    exact ⟨a,Finset.mem_filter.mpr ⟨ha,hp⟩⟩
  rw [prioritySet,ite_eq_left hn] at hb
  exact (Finset.mem_filter.mp hb).2

theorem prioritySet_second (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    {s : Finset α} (hp : ¬ ∃ a ∈ s, P a) (hq : ∃ a ∈ s, Q a)
    {b : α} (hb : b ∈ prioritySet P Q s) : Q b := by
  have hn : ¬ (s.filter P).Nonempty := by
    rintro ⟨a,ha⟩
    exact hp ⟨a,(Finset.mem_filter.mp ha).1,(Finset.mem_filter.mp ha).2⟩
  have hm : (s.filter Q).Nonempty := by
    obtain ⟨a,ha,hq⟩ := hq
    exact ⟨a,Finset.mem_filter.mpr ⟨ha,hq⟩⟩
  rw [prioritySet,ite_eq_right hn,ite_eq_left hm] at hb
  exact (Finset.mem_filter.mp hb).2

end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open Relation
variable {H B T : Type*} [Fintype H] [Fintype B] [Fintype T]
  [DecidableEq H] [DecidableEq B] [DecidableEq T] [LinearOrder (Sector H B T)]
variable (table : Table H B T) (P Q : Sector H B T → Prop) [DecidablePred P] [DecidablePred Q]

def representative (v : Sector H B T) : Sector H B T :=
  (prioritySet P Q (literalComponent table v)).min'
    (prioritySet_nonempty P Q _ (literalComponent_nonempty table v))

theorem representative_mem (v : Sector H B T) :
    representative table P Q v ∈ prioritySet P Q (literalComponent table v) :=
  Finset.min'_mem _ _

theorem representative_connected (v : Sector H B T) :
    EqvGen (Step table) v (representative table P Q v) :=
  (mem_literalComponent table _ _).mp
    (prioritySet_subset _ _ _ (representative_mem table P Q v))

theorem representative_eq {v w : Sector H B T} (h : EqvGen (Step table) v w) :
    representative table P Q v = representative table P Q w := by
  unfold representative
  simp only [literalComponent_eq table h]

theorem representative_first (v : Sector H B T)
    (h : ∃ w, EqvGen (Step table) v w ∧ P w) : P (representative table P Q v) := by
  apply prioritySet_first P Q _ (representative_mem table P Q v)
  simpa only [mem_literalComponent] using h

theorem representative_second (v : Sector H B T)
    (hp : ¬ ∃ w, EqvGen (Step table) v w ∧ P w)
    (hq : ∃ w, EqvGen (Step table) v w ∧ Q w) : Q (representative table P Q v) := by
  apply prioritySet_second P Q _ _ (representative_mem table P Q v)
  · simpa only [mem_literalComponent] using hp
  · simpa only [mem_literalComponent] using hq

end FiniteAlgebraicEnvelopes.Compiler.Scan

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Surface
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Surface alphabet, preprocessing, and grading estimates.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Surface

section
open Relation

abbrev Sector (S Γ H : Type*) := Scan.Sector (Head H) (Base S) (Tag S Γ)
variable {S Γ H : Type*}
abbrev Cells (S Γ : Type*) := List (Base S × Tag S Γ)

/-- Literal clean-anchor slides, oriented to the leftmost reachable head gap. -/
inductive RawStep (blank : Γ) : Sector S Γ H → Sector S Γ H → Prop
  | slide (a : S) (l r : Cells S Γ) (lb rb : Bool) :
      RawStep blank ⟨Validator.cell blank (.anchor a)::l,.raw,r,lb,rb⟩
        ⟨l,.raw,Validator.cell blank (.anchor a)::r,lb,rb⟩

theorem rawStep_deterministic (blank : Γ) : Relator.RightUnique (RawStep (H := H) (S := S) blank) := by
  intro a b c hab hac
  cases hab; cases hac; rfl

def grade (v : Sector S Γ H) : ℕ :=
  Cleanup.cellsGrade v.left + 1 + Cleanup.cellsGrade v.right +
    (if v.leftBoundary then 1 else 0) + (if v.rightBoundary then 1 else 0)

theorem rawStep_grade (blank : Γ) {v w : Sector S Γ H} (h : RawStep blank v w) :
    grade v = grade w := by
  cases h
  simp [grade,Cleanup.cellsGrade,Validator.cell,Cleanup.grade]
  omega

variable (blank : Γ) [DecidableEq S] [DecidableEq Γ]

def rawSweep : Cells S Γ → Cells S Γ → Bool → Bool → Sector S Γ H
  | [],r,lb,rb => ⟨[],.raw,r,lb,rb⟩
  | (b,t)::l,r,lb,rb => match b with
    | .anchor _a => if t = clean blank then rawSweep l ((b,t)::r) lb rb
        else ⟨(b,t)::l,.raw,r,lb,rb⟩
    | _ => ⟨(b,t)::l,.raw,r,lb,rb⟩

theorem rawSweep_reaches (l r : Cells S Γ) (lb rb : Bool) :
    ReflTransGen (RawStep blank) (⟨l,.raw,r,lb,rb⟩ : Sector S Γ H) (rawSweep blank l r lb rb) := by
  induction l generalizing r with
  | nil => exact .refl
  | cons c l ih =>
      rcases c with ⟨b,t⟩
      cases b with
      | anchor a =>
          by_cases ht : t = clean blank
          · subst t
            simpa [rawSweep,Validator.cell] using
              (ReflTransGen.single (RawStep.slide a l r lb rb)).trans
                (ih (Validator.cell blank (.anchor a)::r))
          · simp only [rawSweep,ite_eq_right ht]
            exact .refl
      | cutC | cutD | workspace => exact .refl

theorem rawSweep_terminal (l r : Cells S Γ) (lb rb : Bool) :
    Terminal (RawStep (H := H) blank) (rawSweep blank l r lb rb) := by
  induction l generalizing r with
  | nil => intro w hw; cases hw
  | cons c l ih =>
      rcases c with ⟨b,t⟩
      cases b with
      | anchor a =>
          by_cases ht : t = clean blank
          · simp only [rawSweep,ite_eq_left ht]
            exact ih _
          · simp only [rawSweep,ite_eq_right ht]
            intro w hw
            cases hw
            exact ht rfl
      | cutC | cutD | workspace => intro w hw; cases hw

def rawNormal (v : Sector S Γ H) : Sector S Γ H :=
  match v.head with
  | .raw => rawSweep blank v.left v.right v.leftBoundary v.rightBoundary
  | _ => v

theorem rawNormal_reaches (v : Sector S Γ H) : ReflTransGen (RawStep blank) v (rawNormal blank v) := by
  rcases v with ⟨l,q,r,a,b⟩
  cases q with
  | raw => exact rawSweep_reaches blank l r a b
  | pending | cleanup | internal _ => exact .refl

theorem rawNormal_terminal (v : Sector S Γ H) : Terminal (RawStep blank) (rawNormal blank v) := by
  rcases v with ⟨l,q,r,a,b⟩
  cases q with
  | raw => exact rawSweep_terminal blank l r a b
  | pending | cleanup | internal _ => intro w hw; cases hw

theorem rawNormal_invariant {v w : Sector S Γ H} (h : EqvGen (RawStep blank) v w) :
    rawNormal blank v = rawNormal blank w := by
  apply terminal_unique (rawStep_deterministic blank) (rawNormal_terminal blank v) (rawNormal_terminal blank w)
  exact .trans _ _ _ (.symm _ _ (EqvGen.reflTransGen_le_eqvGen _ _ _ (rawNormal_reaches blank v)))
    (.trans _ _ _ h (EqvGen.reflTransGen_le_eqvGen _ _ _ (rawNormal_reaches blank w)))

theorem rawNormal_grade (v : Sector S Γ H) : grade (rawNormal blank v) = grade v := by
  have aux : ∀ {a b : Sector S Γ H}, ReflTransGen (RawStep blank) a b → grade b = grade a := by
    intro a b h
    induction h with
    | refl => rfl
    | tail _ h ih => exact (rawStep_grade blank h).symm.trans ih
  exact aux (rawNormal_reaches blank v)

/-- Literal raw singleton; in particular no program is evaluated on it. -/
def raw (w : List S) : Sector S Γ H :=
  ⟨[],.raw,w.map (Validator.cell blank ∘ Base.anchor),true,true⟩

@[simp] theorem rawNormal_raw (w : List S) : rawNormal blank (raw (H := H) blank w) = raw blank w := rfl

theorem rawSweep_clean (w : List S) (r : Cells S Γ) (lb rb : Bool) :
    rawSweep (H := H) blank (w.map (Validator.cell blank ∘ Base.anchor)) r lb rb =
      ⟨[],.raw,(w.reverse.map (Validator.cell blank ∘ Base.anchor))++r,lb,rb⟩ := by
  induction w generalizing r with
  | nil => rfl
  | cons a w ih =>
      simp only [List.map_cons,Function.comp_apply,Validator.cell,rawSweep,↓reduceIte]
      rw [ih]
      simp [List.reverse_cons,List.append_assoc,Validator.cell]

end

section
open Relation
variable {S Γ H : Type*} (blank : Γ)

/-- The quota rule is applicable only at the literal clean right cut. -/
inductive QuotaStep : Sector S Γ H → Sector S Γ H → Prop
  | trim (l r : Cells S Γ) (lb rb : Bool) :
      QuotaStep ⟨Validator.cell blank .workspace::l,.pending,
          Validator.cell blank .cutD::r,lb,rb⟩
        ⟨l,.pending,Validator.cell blank .cutD::r,lb,rb⟩

theorem quotaStep_deterministic : Relator.RightUnique (QuotaStep (S := S) (H := H) blank) := by
  intro a b c hab hac
  cases hab; cases hac; rfl

theorem quotaStep_grade {v w : Sector S Γ H} (h : QuotaStep blank v w) :
    grade v = grade w := by
  cases h
  simp [grade,Cleanup.cellsGrade,Validator.cell,Cleanup.grade]

theorem quotaStep_left {v w : Sector S Γ H} (h : QuotaStep blank v w) :
    ∃ l, v.left = Validator.cell blank .workspace::l := by
  cases h
  exact ⟨_,rfl⟩

variable [DecidableEq S] [DecidableEq Γ]

def trimQuota : Cells S Γ → Cells S Γ
  | [] => []
  | c::l => if c = Validator.cell blank .workspace then trimQuota l else c::l

theorem trimQuota_terminal (l : Cells S Γ) :
    ∀ r, trimQuota blank l ≠ Validator.cell blank .workspace::r := by
  induction l with
  | nil => intro r h; cases h
  | cons c l ih =>
      by_cases h : c = Validator.cell blank .workspace
      · simpa only [trimQuota,ite_eq_left h] using ih
      · simp only [trimQuota,ite_eq_right h]
        intro r hh
        exact h (List.cons.inj hh).1

def quotaNormal (v : Sector S Γ H) : Sector S Γ H :=
  match v.head,v.right with
  | .pending,d::_ => if d = Validator.cell blank .cutD then {v with left := trimQuota blank v.left} else v
  | _,_ => v

theorem trimQuota_reaches (l r : Cells S Γ) (lb rb : Bool) :
    ReflTransGen (QuotaStep blank)
      (⟨l,.pending,Validator.cell blank .cutD::r,lb,rb⟩ : Sector S Γ H)
      ⟨trimQuota blank l,.pending,Validator.cell blank .cutD::r,lb,rb⟩ := by
  induction l with
  | nil => exact .refl
  | cons c l ih =>
      by_cases h : c = Validator.cell blank .workspace
      · subst c
        simpa only [trimQuota,↓reduceIte] using (ReflTransGen.single (QuotaStep.trim l r lb rb)).trans ih
      · simpa only [trimQuota,ite_eq_right h] using
          (ReflTransGen.refl : ReflTransGen (QuotaStep blank)
            (⟨c::l,.pending,Validator.cell blank .cutD::r,lb,rb⟩ : Sector S Γ H) _)

theorem quotaNormal_reaches (v : Sector S Γ H) :
    ReflTransGen (QuotaStep blank) v (quotaNormal blank v) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q with
  | pending =>
      cases r with
      | nil => exact .refl
      | cons d r =>
          by_cases h : d = Validator.cell blank .cutD
          · subst d
            simpa only [quotaNormal,↓reduceIte] using trimQuota_reaches blank l r lb rb
          · simp only [quotaNormal,ite_eq_right h]
            exact .refl
  | raw | cleanup | internal _ => exact .refl

theorem quotaNormal_terminal (v : Sector S Γ H) : Terminal (QuotaStep blank) (quotaNormal blank v) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q with
  | pending =>
      cases r with
      | nil => intro z hz; cases hz
      | cons d r =>
          by_cases h : d = Validator.cell blank .cutD
          · subst d
            simp only [quotaNormal,↓reduceIte]
            intro z hz
            obtain ⟨l',hl⟩ := quotaStep_left blank hz
            exact trimQuota_terminal blank l l' hl
          · simp only [quotaNormal,ite_eq_right h]
            intro z hz
            cases hz
            exact h rfl
  | raw | cleanup | internal _ => intro z hz; cases hz

theorem quotaNormal_invariant {v w : Sector S Γ H} (h : EqvGen (QuotaStep blank) v w) :
    quotaNormal blank v = quotaNormal blank w := by
  apply terminal_unique (quotaStep_deterministic blank) (quotaNormal_terminal blank v) (quotaNormal_terminal blank w)
  exact .trans _ _ _ (.symm _ _ (EqvGen.reflTransGen_le_eqvGen _ _ _ (quotaNormal_reaches blank v)))
    (.trans _ _ _ h (EqvGen.reflTransGen_le_eqvGen _ _ _ (quotaNormal_reaches blank w)))

theorem quotaNormal_grade (v : Sector S Γ H) : grade (quotaNormal blank v) = grade v := by
  have aux : ∀ {a b : Sector S Γ H}, ReflTransGen (QuotaStep blank) a b → grade b = grade a := by
    intro a b h
    induction h with
    | refl => rfl
    | tail _ h ih => exact (quotaStep_grade blank h).symm.trans ih
  exact aux (quotaNormal_reaches blank v)

/-- Unmerge after trimming. The outer boundaries may be absent and the outer
    cells may be arbitrarily dirty. Only the two displayed cut cells are tested. -/
def unmerge (v : Sector S Γ H) : List (Sector S Γ H) :=
  match v.left,v.head,v.right with
  | c::l,.pending,d::r =>
    if c = Validator.cell blank .cutC ∧ d = Validator.cell blank .cutD then
      [rawNormal blank ⟨l,.raw,[],v.leftBoundary,true⟩,
        rawNormal blank ⟨[],.raw,r,true,v.rightBoundary⟩]
    else [v]
  | _,_,_ => [v]

def pendingPreprocess (v : Sector S Γ H) : List (Sector S Γ H) :=
  unmerge blank (quotaNormal blank v)

theorem pendingPreprocess_invariant {v w : Sector S Γ H} (h : EqvGen (QuotaStep blank) v w) :
    pendingPreprocess blank v = pendingPreprocess blank w := by
  simp only [pendingPreprocess,quotaNormal_invariant blank h]

def listGrade (l : List (Sector S Γ H)) : ℕ := (l.map grade).sum

theorem unmerge_grade (v : Sector S Γ H) : listGrade (unmerge blank v) = grade v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases l with
  | nil => rfl
  | cons c l =>
      cases q with
      | pending =>
          cases r with
          | nil => rfl
          | cons d r =>
              by_cases h : c = Validator.cell blank .cutC ∧ d = Validator.cell blank .cutD
              · rcases h with ⟨rfl,rfl⟩
                simp [unmerge,listGrade,rawNormal_grade]
                simp [grade,Cleanup.cellsGrade,Validator.cell,Cleanup.grade]
                omega
              · simp [unmerge,h,listGrade]
      | raw | cleanup | internal _ => simp [unmerge,listGrade]

theorem pendingPreprocess_grade (v : Sector S Γ H) :
    listGrade (pendingPreprocess blank v) = grade v := by
  rw [pendingPreprocess,unmerge_grade,quotaNormal_grade]

theorem trimQuota_workspace (s : ℕ) (l : Cells S Γ) :
    trimQuota blank (List.replicate s (Validator.cell blank .workspace) ++ l) = trimQuota blank l := by
  induction s with
  | zero => rfl
  | succ s ih => simpa [List.replicate_succ,trimQuota] using ih

/-- The literal merge is undone, even on dirty/incomplete surroundings. -/
theorem pendingPreprocess_merge (l r : Cells S Γ) (s : ℕ) (lb rb : Bool) :
    pendingPreprocess (H := H) blank
      ⟨List.replicate s (Validator.cell blank .workspace) ++ Validator.cell blank .cutC::l,
        .pending,Validator.cell blank .cutD::r,lb,rb⟩ =
      [rawNormal blank ⟨l,.raw,[],lb,true⟩,rawNormal blank ⟨[],.raw,r,true,rb⟩] := by
  simp only [pendingPreprocess,quotaNormal]
  rw [trimQuota_workspace]
  simp [trimQuota,unmerge,Validator.cell]

end

open Relation
variable {S Γ H : Type*}

def ofCleanup (v : Cleanup.Sector S Γ) : Sector S Γ H := Scan.mapHead cleanupHead v

def cleanupNormal (blank : Γ) (v : Sector S Γ H) : Sector S Γ H :=
  match v.head with
  | .cleanup => ofCleanup (Cleanup.normal blank
      ⟨v.left,.cleanup,v.right,v.leftBoundary,v.rightBoundary⟩)
  | _ => v

@[simp] theorem cleanupNormal_ofCleanup (blank : Γ) (v : Cleanup.Sector S Γ) :
    cleanupNormal blank (ofCleanup (H := H) v) = ofCleanup (Cleanup.normal blank v) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> rfl

theorem cleanupNormal_grade (blank : Γ) (v : Sector S Γ H) :
    grade (cleanupNormal blank v) ≤ grade v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q with
  | cleanup =>
      have h := Cleanup.output_grade_le blank l.reverse
      rw [Cleanup.cellsGrade_reverse] at h
      simp only [cleanupNormal,Cleanup.normal,ofCleanup,Scan.mapHead,grade,
        Cleanup.cellsGrade_append]
      simp only [Cleanup.cellsGrade,List.map_nil,List.sum_nil] at h ⊢
      cases lb <;> cases rb <;> simp_all
      all_goals omega
  | raw | pending | internal _ => exact le_rfl

variable (blank : Γ) [DecidableEq S] [DecidableEq Γ]

def cleanupPreprocess (v : Sector S Γ H) : Sector S Γ H :=
  rawNormal blank (cleanupNormal blank v)

theorem cleanupPreprocess_grade (v : Sector S Γ H) :
    grade (cleanupPreprocess blank v) ≤ grade v := by
  rw [cleanupPreprocess,rawNormal_grade]
  exact cleanupNormal_grade blank v

@[simp] theorem cleanupPreprocess_ofCleanup (v : Cleanup.Sector S Γ) :
    cleanupPreprocess blank (ofCleanup (H := H) v) =
      rawNormal blank (ofCleanup (Cleanup.normal blank v)) := by
  rw [cleanupPreprocess,cleanupNormal_ofCleanup]

theorem cleanupPreprocess_invariant {v w : Cleanup.Sector S Γ}
    (h : EqvGen (Cleanup.Step blank) v w) :
    cleanupPreprocess blank (ofCleanup (H := H) v) = cleanupPreprocess blank (ofCleanup w) := by
  simp only [cleanupPreprocess_ofCleanup,Cleanup.normal_invariant blank h]

@[simp] theorem cleanupPreprocess_raw (w : List S) :
    cleanupPreprocess blank (raw (H := H) blank w) = raw blank w := rfl

end FiniteAlgebraicEnvelopes.Compiler.Surface

namespace FiniteAlgebraicEnvelopes.Compiler.Control
open Relation
variable {S Γ Q : Type*}

/-- Literal entry and successful exit tests, both finite data predicates. -/
def Entry (blank : Γ) (v : Sector S Γ Q) : Prop :=
  v.head = .initial ∧ v.right.head? = some (Validator.cell blank .cutD)

def Success (v : Sector S Γ Q) : Prop :=
  v.head = .machine .ok ∧ v.right = [] ∧ v.rightBoundary = true

instance entryDecidable (blank : Γ) [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] :
    DecidablePred (Entry (S := S) (Q := Q) blank) := fun _ => inferInstanceAs (Decidable (_ ∧ _))

instance successDecidable [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] :
    DecidablePred (Success (S := S) (Γ := Γ) (Q := Q)) := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem entry_cases (blank : Γ) {v : Sector S Γ Q} (h : Entry blank v) :
    ∃ w : Validator.Sector S Γ, Validator.Entry blank w ∧ v = validator w := by
  rcases v with ⟨l,q,r,lb,rb⟩
  obtain ⟨rfl,hr⟩ := h
  refine ⟨⟨.initial,l,r,lb,rb⟩,⟨rfl,?_⟩,rfl⟩
  cases r with
  | nil => cases hr
  | cons d r => exact ⟨r,by simpa using hr⟩

theorem entry_validator (blank : Γ) {w : Validator.Sector S Γ} (h : Validator.Entry blank w) :
    Entry blank (validator (Q := Q) w) := by
  rcases w with ⟨q,l,r,lb,rb⟩
  obtain ⟨rfl,r,rfl⟩ := h
  exact ⟨rfl,rfl⟩

theorem success_cases {v : Sector S Γ Q} (h : Success v) :
    ∃ w : Compiled.MachineSector S Γ Q, w.head = .ok ∧ w.right = [] ∧
      w.rightBoundary = true ∧ v = machine w := by
  rcases v with ⟨l,q,r,lb,rb⟩
  obtain ⟨rfl,rfl,rfl⟩ := h
  exact ⟨⟨l,.ok,[],lb,true⟩,rfl,rfl,rfl,rfl⟩

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

theorem entries_unique {v w : Sector S Γ Q} (hv : Entry A.blank v) (hw : Entry A.blank w)
    (h : EqvGen (Scan.Step (table A M)) v w) : v = w := by
  obtain ⟨v,hve,rfl⟩ := entry_cases A.blank hv
  obtain ⟨w,hwe,rfl⟩ := entry_cases A.blank hw
  have hc := cfg_connected A M h
  rw [cfg_validator,cfg_validator] at hc
  exact congrArg validator (Compiled.entries_unique A M hve hwe hc)

theorem successes_unique {v w : Sector S Γ Q} (hv : Success v) (hw : Success w)
    (h : EqvGen (Scan.Step (table A M)) v w) : v = w := by
  obtain ⟨v,hve,_,_,rfl⟩ := success_cases hv
  obtain ⟨w,hwe,_,_,rfl⟩ := success_cases hw
  have hc := cfg_connected A M h
  rw [cfg_machine,cfg_machine] at hc
  exact congrArg machine (Compiled.ok_unique A M hve hwe hc)

variable [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
  [LinearOrder (Sector S Γ Q)]

def representative (v : Sector S Γ Q) : Sector S Γ Q :=
  Scan.representative (table A M) (Entry A.blank) Success v

theorem representative_connected (v : Sector S Γ Q) :
    EqvGen (Scan.Step (table A M)) v (representative A M v) :=
  Scan.representative_connected _ _ _ v

theorem representative_eq {v w : Sector S Γ Q}
    (h : EqvGen (Scan.Step (table A M)) v w) : representative A M v = representative A M w :=
  Scan.representative_eq _ _ _ h

theorem representative_entry {v : Sector S Γ Q} (hv : Entry A.blank v) :
    representative A M v = v := by
  apply (entries_unique A M hv _ (representative_connected A M v)).symm
  exact Scan.representative_first _ _ _ v ⟨v,.refl _,hv⟩

theorem representative_success {v : Sector S Γ Q} (hv : Success v)
    (hn : ¬ ∃ w, EqvGen (Scan.Step (table A M)) v w ∧ Entry A.blank w) :
    representative A M v = v := by
  apply (successes_unique A M hv _ (representative_connected A M v)).symm
  exact Scan.representative_second _ _ _ v hn ⟨v,.refl _,hv⟩

end FiniteAlgebraicEnvelopes.Compiler.Control

namespace FiniteAlgebraicEnvelopes.Compiler.Surface

section
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- Internal finite-component search, with entry priority. No invocation of the
    compiled machine as an evaluator occurs here. -/
def internalPreprocess (v : Control.Sector S Γ Q) : List (Sector S Γ (Control.Head S Q)) :=
  let w := Control.representative A M v
  if Control.Entry A.blank w then
    pendingPreprocess A.blank ⟨w.left,.pending,w.right,w.leftBoundary,w.rightBoundary⟩
  else if Control.Success w then
    [cleanupPreprocess A.blank ⟨w.left,.cleanup,w.right,w.leftBoundary,w.rightBoundary⟩]
  else [Scan.mapHead Head.internal w]

theorem internalPreprocess_invariant {v w : Control.Sector S Γ Q}
    (h : EqvGen (Scan.Step (Control.table A M)) v w) :
    internalPreprocess A M v = internalPreprocess A M w := by
  simp only [internalPreprocess,Control.representative_eq A M h]

theorem internalPreprocess_entry (v : Control.Sector S Γ Q) (hv : Control.Entry A.blank v) :
    internalPreprocess A M v = pendingPreprocess A.blank
      ⟨v.left,.pending,v.right,v.leftBoundary,v.rightBoundary⟩ := by
  simp only [internalPreprocess,Control.representative_entry A M hv,ite_eq_left hv]

theorem internalPreprocess_success (v : Control.Sector S Γ Q) (hv : Control.Success v)
    (hn : ¬ ∃ w, EqvGen (Scan.Step (Control.table A M)) v w ∧ Control.Entry A.blank w) :
    internalPreprocess A M v =
      [cleanupPreprocess A.blank ⟨v.left,.cleanup,v.right,v.leftBoundary,v.rightBoundary⟩] := by
  have he : ¬ Control.Entry A.blank v := fun h => hn ⟨v,.refl _,h⟩
  simp only [internalPreprocess,Control.representative_success A M hv hn,ite_eq_right he,ite_eq_left hv]

/-- Complete sector preprocessing, prior to the only partial operation: maximal
    full-raw-run evaluation. Headless sectors will be preserved by the parser. -/
def preprocess (v : Sector S Γ (Control.Head S Q)) : List (Sector S Γ (Control.Head S Q)) :=
  match v.head with
  | .raw => [rawNormal A.blank v]
  | .pending => pendingPreprocess A.blank v
  | .cleanup => [cleanupPreprocess A.blank v]
  | .internal q => internalPreprocess A M ⟨v.left,q,v.right,v.leftBoundary,v.rightBoundary⟩

@[simp] theorem preprocess_raw (w : List S) : preprocess A M (raw A.blank w) = [raw A.blank w] := rfl

end

open Relation
variable {S Γ H H' : Type*}

def skeletonGrade (s : List (Base S) × Bool × Bool) : ℕ :=
  (s.1.map Cleanup.grade).sum + 1 + (if s.2.1 then 1 else 0) + (if s.2.2 then 1 else 0)

theorem grade_skeleton (v : Sector S Γ H) : grade v = skeletonGrade (Scan.baseSkeleton v) := by
  simp [grade,skeletonGrade,Scan.baseSkeleton,Cleanup.cellsGrade,List.map_reverse,
    List.map_append,List.map_map]
  omega

theorem grade_eq_of_skeleton {v : Sector S Γ H} {w : Sector S Γ H'}
    (h : Scan.baseSkeleton v = Scan.baseSkeleton w) : grade v = grade w := by
  rw [grade_skeleton,grade_skeleton,h]

variable {Q : Type*} (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

theorem internalPreprocess_grade (v : Control.Sector S Γ Q) :
    listGrade (internalPreprocess A M v) ≤ grade (Scan.mapHead Head.internal v) := by
  have he : grade (Scan.mapHead Head.internal (Control.representative A M v)) =
      grade (Scan.mapHead Head.internal v) := by
    apply grade_eq_of_skeleton
    simp only [Scan.skeleton_mapHead]
    exact (Scan.connected_skeleton _ (Control.representative_connected A M v)).symm
  unfold internalPreprocess
  dsimp only
  split
  · rw [pendingPreprocess_grade]
    exact he.le
  · split
    · simp only [listGrade,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
      exact (cleanupPreprocess_grade A.blank _).trans he.le
    · simpa only [listGrade,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using he.le

theorem preprocess_grade (v : Sector S Γ (Control.Head S Q)) :
    listGrade (preprocess A M v) ≤ grade v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q with
  | raw => simp [preprocess,listGrade,rawNormal_grade]
  | pending => exact (pendingPreprocess_grade A.blank _).le
  | cleanup => exact cleanupPreprocess_grade A.blank _
  | internal q => exact internalPreprocess_grade A M ⟨l,q,r,lb,rb⟩

theorem preprocess_rawStep {v w : Sector S Γ (Control.Head S Q)} (h : RawStep A.blank v w) :
    preprocess A M v = preprocess A M w := by
  cases h
  exact congrArg (fun x => [x]) (rawNormal_invariant A.blank (.rel _ _ (.slide _ _ _ _ _)))

theorem preprocess_quotaStep {v w : Sector S Γ (Control.Head S Q)} (h : QuotaStep A.blank v w) :
    preprocess A M v = preprocess A M w := by
  cases h
  exact pendingPreprocess_invariant A.blank (.rel _ _ (.trim _ _ _ _))

@[simp] theorem preprocess_ofCleanup (v : Cleanup.Sector S Γ) :
    preprocess A M (ofCleanup v) = [cleanupPreprocess A.blank (ofCleanup v)] := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q <;> rfl

theorem preprocess_cleanupStep {v w : Cleanup.Sector S Γ} (h : Cleanup.Step A.blank v w) :
    preprocess A M (ofCleanup v) = preprocess A M (ofCleanup w) := by
  simp only [preprocess_ofCleanup,cleanupPreprocess_invariant A.blank (.rel _ _ h)]

theorem preprocess_entryStep (l r : Cells S Γ) (lb rb : Bool) :
    preprocess A M ⟨l,.pending,Validator.cell A.blank .cutD::r,lb,rb⟩ =
    preprocess A M ⟨l,.internal .initial,Validator.cell A.blank .cutD::r,lb,rb⟩ := by
  exact (internalPreprocess_entry A M
    (⟨l,.initial,Validator.cell A.blank .cutD::r,lb,rb⟩ : Control.Sector S Γ Q) ⟨rfl,rfl⟩).symm

theorem preprocess_internalStep {v w : Control.Sector S Γ Q}
    (h : Scan.Step (Control.table A M) v w) :
    preprocess A M (Scan.mapHead Head.internal v) = preprocess A M (Scan.mapHead Head.internal w) := by
  rcases v with ⟨l,q,r,a,b⟩
  rcases w with ⟨l',q',r',a',b'⟩
  change internalPreprocess A M ⟨l,q,r,a,b⟩ = internalPreprocess A M ⟨l',q',r',a',b'⟩
  exact internalPreprocess_invariant A M (.rel _ _ h)

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
    [LinearOrder (Control.Sector S Γ Q)] in
/-- The two outputs of unmerging a *clean full* entry are precisely the two
    full raw words. This includes zero workspace and empty x or y. -/
theorem pendingPreprocess_cleanEntry (x y : List S) (s : ℕ) :
    pendingPreprocess (H := Control.Head S Q) A.blank
      ⟨(Compiled.cleanEntry A.blank x y s).left,.pending,
        (Compiled.cleanEntry A.blank x y s).right,true,true⟩ =
      [raw A.blank x,raw A.blank y] := by
  rw [Compiled.cleanEntry,pendingPreprocess_merge]
  change [rawSweep A.blank ((x.map (Validator.cell A.blank ∘ Base.anchor)).reverse) [] true true,
    raw A.blank y] = [raw A.blank x,raw A.blank y]
  rw [← List.map_reverse,rawSweep_clean]
  simp [raw]

end FiniteAlgebraicEnvelopes.Compiler.Surface

/- Literal path alphabet and sector parsing for the finite compiler.
   All definitions are independent of the partial program. -/

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Normalization
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path.instPrimcodableShape _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.instPrimcodableInstruction _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
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

/-- Full raw sectors have three structural letters alpha,Q,omega. -/
def itemGrade (g : C → ℕ) : Item C S → ℕ
  | .inl c => g c
  | .inr w => w.length + 3

def grade (g : C → ℕ) (w : List (Item C S)) : ℕ := (w.map (itemGrade g)).sum

@[simp] theorem grade_nil (g : C → ℕ) : grade g ([] : List (Item C S)) = 0 := rfl
@[simp] theorem grade_cons (g : C → ℕ) (a : Item C S) (w : List (Item C S)) :
    grade g (a::w) = itemGrade g a + grade g w := rfl
@[simp] theorem grade_append (g : C → ℕ) (u v : List (Item C S)) :
    grade g (u++v) = grade g u + grade g v := by simp [grade]

/-- Fold a nonempty raw run by adjacent pair replacement. We prove below that
    it agrees with the source's single call on the concatenated maximal run. -/
def prepend (f : List S → List S) : Item C S → List (Item C S) → List (Item C S)
  | .inr x,.inr y::w => .inr (f (x++y))::w
  | a,w => a::w

def normalize (f : List S → List S) : List (Item C S) → List (Item C S)
  | [] => []
  | a::w => prepend f a (normalize f w)

@[simp] theorem normalize_nil (f : List S → List S) : normalize f ([] : List (Item C S)) = [] := rfl
@[simp] theorem normalize_cons (f : List S → List S) (a : Item C S) (w : List (Item C S)) :
    normalize f (a::w) = prepend f a (normalize f w) := rfl

variable {f : List S → List S} {m : ℕ}

 theorem prepend_grade (g : C → ℕ) (h : Budget f m) (a : Item C S) (w : List (Item C S))
    (hm : itemGrade g a + grade g w ≤ m) :
    grade g (prepend f a w) ≤ itemGrade g a + grade g w := by
  cases a with
  | inl c => rfl
  | inr x =>
    cases w with
    | nil => rfl
    | cons b w =>
      cases b with
      | inl c => rfl
      | inr y =>
        have hb : (x++y).length ≤ m := by simp only [grade_cons,itemGrade,List.length_append] at *; omega
        have hl := h.length (x++y) hb
        simp only [prepend,grade_cons,itemGrade,List.length_append] at *
        omega

theorem normalize_grade (g : C → ℕ) (h : Budget f m) (w : List (Item C S))
    (hm : grade g w ≤ m) : grade g (normalize f w) ≤ grade g w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have hw : grade g w ≤ m := by simp only [grade_cons] at hm; omega
    have hi := ih hw
    exact (prepend_grade g h a (normalize f w) (by simp only [grade_cons] at hm; omega)).trans
      (by simpa only [grade_cons] using Nat.add_le_add_left hi (itemGrade g a))

theorem prepend_pair (g : C → ℕ) (h : Budget f m) (x y : List S) (w : List (Item C S))
    (hm : x.length + y.length + grade g w ≤ m) :
    prepend f (.inr x) (prepend f (.inr y) w) = prepend f (.inr (f (x++y))) w := by
  cases w with
  | nil => rfl
  | cons a w =>
    cases a with
    | inl c => rfl
    | inr z =>
      simp only [prepend]
      congr 2
      apply triple h x y z
      simp only [grade_cons,itemGrade,List.length_append] at *
      omega

/-- Left contexts commute with equality of folded normal forms, without any
    stability-of-sector-boundaries claim. -/
theorem normalize_left_context {u v : List (Item C S)} (h : normalize f u = normalize f v)
    (a : List (Item C S)) : normalize f (a++u) = normalize f (a++v) := by
  induction a with
  | nil => exact h
  | cons a w ih => simpa only [List.cons_append,normalize_cons] using congrArg (prepend f a) ih

/-- Contextual invariance of pair versus its genuine returned singleton; this
    is the only nontrivial comparison at q_ok--cleanup with entry priority. -/
theorem pair_context (g : C → ℕ) (h : Budget f m) (x y : List S) (a b : List (Item C S))
    (hm : grade g (a ++ .inr x :: .inr y :: b) ≤ m) :
    normalize f (a ++ .inr x :: .inr y :: b) =
      normalize f (a ++ .inr (f (x++y)) :: b) := by
  apply normalize_left_context
  simp only [normalize_cons]
  apply prepend_pair g h
  have hb : grade g b ≤ m := by simp only [grade_append,grade_cons,itemGrade] at hm; omega
  have hi := normalize_grade g h b hb
  simp only [grade_append,grade_cons,itemGrade] at hm
  omega

/-- On one full raw sector the evaluator never calls the program. -/
@[simp] theorem normalize_singleton (x : List S) :
    normalize f ([.inr x] : List (Item C S)) = [.inr x] := rfl

/-- On a raw run of size at least two this fold is exactly a single application
    to the literal concatenation, as specified by the frozen source. -/
theorem normalize_run (h : Budget f m) (x y : List S) (ws : List (List S))
    (hm : (x++y++ws.flatten).length ≤ m) :
    normalize f (((x::y::ws).map Sum.inr) : List (Item C S)) =
      [.inr (f (x++y++ws.flatten))] := by
  induction ws generalizing x y with
  | nil => simp [prepend]
  | cons z ws ih =>
    have hb : (y++z++ws.flatten).length ≤ m := by
      simp only [List.flatten_cons,List.length_append] at hm ⊢
      omega
    rw [List.map_cons,normalize_cons,ih y z hb]
    simp only [prepend]
    congr 2
    simpa [List.append_assoc] using h.context x (y++z++ws.flatten) []
      (by simpa [List.append_assoc] using hm)

/-- Split off the entire initial raw run, without changing raw contents. -/
def splitRun : List (Item C S) → List (List S) × List (Item C S)
  | [] => ([],[])
  | .inl c::w => ([],.inl c::w)
  | .inr x::w => let p := splitRun w; (x::p.1,p.2)

@[simp] theorem splitRun_join (w : List (Item C S)) :
    (splitRun w).1.map .inr ++ (splitRun w).2 = w := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp_all [splitRun]

theorem splitRun_length (w : List (Item C S)) : (splitRun w).2.length ≤ w.length := by
  have hh := congrArg List.length (splitRun_join w)
  simp only [List.length_append,List.length_map] at hh
  omega

theorem splitRun_stops (w : List (Item C S)) :
    (splitRun w).2 = [] ∨ ∃ c t, (splitRun w).2 = .inl c::t := by
  induction w with
  | nil => exact .inl rfl
  | cons a w ih =>
    cases a with
    | inl c => exact .inr ⟨c,w,rfl⟩
    | inr x => exact ih

@[simp] theorem grade_raws (g : C → ℕ) (ws : List (List S)) :
    grade g (ws.map (Sum.inr : List S → Item C S)) = ws.flatten.length + 3*ws.length := by
  induction ws with
  | nil => simp
  | cons w ws ih => simp only [List.map_cons,grade_cons,itemGrade,ih,List.flatten_cons,
      List.length_append,List.length_cons]; omega

theorem prepend_append_separator (a : Item C S) (u v : List (Item C S)) (c : C) :
    prepend f a (u ++ .inl c::v) = prepend f a u ++ .inl c::v := by
  cases a <;> cases u with
  | nil => rfl
  | cons b w => cases b <;> rfl

theorem normalize_append_separator (u v : List (Item C S)) (c : C) :
    normalize f (u ++ .inl c::v) = normalize f u ++ .inl c::normalize f v := by
  induction u with
  | nil => rfl
  | cons a w ih =>
    simp only [List.cons_append,normalize_cons,ih,prepend_append_separator]

/-- The literal source algorithm: a singleton does not invoke f; every longer
    maximal raw run invokes f once on its unmodified concatenation. -/
def source (f : List S → List S) : List (Item C S) → List (Item C S)
  | [] => []
  | .inl c::w => .inl c::source f w
  | .inr x::w =>
    let p := splitRun w
    let z := match p.1 with
      | [] => x
      | _::_ => f (x++p.1.flatten)
    .inr z :: source f p.2
termination_by w => w.length
decreasing_by
  · simp_wf
  · have := splitRun_length w
    simp_wf
    omega

/-- Bounded comparison with the fold is a theorem, not an alteration of the
    source algorithm. In particular source calls obey the same grade budget. -/
theorem source_eq_normalize (g : C → ℕ) (h : Budget f m) (w : List (Item C S))
    (hm : grade g w ≤ m) : source f w = normalize f w := by
  cases w with
  | nil => simp [source]
  | cons a w =>
    cases a with
    | inl c =>
      have hb : grade g w ≤ m := by simp only [grade_cons] at hm; omega
      simp only [source,normalize_cons,prepend,source_eq_normalize g h w hb]
    | inr x =>
      obtain ⟨ys,t,he⟩ : ∃ ys t, splitRun w = (ys,t) := ⟨_,_,rfl⟩
      have hj : ys.map (Sum.inr : List S → Item C S) ++ t = w := by
        simpa only [he] using splitRun_join w
      have ht : t.length ≤ w.length := by simpa only [he] using splitRun_length w
      have hs : t = [] ∨ ∃ c u, t = .inl c::u := by simpa only [he] using splitRun_stops w
      have hb : grade g t ≤ m := by
        rw [← hj] at hm
        simp only [grade_cons,grade_append,itemGrade] at hm
        omega
      have hi := source_eq_normalize g h t hb
      rw [source,he]
      dsimp only
      rw [hi,← hj]
      cases ys with
      | nil =>
        rcases hs with rfl | ⟨c,u,rfl⟩ <;> rfl
      | cons y ys =>
        have hl : (x++y++ys.flatten).length ≤ m := by
          rw [← hj] at hm
          simp only [grade_cons,itemGrade,grade_append,grade_raws,List.flatten_cons,
            List.length_cons,List.length_append] at hm ⊢
          omega
        have hr := normalize_run (C := C) h x y ys hl
        rcases hs with rfl | ⟨c,u,rfl⟩
        · simpa only [List.append_nil,normalize_nil,List.map_cons,List.flatten_cons,
            List.append_assoc] using hr.symm
        · rw [← List.cons_append,← List.map_cons,normalize_append_separator,hr]
          simp only [List.flatten_cons,List.append_assoc,normalize_cons,prepend,
            List.singleton_append]
termination_by w.length
decreasing_by
  all_goals simp_all only [List.length_cons]
  all_goals omega

end FiniteAlgebraicEnvelopes.Compiler.RawRuns

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
variable {H B T K : Type*}

/-- Only a change of representation. The cell order and both literal boundary
    flags are retained exactly. -/
def literal (m : H → K) (v : Sector H B T) : Path.Sector (B×T) K :=
  ⟨v.left,m v.head,v.right,v.leftBoundary,v.rightBoundary⟩

def unliteral (v : Path.Sector (B×T) H) : Sector H B T :=
  ⟨v.left,v.head,v.right,v.leftBoundary,v.rightBoundary⟩

@[simp] theorem literal_unliteral (v : Path.Sector (B×T) H) : literal id (unliteral v) = v := by
  cases v; rfl
@[simp] theorem unliteral_literal (v : Sector H B T) : unliteral (literal id v) = v := by
  cases v; rfl

namespace Literal
open _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path

inductive Rule (table : Table H B T) (m : H → K) :
    List (Letter (B×T) K) → List (Letter (B×T) K) → Prop
  | cell (q : H) (b : B) (t : T) (i : Instruction H T) (h : table.cell q b t = some i) :
      Rule table m
        (headed (inLeft (table.direction q) (b,t)) (m q) (inRight (table.direction q) (b,t)) false false)
        (headed (outLeft (table.direction q) i.cross (b,i.tag)) (m i.head)
          (outRight (table.direction q) i.cross (b,i.tag)) false false)
  | left (q q' : H) (hd : table.direction q = .left) (h : table.boundary q = some q') :
      Rule table m [.enter,.head (m q)] [.enter,.head (m q')]
  | right (q q' : H) (hd : table.direction q = .right) (h : table.boundary q = some q') :
      Rule table m [.head (m q),.leave] [.head (m q'),.leave]

 theorem cell_step (table : Table H B T) (q : H) (b : B) (t : T)
    (i : Instruction H T) (h : table.cell q b t = some i)
    (l r : List (B×T)) (lb rb : Bool) :
    Step table
      ⟨inLeft (table.direction q) (b,t)++l,q,inRight (table.direction q) (b,t)++r,lb,rb⟩
      ⟨outLeft (table.direction q) i.cross (b,i.tag)++l,i.head,
        outRight (table.direction q) i.cross (b,i.tag)++r,lb,rb⟩ := by
  cases hd : table.direction q <;> cases hc : i.cross <;>
    simp [Step,step,inLeft,inRight,outLeft,outRight,hd,hc,h]

 theorem rule_shape (table : Table H B T) (m : H → K) {u v : List (Letter (B×T) K)}
    (h : Rule table m u v) : shape u = shape v := by
  cases h with
  | cell => simp
  | left => simp [typeOf]
  | right => simp [typeOf]

variable [DecidableEq B] [DecidableEq T] [DecidableEq K]

/-- Sector invariance for a deterministic table implies literal invariance for
    every cell and boundary equation in every word context. -/
theorem prepare_rule (table : Table H B T) (m : H → K)
    (P : Path.Sector (B×T) K → List (Path.Sector (B×T) K))
    (hinv : ∀ v w, Step table v w → P (literal m v) = P (literal m w))
    {u v : List (Letter (B×T) K)} (h : Rule table m u v)
    (x y : List (Letter (B×T) K)) (hn : shape (x++u++y) ≠ .zero) :
    prepare P (x++u++y) = prepare P (x++v++y) := by
  cases h with
  | cell q b t i hi =>
    apply prepare_context_headed P x y _ _ _ _ _ _ hn
    intro l r lb rb
    exact hinv _ _ (cell_step table q b t i hi l r lb rb)
  | left q q' hd hi =>
    apply prepare_context_left_boundary P x y _ _ hn
    intro r rb
    exact hinv ⟨[],q,r,true,rb⟩ ⟨[],q',r,true,rb⟩ (by simp [Step,step,hd,hi])
  | right q q' hd hi =>
    apply prepare_context_right_boundary P x y _ _ hn
    intro l lb
    exact hinv ⟨l,q,[],lb,true⟩ ⟨l,q',[],lb,true⟩ (by simp [Step,step,hd,hi])

end Literal
end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Word

section
open _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path
variable {S Γ Q : Type*}

abbrev Cell (S Γ : Type*) := Base S × Tag S Γ
abbrev Head (S Q : Type*) := Surface.Head (Control.Head S Q)
abbrev Letter (S Γ Q : Type*) := Path.Letter (Cell S Γ) (Head S Q)
abbrev Sector (S Γ Q : Type*) := Path.Sector (Cell S Γ) (Head S Q)

def encode (v : Surface.Sector S Γ (Control.Head S Q)) : List (Letter S Γ Q) :=
  Path.encode (Scan.literal id v)

/-- The actual source equations, separate from the exceptional accepting exit
    for which only the *complete* raw-run evaluator is invariant. -/
inductive Ordinary (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
    [DecidableEq S] [DecidableEq Γ] : List (Letter S Γ Q) → List (Letter S Γ Q) → Prop
  | raw (a : S) : Ordinary A M
      [.left (Validator.cell A.blank (.anchor a)),.head .raw]
      [.head .raw,.right (Validator.cell A.blank (.anchor a))]
  | merge : Ordinary A M [.head .raw,.leave,.enter,.head .raw]
      [.left (Validator.cell A.blank .cutC),.head .pending,.right (Validator.cell A.blank .cutD)]
  | quota : Ordinary A M
      [.left (Validator.cell A.blank .workspace),.head .pending,.right (Validator.cell A.blank .cutD)]
      [.head .pending,.right (Validator.cell A.blank .cutD)]
  | entry : Ordinary A M [.head .pending,.right (Validator.cell A.blank .cutD)]
      [.head (.internal .initial),.right (Validator.cell A.blank .cutD)]
  | internal {u v} (h : Scan.Literal.Rule (Control.table A M) Surface.Head.internal u v) :
      Ordinary A M u v
  | clean (c : Cell S Γ) : Ordinary A M [.left c,.head .cleanup]
      ([.head .cleanup]++((Cleanup.emit c).toList.map (Cleanup.letter A.blank)).map .right)
  | finish : Ordinary A M [.enter,.head .cleanup] [.enter,.head .raw]

inductive Rule (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
    [DecidableEq S] [DecidableEq Γ] : List (Letter S Γ Q) → List (Letter S Γ Q) → Prop
  | zero {u v} (h : Path.ZeroStep u v) : Rule A M u v
  | ordinary {u v} (h : Ordinary A M u v) : Rule A M u v
  | exit : Rule A M [.head (.internal (.machine .ok)),.leave] [.head .cleanup,.leave]

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

 theorem ordinary_shape {u v : List (Letter S Γ Q)} (h : Ordinary A M u v) : shape u = shape v := by
  cases h with
  | internal h => exact Scan.Literal.rule_shape _ _ h
  | clean c => cases he : Cleanup.emit c <;> simp [Cleanup.letter,typeOf]
  | raw => simp [typeOf]
  | merge => simp [typeOf]
  | quota => simp [typeOf]
  | entry => simp [typeOf]
  | finish => simp [typeOf]

 theorem rule_shape {u v : List (Letter S Γ Q)} (h : Rule A M u v) : shape u = shape v := by
  cases h with
  | ordinary h => exact ordinary_shape A M h
  | zero h => cases h with | pair a b h => simpa [typeOf] using h
  | exit => simp [typeOf]

variable [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
  [LinearOrder (Control.Sector S Γ Q)]

def sectorPreprocess (v : Sector S Γ Q) : List (Sector S Γ Q) :=
  (Surface.preprocess A M (Scan.unliteral v)).map (Scan.literal id)

def preprocess (w : List (Letter S Γ Q)) : List (List (Letter S Γ Q)) :=
  Path.prepare (sectorPreprocess A M) w

@[simp] theorem sectorPreprocess_literal (v : Surface.Sector S Γ (Control.Head S Q)) :
    sectorPreprocess A M (Scan.literal id v) = (Surface.preprocess A M v).map (Scan.literal id) := by
  simp [sectorPreprocess]

/-- Every ordinary source equation has identical preprocessed sector lists in
    any literal nonzero context. Only the accepting exit needs a program law. -/
theorem preprocess_ordinary {u v : List (Letter S Γ Q)} (h : Ordinary A M u v)
    (x y : List (Letter S Γ Q)) (hn : shape (x++u++y) ≠ .zero) :
    preprocess A M (x++u++y) = preprocess A M (x++v++y) := by
  unfold preprocess
  cases h with
  | raw a =>
    apply Path.prepare_context_headed (sectorPreprocess A M) x y
      [Validator.cell A.blank (.anchor a)] [] [] [Validator.cell A.blank (.anchor a)] .raw .raw hn
    intro l r lb rb
    exact congrArg (fun z => z.map (Scan.literal id))
      (Surface.preprocess_rawStep A M (.slide a l r lb rb))
  | merge =>
    apply Path.prepare_context_merge (sectorPreprocess A M) x y .raw .pending _ _ hn
    intro l r lb rb
    change (Surface.pendingPreprocess A.blank
      ⟨Validator.cell A.blank .cutC::l,.pending,Validator.cell A.blank .cutD::r,lb,rb⟩).map _ = _
    rw [show Validator.cell A.blank .cutC::l =
      List.replicate 0 (Validator.cell A.blank .workspace)++Validator.cell A.blank .cutC::l by rfl,
      Surface.pendingPreprocess_merge]
    rfl
  | quota =>
    apply Path.prepare_context_headed (sectorPreprocess A M) x y
      [Validator.cell A.blank .workspace] [] [Validator.cell A.blank .cutD]
      [Validator.cell A.blank .cutD] .pending .pending hn
    intro l r lb rb
    exact congrArg (fun z => z.map (Scan.literal id))
      (Surface.preprocess_quotaStep A M (.trim l r lb rb))
  | entry =>
    apply Path.prepare_context_headed (sectorPreprocess A M) x y [] []
      [Validator.cell A.blank .cutD] [Validator.cell A.blank .cutD] .pending (.internal .initial) hn
    intro l r lb rb
    exact congrArg (fun z => z.map (Scan.literal id)) (Surface.preprocess_entryStep A M l r lb rb)
  | internal h =>
    apply Scan.Literal.prepare_rule _ _ _ ?_ h x y hn
    intro v w hvw
    exact congrArg (fun z => z.map (Scan.literal id)) (Surface.preprocess_internalStep A M hvw)
  | clean c =>
    have hinv := fun l r lb rb => congrArg (fun z => z.map (Scan.literal id))
      (Surface.preprocess_cleanupStep A M (v := ⟨c::l,.cleanup,r,lb,rb⟩)
        (w := ⟨l,.cleanup,(Cleanup.emit c).toList.map (Cleanup.letter A.blank)++r,lb,rb⟩) rfl)
    have hh := Path.prepare_context_headed (sectorPreprocess A M) x y [c] [] []
      ((Cleanup.emit c).toList.map (Cleanup.letter A.blank)) .cleanup .cleanup
    simpa [Path.headed] using hh (by simpa [Path.headed] using hn) hinv
  | finish =>
    apply Path.prepare_context_left_boundary (sectorPreprocess A M) x y .cleanup .raw hn
    intro r rb
    exact congrArg (fun z => z.map (Scan.literal id))
      (Surface.preprocess_cleanupStep A M (v := ⟨[],.cleanup,r,true,rb⟩)
        (w := ⟨[],.raw,r,true,rb⟩) rfl)

end

section
open Relation
variable {S Γ Q : Type*}

def gradeCell (c : Cell S Γ) : ℕ := Cleanup.grade c.1
def grade (w : List (Letter S Γ Q)) : ℕ := Path.grade gradeCell w
def chunksGrade (ws : List (List (Letter S Γ Q))) : ℕ := (ws.map grade).sum

@[simp] theorem grade_encode (v : Surface.Sector S Γ (Control.Head S Q)) :
    grade (encode v) = Surface.grade v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  simp [grade,encode,Scan.literal,Path.encode,Path.grade_headed,Surface.grade,
    Cleanup.cellsGrade,Function.comp_def]
  rfl

@[simp] theorem grade_append (u v : List (Letter S Γ Q)) : grade (u++v) = grade u+grade v :=
  Path.grade_append _ _ _

@[simp] theorem chunksGrade_append (u v : List (List (Letter S Γ Q))) :
    chunksGrade (u++v) = chunksGrade u+chunksGrade v := by simp [chunksGrade]

@[simp] theorem chunksGrade_flatten (ws : List (List (Letter S Γ Q))) :
    grade ws.flatten = chunksGrade ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [List.flatten_cons,chunksGrade,ih]

@[simp] theorem grade_raw (b : Γ) (w : List S) :
    grade (encode (Surface.raw (H := Control.Head S Q) b w)) = w.length + 3 := by
  rw [grade_encode]
  simp [Surface.raw,Surface.grade,Cleanup.cellsGrade,Validator.cell,Cleanup.grade,List.map_map,
    Function.comp_def]
  omega

variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

 theorem sectorPreprocess_grade (v : Sector S Γ Q) :
    chunksGrade ((sectorPreprocess A M v).map Path.encode) ≤ grade (Path.encode v) := by
  have h := Surface.preprocess_grade A M (Scan.unliteral v)
  have he : Path.encode v = encode (Scan.unliteral v) := by simp [encode]
  rw [he,grade_encode]
  simpa only [chunksGrade,sectorPreprocess,List.map_map,Function.comp_def,
    show (fun x : Surface.Sector S Γ (Control.Head S Q) => grade (Path.encode (Scan.literal id x))) =
      Surface.grade from funext grade_encode,Surface.listGrade] using h

 theorem prepareChunk_grade (w : List (Letter S Γ Q)) :
    chunksGrade (Path.prepareChunk (sectorPreprocess A M) w) ≤ grade w := by
  cases he : Path.decode w with
  | none => simp [Path.prepareChunk,he,chunksGrade]
  | some v =>
    have hw := Path.decode_sound he
    rw [←hw]
    simpa using sectorPreprocess_grade A M v

 theorem prepareChunks_grade (ws : List (List (Letter S Γ Q))) :
    chunksGrade (Path.prepareChunks (sectorPreprocess A M) ws) ≤ chunksGrade ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simpa only [Path.prepareChunks,List.flatMap_cons,chunksGrade_append,
      chunksGrade,List.map_cons,List.sum_cons,List.map_append,List.sum_append] using Nat.add_le_add (prepareChunk_grade A M w) ih

 theorem preprocess_grade (w : List (Letter S Γ Q)) :
    chunksGrade (preprocess A M w) ≤ grade w := by
  have h := prepareChunks_grade A M (Path.cuts w)
  simpa only [preprocess,Path.prepare,← chunksGrade_flatten,Path.flatten_cuts] using h

end

variable {S Γ Q : Type*} (blank : Γ)

def raw (w : List S) : List (Letter S Γ Q) := encode (Surface.raw blank w)

/-- Candidate extraction followed by a literal check recognizes *only* full,
    clean raw sectors. Dirty tags or absent boundaries cannot silently pass. -/
def rawLetters (w : List (Letter S Γ Q)) : List S := w.filterMap fun a =>
  match a with
  | .right (.anchor s,_) => some s
  | _ => none

@[simp] theorem rawLetters_raw (w : List S) : rawLetters (raw (Q := Q) blank w) = w := by
  simp [raw,encode,Scan.literal,Path.encode,Surface.raw,Path.headed,rawLetters,
    List.filterMap_append,List.filterMap_map,Validator.cell,Function.comp_def]

variable [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]

def readRaw (w : List (Letter S Γ Q)) : Option (List S) :=
  let x := rawLetters w
  if raw blank x = w then some x else none

@[simp] theorem readRaw_raw (w : List S) : readRaw blank (raw (Q := Q) blank w) = some w := by
  simp [readRaw]

 theorem readRaw_sound {w : List (Letter S Γ Q)} {x : List S} (h : readRaw blank w = some x) :
    raw blank x = w := by
  dsimp only [readRaw] at h
  split at h
  · cases h; assumption
  · cases h

abbrev Item (S Γ Q : Type*) := RawRuns.Item (List (Letter S Γ Q)) S

def classify (w : List (Letter S Γ Q)) : Item S Γ Q :=
  match readRaw blank w with
  | some x => .inr x
  | none => .inl w

def realize : Item S Γ Q → List (Letter S Γ Q)
  | .inl w => w
  | .inr x => raw blank x

@[simp] theorem classify_raw (w : List S) : classify blank (raw (Q := Q) blank w) = .inr w := by
  simp [classify]

@[simp] theorem realize_classify (w : List (Letter S Γ Q)) : realize blank (classify blank w) = w := by
  unfold classify
  cases he : readRaw blank w with
  | none => rfl
  | some x => exact readRaw_sound blank he

@[simp] theorem itemGrade_classify (w : List (Letter S Γ Q)) :
    RawRuns.itemGrade grade (classify blank w) = grade w := by
  unfold classify
  cases he : readRaw blank w with
  | none => rfl
  | some x => rw [←readRaw_sound blank he]; exact (grade_raw blank x).symm

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] in
@[simp] theorem grade_realize (w : Item S Γ Q) :
    grade (realize blank w) = RawRuns.itemGrade grade w := by
  cases w with
  | inl w => rfl
  | inr x => exact grade_raw blank x

@[simp] theorem classify_grade (ws : List (List (Letter S Γ Q))) :
    RawRuns.grade grade (ws.map (classify blank)) = chunksGrade ws := by
  simp only [RawRuns.grade,List.map_map,Function.comp_def,itemGrade_classify,chunksGrade]

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] in
@[simp] theorem realizeList_grade (ws : List (Item S Γ Q)) :
    grade (ws.flatMap (realize blank)) = RawRuns.grade grade ws := by
  rw [List.flatMap_def,chunksGrade_flatten]
  simp only [chunksGrade,List.map_map,Function.comp_def,grade_realize,RawRuns.grade]

end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.Compiler.Surface
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- The exact exceptional comparison. When entry priority changes the answer,
    both boundaries really exist, and a bounded run of the specified machine
    returns the output of cleanup. No program equation is assumed here. -/
theorem exit_alternative
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    (l : Cells S Γ) (lb : Bool) :
    preprocess A M ⟨l,.internal (.machine .ok),[],lb,true⟩ =
      preprocess A M ⟨l,.cleanup,[],lb,true⟩ ∨
    ∃ x y out n c,
      preprocess A M ⟨l,.internal (.machine .ok),[],lb,true⟩ =
        [raw A.blank x,raw A.blank y] ∧
      preprocess A M ⟨l,.cleanup,[],lb,true⟩ = [raw A.blank out] ∧
      ReflTransGen (Simulator.TapeStep M)
        (Simulator.pad A (Simulator.initialTape A M (x++y)) (n+1)) c ∧
      Simulator.Halted A M c ∧ Simulator.Returns A c out := by
  let v : Control.Sector S Γ Q := ⟨l,.machine .ok,[],lb,true⟩
  by_cases he : ∃ w, EqvGen (Scan.Step (Control.table A M)) v w ∧ Control.Entry A.blank w
  · obtain ⟨w,hw,hwe⟩ := he
    obtain ⟨a,ha,rfl⟩ := Control.entry_cases A.blank hwe
    have hc := Control.cfg_connected A M (EqvGen.symm _ _ hw)
    change EqvGen (Compiled.Step A M) (Control.toCfg (Control.validator a))
      (Control.toCfg (Control.machine ⟨l,.ok,[],lb,true⟩)) at hc
    rw [Control.cfg_validator,Control.cfg_machine] at hc
    obtain ⟨x,y,s,n,c,out,result,rfl,_,hr,hh,ho,_,hb,hclean⟩ :=
      Compiled.accepting_entry_sound A M hdecode ha rfl hc
    right
    refine ⟨x,y,out,n,c,?_,?_,hr,hh,ho⟩
    · change internalPreprocess A M v = _
      rw [internalPreprocess_invariant A M hw,
        internalPreprocess_entry A M _ (Control.entry_validator A.blank ha)]
      exact pendingPreprocess_cleanEntry A x y s
    · have hn := cleanupPreprocess_invariant (H := Control.Head S Q) A.blank
        (EqvGen.reflTransGen_le_eqvGen _ _ _ hclean)
      have he : (⟨l,.cleanup,[],lb,true⟩ : Cleanup.Sector S Γ) =
          ⟨result.reverse,.cleanup,[],true,true⟩ := by
        have h₁ := congrArg (fun v : Compiled.MachineSector S Γ Q => v.left) hb
        have h₂ := congrArg (fun v : Compiled.MachineSector S Γ Q => v.leftBoundary) hb
        simp only at h₁ h₂
        subst l; subst lb; rfl
      rw [←he] at hn
      change [cleanupPreprocess A.blank (ofCleanup ⟨l,.cleanup,[],lb,true⟩)] = _
      rw [hn]
      rfl
  · left
    exact internalPreprocess_success A M v ⟨rfl,rfl,rfl⟩ he

end FiniteAlgebraicEnvelopes.Compiler.Surface

namespace FiniteAlgebraicEnvelopes.Compiler.Word
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- The source algorithm, with the partial call separated as f. Its actual
    computable domain/realization is established at the program boundary. -/
def normal (f : List S → List S) (w : List (Letter S Γ Q)) : List (Letter S Γ Q) :=
  if Path.shape w = .zero then [.zero] else
    (RawRuns.source f ((preprocess A M w).map (classify A.blank))).flatMap (realize A.blank)

theorem normal_eq_fold {f : List S → List S} {m : ℕ} (h : RawRuns.Budget f m)
    (w : List (Letter S Γ Q)) (hn : Path.shape w ≠ .zero) (hm : grade w ≤ m) :
    normal A M f w =
      (RawRuns.normalize f ((preprocess A M w).map (classify A.blank))).flatMap (realize A.blank) := by
  rw [normal,ite_eq_right hn,RawRuns.source_eq_normalize grade h]
  exact (by rw [classify_grade]; exact (preprocess_grade A M w).trans hm)

theorem normal_ordinary (f : List S → List S) {u v : List (Letter S Γ Q)}
    (h : Ordinary A M u v) (x y : List (Letter S Γ Q)) :
    normal A M f (x++u++y) = normal A M f (x++v++y) := by
  have hs := Path.shape_context (ordinary_shape A M h) x y
  by_cases hn : Path.shape (x++u++y) = .zero
  · simp only [normal,hn,←hs,ite_eq_left]
  · simp only [normal,hn,←hs,ite_false,preprocess_ordinary A M h x y hn]

theorem normal_zero (f : List S → List S) {u v : List (Letter S Γ Q)}
    (h : Path.ZeroStep u v) (x y : List (Letter S Γ Q)) :
    normal A M f (x++u++y) = normal A M f (x++v++y) := by
  have h₁ : Path.shape (x++u++y) = .zero := by
    cases h with
    | pair a b h => simp only [Path.shape_append,Path.shape_cons,Path.shape_nil,
        Path.mul_unit,h,Path.mul_zero,Path.zero_mul]
  have h₂ := Path.shape_context (rule_shape A M (.zero h)) x y
  simp only [normal,h₁,←h₂,ite_eq_left]

@[simp] theorem preprocess_raw (w : List S) : preprocess A M (raw (Q := Q) A.blank w) =
    [raw A.blank w] := by
  unfold preprocess raw encode Path.prepare Path.encode
  rw [Path.cuts_headed]
  change Path.prepareChunks (sectorPreprocess A M) [Path.encode (Scan.literal id (Surface.raw A.blank w))] = _
  rw [Path.prepareChunks_singleton,sectorPreprocess_literal]
  rfl

@[simp] theorem normal_raw (f : List S → List S) (w : List S) :
    normal A M f (raw (Q := Q) A.blank w) = raw A.blank w := by
  have hn : Path.shape (raw (Q := Q) A.blank w) ≠ .zero := by
    simp [raw,encode,Path.encode]
  simp [normal,hn,RawRuns.source,RawRuns.splitRun,realize]

/-- Finite tape realization at a bound. This is a *lemma parameter*, not an
    assumption of either main theorem; the partial-recursive adapter must prove it. -/
def ComputesAt (f : List S → List S) (m : ℕ) : Prop :=
  ∀ w, w.length ≤ m → ∃ c,
    ReflTransGen (Simulator.UnboundedStep A M) (Simulator.initialTape A M w) c ∧
    Simulator.Halted A M c ∧ Simulator.Returns A c (f w)

theorem normal_exit
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} {m : ℕ} (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    (a b : List (Letter S Γ Q))
    (h₁ : grade (a++[.head (.internal (.machine .ok)),.leave]++b) ≤ m)
    (h₂ : grade (a++[.head .cleanup,.leave]++b) ≤ m) :
    normal A M f (a++[.head (.internal (.machine .ok)),.leave]++b) =
      normal A M f (a++[.head .cleanup,.leave]++b) := by
  have hs := Path.shape_context (rule_shape A M .exit) a b
  by_cases hn : Path.shape (a++[.head (.internal (.machine .ok)),.leave]++b) = .zero
  · simp only [normal,hn,←hs,ite_eq_left]
  have hn₂ : Path.shape (a++[.head .cleanup,.leave]++b) ≠ .zero := by rwa [←hs]
  obtain ⟨cs,ds,l,lb,hframe⟩ := Path.right_boundary_frame a b (.internal (.machine .ok)) hn
  have hf : ∀ q : Head S Q, preprocess A M (a++[.head q,.leave]++b) =
      Path.prepareChunks (sectorPreprocess A M) cs ++
      (Surface.preprocess A M ⟨l,q,[],lb,true⟩).map encode ++
      Path.prepareChunks (sectorPreprocess A M) ds := by
    intro q
    simp only [preprocess,Path.prepare,hframe,Path.prepareChunks_append]
    change _ ++ Path.prepareChunks (sectorPreprocess A M) [Path.encode (Scan.literal id ⟨l,q,[],lb,true⟩)] ++ _ = _
    rw [Path.prepareChunks_singleton,sectorPreprocess_literal]
    simp only [List.map_map,Function.comp_def]
    rfl
  rcases Surface.exit_alternative A M hdecode l lb with he | ⟨x,y,out,n,c,hx,hy,hr,hh,ho⟩
  · simp only [normal,ite_eq_right hn,ite_eq_right hn₂,hf,he]
  · let p := (Path.prepareChunks (sectorPreprocess A M) cs).map (classify A.blank)
    let q := (Path.prepareChunks (sectorPreprocess A M) ds).map (classify A.blank)
    have hp : (preprocess A M (a++[.head (.internal (.machine .ok)),.leave]++b)).map
        (classify A.blank) = p ++ .inr x :: .inr y :: q := by
      simp only [hf,hx,List.map_cons,List.map_nil,List.map_append]
      change p ++ [classify A.blank (raw A.blank x),classify A.blank (raw A.blank y)] ++ q = _
      simp [List.append_assoc]
    have hq : (preprocess A M (a++[.head .cleanup,.leave]++b)).map (classify A.blank) =
        p ++ .inr out :: q := by
      simp only [hf,hy,List.map_cons,List.map_nil,List.map_append]
      change p ++ [classify A.blank (raw A.blank out)] ++ q = _
      simp [List.append_assoc]
    have hbound : RawRuns.grade grade (p ++ .inr x :: .inr y :: q) ≤ m := by
      rw [←hp,classify_grade]
      exact (preprocess_grade A M _).trans h₁
    have hlen : (x++y).length ≤ m := by
      simp only [RawRuns.grade_append,RawRuns.grade_cons,RawRuns.itemGrade,List.length_append] at hbound ⊢
      omega
    obtain ⟨d,hd,hdh,hdo⟩ := hcomp (x++y) hlen
    have hout : out = f (x++y) := Simulator.returned_quota_unique A M (n+1) hr hd hh hdh ho hdo
    rw [normal_eq_fold A M h _ hn h₁,normal_eq_fold A M h _ hn₂ h₂,hp,hq,hout]
    exact congrArg (fun z => z.flatMap (realize A.blank)) (RawRuns.pair_context grade h x y p q hbound)

/-- Every literal defining equation is invariant in arbitrary word contexts,
    including dirty and incomplete sectors, within the *unchanged* grade bound. -/
theorem normal_rule
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} {m : ℕ} (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    {u v : List (Letter S Γ Q)} (hr : Rule A M u v) (a b : List (Letter S Γ Q))
    (h₁ : grade (a++u++b) ≤ m) (h₂ : grade (a++v++b) ≤ m) :
    normal A M f (a++u++b) = normal A M f (a++v++b) := by
  cases hr with
  | zero hr => exact normal_zero A M f hr a b
  | ordinary hr => exact normal_ordinary A M f hr a b
  | exit => exact normal_exit A M hdecode h hcomp a b h₁ h₂

end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.Compiler.Scan.Literal
open _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path
variable {H B T K : Type*}

theorem encode_step (table : Table H B T) (m : H → K) {v w : Sector H B T}
    (h : Step table v w) :
    Context (Rule table m) (Path.encode (literal m v)) (Path.encode (literal m w)) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  unfold Step step at h
  cases hd : table.direction q <;> simp only [hd] at h
  · cases l with
    | nil =>
      cases lb <;> simp only [Bool.false_eq_true,↓reduceIte] at h
      · contradiction
      · obtain ⟨q',hq,rfl⟩ := Option.map_eq_some_iff.mp h
        have hh := Context.apply [] (r.map .right++(if rb then [.leave] else []))
          (Rule.left (table := table) (m := m) q q' hd hq)
        simp only [Path.encode,literal,headed,List.nil_append,List.append_nil,
          List.map_nil,List.reverse_nil,ite_true,List.singleton_append,List.append_assoc] at hh ⊢
        exact hh
    | cons c l =>
      rcases c with ⟨b,t⟩
      obtain ⟨i,hi,rfl⟩ := Option.map_eq_some_iff.mp h
      have hh := context_headed (Rule.cell (table := table) (m := m) q b t i hi) l r lb rb
      cases hc : i.cross <;>
        simpa [Path.encode,literal,inLeft,inRight,outLeft,outRight,hd,hc] using hh
  · cases r with
    | nil =>
      cases rb <;> simp only [Bool.false_eq_true,↓reduceIte] at h
      · contradiction
      · obtain ⟨q',hq,rfl⟩ := Option.map_eq_some_iff.mp h
        have hh := Context.apply ((if lb then [.enter] else [])++l.reverse.map .left) []
          (Rule.right (table := table) (m := m) q q' hd hq)
        simp only [Path.encode,literal,headed,List.append_nil,
          List.map_nil,ite_true,List.append_assoc] at hh ⊢
        exact hh
    | cons c r =>
      rcases c with ⟨b,t⟩
      obtain ⟨i,hi,rfl⟩ := Option.map_eq_some_iff.mp h
      have hh := context_headed (Rule.cell (table := table) (m := m) q b t i hi) l r lb rb
      cases hc : i.cross <;>
        simpa [Path.encode,literal,inLeft,inRight,outLeft,outRight,hd,hc] using hh

end FiniteAlgebraicEnvelopes.Compiler.Scan.Literal

namespace FiniteAlgebraicEnvelopes.Compiler.Word
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

/-- A literal equation in either direction, used without any grade increase. -/
def Reduce (u v : List (Letter S Γ Q)) : Prop :=
  Path.Context (SymmGen (Rule A M)) u v ∧ grade v ≤ grade u
abbrev Reduces := ReflTransGen (Reduce A M)

theorem reduces_grade {u v : List (Letter S Γ Q)} (h : Reduces A M u v) : grade v ≤ grade u := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact h.2.trans ih

theorem reduce_context {u v : List (Letter S Γ Q)} (h : Reduce A M u v)
    (x y : List (Letter S Γ Q)) : Reduce A M (x++u++y) (x++v++y) := by
  refine ⟨Path.context_context h.1 x y,?_⟩
  simpa only [grade_append] using Nat.add_le_add_right (Nat.add_le_add_left h.2 (grade x)) (grade y)

theorem reduces_context {u v : List (Letter S Γ Q)} (h : Reduces A M u v)
    (x y : List (Letter S Γ Q)) : Reduces A M (x++u++y) (x++v++y) :=
  h.lift (fun w => x++w++y) (fun _ _ hh => reduce_context A M hh x y)

theorem reduces_append {u v x y : List (Letter S Γ Q)}
    (h₁ : Reduces A M u v) (h₂ : Reduces A M x y) : Reduces A M (u++x) (v++y) := by
  have ha : Reduces A M (u++x) (v++x) := by simpa using reduces_context A M h₁ [] x
  have hb : Reduces A M (v++x) (v++y) := by simpa using reduces_context A M h₂ v []
  exact ha.trans hb

variable [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
  [LinearOrder (Control.Sector S Γ Q)]

theorem normal_reduce
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} {m : ℕ} (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    {u v : List (Letter S Γ Q)} (hr : Reduce A M u v) (hm : grade u ≤ m) :
    normal A M f u = normal A M f v := by
  have hv := hr.2.trans hm
  rcases hr with ⟨hr,_⟩
  cases hr with
  | apply x y hr =>
    rcases hr with hr | hr
    · exact normal_rule A M hdecode h hcomp hr x y hm hv
    · exact (normal_rule A M hdecode h hcomp hr x y hv hm).symm

theorem normal_reduces
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} {m : ℕ} (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    {u v : List (Letter S Γ Q)} (hr : Reduces A M u v) (hm : grade u ≤ m) :
    normal A M f u = normal A M f v := by
  induction hr with
  | refl => rfl
  | tail hp hs ih => exact ih.trans (normal_reduce A M hdecode h hcomp hs ((reduces_grade A M hp).trans hm))

end FiniteAlgebraicEnvelopes.Compiler.Word

namespace FiniteAlgebraicEnvelopes.Compiler.Word

section
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

theorem internal_rule_grade {u v : List (Letter S Γ Q)}
    (h : Scan.Literal.Rule (Control.table A M) Surface.Head.internal u v) : grade u = grade v := by
  cases h with
  | cell q b t i hi =>
    cases hd : (Control.table A M).direction q <;> cases hc : i.cross <;>
      simp [grade,Path.grade_headed,Scan.Literal.inLeft,Scan.Literal.inRight,
        Scan.Literal.outLeft,Scan.Literal.outRight,gradeCell,Nat.add_comm]
  | left => rfl
  | right => rfl

theorem ordinary_grade {u v : List (Letter S Γ Q)} (h : Ordinary A M u v) : grade v ≤ grade u := by
  cases h with
  | internal h => exact (internal_rule_grade A M h).symm.le
  | clean c =>
    have hh := Cleanup.output_grade_le A.blank [c]
    simp only [Cleanup.output_singleton,Cleanup.cellsGrade,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      Nat.add_zero,Function.comp_def] at hh
    simpa [grade,Path.grade,Path.letterGrade,List.map_map,Function.comp_def,gradeCell,Nat.add_comm] using Nat.add_le_add_left hh 1
  | raw | merge | quota | entry | finish =>
    simp [grade,Path.grade,Path.letterGrade,gradeCell,Validator.cell,Cleanup.grade]

theorem rule_grade {u v : List (Letter S Γ Q)} (h : Rule A M u v) : grade v ≤ grade u := by
  cases h with
  | ordinary h => exact ordinary_grade A M h
  | zero h => exact Path.zeroStep_grade gradeCell h
  | exit => rfl

theorem reduce_rule {u v : List (Letter S Γ Q)} (h : Rule A M u v) : Reduce A M u v := by
  refine ⟨?_,rule_grade A M h⟩
  simpa using Path.Context.apply [] [] (Or.inl h : SymmGen (Rule A M) u v)

theorem reduce_rule_reverse {u v : List (Letter S Γ Q)} (h : Rule A M u v)
    (hg : grade u = grade v) : Reduce A M v u := by
  refine ⟨?_,hg.le⟩
  simpa using Path.Context.apply [] [] (Or.inr h : SymmGen (Rule A M) v u)

theorem reduce_internal {v w : Control.Sector S Γ Q} (h : Scan.Step (Control.table A M) v w) :
    Reduce A M (encode (Scan.mapHead Surface.Head.internal v))
      (encode (Scan.mapHead Surface.Head.internal w)) ∧
    Reduce A M (encode (Scan.mapHead Surface.Head.internal w))
      (encode (Scan.mapHead Surface.Head.internal v)) := by
  have hc := Scan.Literal.encode_step (Control.table A M) Surface.Head.internal h
  have hg : grade (encode (Scan.mapHead Surface.Head.internal v)) =
      grade (encode (Scan.mapHead Surface.Head.internal w)) := by
    rw [grade_encode,grade_encode]
    apply Surface.grade_eq_of_skeleton
    simpa using Scan.step_skeleton _ h
  have hf : Path.Context (SymmGen (Rule A M)) (encode (Scan.mapHead Surface.Head.internal v))
      (encode (Scan.mapHead Surface.Head.internal w)) :=
    Path.context_mono hc (fun _ _ hs => .inl (.ordinary (.internal hs)))
  refine ⟨⟨hf,hg.symm.le⟩,⟨?_,hg.le⟩⟩
  exact Path.context_symm hf

theorem reduces_internal {v w : Control.Sector S Γ Q}
    (h : EqvGen (Scan.Step (Control.table A M)) v w) :
    Reduces A M (encode (Scan.mapHead Surface.Head.internal v))
      (encode (Scan.mapHead Surface.Head.internal w)) := by
  have hh : ∀ {v w : Control.Sector S Γ Q}, EqvGen (Scan.Step (Control.table A M)) v w →
      Reduces A M (encode (Scan.mapHead Surface.Head.internal v))
        (encode (Scan.mapHead Surface.Head.internal w)) ∧
      Reduces A M (encode (Scan.mapHead Surface.Head.internal w))
        (encode (Scan.mapHead Surface.Head.internal v)) := by
    intro v w h
    induction h with
    | rel _ _ h => exact ⟨.single (reduce_internal A M h).1,.single (reduce_internal A M h).2⟩
    | refl _ => exact ⟨.refl,.refl⟩
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ⟨ih₁.1.trans ih₂.1,ih₂.2.trans ih₁.2⟩
  exact (hh h).1

theorem reduce_of_context_rule {u v : List (Letter S Γ Q)} (h : Path.Context (Rule A M) u v) :
    Reduce A M u v := by
  refine ⟨Path.context_mono h (fun _ _ hh => .inl hh),?_⟩
  cases h with
  | apply x y h =>
    simp only [grade_append]
    exact Nat.add_le_add_right (Nat.add_le_add_left (rule_grade A M h) _) _

theorem reduce_reverse {u v : List (Letter S Γ Q)} (h : Reduce A M u v)
    (hg : grade u = grade v) : Reduce A M v u := ⟨Path.context_symm h.1,hg.le⟩

theorem reduces_reverse {u v : List (Letter S Γ Q)} (h : Reduces A M u v)
    (hg : grade u = grade v) : Reduces A M v u := by
  induction h with
  | refl => exact .refl
  | @tail v w hp hs ih =>
    have h₁ := reduces_grade A M hp
    have h₂ := hs.2
    have he : grade u = grade v := by omega
    have he' : grade v = grade w := by omega
    exact (ReflTransGen.single (reduce_reverse A M hs he')).trans (ih he)

theorem reduce_headed {l₁ l₂ r₁ r₂ : List (Cell S Γ)} {q₁ q₂ : Head S Q}
    (h : Rule A M (Path.headed l₁ q₁ r₁ false false) (Path.headed l₂ q₂ r₂ false false))
    (l r : List (Cell S Γ)) (lb rb : Bool) :
    Reduce A M (encode ⟨l₁++l,q₁,r₁++r,lb,rb⟩) (encode ⟨l₂++l,q₂,r₂++r,lb,rb⟩) :=
  reduce_of_context_rule A M (Path.context_headed h l r lb rb)

theorem reduce_rawStep {v w : Surface.Sector S Γ (Control.Head S Q)}
    (h : Surface.RawStep A.blank v w) : Reduce A M (encode v) (encode w) := by
  cases h with
  | slide a l r lb rb =>
    apply reduce_headed A M (l₁ := [Validator.cell A.blank (.anchor a)]) (l₂ := [])
      (r₁ := []) (r₂ := [Validator.cell A.blank (.anchor a)]) ?_ l r lb rb
    simpa [Path.headed] using (Rule.ordinary (Ordinary.raw (A := A) (M := M) a))

theorem reduces_rawNormal (v : Surface.Sector S Γ (Control.Head S Q)) :
    Reduces A M (encode v) (encode (Surface.rawNormal A.blank v)) :=
  (Surface.rawNormal_reaches A.blank v).lift encode (fun _ _ h => reduce_rawStep A M h)

theorem reduces_quotaNormal (v : Surface.Sector S Γ (Control.Head S Q)) :
    Reduces A M (encode v) (encode (Surface.quotaNormal A.blank v)) := by
  apply (Surface.quotaNormal_reaches A.blank v).lift encode
  intro v w h
  cases h with
  | trim l r lb rb =>
    apply reduce_headed A M (l₁ := [Validator.cell A.blank .workspace]) (l₂ := [])
      (r₁ := [Validator.cell A.blank .cutD]) (r₂ := [Validator.cell A.blank .cutD]) ?_ l r lb rb
    simpa [Path.headed] using (Rule.ordinary (Ordinary.quota (A := A) (M := M)))

theorem reduce_entry (l r : List (Cell S Γ)) (lb rb : Bool) :
    Reduce A M (encode ⟨l,.pending,Validator.cell A.blank .cutD::r,lb,rb⟩)
      (encode ⟨l,.internal .initial,Validator.cell A.blank .cutD::r,lb,rb⟩) := by
  apply reduce_headed A M (l₁ := []) (l₂ := [])
    (r₁ := [Validator.cell A.blank .cutD]) (r₂ := [Validator.cell A.blank .cutD]) ?_ l r lb rb
  simpa [Path.headed] using (Rule.ordinary (Ordinary.entry (A := A) (M := M)))

theorem reduce_cleanup {v w : Cleanup.Sector S Γ} (h : Cleanup.Step A.blank v w) :
    Reduce A M (encode (Surface.ofCleanup v)) (encode (Surface.ofCleanup w)) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q with
  | raw => cases h
  | cleanup =>
    cases l with
    | nil =>
      cases lb with
      | false => cases h
      | true =>
        cases Option.some.inj h
        apply reduce_of_context_rule A M
        have hh := Path.Context.apply [] (r.map .right++(if rb then [.leave] else []))
            (Rule.ordinary (Ordinary.finish (A := A) (M := M)))
        simp only [encode,Scan.literal,Path.encode,Path.headed,Surface.ofCleanup,Scan.mapHead,Surface.cleanupHead,
          List.map_nil,List.reverse_nil,List.nil_append,List.append_nil,ite_true,
          List.singleton_append,List.append_assoc] at hh ⊢
        exact hh
    | cons c l =>
      cases Option.some.inj h
      apply reduce_headed A M (l₁ := [c]) (l₂ := []) (r₁ := [])
        (r₂ := (Cleanup.emit c).toList.map (Cleanup.letter A.blank)) ?_ l r lb rb
      simpa only [Surface.cleanupHead,Path.headed,List.map_nil,List.nil_append,List.map_cons,
        List.reverse_cons,List.reverse_nil,List.append_nil,List.singleton_append,Bool.false_eq_true,ite_false] using
          (Rule.ordinary (Ordinary.clean (A := A) (M := M) c))

theorem reduces_cleanupNormal (v : Surface.Sector S Γ (Control.Head S Q)) :
    Reduces A M (encode v) (encode (Surface.cleanupNormal A.blank v)) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q with
  | cleanup =>
    exact (Cleanup.normal_reached A.blank ⟨l,.cleanup,r,lb,rb⟩).lift
      (fun v => encode (Surface.ofCleanup v)) (fun _ _ h => reduce_cleanup A M h)
  | raw | pending | internal _ => exact .refl

theorem reduces_cleanupPreprocess (v : Surface.Sector S Γ (Control.Head S Q)) :
    Reduces A M (encode v) (encode (Surface.cleanupPreprocess A.blank v)) :=
  (reduces_cleanupNormal A M v).trans (reduces_rawNormal A M _)

theorem reduce_unmerge (l r : List (Cell S Γ)) (lb rb : Bool) :
    Reduce A M (encode ⟨Validator.cell A.blank .cutC::l,.pending,Validator.cell A.blank .cutD::r,lb,rb⟩)
      (encode ⟨l,.raw,[],lb,true⟩ ++ encode ⟨[],.raw,r,true,rb⟩) := by
  have hr := reduce_rule_reverse A M (.ordinary .merge) (by
    simp [grade,Path.grade,Path.letterGrade,gradeCell,Validator.cell,Cleanup.grade])
  have hh := reduce_context A M hr ((if lb then [.enter] else [])++l.reverse.map .left)
      (r.map .right++(if rb then [.leave] else []))
  simp only [encode,Scan.literal,Path.encode,Path.headed,List.reverse_cons,List.reverse_nil,
    List.map_cons,List.map_append,List.map_nil,List.append_nil,
    List.singleton_append,ite_true,List.append_assoc] at hh ⊢
  exact hh

theorem reduces_unmerge (v : Surface.Sector S Γ (Control.Head S Q)) :
    Reduces A M (encode v) ((Surface.unmerge A.blank v).flatMap encode) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases l with
  | nil =>
    simp only [Surface.unmerge,List.flatMap_cons,List.flatMap_nil,List.append_nil]; exact .refl
  | cons c l =>
    cases q with
    | raw | cleanup | internal _ =>
      simp only [Surface.unmerge,List.flatMap_cons,List.flatMap_nil,List.append_nil]; exact .refl
    | pending =>
      cases r with
      | nil =>
        simp only [Surface.unmerge,List.flatMap_cons,List.flatMap_nil,List.append_nil]; exact .refl
      | cons d r =>
        by_cases h : c = Validator.cell A.blank .cutC ∧ d = Validator.cell A.blank .cutD
        · rcases h with ⟨rfl,rfl⟩
          have hp := (reduces_rawNormal A M ⟨l,.raw,[],lb,true⟩)
          have hq := (reduces_rawNormal A M ⟨[],.raw,r,true,rb⟩)
          simpa [Surface.unmerge] using
            ((ReflTransGen.single (reduce_unmerge A M l r lb rb)).trans (reduces_append A M hp hq))
        · simpa only [Surface.unmerge,ite_eq_right h,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
            (ReflTransGen.refl (a := encode ⟨c::l,.pending,d::r,lb,rb⟩) : Reduces A M _ _)

theorem reduces_pendingPreprocess (v : Surface.Sector S Γ (Control.Head S Q)) :
    Reduces A M (encode v) ((Surface.pendingPreprocess A.blank v).flatMap encode) :=
  (reduces_quotaNormal A M v).trans (reduces_unmerge A M _)

theorem reduce_exit (l : List (Cell S Γ)) (lb : Bool) :
    Reduce A M (encode ⟨l,.internal (.machine .ok),[],lb,true⟩)
      (encode ⟨l,.cleanup,[],lb,true⟩) := by
  have hh := reduce_context A M (reduce_rule A M .exit) ((if lb then [.enter] else [])++l.reverse.map .left) []
  simp only [encode,Scan.literal,Path.encode,Path.headed,List.map_nil,List.append_nil,
    ite_true,List.append_assoc] at hh ⊢
  exact hh

variable [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
  [LinearOrder (Control.Sector S Γ Q)]

theorem reduces_internalPreprocess (v : Control.Sector S Γ Q) :
    Reduces A M (encode (Scan.mapHead Surface.Head.internal v))
      ((Surface.internalPreprocess A M v).flatMap encode) := by
  have hp := reduces_internal A M (Control.representative_connected A M v)
  refine hp.trans ?_
  generalize hw : Control.representative A M v = w at *
  rcases w with ⟨l,q,r,lb,rb⟩
  unfold Surface.internalPreprocess
  rw [hw]
  dsimp only
  by_cases he : Control.Entry A.blank ⟨l,q,r,lb,rb⟩
  · rw [ite_eq_left he]
    rcases he with ⟨rfl,hr⟩
    cases r with
    | nil => cases hr
    | cons c r =>
      cases Option.some.inj hr
      have hh := reduce_entry A M l r lb rb
      have hg : grade (Q := Q) (encode ⟨l,.pending,Validator.cell A.blank .cutD::r,lb,rb⟩) =
          grade (Q := Q) (encode ⟨l,.internal .initial,Validator.cell A.blank .cutD::r,lb,rb⟩) := by
        rw [grade_encode,grade_encode]; rfl
      exact (ReflTransGen.single (reduce_reverse A M hh hg)).trans (reduces_pendingPreprocess A M _)
  · rw [ite_eq_right he]
    by_cases hs : Control.Success ⟨l,q,r,lb,rb⟩
    · rw [ite_eq_left hs]
      rcases hs with ⟨rfl,rfl,rfl⟩
      simpa only [Scan.mapHead,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
        ((ReflTransGen.single (reduce_exit A M l lb)).trans (reduces_cleanupPreprocess A M _))
    · rw [ite_eq_right hs]
      simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
      exact .refl

theorem reduces_sectorPreprocess (v : Surface.Sector S Γ (Control.Head S Q)) :
    Reduces A M (encode v) ((Surface.preprocess A M v).flatMap encode) := by
  rcases v with ⟨l,q,r,lb,rb⟩
  cases q with
  | raw =>
    simpa only [Surface.preprocess,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
      reduces_rawNormal A M ⟨l,.raw,r,lb,rb⟩
  | pending => exact reduces_pendingPreprocess A M _
  | cleanup =>
    simpa only [Surface.preprocess,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
      reduces_cleanupPreprocess A M ⟨l,.cleanup,r,lb,rb⟩
  | internal q => exact reduces_internalPreprocess A M ⟨l,q,r,lb,rb⟩

end

section
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

theorem reduces_prepareChunk (w : List (Letter S Γ Q)) :
    Reduces A M w (Path.prepareChunk (sectorPreprocess A M) w).flatten := by
  cases hd : Path.decode w with
  | none => simp only [Path.prepareChunk,hd,List.flatten_cons,List.flatten_nil,List.append_nil]; exact .refl
  | some v =>
    have hw := Path.decode_sound hd
    subst w
    have hh := reduces_sectorPreprocess A M (Scan.unliteral v)
    simp only [Path.prepareChunk_encode,sectorPreprocess,List.map_map,List.flatMap_def,
      Function.comp_def,encode,Scan.literal_unliteral] at hh ⊢
    exact hh

theorem reduces_prepareChunks (cs : List (List (Letter S Γ Q))) :
    Reduces A M cs.flatten (Path.prepareChunks (sectorPreprocess A M) cs).flatten := by
  induction cs with
  | nil => exact .refl
  | cons c cs ih =>
    simpa only [Path.prepareChunks,List.flatMap_cons,List.flatten_cons,List.flatten_append] using
      reduces_append A M (reduces_prepareChunk A M c) ih

theorem reduces_preprocess (w : List (Letter S Γ Q)) :
    Reduces A M w (preprocess A M w).flatten := by
  simpa only [preprocess,Path.prepare,Path.flatten_cuts] using reduces_prepareChunks A M (Path.cuts w)

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
    [LinearOrder (Control.Sector S Γ Q)] in
 theorem reduces_zero {w : List (Letter S Γ Q)} (h : Path.shape w = .zero) :
    Reduces A M w [.zero] := by
  exact ReflTransGen.mono (fun _ _ hs =>
    reduce_of_context_rule A M (Path.context_mono hs (fun _ _ hh => .zero hh))) _ _ (Path.zero_reaches h)

end

section
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ]

omit [DecidableEq S] [DecidableEq Γ] in
theorem grade_flatMap_encode (vs : List (Surface.Sector S Γ (Control.Head S Q))) :
    grade (vs.flatMap encode) = Surface.listGrade vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [List.flatMap_cons,grade_append,grade_encode,ih,Surface.listGrade,
      List.map_cons,List.sum_cons]

theorem reduces_rawPair_of_run (x y out : List S)
    (c : Simulator.Tape (S := S) (Γ := Γ) (Q := Q))
    (hrun : ReflTransGen (Simulator.UnboundedStep A M) (Simulator.initialTape A M (x++y)) c)
    (hhalt : Simulator.Halted A M c) (hout : Simulator.Returns A c out)
    (hlen : out.length ≤ x.length+y.length) :
    Reduces A M (raw A.blank x ++ raw A.blank y) (raw A.blank out) := by
  obtain ⟨s,result,hr,hclean⟩ := Compiled.clean_success A M x y out c hrun hhalt hout hlen
  let e : Surface.Sector S Γ (Control.Head S Q) :=
    ⟨(Compiled.cleanEntry A.blank x y s).left,.pending,
      (Compiled.cleanEntry A.blank x y s).right,true,true⟩
  have he : (Surface.pendingPreprocess A.blank e).flatMap encode = raw A.blank x++raw A.blank y := by
    rw [show Surface.pendingPreprocess A.blank e = [Surface.raw A.blank x,Surface.raw A.blank y] from
      Surface.pendingPreprocess_cleanEntry A x y s]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,raw]
  have hp := reduces_pendingPreprocess A M e
  have hg : grade (encode e) = grade ((Surface.pendingPreprocess A.blank e).flatMap encode) := by
    rw [grade_encode,grade_flatMap_encode,Surface.pendingPreprocess_grade]
  have hp' := reduces_reverse A M hp hg
  rw [he] at hp'
  have hentry : Reduce A M (encode e)
      (encode (Scan.mapHead Surface.Head.internal (Control.validator (Compiled.cleanEntry A.blank x y s)))) :=
    reduce_entry A M _ _ true true
  have hrun' := reduces_internal A M (EqvGen.reflTransGen_le_eqvGen _ _ _ (Control.ofCfg_runs A M hr))
  simp only [Control.ofCfg] at hrun'
  have hc : Reduces A M (encode (Surface.ofCleanup ⟨result.reverse,.cleanup,[],true,true⟩))
      (raw A.blank out) := by
    exact hclean.lift (fun v => encode (Surface.ofCleanup v)) (fun _ _ hh => reduce_cleanup A M hh)
  exact hp'.trans ((ReflTransGen.single hentry).trans
    (hrun'.trans ((ReflTransGen.single (reduce_exit A M result.reverse true)).trans hc)))

theorem reduces_rawPair {f : List S → List S} {m : ℕ}
    (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    (x y : List S) (hm : (x++y).length ≤ m) :
    Reduces A M (raw A.blank x++raw A.blank y) (raw A.blank (f (x++y))) := by
  obtain ⟨c,hc,hh,ho⟩ := hcomp (x++y) hm
  exact reduces_rawPair_of_run A M x y (f (x++y)) c hc hh ho (by simpa using h.length (x++y) hm)

end

section
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]

omit [DecidableEq Q] in
 theorem reduces_prepend {f : List S → List S} {m : ℕ}
    (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    (a : Item S Γ Q) (w : List (Item S Γ Q))
    (hm : RawRuns.itemGrade grade a + RawRuns.grade grade w ≤ m) :
    Reduces A M (realize A.blank a ++ w.flatMap (realize A.blank))
      ((RawRuns.prepend f a w).flatMap (realize A.blank)) := by
  cases a with
  | inl c => exact .refl
  | inr x =>
    cases w with
    | nil => exact .refl
    | cons a w =>
      cases a with
      | inl c => exact .refl
      | inr y =>
        have hl : (x++y).length ≤ m := by
          simp only [RawRuns.itemGrade,RawRuns.grade_cons,List.length_append] at *
          omega
        have hp := reduces_context A M (reduces_rawPair A M h hcomp x y hl) [] (w.flatMap (realize A.blank))
        simpa only [List.nil_append,List.flatMap_cons,RawRuns.prepend,realize,List.append_assoc] using hp

omit [DecidableEq Q] in
 theorem reduces_rawRuns {f : List S → List S} {m : ℕ}
    (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    (w : List (Item S Γ Q)) (hm : RawRuns.grade grade w ≤ m) :
    Reduces A M (w.flatMap (realize A.blank))
      ((RawRuns.normalize f w).flatMap (realize A.blank)) := by
  induction w with
  | nil => exact .refl
  | cons a w ih =>
    have hb : RawRuns.grade grade w ≤ m := by simp only [RawRuns.grade_cons] at hm; omega
    have hp := reduces_append A M (ReflTransGen.refl (a := realize A.blank a)) (ih hb)
    have hg := RawRuns.normalize_grade grade h w hb
    have hh := reduces_prepend A M h hcomp a (RawRuns.normalize f w)
      (by simp only [RawRuns.grade_cons] at hm; omega)
    exact hp.trans hh

variable [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- A literal, grade-nonincreasing derivation to the source's whole-word
    evaluator, not just equality in an assumed quotient. -/
 theorem reduces_normal {f : List S → List S} {m : ℕ}
    (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    (w : List (Letter S Γ Q)) (hm : grade w ≤ m) :
    Reduces A M w (normal A M f w) := by
  by_cases hn : Path.shape w = .zero
  · simpa only [normal,ite_eq_left hn] using reduces_zero A M hn
  · rw [normal_eq_fold A M h w hn hm]
    have hp := reduces_preprocess A M w
    have hh := reduces_rawRuns A M h hcomp ((preprocess A M w).map (classify A.blank))
      (by rw [classify_grade]; exact (preprocess_grade A M w).trans hm)
    have hj : ((preprocess A M w).map (classify A.blank)).flatMap (realize A.blank) =
        (preprocess A M w).flatten := by
      simp only [List.flatMap_def,List.map_map,Function.comp_def,realize_classify,List.map_id']
    rw [hj] at hh
    exact hp.trans hh

end

section
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- The bounded context conclusion uses the nonincreasing literal derivations;
    the attachment need not preserve sector boundaries. -/
theorem normal_context
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} {m : ℕ} (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    {u v : List (Letter S Γ Q)} (he : normal A M f u = normal A M f v)
    (x y : List (Letter S Γ Q))
    (hu : grade (x++u++y) ≤ m) (hv : grade (x++v++y) ≤ m) :
    normal A M f (x++u++y) = normal A M f (x++v++y) := by
  have hu' : grade u ≤ m := by simp only [grade_append] at hu; omega
  have hv' : grade v ≤ m := by simp only [grade_append] at hv; omega
  have hp := normal_reduces A M hdecode h hcomp
    (reduces_context A M (reduces_normal A M h hcomp u hu') x y) hu
  have hq := normal_reduces A M hdecode h hcomp
    (reduces_context A M (reduces_normal A M h hcomp v hv') x y) hv
  rw [he] at hp
  exact hp.trans hq.symm

/-- The compiler's finite monoid presentation is formed from the literal rule
    table; neither a normalizer nor program totality enters its definition. -/
abbrev Rel (u v : FreeMonoid (Letter S Γ Q)) : Prop := Rule A M u v
abbrev Presentation := PresentedMonoid (Rel A M)
def present (w : List (Letter S Γ Q)) : Presentation A M := PresentedMonoid.mk (Rel A M) w

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
    [LinearOrder (Control.Sector S Γ Q)] in
theorem present_append (u v : List (Letter S Γ Q)) :
    present A M (u++v) = present A M u * present A M v := rfl

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
    [LinearOrder (Control.Sector S Γ Q)] in
theorem present_context {u v : List (Letter S Γ Q)} (he : present A M u = present A M v)
    (x y : List (Letter S Γ Q)) : present A M (x++u++y) = present A M (x++v++y) := by
  simp only [present_append,he]

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
    [LinearOrder (Control.Sector S Γ Q)] in
theorem present_reduce {u v : List (Letter S Γ Q)} (h : Reduce A M u v) :
    present A M u = present A M v := by
  cases h.1 with
  | apply x y hr =>
    apply present_context A M ?_ x y
    rcases hr with hr | hr
    · exact PresentedMonoid.mk_eq_mk_of_rel hr
    · exact (PresentedMonoid.mk_eq_mk_of_rel hr).symm

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
    [LinearOrder (Control.Sector S Γ Q)] in
theorem present_reduces {u v : List (Letter S Γ Q)} (h : Reduces A M u v) :
    present A M u = present A M v := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans (present_reduce A M h)

theorem present_normal {f : List S → List S} {m : ℕ}
    (h : RawRuns.Budget f m) (hcomp : ComputesAt A M f m)
    (w : List (Letter S Γ Q)) (hm : grade w ≤ m) :
    present A M w = present A M (normal A M f w) :=
  present_reduces A M (reduces_normal A M h hcomp w hm)

/-- No maximum grade of a presentation derivation is assumed. Its finitely many
    contextual uses are handled by the theorem at all finite budgets. -/
theorem normal_conGen
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} (h : ∀ m, RawRuns.Budget f m) (hcomp : ∀ m, ComputesAt A M f m)
    {u v : FreeMonoid (Letter S Γ Q)} (he : conGen (Rel A M) u v) :
    normal A M f u = normal A M f v := by
  induction he with
  | of u v hr =>
    change Rule A M u.toList v.toList at hr
    change normal A M f u.toList = normal A M f v.toList
    have hp := normal_rule A M hdecode (h (max (grade u.toList) (grade v.toList)))
      (hcomp (max (grade u.toList) (grade v.toList))) hr [] []
      (by simpa only [List.nil_append,List.append_nil] using le_max_left (grade u.toList) (grade v.toList))
      (by simpa only [List.nil_append,List.append_nil] using le_max_right (grade u.toList) (grade v.toList))
    simpa only [List.nil_append,List.append_nil] using hp
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ij => exact ih.trans ij
  | @mul w x y z _ _ ih ij =>
    change normal A M f (w.toList++y.toList) = normal A M f (x.toList++z.toList)
    change normal A M f w.toList = normal A M f x.toList at ih
    change normal A M f y.toList = normal A M f z.toList at ij
    have hp := normal_context A M hdecode
      (h (max (grade (w.toList++y.toList)) (grade (x.toList++y.toList))))
      (hcomp (max (grade (w.toList++y.toList)) (grade (x.toList++y.toList)))) ih [] y.toList
      (by simpa only [List.nil_append] using le_max_left (grade (w.toList++y.toList)) (grade (x.toList++y.toList)))
      (by simpa only [List.nil_append] using le_max_right (grade (w.toList++y.toList)) (grade (x.toList++y.toList)))
    have hq := normal_context A M hdecode
      (h (max (grade (x.toList++y.toList)) (grade (x.toList++z.toList))))
      (hcomp (max (grade (x.toList++y.toList)) (grade (x.toList++z.toList)))) ij x.toList []
      (by simpa only [List.append_nil] using le_max_left (grade (x.toList++y.toList)) (grade (x.toList++z.toList)))
      (by simpa only [List.append_nil] using le_max_right (grade (x.toList++y.toList)) (grade (x.toList++z.toList)))
    simp only [List.nil_append,List.append_nil] at hp hq
    exact hp.trans hq

/-- Exact equality criterion for the finite presentation under the global
    (not assumed for constructing the presentation) evaluator hypotheses. -/
theorem present_eq_iff_normal
    (hdecode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → List S} (h : ∀ m, RawRuns.Budget f m) (hcomp : ∀ m, ComputesAt A M f m)
    (u v : List (Letter S Γ Q)) :
    present A M u = present A M v ↔ normal A M f u = normal A M f v := by
  constructor
  · intro he
    exact normal_conGen A M hdecode h hcomp (PresentedMonoid.mk_eq_mk_iff.mp he)
  · intro he
    rw [present_normal A M (h (grade u)) (hcomp (grade u)) u le_rfl,
      present_normal A M (h (grade v)) (hcomp (grade v)) v le_rfl,he]

end

open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

@[simp] theorem normal_nil (f : List S → List S) : normal A M f [] = [] := by
  simp [normal,preprocess,Path.prepare,Path.prepareChunks,RawRuns.source]

@[simp] theorem normal_omega (f : List S → List S) :
    normal A M f [.zero] = [.zero] := by simp [normal,Path.typeOf]

@[simp] theorem preprocess_raw_pair (u v : List S) :
    preprocess A M (raw (Q := Q) A.blank u ++ raw A.blank v) =
      [raw A.blank u,raw A.blank v] := by
  have hr (w : List S) : raw (Q := Q) A.blank w =
      [.enter,.head .raw] ++ (w.map (Validator.cell A.blank ∘ Base.anchor)).map Path.Letter.right ++ [.leave] := by
    simp [raw,encode,Surface.raw,Scan.literal,Path.encode,Path.headed]
  have hc : Path.cuts (raw (Q := Q) A.blank u ++ raw A.blank v) =
      Path.cuts (raw A.blank u) ++ Path.cuts (raw A.blank v) := by
    rw [hr u]
    rw [List.append_assoc, List.singleton_append, Path.cuts_append_leave]
  unfold preprocess Path.prepare
  rw [hc]
  change Path.prepareChunks (sectorPreprocess A M)
    (Path.cuts (raw A.blank u) ++ Path.cuts (raw A.blank v)) = _
  rw [Path.prepareChunks_append]
  exact congrArg₂ List.append (preprocess_raw A M u) (preprocess_raw A M v)

/-- Singleton raw words are fixed, but adjacent full raw words call the program
    on their concatenation, exactly as in the manuscript. -/
theorem normal_raw_product (f : List S → List S) (u v : List S) :
    normal A M f (raw (Q := Q) A.blank u ++ raw A.blank v) = raw A.blank (f (u++v)) := by
  have hn : Path.shape (raw (Q := Q) A.blank u ++ raw A.blank v) ≠ .zero := by
    simp [raw,encode,Path.encode,Path.path_mul_path,Surface.raw,Scan.literal]
  rw [normal,ite_eq_right hn]
  simp [RawRuns.source,RawRuns.splitRun,realize]

end FiniteAlgebraicEnvelopes.Compiler.Word

/- The actual partial evaluator is a finite plan followed by partial calls.
   Its definition has no budget and does not totalize an undefined program. -/

namespace FiniteAlgebraicEnvelopes.Compiler

theorem partValue_mem {S : Type*} {p : Part (List S)} (h : p.Dom) : partValue p ∈ p := by
  simp only [partValue,dite_eq_left h]
  exact Part.get_mem h

theorem PartialBudget.totalize {S : Type*} {f : List S → Part (List S)} {m : ℕ}
    (h : PartialBudget f m) : RawRuns.Budget (fun w => partValue (f w)) m where
  length w hw := h.length w hw _ (partValue_mem (h.total w hw))
  context x w y hw := by
    have hh : w.length ≤ m := by simp only [List.length_append] at hw; omega
    exact congrArg partValue (h.context x w y hw _ (partValue_mem (h.total w hh)))

end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Compiler.Word
open Relation
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

/-- The finite-machine adapter has to *prove* this execution specification for
    any supplied partial-recursive program. It is not an extra main hypothesis. -/
def Realizes (f : List S → Part (List S)) : Prop :=
  ∀ w out, out ∈ f w ↔ ∃ c,
    ReflTransGen (Simulator.UnboundedStep A M) (Simulator.initialTape A M w) c ∧
    Simulator.Halted A M c ∧ Simulator.Returns A c out

omit [DecidableEq S] [DecidableEq Γ] [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
    [LinearOrder (Control.Sector S Γ Q)] in
theorem Realizes.computesAt {f : List S → Part (List S)} (hr : Realizes A M f) {m : ℕ}
    (h : PartialBudget f m) : ComputesAt A M (fun w => partValue (f w)) m := by
  intro w hw
  exact (hr w _).mp (partValue_mem (h.total w hw))

end FiniteAlgebraicEnvelopes.Compiler.Word

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

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {H B T : Type*}

def Sector.code : Sector H B T ≃ List (B×T) × (H × (List (B×T) × (Bool × Bool))) where
  toFun v := (v.left,v.head,v.right,v.leftBoundary,v.rightBoundary)
  invFun p := ⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instPrimcodableSector [Primcodable H] [Primcodable B] [Primcodable T] : Primcodable (Sector H B T) :=
  Primcodable.ofEquiv _ Sector.code

variable [Primcodable H] [Primcodable B] [Primcodable T]

theorem Sector.primrec_code : Primrec (Sector.code (H := H) (B := B) (T := T)) := Primrec.of_equiv
theorem Sector.primrec_head : Primrec (Sector.head (Head := H) (Base := B) (Tag := T)) :=
  Primrec.fst.comp (Primrec.snd.comp Sector.primrec_code)
theorem Sector.primrec_right : Primrec (Sector.right (Head := H) (Base := B) (Tag := T)) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Sector.primrec_code))
theorem Sector.primrec_rb : Primrec (Sector.rightBoundary (Head := H) (Base := B) (Tag := T)) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Sector.primrec_code)))

variable [Fintype H] [Fintype B] [Fintype T]

noncomputable def sectorList (n : ℕ) : List (Sector H B T) :=
  (finiteList H).flatMap fun q =>
    (wordList (B×T) n).flatMap fun l =>
      (wordList (B×T) n).flatMap fun r =>
        [⟨l,q,r,false,false⟩,⟨l,q,r,false,true⟩,⟨l,q,r,true,false⟩,⟨l,q,r,true,true⟩]

omit [Primcodable H] [Primcodable B] [Primcodable T] in
@[simp] theorem mem_sectorList (n : ℕ) (v : Sector H B T) :
    v ∈ sectorList n ↔ v.left.length ≤ n ∧ v.right.length ≤ n := by
  rcases v with ⟨l,q,r,a,b⟩
  cases a <;> cases b <;> simp [sectorList,Sector.mk.injEq]

variable [DecidableEq H] [DecidableEq B] [DecidableEq T]

noncomputable def universeList (v : Sector H B T) : List (Sector H B T) :=
  (sectorList (v.left.length+v.right.length)).filter fun w => baseSkeleton w = baseSkeleton v

omit [Primcodable H] [Primcodable B] [Primcodable T] [DecidableEq H] [DecidableEq T] in
@[simp] theorem mem_universeList (v w : Sector H B T) :
    w ∈ universeList v ↔ baseSkeleton w = baseSkeleton v := by
  simp only [universeList,List.mem_filter,mem_sectorList,decide_eq_true_eq,and_iff_right_iff_imp]
  intro h
  have hl := skeleton_length h
  constructor <;> omega

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open Relation
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {H B T : Type*}

variable [Primcodable H] [Primcodable B] [Primcodable T]

variable [Fintype H] [Fintype B] [Fintype T] (table : Table H B T)

variable [DecidableEq H] [DecidableEq B] [DecidableEq T]

def stepBool (v w : Sector H B T) : Bool := decide (step table v = some w)

noncomputable def componentList (v : Sector H B T) : List (Sector H B T) :=
  FiniteAlgebraicEnvelopes.Effect.Graph.component (stepBool table) (universeList v) v

omit [Primcodable H] [Primcodable B] [Primcodable T] in
@[simp] theorem mem_componentList (v w : Sector H B T) :
    w ∈ componentList table v ↔ EqvGen (Step table) v w := by
  change w ∈ componentList table v ↔ EqvGen (fun a b => step table a = some b) v w
  simpa only [componentList,stepBool,decide_eq_true_eq,Step] using
    (FiniteAlgebraicEnvelopes.Effect.Graph.mem_component_iff (stepBool table)
      (b := w) ((mem_universeList v v).mpr rfl) (by
        intro c hc d hd
        rw [mem_universeList] at hc ⊢
        rcases hd with hd | hd
        · exact (step_skeleton table ((show Step table c d from of_decide_eq_true (p := step table c = some d) hd))).symm.trans hc
        · exact (step_skeleton table ((show Step table d c from of_decide_eq_true (p := step table d = some c) hd))).trans hc))

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler
open FiniteAlgebraicEnvelopes.Effect
noncomputable instance instPrimcodableBaseOfFintype {S : Type*} [Fintype S] : Primcodable (Base S) := finitePrimcodable _
noncomputable instance instPrimcodableTagOfFintype {S Γ : Type*} [Fintype S] [Fintype Γ] : Primcodable (Tag S Γ) := finitePrimcodable _
end FiniteAlgebraicEnvelopes.Compiler

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Selectors
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Literal selector envelopes, rewrite saturation, and zero recognition.
-/

/- Literal selector envelopes from the self-reference construction. -/
namespace FiniteAlgebraicEnvelopes.Bootstrap

namespace Canonical
variable {A Q : Type*} {r : A → A → Prop} [DecidableEq Q] [DecidableRel (List.Shortlex r)]

variable (wf : WellFounded r) (q : List A → Q)

theorem pick_least_fixed {ps : List (List A × Q)} {w : List A}
    (hps : ∀ p ∈ ps,p.2=q p.1) :
    pick (r:=r) ps (least wf q w) (q w)=least wf q w := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hh : ¬ (p.2=q w ∧ List.Shortlex r p.1 (least wf q w)) := by
      rintro ⟨hq,hr⟩
      exact least_global_min wf q ((hps p List.mem_cons_self).symm.trans hq) hr
    simp only [pick,List.foldl_cons,pickStep,ite_eq_right hh]
    exact ih (fun p hp => hps p (List.mem_cons_of_mem _ hp))

variable [Std.Trichotomous r]

/-- The finite answer list computes the same least shortlex representative as
    the manuscript, even though it tests every word in the common length ball. -/
theorem pick_eq_least {ps : List (List A × Q)} {w : List A}
    (hps : ∀ p ∈ ps,p.2=q p.1) (hm : (least wf q w,q w) ∈ ps) :
    pick (r:=r) ps w (q w)=least wf q w := by
  obtain ⟨before,after,rfl⟩ := List.mem_iff_append.mp hm
  have hb : ∀ p ∈ before,p.2=q p.1 := fun p hp => hps p (List.mem_append_left _ hp)
  have ha : ∀ p ∈ after,p.2=q p.1 := fun p hp =>
    hps p (List.mem_append_right _ (List.mem_cons_of_mem _ hp))
  have hclass := pick_class (r:=r) q hb (w:=w) rfl
  have hsel : pickStep (r:=r) (q w) (pick (r:=r) before w (q w)) (least wf q w,q w) = least wf q w := by
    unfold pickStep
    simp only [true_and]
    split
    · rfl
    next h =>
      apply Std.Trichotomous.trichotomous (r:=List.Shortlex r)
      · exact least_global_min wf q hclass
      · exact h
  simp only [pick,List.foldl_append,List.foldl_cons]
  change after.foldl (pickStep (r:=r) (q w))
    (pickStep (r:=r) (q w) (pick (r:=r) before w (q w)) (least wf q w,q w)) = _
  rw [hsel]
  exact pick_least_fixed wf q ha

end Canonical

namespace Search

section
variable {A : Type*} [DecidableEq A]

theorem lexBool_eq [LinearOrder A] (u v : List A) :
    lexBool (fun a b : A => decide (a<b)) u v = decide (List.Lex (·<·) u v) := by
  induction u generalizing v with
  | nil => cases v <;> simp [lexBool]
  | cons a u ih =>
    cases v with
    | nil => simp [lexBool]
    | cons b v =>
      by_cases hab : a=b
      · subst b
        simp [lexBool,ih,List.lex_cons_iff]
      · simp only [lexBool,ite_eq_right hab]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · exact List.Lex.rel
        · intro h
          cases h with
          | rel h => exact h
          | cons h => exact False.elim (hab rfl)

variable [Primcodable A]

 theorem primrec_shortlex [LinearOrder A] (hr : PrimrecRel (fun a b : A => a<b)) :
    PrimrecRel (List.Shortlex (fun a b : A => a<b)) := by
  have hlex : PrimrecRel (List.Lex (fun a b : A => a<b)) := by
    apply PrimrecRel.of_eq
      (Primrec.eq.comp₂ (primrec_lexBool (fun a b : A => decide (a<b)) hr.decide)
        (Primrec.const true).to₂)
    intro u v
    rw [lexBool_eq,decide_eq_true_eq]
  exact ((Primrec.nat_lt.comp (Primrec.list_length.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd)).or
    ((Primrec.eq.comp (Primrec.list_length.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd)).and hlex)).of_eq
      (fun p => List.shortlex_def.symm)

end

end Search
end FiniteAlgebraicEnvelopes.Bootstrap

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Quotients
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical compiler quotients and effective tested classes for word problems.
-/

namespace FiniteAlgebraicEnvelopes

namespace Bootstrap
namespace Search
variable {A S Q : Type*} [DecidableEq A] [DecidableEq S] [DecidableEq Q]
variable {r : A → A → Prop} [DecidableRel (List.Shortlex r)]

omit [DecidableEq A] [DecidableEq S] [DecidableEq Q] [DecidableRel (List.Shortlex r)] in
theorem value_mem {f : List A → Part (Option Q)} {w : List A} (h : (f w).Dom) : value f w ∈ f w := by
  simp only [value,dite_eq_left h]
  exact Part.get_mem h

end Search

end Bootstrap
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.Bootstrap

section

namespace Quotient
open Relation
variable {S : Type*} [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))

variable {r : S → S → Prop} (wf : WellFounded r)
  (good : ∀ n,GoodTable (r:=r) T n)
  (stable : ∀ k n,k ≤ n → ∀ rk∈T k,∀ rn∈T n,Selectors.BoundedEq rk rn k)
include wf good stable

 theorem normal_mem (w : List S) : normal T w ∈ tableNormal T w :=
  Compiler.partValue_mem ((budget T wf good stable w.length).total w le_rfl)

 theorem present_normal (w : List S) : present T w=present T (normal T w) := by
  obtain ⟨rs,hrs,hd,_⟩ := good w.length
  have h := normal_mem T wf good stable w
  rw [tableNormal,Part.eq_some_iff.mpr hrs,Part.bind_some] at h
  exact present_steps T hrs hd le_rfl (evaluate_sound h).1

 theorem normal_context (x w y : List S) :
    normal T (x++normal T w++y)=normal T (x++w++y) := by
  exact congrArg Compiler.partValue ((budget T wf good stable (x++w++y).length).context
    x w y le_rfl _ (normal_mem T wf good stable w))

 theorem normal_append (u v : List S) :
    normal T (u++v)=normal T (normal T u++normal T v) := by
  have hu := normal_context T wf good stable [] u v
  have hv := normal_context T wf good stable (normal T u) v []
  simp only [List.nil_append,List.append_nil] at hu hv
  exact hu.symm.trans hv.symm

 theorem normal_rel {u v : FreeMonoid S} (h : Rel T u v) : normal T u.toList=normal T v.toList := by
  obtain ⟨n,rs,hrs,huv,hu⟩ := h
  obtain ⟨rt,hrt,hd,hc⟩ := good n
  have he := Part.mem_unique hrt hrs
  subst rt
  have hstep : Step rs u.toList v.toList := by
    simpa only [List.nil_append,List.append_nil] using Step.apply huv [] []
  have hv : v.toList.length ≤ n := (steps_length hd (.single hstep)).trans hu
  have hat (w : List S) (hw : w.length ≤ n) : tableNormal T w=evaluate rs w :=
    tableNormal_at wf (fun _ _ => good _) (fun k hk => stable k n hk) hrs hw
  have hnu := normal_mem T wf good stable u.toList
  have hnv := normal_mem T wf good stable v.toList
  rw [hat _ hu] at hnu
  rw [hat _ hv] at hnv
  exact evaluate_unique_on wf hd n (fun _ _ _ h => critical_localJoin hc h) hu
    (evaluate_sound hnu).1 ((ReflTransGen.single hstep).trans (evaluate_sound hnv).1)
    (evaluate_sound hnu).2 (evaluate_sound hnv).2

noncomputable def normalCon : Con (FreeMonoid S) where
  r u v := normal T u.toList=normal T v.toList
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h g => h.trans g⟩
  mul' := by
    intro u v x y huv hxy
    change normal T (u.toList++x.toList)=normal T (v.toList++y.toList)
    exact (normal_append T wf good stable _ _).trans
      ((congrArg₂ (fun a b => normal T (a++b)) huv hxy).trans
        (normal_append T wf good stable _ _).symm)

 theorem present_eq_iff (u v : List S) : present T u=present T v ↔ normal T u=normal T v := by
  constructor
  · intro h
    exact (Con.conGen_le.mpr (fun _ _ h => normal_rel T wf good stable h) :
      conGen (Rel T) ≤ normalCon T wf good stable) (PresentedMonoid.mk_eq_mk_iff.mp h)
  · intro h
    exact (present_normal T wf good stable u).trans (h ▸ (present_normal T wf good stable v).symm)

end Quotient

open Relation

namespace Quotient
variable {S : Type*} [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))
variable {r : S → S → Prop} (wf : WellFounded r)
  (good : ∀ n,GoodTable (r:=r) T n)
  (stable : ∀ k n,k ≤ n → ∀ rk∈T k,∀ rn∈T n,Selectors.BoundedEq rk rn k)
include wf good stable

 theorem normal_idempotent (w : List S) : normal T (normal T w)=normal T w := by
  simpa only [List.nil_append,List.append_nil] using normal_context T wf good stable [] w []

 theorem normal_eq_self {w : List S} {rs : List (List S × List S)} (hrs : rs∈T w.length)
    (hi : Irreducible (Step rs) w) : normal T w=w := by
  have hw := normal_mem T wf good stable w
  rw [tableNormal,Part.eq_some_iff.mpr hrs,Part.bind_some] at hw
  exact (irreducible_reaches (Step rs) hi (evaluate_sound hw).1).symm

 theorem present_representative (x : Mon T) : present T (representative T x)=x := by
  rw [representative,←present_normal T wf good stable]
  exact Classical.choose_spec (present_surjective T x)

 theorem representative_injective : Function.Injective (representative T) := by
  intro x y he
  rw [←present_representative T wf good stable x,←present_representative T wf good stable y,he]

 theorem present_nil_ne_zero (z : S)
    (hshort : ∀ n rs,rs∈T n → ∀ p∈rs,1<p.1.length) :
    (1 : Mon T)≠present T [z] := by
  obtain ⟨r0,hr0,_⟩ := good 0
  obtain ⟨r1,hr1,_⟩ := good 1
  have h0 : normal T []=[] := normal_eq_self T wf good stable hr0
    (irreducible_of_short (fun p hp => by simpa using Nat.lt_trans Nat.zero_lt_one (hshort 0 r0 hr0 p hp)))
  have h1 : normal T [z]=[z] := normal_eq_self T wf good stable hr1
    (irreducible_of_short (fun p hp => hshort 1 r1 hr1 p hp))
  intro he
  have hh := (present_eq_iff T wf good stable [] [z]).mp he
  rw [h0,h1] at hh
  simp at hh

end Quotient
end

end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes
namespace Compiler.Word
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
  [LinearOrder (Control.Sector S Γ Q)] in
 theorem present_surjective : Function.Surjective (present A M) := by
  intro x
  obtain ⟨w,rfl⟩ := PresentedMonoid.surjective_mk x
  exact ⟨w.toList,rfl⟩

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
  [LinearOrder (Control.Sector S Γ Q)] in
 theorem present_zero_mul (w : List (Letter S Γ Q)) :
    present A M [.zero] * present A M w=present A M [.zero] := by
  induction w with
  | nil => exact mul_one _
  | cons c w ih =>
    have hh : present A M [.zero,c]=present A M [.zero] :=
      PresentedMonoid.mk_eq_mk_of_rel (.zero (.pair _ _ (by simp [Path.typeOf])))
    have hp : present A M (c::w)=present A M [c]*present A M w := rfl
    rw [hp,←mul_assoc]
    change present A M [.zero,c]*present A M w=_
    rw [hh,ih]

omit [DecidableEq Q] [Fintype S] [Fintype Γ] [Fintype Q]
  [LinearOrder (Control.Sector S Γ Q)] in
 theorem present_mul_zero (w : List (Letter S Γ Q)) :
    present A M w * present A M [.zero]=present A M [.zero] := by
  induction w with
  | nil => exact one_mul _
  | cons c w ih =>
    have hh : present A M [c,.zero]=present A M [.zero] :=
      PresentedMonoid.mk_eq_mk_of_rel (.zero (.pair _ _ (by simp [Path.typeOf])))
    have hp : present A M (c::w)=present A M [c]*present A M w := rfl
    rw [hp,mul_assoc,ih]
    exact hh

@[instance_reducible]
noncomputable def monoidWithZero : MonoidWithZero (Presentation A M) where
  __ := (inferInstance : Monoid (Presentation A M))
  zero := present A M [.zero]
  zero_mul x := by
    obtain ⟨w,rfl⟩ := present_surjective A M x
    exact present_zero_mul A M w
  mul_zero x := by
    obtain ⟨w,rfl⟩ := present_surjective A M x
    exact present_mul_zero A M w

end Compiler.Word

namespace Bootstrap.Quotient
variable {S : Type*} [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))
variable {r : S → S → Prop} (wf : WellFounded r)
  (good : ∀ n,GoodTable (r:=r) T n)
  (stable : ∀ k n,k ≤ n → ∀ rk∈T k,∀ rn∈T n,Selectors.BoundedEq rk rn k)
include wf good stable

theorem representative_mul (x y : Mon T) : representative T (x*y)=
    normal T (representative T x++representative T y) := by
  have he : present T (representative T (x*y))=
      present T (representative T x++representative T y) := by
    rw [present_append,present_representative T wf good stable,
      present_representative T wf good stable,present_representative T wf good stable]
  have hn := (present_eq_iff T wf good stable _ _).mp he
  simpa only [representative,normal_idempotent T wf good stable] using hn

variable {Γ Q : Type*} [Fintype S] [Fintype Γ] [Fintype Q]
  [DecidableEq Γ] [DecidableEq Q] [LinearOrder (Compiler.Control.Sector S Γ Q)]
variable (A : Compiler.Simulator.Alphabet S Γ) (M : Compiler.Simulator.Machine Q Γ)
variable (hdecode : ∀ g a,A.output g=some a → g=A.input a)
variable (hr : Compiler.Word.Realizes A M (tableNormal T))

noncomputable def rawMap (hdecode : ∀ g a,A.output g=some a → g=A.input a)
    (hr : Compiler.Word.Realizes A M (tableNormal T)) : Mon T →ₙ* Compiler.Word.Presentation A M where
  toFun x := Compiler.Word.present A M (Compiler.Word.raw A.blank (representative T x))
  map_mul' x y := by
    have hb := fun n => (budget T wf good stable n).totalize
    have hc := fun n => Compiler.Word.Realizes.computesAt A M hr (budget T wf good stable n)
    apply (Compiler.Word.present_eq_iff_normal A M hdecode hb hc _ _).mpr
    change Compiler.Word.normal A M (fun w => Compiler.partValue (tableNormal T w))
      (Compiler.Word.raw A.blank (representative T (x*y))) =
      Compiler.Word.normal A M (fun w => Compiler.partValue (tableNormal T w))
      (Compiler.Word.raw A.blank (representative T x) ++
        Compiler.Word.raw A.blank (representative T y))
    rw [Compiler.Word.normal_raw,Compiler.Word.normal_raw_product,
      representative_mul T wf good stable]
    rfl

include hdecode hr in
theorem rawMap_injective : Function.Injective (rawMap T wf good stable A M hdecode hr) := by
  intro x y hxy
  have hn := (Compiler.Word.present_eq_iff_normal A M hdecode
    (fun n => (budget T wf good stable n).totalize)
    (fun n => Compiler.Word.Realizes.computesAt A M hr (budget T wf good stable n)) _ _).mp hxy
  simp only [Compiler.Word.normal_raw] at hn
  have he := congrArg Compiler.Word.rawLetters hn
  simp only [Compiler.Word.rawLetters_raw] at he
  exact representative_injective T wf good stable he

include hdecode hr in
theorem rawMap_ne_zero (x : Mon T) :
    rawMap T wf good stable A M hdecode hr x≠Compiler.Word.present A M [.zero] := by
  intro hx
  have hn := (Compiler.Word.present_eq_iff_normal A M hdecode
    (fun n => (budget T wf good stable n).totalize)
    (fun n => Compiler.Word.Realizes.computesAt A M hr (budget T wf good stable n))
    (Compiler.Word.raw A.blank (representative T x)) [.zero]).mp hx
  simp only [Compiler.Word.normal_raw,Compiler.Word.normal_omega] at hn
  simp [Compiler.Word.raw,Compiler.Word.encode,Compiler.Surface.raw,Compiler.Scan.literal,
    Compiler.Path.encode,Compiler.Path.headed] at hn

end Bootstrap.Quotient
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes

namespace Bootstrap.Canonical
variable {A Q : Type*} [Fintype A] [Primcodable A]
  {r : A → A → Prop} [DecidableRel (List.Shortlex r)] [Std.Trichotomous r]
  (wf : WellFounded r) (q : List A → Q)

/-- Canonical representatives do not require a coding of the semantic class
    type. Only its word-equivalence test must be algorithmic. -/
theorem computable_least (hr : PrimrecRel (List.Shortlex r))
    (hq : ComputablePred (fun p : List A × List A => q p.1=q p.2)) : Computable (least wf q) := by
  classical
  let e (w v : List A) : Option Bool := some (decide (q v=q w))
  have he : Computable₂ e := (Primrec.option_some.to_comp.comp (hq.decide.comp (Computable.snd.pair Computable.fst))).to₂
  let ps (w : List A) := (Static.words A w.length).map (fun v => (v,e w v))
  have hp : Computable ps :=
    (Effect.computable_map_parameter (Computable.snd.pair he).to₂).comp
      Computable.id (Search.primrec_words.to_comp.comp Primrec.list_length.to_comp)
  have hc : Computable (fun w => pick (r:=r) (ps w) w (some true)) :=
    ((Search.primrec_pick (Q:=Bool) hr Primrec.snd Primrec.fst (Primrec.const (some true))).to_comp.comp
      (Computable.id.pair hp))
  apply hc.of_eq
  intro w
  have hew : e w w=some true := by simp [e]
  have heq : least wf (e w) w=least wf q w := by
    apply (eq_least_iff wf q).mpr
    refine ⟨least_length wf (e w) w,?_,?_⟩
    · have hh := least_class wf (e w) w
      simpa [e] using hh
    · intro v hv hh
      apply least_min wf (e w) hv
      simp [e,hh]
  rw [← hew]
  rw [pick_eq_least wf (e w) (fun p hp => by
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hp
    rfl)]
  · exact heq
  · apply List.mem_map.mpr
    refine ⟨least wf (e w) w,(Static.mem_words _ _).mpr (least_length wf (e w) w),?_⟩
    simp only [Prod.mk.injEq,true_and]
    exact least_class wf (e w) w

end Bootstrap.Canonical

end FiniteAlgebraicEnvelopes

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

/-- Only control heads in the supplied literal support are enumerated. The
    ambient coded head type need not be finite. -/
noncomputable def sectorList [Fintype B] [Fintype T] (heads : List H) (n : ℕ) : List (Sector H B T) :=
  heads.flatMap fun q => (wordList (B×T) n).flatMap fun l =>
    (wordList (B×T) n).flatMap fun r =>
      [⟨l,q,r,false,false⟩,⟨l,q,r,false,true⟩,⟨l,q,r,true,false⟩,⟨l,q,r,true,true⟩]

omit [Primcodable H] [Primcodable B] [Primcodable T] in
@[simp] theorem mem_sectorList [Fintype B] [Fintype T] (heads : List H) (n : ℕ) (v : Sector H B T) :
    v ∈ sectorList heads n ↔ v.head ∈ heads ∧ v.left.length ≤ n ∧ v.right.length ≤ n := by
  rcases v with ⟨l,q,r,a,b⟩
  cases a <;> cases b <;> simp [sectorList,Sector.mk.injEq]

variable [Fintype B] [Fintype T]

variable [DecidableEq H] [DecidableEq B] [DecidableEq T]
noncomputable def universeList (heads : List H) (v : Sector H B T) : List (Sector H B T) :=
  (sectorList heads (v.left.length+v.right.length)).filter fun w => baseSkeleton w=baseSkeleton v

end FiniteAlgebraicEnvelopes.Compiler.Scan.Uniform

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open Simulator

inductive Static (S : Type*)
  | start | rewind : Resume S → Static S | scan : Resume S → Static S
  | finish | ok
  deriving DecidableEq, Fintype

variable {S Q Q' H C : Type*}

def ofStatic : Static S → Simulator.Head S Q
  | .start => .start
  | .rewind r => .rewind r
  | .scan r => .scan r
  | .finish => .finish
  | .ok => .ok

def dynamic (p : Bool × Q) : Simulator.Head S Q := if p.1 then .left p.2 else .run p.2

def simCode : Simulator.Head S Q ≃ Static S ⊕ (Bool × Q) where
  toFun
    | .start => .inl .start
    | .rewind r => .inl (.rewind r)
    | .scan r => .inl (.scan r)
    | .finish => .inl .finish
    | .ok => .inl .ok
    | .run q => .inr (false,q)
    | .left q => .inr (true,q)
  invFun := Sum.elim ofStatic dynamic
  left_inv q := by cases q <;> rfl
  right_inv q := by
    cases q with
    | inl q => cases q <;> rfl
    | inr q => rcases q with ⟨a,q⟩; cases a <;> rfl

def controlCode : Control.Head S Q ≃ Fin 5 ⊕ Simulator.Head S Q where
  toFun
    | .initial => .inl 0
    | .left => .inl 1
    | .right => .inl 2
    | .workspace => .inl 3
    | .suffix => .inl 4
    | .machine q => .inr q
  invFun
    | .inl k => if k=0 then .initial else if k=1 then .left else if k=2 then .right
      else if k=3 then .workspace else .suffix
    | .inr q => .machine q
  left_inv q := by cases q <;> rfl
  right_inv q := by
    cases q with
    | inl k => fin_cases k <;> rfl
    | inr q => rfl

noncomputable scoped instance staticPrimcodable [Fintype S] : Primcodable (Static S) :=
  Effect.finitePrimcodable _
noncomputable scoped instance simulatorPrimcodable [Fintype S] [Primcodable Q] :
    Primcodable (Simulator.Head S Q) := Primcodable.ofEquiv _ simCode
noncomputable scoped instance controlPrimcodable [Fintype S] [Primcodable Q] :
    Primcodable (Control.Head S Q) := Primcodable.ofEquiv _ controlCode

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open Simulator
open scoped HeadCodec
variable {S Γ Q Q' P : Type*}

def commandCode : Command Q Γ ≃ Q × Γ × Move where
  toFun c := (c.state,c.write,c.move)
  invFun c := ⟨c.1,c.2.1,c.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable scoped instance movePrimcodable : Primcodable Move := Effect.finitePrimcodable _
noncomputable scoped instance commandPrimcodable [Primcodable Q] [Primcodable Γ] : Primcodable (Command Q Γ) :=
  Primcodable.ofEquiv _ commandCode

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open Simulator
open scoped HeadCodec
variable {S Γ Q P : Type*} [Fintype S] [Fintype Γ] [DecidableEq S] [DecidableEq Γ]
  [Primcodable Γ] [Primcodable Q] [Primcodable P]
variable (A : Alphabet S Γ) (M : P → Machine Q Γ)
  (hinit : Primrec (fun p => (M p).initial))
  (htrans : Primrec (fun x : P × Q × Γ => (M x.1).transition x.2.1 x.2.2))

def dummy : Machine Unit Γ := ⟨(),fun _ _ => none⟩

def staticControl (k : Fin 5) : Control.Head S Q := controlCode.symm (.inl k)

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open FiniteAlgebraicEnvelopes.Effect
open scoped HeadCodec
variable {S Q : Type*} [Fintype S]

noncomputable def simSupport (qs : List Q) : List (Simulator.Head S Q) :=
  (Scan.finiteList (Static S)).map ofStatic ++ qs.flatMap (fun q => [.run q,.left q])
noncomputable def controlSupport (qs : List Q) : List (Control.Head S Q) :=
  (Scan.finiteList (Fin 5)).map staticControl ++ (simSupport qs).map Control.Head.machine

@[simp] theorem mem_simSupport (qs : List Q) (h : Simulator.Head S Q) :
    h∈simSupport qs ↔ match h with | .run q | .left q => q∈qs | _ => True := by
  cases h <;> simp [simSupport,ofStatic]
  case start => exact ⟨.start,rfl⟩
  case rewind r => exact ⟨.rewind r,rfl⟩
  case scan r => exact ⟨.scan r,rfl⟩
  case finish => exact ⟨.finish,rfl⟩
  case ok => exact ⟨.ok,rfl⟩
  case run q => intro a ha; cases a <;> cases ha
  case left q => intro a ha; cases a <;> cases ha

@[simp] theorem mem_controlSupport (qs : List Q) (h : Control.Head S Q) :
    h∈controlSupport qs ↔ match h with | .machine (.run q) | .machine (.left q) => q∈qs | _ => True := by
  cases h <;> simp only [controlSupport,List.mem_append,List.mem_map,Scan.mem_finiteList,true_and]
  case initial => exact iff_true_intro (Or.inl ⟨0,rfl⟩)
  case left => exact iff_true_intro (Or.inl ⟨1,rfl⟩)
  case right => exact iff_true_intro (Or.inl ⟨2,rfl⟩)
  case workspace => exact iff_true_intro (Or.inl ⟨3,rfl⟩)
  case suffix => exact iff_true_intro (Or.inl ⟨4,rfl⟩)
  case machine h =>
    have hn : ¬∃ a,staticControl a=Control.Head.machine h := by
      rintro ⟨a,ha⟩; fin_cases a <;> cases ha
    simp only [hn,false_or,Control.Head.machine.injEq,exists_eq_right,mem_simSupport]
    cases h <;> rfl

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SphereCover
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
namespace DiscreteCoverCharts
variable {ι X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
variable (Z : FiberBundleCore ι X Q)

def fiberEquiv (i : ι) (x : X) (hx : x ∈ Z.baseSet i) : Q ≃ Z.proj ⁻¹' {x} where
  toFun q := ⟨point Z i x q,rfl⟩
  invFun y := (Z.localTriv i y.1).2
  left_inv q := by
    change Z.coordChange (Z.indexAt x) i x (Z.coordChange i (Z.indexAt x) x q) = q
    rw [Z.coordChange_comp i (Z.indexAt x) i x ⟨⟨hx,Z.mem_baseSet_at x⟩,hx⟩ q,
      Z.coordChange_self i x hx q]
  right_inv y := by
    rcases y with ⟨⟨y,q⟩,hy⟩
    have he : y = x := hy
    subst y
    apply Subtype.ext
    change (⟨x,Z.coordChange i (Z.indexAt x) x (Z.coordChange (Z.indexAt x) i x q)⟩ : Z.TotalSpace) =
      ⟨x,q⟩
    rw [Z.coordChange_comp (Z.indexAt x) i (Z.indexAt x) x
      ⟨⟨Z.mem_baseSet_at x,hx⟩,Z.mem_baseSet_at x⟩ q,
      Z.coordChange_self (Z.indexAt x) x (Z.mem_baseSet_at x) q]

variable [DiscreteTopology Q]

theorem monodromy_chartPath (i : ι) {a b : X} (p : Path a b)
    (hp : Set.range p ⊆ Z.baseSet i) (q : Q) :
    (covering Z).monodromy (Path.Homotopic.Quotient.mk p)
      ⟨point Z i a q,rfl⟩ = ⟨point Z i b q,rfl⟩ := by
  apply (covering Z).monodromy_eq_of_map_eq
    (Path.Homotopic.Quotient.mk (chartPath Z i p hp q))
  change Path.Homotopic.Quotient.mk ((chartPath Z i p hp q).map Z.continuous_proj) =
    (Path.Homotopic.Quotient.mk p).cast rfl rfl
  rw [chartPath_map]
  rfl

end DiscreteCoverCharts

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

namespace FiberCoreMap
open Set Topology DiscreteCoverCharts
variable {ι κ X Y Q : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Q]
  (Z : FiberBundleCore ι X Q) (W : FiberBundleCore κ Y Q)
  (f : C(X,Y)) (idx : ι → κ)
  (hs : ∀ i x, x ∈ Z.baseSet i → f x ∈ W.baseSet (idx i))
  (ht : ∀ i j x, x ∈ Z.baseSet i ∩ Z.baseSet j → ∀ q,
    W.coordChange (idx i) (idx j) (f x) q = Z.coordChange i j x q)

include hs ht in
lemma fiber_bijective (x : X) : Function.Bijective
    (fun z : Z.proj ⁻¹' {x} =>
      (⟨map Z W f idx z.1,(map_proj Z W f idx z.1).trans (congrArg f z.2)⟩ : W.proj ⁻¹' {f x})) := by
  let i := Z.indexAt x
  let e := fiberEquiv Z i x (Z.mem_baseSet_at x)
  let e' := fiberEquiv W (idx i) (f x) (hs i x (Z.mem_baseSet_at x))
  have he (z : Z.proj ⁻¹' {x}) :
      (⟨map Z W f idx z.1,(map_proj Z W f idx z.1).trans (congrArg f z.2)⟩ : W.proj ⁻¹' {f x}) =
        e' (e.symm z) := by
    obtain ⟨⟨y,q⟩,hy⟩ := z
    change y = x at hy
    subst y
    apply Subtype.ext
    exact map_chart Z W f idx hs ht i ⟨x,q⟩ (Z.mem_baseSet_at x)
  simpa only [he,Function.comp_def] using e'.bijective.comp e.symm.bijective
end FiberCoreMap

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_FiberCoreMap
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
namespace FiberCoreMap
open Set Topology DiscreteCoverCharts
variable {ι κ X Y Q : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Q]
  (Z : FiberBundleCore ι X Q) (W : FiberBundleCore κ Y Q)
  (f : C(X,Y)) (idx : ι → κ)
  (hs : ∀ i x, x ∈ Z.baseSet i → f x ∈ W.baseSet (idx i))
  (ht : ∀ i j x, x ∈ Z.baseSet i ∩ Z.baseSet j → ∀ q,
    W.coordChange (idx i) (idx j) (f x) q = Z.coordChange i j x q)

include hs ht in
lemma map_injective (hf : Function.Injective f) : Function.Injective (map Z W f idx) := by
  intro a b h
  have hx : Z.proj a = Z.proj b := hf (congrArg W.proj h)
  have hh := @(fiber_bijective Z W f idx hs ht (Z.proj a)).1
    ⟨a,rfl⟩ ⟨b,hx.symm⟩ (Subtype.ext h)
  exact congrArg Subtype.val hh

include hs ht in

lemma isEmbedding (hf : IsEmbedding f) : IsEmbedding (map Z W f idx) := by
  let e := Equiv.ofInjective (map Z W f idx) (map_injective Z W f idx hs ht hf.injective)
  let R := Set.range (map Z W f idx)
  have hp (r : R) : W.proj r.1 ∈ Set.range f := by
    obtain ⟨a,ha⟩ := r.2
    exact ⟨Z.proj a,congrArg W.proj ha⟩
  let rb : C(R,Set.range f) :=
    ⟨fun r => ⟨W.proj r.1,hp r⟩,
      (W.continuous_proj.comp continuous_subtype_val).subtype_mk hp⟩
  let B : C(R,X) := (⟨hf.toHomeomorph.symm,hf.toHomeomorph.symm.continuous⟩ : C(Set.range f,X)).comp rb
  have hmap (r : R) : map Z W f idx (e.symm r) = r.1 :=
    congrArg Subtype.val (e.apply_symm_apply r)
  have hfr (r : R) : f (B r) = W.proj r.1 :=
    congrArg Subtype.val (hf.toHomeomorph.apply_symm_apply (rb r))
  have hB (r : R) : Z.proj (e.symm r) = B r := by
    apply hf.injective
    exact (congrArg W.proj (hmap r)).trans (hfr r).symm
  have hi : Continuous e.symm := by
    apply continuous_iff_continuousAt.mpr
    intro r
    let i := Z.indexAt (B r)
    let U : Set R := B ⁻¹' Z.baseSet i
    have hr : r ∈ U := Z.mem_baseSet_at (B r)
    have hU : IsOpen U := (Z.isOpen_baseSet i).preimage B.continuous
    have hW (r : R) (hr : r ∈ U) : (r.1 : W.TotalSpace) ∈ (W.localTriv (idx i)).source := by
      rw [← hmap r]
      exact hs i _ (by change Z.proj (e.symm r) ∈ Z.baseSet i; rw [hB]; exact hr)
    have hEq (r : R) (hr : r ∈ U) : e.symm r =
        point Z i (B r) ((W.localTriv (idx i)) r.1).2 := by
      have hz : Z.proj (e.symm r) ∈ Z.baseSet i := by rw [hB]; exact hr
      have hw : f (Z.proj (e.symm r)) ∈ W.baseSet (idx i) := hs i _ hz
      have hm := map_chart Z W f idx hs ht i (e.symm r) hz
      rw [hmap] at hm
      have hc := congrArg (fun a => ((W.localTriv (idx i)) a).2) hm
      have ht' := (fiberEquiv W (idx i) (f (Z.proj (e.symm r))) hw).left_inv
        ((Z.localTriv i) (e.symm r)).2
      change ((W.localTriv (idx i)) (point W (idx i) (f (Z.proj (e.symm r)))
        ((Z.localTriv i) (e.symm r)).2)).2 = _ at ht'
      rw [ht'] at hc
      rw [hc,← hB]
      exact congrArg Subtype.val ((fiberEquiv Z i (Z.proj (e.symm r)) hz).right_inv ⟨e.symm r,rfl⟩) |>.symm
    have hc : ContinuousOn (fun r : R => point Z i (B r) ((W.localTriv (idx i)) r.1).2) U := by
      apply (Z.localTriv i).toOpenPartialHomeomorph.symm.continuousOn.comp
      · exact B.continuous.continuousOn.prodMk (continuous_snd.comp_continuousOn
          ((W.localTriv (idx i)).continuousOn.comp continuous_subtype_val.continuousOn hW))
      · intro r hr
        exact (Z.mem_localTriv_target i _).mpr hr
    exact (hc.congr hEq).continuousAt (hU.mem_nhds hr)
  let h : Z.TotalSpace ≃ₜ R :=
    { e with
      continuous_toFun := (continuous_map Z W f idx hs ht).subtype_mk _
      continuous_invFun := hi }
  exact IsEmbedding.subtypeVal.comp h.isEmbedding
end FiberCoreMap

open Set Topology unitInterval

namespace CoveringCellGeometry

open Set
variable {X E A B : Type} [TopologicalSpace X] [TopologicalSpace E]
  [TopologicalSpace A] [TopologicalSpace B] [ContractibleSpace A] [PreconnectedSpace B]
  {p : E → X} (cov : IsCoveringMap p) (f : C(A,X)) (i : C(B,A))
  (s : C(B,E)) (hs : p ∘ s = f ∘ i) (b : B)

include cov hs b in

theorem exists_extension : ∃ L : C(A,E), p ∘ L = f ∧ L.comp i = s := by
  let j := sheet cov f ⟨(i b,s b),congrFun hs b⟩
  let L := characteristicLift cov f j
  refine ⟨L,funext (characteristicLift_proj cov f j),?_⟩
  apply DFunLike.coe_injective
  refine cov.eq_of_comp_eq (L.comp i).continuous s.continuous ?_ b ?_
  · funext z
    exact (characteristicLift_proj cov f j (i z)).trans (congrFun hs z).symm
  · exact characteristicLift_sheet cov f ⟨(i b,s b),congrFun hs b⟩

include cov hs b in
lemma boundary_nullhomotopic : ∃ e : E, s.Homotopic (ContinuousMap.const B e) := by
  obtain ⟨L,_,hL⟩ := exists_extension cov f i s hs b
  obtain ⟨a,⟨H⟩⟩ := id_nullhomotopic A
  refine ⟨L a,?_⟩
  rw [← hL]
  exact ⟨(ContinuousMap.Homotopy.refl L).comp (H.comp (ContinuousMap.Homotopy.refl i))⟩

end CoveringCellGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_StandardShapiro
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct
namespace StandardShapiro
open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct
variable {R G : Type} [CommRing R] [Group G] (S : Subgroup G)

lemma inclusion_π : inclusion (R := R) S ≫ (restrictedResolution S).π =
    (Rep.standardResolution R S).π := by
  apply HomologicalComplex.to_single_hom_ext
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  change (Rep.standardComplex.ε R G).hom
      (MonoidAlgebra.mapDomainLinearMap R R (fun s : Fin 1 → S => S.subtype ∘ s)
        (MonoidAlgebra.single s 1)) =
    (Rep.standardComplex.ε R S).hom (MonoidAlgebra.single s 1)
  simp [Rep.standardComplex.ε]
  rfl

def comparisonEquiv : HomotopyEquiv (Rep.standardResolution R S).complex
    (restrictedResolution (R := R) S).complex :=
  (ProjectiveResolution.homotopyEquiv (Rep.standardResolution R S) (restrictedResolution S)).copy
    (ProjectiveResolution.liftHomotopy (𝟙 (Rep.trivial R S R)) _ (inclusion S)
      (by rw [CategoryTheory.Functor.map_id, Category.comp_id]; exact
        ProjectiveResolution.homotopyEquiv_hom_π (Rep.standardResolution R S) (restrictedResolution S))
      (by rw [CategoryTheory.Functor.map_id, Category.comp_id]; exact inclusion_π S))

def indEquiv (A : Rep R S) :
    HomotopyEquiv ((Rep.standardComplex R S).coinvariantsTensorObj A)
      ((Rep.standardComplex R G).coinvariantsTensorObj (Rep.ind S.subtype A)) :=
  (((Rep.coinvariantsTensor R S).obj A).mapHomotopyEquiv (comparisonEquiv S)).trans
    (HomotopyEquiv.ofIso
      (groupHomology.coinvariantsTensorResProjectiveResolutionIso S A (Rep.standardResolution R G)))

lemma indEquiv_hom_f_mk_tmul (A : Rep R S) (n : ℕ) (a : A)
    (z : MonoidAlgebra R (Fin (n+1) → S)) :
    (indEquiv S A).hom.f n (Coinvariants.mk _ (a ⊗ₜ[R] z)) =
      Coinvariants.mk _ (IndV.mk S.subtype A.ρ 1 a ⊗ₜ[R]
        StandardVertex.map S.subtype S.subtype (by intro g x; rfl) n z) := by
  change Rep.coinvariantsTensorIndInv S.subtype A ((Rep.standardComplex R G).X n)
    (Coinvariants.mk _ (a ⊗ₜ[R]
      StandardVertex.map S.subtype S.subtype (by intro g x; rfl) n z)) = _
  exact Rep.coinvariantsTensorIndInv_mk_tmul_indMk _ _ _

end StandardShapiro

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CosetInduction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct
namespace CosetInduction
open _root_.CategoryTheory _root_.Representation
variable {R G : Type} [CommRing R] [Group G] (S : Subgroup G) (A : Rep R G)

def indCosetIso : Rep.ind S.subtype (Rep.res S.subtype A) ≅ cosetRep S A := by
  letI : Mono (indToCosets S A) := (Rep.mono_iff_injective _).mpr (by
    intro x y h
    have hx := LinearMap.congr_fun (cosetsToInd_indToCosets S A) x
    have hy := LinearMap.congr_fun (cosetsToInd_indToCosets S A) y
    change cosetsToInd S A (indToCosets S A x) = x at hx
    change cosetsToInd S A (indToCosets S A y) = y at hy
    exact hx.symm.trans ((congrArg (cosetsToInd S A) h).trans hy))
  letI : Epi (indToCosets S A) := (Rep.epi_iff_surjective _).mpr (by
    intro y
    refine ⟨cosetsToInd S A y,?_⟩
    exact LinearMap.congr_fun (indToCosets_cosetsToInd S A) y)
  letI := CategoryTheory.isIso_of_mono_of_epi (indToCosets S A)
  exact CategoryTheory.asIso (indToCosets S A)

end CosetInduction

namespace StandardShapiro
open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct
variable {R G : Type} [CommRing R] [Group G] (S : Subgroup G) (A : Rep R G)

def cosetCoefficientIso :
    (Rep.standardComplex R G).coinvariantsTensorObj (Rep.ind S.subtype (Rep.res S.subtype A)) ≅
      (Rep.standardComplex R G).coinvariantsTensorObj (CosetInduction.cosetRep S A) :=
  (NatIso.mapHomologicalComplex
    ((Rep.coinvariantsTensor R G).mapIso (CosetInduction.indCosetIso S A)) _).app _

def cosetEquiv :
    HomotopyEquiv ((Rep.standardComplex R S).coinvariantsTensorObj (Rep.res S.subtype A))
      ((Rep.standardComplex R G).coinvariantsTensorObj (CosetInduction.cosetRep S A)) :=
  (indEquiv S (Rep.res S.subtype A)).trans (HomotopyEquiv.ofIso (cosetCoefficientIso S A))

lemma cosetEquiv_hom_f_mk_tmul (n : ℕ) (a : A)
    (z : MonoidAlgebra R (Fin (n+1) → S)) :
    (cosetEquiv S A).hom.f n (Coinvariants.mk _ (a ⊗ₜ[R] z)) =
      Coinvariants.mk _ (Finsupp.single (QuotientGroup.mk (1 : G)) a ⊗ₜ[R]
        StandardVertex.map S.subtype S.subtype (by intro g x; rfl) n z) := by
  change (cosetCoefficientIso S A).hom.f n
    ((indEquiv S (Rep.res S.subtype A)).hom.f n (Coinvariants.mk _ (a ⊗ₜ[R] z))) = _
  rw [indEquiv_hom_f_mk_tmul]
  change Coinvariants.mk _ (CosetInduction.indToCosets S A
    (IndV.mk S.subtype (Rep.res S.subtype A).ρ 1 a) ⊗ₜ[R] _) = _
  rw [CosetInduction.indToCosets_mk]
  simp only [inv_one,map_one,Module.End.one_apply]
  rfl

end StandardShapiro

open _root_.CategoryTheory CategoryTheory.Limits

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SemilinearCoinvariants
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct
open _root_.CategoryTheory CategoryTheory.Limits
namespace SemilinearCoinvariants
variable {R G H : Type} [CommRing R] [Group G] [Group H]
variable (φ : G →* H) {A : Rep R G} {B : Rep R H}

lemma tensorNatTrans_mk_tmul (α : A ⟶ Rep.res φ B) (Q : Rep R H)
    (a : A) (q : Q) :
    (tensorNatTrans φ α).app Q (Coinvariants.mk _ (a ⊗ₜ[R] q)) =
      Coinvariants.mk _ (α a ⊗ₜ[R] q) := by
  simp [tensorNatTrans,Rep.coinvariantsTensorIndInv,Rep.coinvariantsTensorMk,
    Rep.indResHomEquiv]

variable (P : ChainComplex (Rep R G) ℕ) (Q : ChainComplex (Rep R H) ℕ)

lemma chainMap_f_mk_tmul (α : A ⟶ Rep.res φ B)
    (β : P ⟶ ((Rep.resFunctor φ).mapHomologicalComplex _).obj Q) (n : ℕ)
    (a : A) (p : P.X n) :
    (chainMap φ P Q α β).f n (Coinvariants.mk _ (a ⊗ₜ[R] p)) =
      Coinvariants.mk _ (α a ⊗ₜ[R] β.f n p) := by
  change (tensorNatTrans φ α).app (Q.X n)
    ((((Rep.coinvariantsTensor R G).obj A).map (β.f n))
      (Coinvariants.mk _ (a ⊗ₜ[R] p))) = _
  change (tensorNatTrans φ α).app (Q.X n)
    (Coinvariants.mk _ (a ⊗ₜ[R] β.f n p)) = _
  exact tensorNatTrans_mk_tmul φ α (Q.X n) a (β.f n p)

end SemilinearCoinvariants

namespace CosetEndpoint
open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct
variable {R G : Type} [CommRing R] [Group G] (S : Subgroup G) (A : Rep R G)
variable (f : S →* S) (t : G) (ht : ∀ s : S, (s : G)*t = t*(f s : G))

def shiftChain :
    (Rep.standardComplex R S).coinvariantsTensorObj (Rep.res S.subtype A) ⟶
      (Rep.standardComplex R S).coinvariantsTensorObj (Rep.res S.subtype A) :=
  SemilinearCoinvariants.chainMap f _ _ (shiftCoeff S A f t ht)
    (StandardVertex.chainMap f f (by intro s u; exact f.map_mul s u))

end CosetEndpoint

namespace StandardTensor

open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct
variable {R G H : Type} [CommRing R] [Group G] [Group H]

lemma semilinear_single (φ : G →* H) {A : Rep R G} {B : Rep R H}
    (α : A ⟶ Rep.res φ B) (v : G → H) (hv : ∀ g x, v (g*x)=φ g*v x)
    (n : ℕ) (a : A) (s : Fin (n+1) → G) :
    (SemilinearCoinvariants.chainMap φ (Rep.standardComplex R G) (Rep.standardComplex R H)
      α (StandardVertex.chainMap φ v hv)).f n
      (Coinvariants.mk _ (a ⊗ₜ[R] MonoidAlgebra.single s 1)) =
        Coinvariants.mk (B.ρ.tprod (Rep.diagonal R H (n+1)).ρ) ((α a : B) ⊗ₜ[R] MonoidAlgebra.single (v ∘ s) 1) := by
  exact (SemilinearCoinvariants.chainMap_f_mk_tmul φ _ _ α
    (StandardVertex.chainMap φ v hv) n a (MonoidAlgebra.single s 1)).trans
      (congrArg (fun z : MonoidAlgebra R (Fin (n+1) → H) => Coinvariants.mk (B.ρ.tprod (Rep.diagonal R H (n+1)).ρ) ((α a : B) ⊗ₜ[R] z))
        (StandardVertex.map_single φ v hv n s 1))

lemma shapiro_single (S : Subgroup G) (A : Rep R G) (n : ℕ) (a : A) (s : Fin (n+1) → S) :
    (StandardShapiro.cosetEquiv S A).hom.f n
      (Coinvariants.mk _ (a ⊗ₜ[R] MonoidAlgebra.single s 1)) =
        Coinvariants.mk ((CosetInduction.cosetRep S A).ρ.tprod (Rep.diagonal R G (n+1)).ρ) ((Finsupp.single (QuotientGroup.mk (1 : G)) a : CosetInduction.cosetRep S A) ⊗ₜ[R]
          MonoidAlgebra.single (S.subtype ∘ s) 1) := by
  exact (StandardShapiro.cosetEquiv_hom_f_mk_tmul S A n a (MonoidAlgebra.single s 1)).trans
    (congrArg (fun z : MonoidAlgebra R (Fin (n+1) → G) =>
      Coinvariants.mk ((CosetInduction.cosetRep S A).ρ.tprod (Rep.diagonal R G (n+1)).ρ)
        (Finsupp.single (QuotientGroup.mk (1 : G)) a ⊗ₜ[R] z))
        (StandardVertex.map_single S.subtype S.subtype (by intro g x; rfl) n s 1))

end StandardTensor

namespace CosetEndpoint
open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct
variable {R G : Type} [CommRing R] [Group G] (S : Subgroup G) (A : Rep R G)
variable (f : S →* S) (t : G) (ht : ∀ s : S, (s : G)*t = t*(f s : G))
variable (p : (G ⧸ S) → G ⧸ S) (peq : ∀ (g : G) (v : G ⧸ S), p (g • v) = g • p v)
variable (pbase : p (QuotientGroup.mk (1 : G)) = QuotientGroup.mk t)

include pbase in
lemma shapiro_parent_eq_left :
    (StandardShapiro.cosetEquiv S A).hom ≫
      StandardTensor.coefficientMap (FunctionalTree.parentHom A p peq) =
        leftChain S A f t ht := by
  apply StandardTensor.chain_ext
  intro n a s
  have h₁ := congrArg
    (fun x => (StandardTensor.coefficientMap (FunctionalTree.parentHom A p peq)).f n x)
    (StandardTensor.shapiro_single S A n a s)
  have h₂ := StandardTensor.coefficientMap_f_mk_tmul (FunctionalTree.parentHom A p peq) n
    (Finsupp.single (QuotientGroup.mk (1 : G)) a)
    (MonoidAlgebra.single (S.subtype ∘ s) 1)
  have h₃ := StandardTensor.semilinear_single (S.subtype.comp f)
    (baseShiftCoeff S A f t ht) (fun s : S => t⁻¹*(s : G))
    (leftVertex_equivariant S f t ht) n a s
  apply (h₁.trans h₂).trans
  apply Eq.trans _ h₃.symm
  change Coinvariants.mk ((CosetInduction.cosetRep S A).ρ.tprod (Rep.diagonal R G (n+1)).ρ)
    (FunctionalTree.parentMap p
      (Finsupp.single (QuotientGroup.mk (1 : G)) a) ⊗ₜ[R]
    MonoidAlgebra.single (S.subtype ∘ s) 1) =
    Coinvariants.mk ((CosetInduction.cosetRep S A).ρ.tprod (Rep.diagonal R G (n+1)).ρ)
      (Finsupp.single (QuotientGroup.mk (1 : G)) (A.ρ t⁻¹ a) ⊗ₜ[R]
      MonoidAlgebra.single ((fun s : S => t⁻¹*(s : G)) ∘ s) 1)
  rw [FunctionalTree.parentMap_single,pbase]
  have h := Coinvariants.mk_self_apply
    ((CosetInduction.cosetRep S A).ρ.tprod (Rep.diagonal R G (n+1)).ρ) t⁻¹
    (Finsupp.single (QuotientGroup.mk t) a ⊗ₜ[R]
      MonoidAlgebra.single (S.subtype ∘ s) 1)
  have hact : ((CosetInduction.cosetRep S A).ρ.tprod
      (Rep.diagonal R G (n+1)).ρ) t⁻¹
      (Finsupp.single (QuotientGroup.mk t) a ⊗ₜ[R]
        MonoidAlgebra.single (S.subtype ∘ s) 1) =
      Finsupp.single (QuotientGroup.mk (1 : G)) (A.ρ t⁻¹ a) ⊗ₜ[R]
        MonoidAlgebra.single ((fun s : S => t⁻¹*(s : G)) ∘ s) 1 := by
    change (FunctionalTree.diagonalRep A).ρ t⁻¹
        (Finsupp.single (QuotientGroup.mk t) a) ⊗ₜ[R]
        (Rep.diagonal R G (n+1)).ρ t⁻¹
        (MonoidAlgebra.single (S.subtype ∘ s) 1) = _
    rw [FunctionalTree.diagonalRep_single]
    simp only [MulAction.Quotient.smul_mk,smul_eq_mul,inv_mul_cancel]
    change _ ⊗ₜ[R] Representation.ofMulAction R G (Fin (n+1) → G) t⁻¹
      (MonoidAlgebra.single (S.subtype ∘ s) 1) = _
    rw [Representation.ofMulAction_single]
    rfl
  rw [hact] at h
  exact h.symm

lemma shift_shapiro_eq_right :
    shiftChain S A f t ht ≫ (StandardShapiro.cosetEquiv S A).hom =
      rightChain S A f t ht := by
  apply StandardTensor.chain_ext
  intro n a s
  have h₁ := congrArg (fun x => (StandardShapiro.cosetEquiv S A).hom.f n x)
    (StandardTensor.semilinear_single f (shiftCoeff S A f t ht) f
      (by intro g x; exact f.map_mul g x) n a s)
  have h₂ := StandardTensor.shapiro_single S A n (A.ρ t⁻¹ a) (f ∘ s)
  have h₃ := StandardTensor.semilinear_single (S.subtype.comp f)
    (baseShiftCoeff S A f t ht) (S.subtype.comp f)
    (by intro g x; exact (S.subtype.comp f).map_mul g x) n a s
  exact (h₁.trans h₂).trans h₃.symm

def shapiroParentHomotopy : Homotopy
    ((StandardShapiro.cosetEquiv S A).hom ≫
      StandardTensor.coefficientMap (FunctionalTree.parentHom A p peq))
    (shiftChain S A f t ht ≫ (StandardShapiro.cosetEquiv S A).hom) := by
  rw [shapiro_parent_eq_left S A f t ht p peq pbase,shift_shapiro_eq_right]
  exact endpointHomotopy S A f t ht

end CosetEndpoint

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

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderListChains
section

variable (G : Type*)

def simplexVertex (a : G) : Simplex G := (a, [])

end

end OrderListChains

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
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits

end

open _root_.CategoryTheory CategoryTheory.Limits
namespace EquivariantOrderChains
open OrderListChains
variable {G P : Type} [Group G] [Preorder P] [MulAction G P]
  [CovariantClass G P HSMul.hSMul LE.le] {n : ℕ}

instance covariantPosetAction : ActionTransport.IsMonotoneAction G P where
  mono g _ _ h := smul_le_smul_left g h

end EquivariantOrderChains

end

end OAI
end


