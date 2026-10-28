-- Prove2me | Definitions.Def_OAIQ085D004
-- name    : OAIQ085D004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T15:55:16.30576+00:00
-- url     : https://prove2.me/theorems/6df93e9d-9d91-438e-8695-b2474aa64f72
-- title:
--   Definitions bundle OAIQ085D004 of the split of OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 453 declarations of OpenAI's Lean: 226 definitions, 16 inductive types or structures, 18 instances and 193 theorems. The definitions and types are `OAI.DFVSGames.Inverse.MatrixChart.lowerRows`, `OAI.DFVSGames.Inverse.MatrixChart.upperColumns`, `OAI.DFVSGames.Inverse.RowErasure.SelectionPartition.fiber`, `OAI.DFVSGames.Inverse.RowErasure.goodUnion`, `OAI.DFVSGames.Inverse.RowErasure.replaceOn`, `OAI.DFVSGames.Inverse.ShortcodeFromGrassmann.zeroFactorMass`, `OAI.DFVSGames.Quadratic.SquarefreeExponent`, `OAI.DFVSGames.Quadratic.UniformSubspaces.Injection`, `OAI.DFVSGames.Quadratic.alignedCharacters`, `OAI.DFVSGames.Quadratic.alignmentMatrix`, `OAI.DFVSGames.Quadratic.alignmentObstruction`, `OAI.DFVSGames.Quadratic.assignmentProbability`, `OAI.DFVSGames.Quadratic.blockExponent`, `OAI.DFVSGames.Quadratic.cubicEvaluationSpan`, `OAI.DFVSGames.Quadratic.cubicPairing`, `OAI.DFVSGames.Quadratic.distinctNonzeroBinaryPairs`, `OAI.DFVSGames.Quadratic.fieldDegree`, `OAI.DFVSGames.Quadratic.finiteAssignmentProbability`, `OAI.DFVSGames.Quadratic.lossIndices`, `OAI.DFVSGames.Quadratic.nonzeroBinaryInputs`, `OAI.DFVSGames.Quadratic.parameterMap`, `OAI.DFVSGames.Quadratic.parameterMapEquiv`, `OAI.DFVSGames.Quadratic.quadraticEvaluationSpan`, `OAI.DFVSGames.Quadratic.reindexAssignments`, `OAI.DFVSGames.Quadratic.selectorAssignment`, `OAI.DFVSGames.Quadratic.separationPolynomial`, `OAI.DFVSGames.Quadratic.universalAlignmentColumn`, `OAI.DFVSGames.Quadratic.universalLinearForm`, `OAI.DFVSGames.Quadratic.universalPairMinor`, `OAI.DFVSGames.Reduction.ActualCanonical.singletonTriple`, `OAI.DFVSGames.Soundness.ConditionalIncidences.coordinateReindex`, `OAI.DFVSGames.Soundness.ConditionalIncidences.incidence`, `OAI.DFVSGames.Soundness.PartnerFullSampling.restrictIndices`, `OAI.DFVSGames.Soundness.PartnerFullSampling.restrictionProductEquiv`, `OAI.DFVSGames.Soundness.ZeroInformation.decodeIndex`, `OAI.DFVSGames.Soundness.ZeroInformation.reconstructQuestion`, `OAI.DFVSMaxCut.Analytic.degree`, `OAI.DFVSMaxCut.BooleanFourthMoment.discreteDiff`, `OAI.DFVSMaxCut.BooleanFourthMoment.energy`, `OAI.DFVSMaxCut.BooleanFourthMoment.polynomial` and 202 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DirectedFeedback_Encoding_ActualGoodRows`, `DirectedFeedback_Games_ActualCanonical`, `DirectedFeedback_Games_BlockOrientations`, `DirectedFeedback_Games_ConditionalIncidences`, `DirectedFeedback_Games_GenericPolynomial`, `DirectedFeedback_Games_Genericity`, `DirectedFeedback_Games_KMSBasisComparisonRetention`, `DirectedFeedback_Games_KernelCardinality`, `DirectedFeedback_Games_MatrixChartDegreeNeighbors`, `DirectedFeedback_Games_NonlinearRecurrence`, `DirectedFeedback_Games_PartnerFullSampling`, `DirectedFeedback_Games_PositiveMultiplier`, `DirectedFeedback_Main`, `DirectedFeedback_Probability_PolynomialProbability`, `DirectedFeedback_Probability_RepeatedGameBounds`, `DirectedFeedback_RankGraph_AllGraph`, `DirectedFeedback_RankGraph_Bias`, `DirectedFeedback_RankGraph_CellCount`, `DirectedFeedback_RankGraph_ExprLayout`, `DirectedFeedback_RankGraph_FailureEvent`, `DirectedFeedback_RankGraph_LastBias`, `DirectedFeedback_RankGraph_OutputDef`, `DirectedFeedback_RankGraph_Point`, `DirectedFeedback_RankGraph_PrefixBit`, `DirectedFeedback_RankGraph_RoundBoolean`, `DirectedFeedback_RankGraph_StackFinite`, `DirectedFeedback_RankGraph_Store`, `DirectedFeedback_RankGraph_UnweightedIntegrated`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ085D009`, `OAIQ085D010` and `OAIQ085D011`.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_Store
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace DirectedFeedback.StackDSL
open Turing

variable {K S : Type} [DecidableEq K]

structure Store (K S : Type) where
  state : S
  tape : K → List Bool

inductive Prim (K S : Type)
  | push (k : K) (value : S → Bool)
  | pop (k : K) (update : S → Option Bool → S)
  | peek (k : K) (update : S → Option Bool → S)
  | load (update : S → S)

namespace Prim

def run : Prim K S → Store K S → Store K S
  | .push k f, s => ⟨s.state, Function.update s.tape k (f s.state :: s.tape k)⟩
  | .pop k f, s => ⟨f s.state (s.tape k).head?, Function.update s.tape k (s.tape k).tail⟩
  | .peek k f, s => ⟨f s.state (s.tape k).head?, s.tape⟩
  | .load f, s => ⟨f s.state,s.tape⟩

end Prim

inductive Code (K S : Type)
  | atom (p : Prim K S)
  | seq (first second : Code K S)
  | branch (test : S → Bool) (yes no : Code K S)
  | scan (input : K) (update : S → Bool → S) (body : Code K S)

namespace Code

theorem iterate_sum {A : Type} (f : A → A) (n m : Nat) (a : A) :
    f^[n+m] a = f^[m] (f^[n] a) := by
  rw [Nat.add_comm,Function.iterate_add_apply]

@[reducible] def Label : Code K S → Type
  | .atom _ => Unit
  | .seq c d => Label c ⊕ Label d
  | .branch _ c d => Unit ⊕ (Label c ⊕ Label d)
  | .scan _ _ c => Unit ⊕ Label c

noncomputable instance labelFintype (c : Code K S) : Fintype c.Label := by
  induction c with
  | atom => exact inferInstanceAs (Fintype Unit)
  | seq c d ihc ihd => exact @instFintypeSum c.Label d.Label ihc ihd
  | branch f c d ihc ihd =>
    exact @instFintypeSum Unit (c.Label ⊕ d.Label) inferInstance
      (@instFintypeSum c.Label d.Label ihc ihd)
  | scan k f c ih => exact @instFintypeSum Unit c.Label inferInstance ih

@[reducible] def entry : (c : Code K S) → c.Label
  | .atom _ => ()
  | .seq c _ => .inl c.entry
  | .branch _ _ _ => .inl ()
  | .scan _ _ _ => .inl ()

def ret {L : Type} (exit : Option L) : TM2.Stmt (fun _ : K => Bool) L (S × Option Bool) :=
  match exit with
  | none => .halt
  | some l => .goto (fun _ => l)

@[simp] theorem ret_eval {L : Type} (exit : Option L) (s : S × Option Bool)
    (t : K → List Bool) : TM2.stepAux (ret exit) s t = ⟨exit,s,t⟩ := by
  cases exit <;> rfl

def primitive {L : Type} (p : Prim K S) (exit : Option L) :
    TM2.Stmt (fun _ : K => Bool) L (S × Option Bool) :=
  match p with
  | .push k f => .push k (fun s => f s.1) (ret exit)
  | .pop k f => .pop k (fun s x => (f s.1 x,s.2)) (ret exit)
  | .peek k f => .peek k (fun s x => (f s.1 x,s.2)) (ret exit)
  | .load f => .load (fun s => (f s.1,s.2)) (ret exit)

def compile {L : Type} : (c : Code K S) → (c.Label → L) → Option L →
    c.Label → TM2.Stmt (fun _ : K => Bool) L (S × Option Bool)
  | .atom p, _, exit, _ => primitive p exit
  | .seq c d, label, _, .inl i =>
    c.compile (fun j => label (.inl j)) (some (label (.inr d.entry))) i
  | .seq _ d, label, exit, .inr i =>
    d.compile (fun j => label (.inr j)) exit i
  | .branch f c d, label, _, .inl _ =>
    .branch (fun s => f s.1) (.goto fun _ => label (.inr (.inl c.entry)))
      (.goto fun _ => label (.inr (.inr d.entry)))
  | .branch _ c _, label, exit, .inr (.inl i) =>
    c.compile (fun j => label (.inr (.inl j))) exit i
  | .branch _ _ d, label, exit, .inr (.inr i) =>
    d.compile (fun j => label (.inr (.inr j))) exit i
  | .scan k update c, label, exit, .inl _ =>
    .pop k (fun s x => (s.1,x))
      (.branch (fun s => s.2.isSome)
        (.load (fun s => (s.2.elim s.1 (update s.1),none))
          (.goto fun _ => label (.inr c.entry)))
        (.load (fun s => (s.1,none)) (ret exit)))
  | .scan _ _ c, label, _, .inr i =>
    c.compile (fun j => label (.inr j)) (some (label (.inl ()))) i

inductive Exec : Code K S → Store K S → Nat → Store K S → Prop
  | atom (p : Prim K S) (s : Store K S) : Exec (.atom p) s 1 (p.run s)
  | seq {c d : Code K S} {s t u : Store K S} {n m : Nat} :
    Exec c s n t → Exec d t m u → Exec (.seq c d) s (n+m) u
  | branch_true {f : S → Bool} {c d : Code K S} {s t : Store K S} {n : Nat} :
    f s.state = true → Exec c s n t → Exec (.branch f c d) s (1+n) t
  | branch_false {f : S → Bool} {c d : Code K S} {s t : Store K S} {n : Nat} :
    f s.state = false → Exec d s n t → Exec (.branch f c d) s (1+n) t
  | scan_nil {k : K} {f : S → Bool → S} {c : Code K S} {s : Store K S} :
    s.tape k = [] → Exec (.scan k f c) s 1 s
  | scan_cons {k : K} {f : S → Bool → S} {c : Code K S}
      {s t u : Store K S} {b : Bool} {rest : List Bool} {n m : Nat} :
    s.tape k = b :: rest →
    Exec c ⟨f s.state b,Function.update s.tape k rest⟩ n t →
    Exec (.scan k f c) t m u → Exec (.scan k f c) s (1+n+m) u

def cfg {L : Type} (l : Option L) (s : Store K S) :
    TM2.Cfg (fun _ : K => Bool) L (S × Option Bool) := ⟨l,(s.state,none),s.tape⟩

def advance {L : Type} (program : L → TM2.Stmt (fun _ : K => Bool) L (S × Option Bool))
    (s : Option (TM2.Cfg (fun _ : K => Bool) L (S × Option Bool))) := s.bind (TM2.step program)

@[simp] theorem advance_some {L : Type} (program : L → TM2.Stmt (fun _ : K => Bool) L (S × Option Bool))
    (s : TM2.Cfg (fun _ : K => Bool) L (S × Option Bool)) :
    advance program (some s) = TM2.step program s := rfl

theorem Exec.trace {c : Code K S} {s t : Store K S} {n : Nat} (h : Exec c s n t)
    {L : Type} (label : c.Label → L) (exit : Option L)
    (program : L → TM2.Stmt (fun _ : K => Bool) L (S × Option Bool))
    (atLabel : ∀ i, program (label i) = c.compile label exit i) :
    (advance program)^[n] (some (cfg (some (label c.entry)) s)) = some (cfg exit t) := by
  induction h generalizing L with
  | atom p s =>
    simp only [Function.iterate_one,advance_some,cfg,TM2.step]
    rw [atLabel]
    cases p <;> simp [compile,primitive,Prim.run]
  | @seq c d s t u n m hc hd ihc ihd =>
    rw [iterate_sum]
    dsimp only [entry]
    rw [ihc (fun i => label (.inl i)) (some (label (.inr d.entry))) program
      (fun i => atLabel (.inl i))]
    exact ihd (fun i => label (.inr i)) exit program (fun i => atLabel (.inr i))
  | @branch_true f c d s t n hf hc ih =>
    rw [iterate_sum]
    have first : advance program (some (cfg (some (label (.inl ()))) s)) =
        some (cfg (some (label (.inr (.inl c.entry)))) s) := by
      simp only [advance_some,cfg,TM2.step]
      rw [atLabel (.inl ())]
      simp only [compile,TM2.stepAux,hf,Bool.cond_true]
    simp only [Function.iterate_one,entry]
    change (advance program)^[n] (advance program (some (cfg _ s))) = _
    rw [first]
    exact ih _ exit program (fun i => atLabel (.inr (.inl i)))
  | @branch_false f c d s t n hf hd ih =>
    rw [iterate_sum]
    have first : advance program (some (cfg (some (label (.inl ()))) s)) =
        some (cfg (some (label (.inr (.inr d.entry)))) s) := by
      simp only [advance_some,cfg,TM2.step]
      rw [atLabel (.inl ())]
      simp only [compile,TM2.stepAux,hf,Bool.cond_false]
    simp only [Function.iterate_one,entry]
    change (advance program)^[n] (advance program (some (cfg _ s))) = _
    rw [first]
    exact ih _ exit program (fun i => atLabel (.inr (.inr i)))
  | @scan_nil k f c s hs =>
    simp only [Function.iterate_one,advance_some,cfg,TM2.step,entry]
    rw [atLabel (.inl ())]
    simp only [compile,TM2.stepAux,hs,List.head?_nil,List.tail_nil,
      Option.isSome_none,Bool.cond_false,ret_eval]
    congr 2
    exact Function.update_eq_self_iff.mpr hs.symm
  | @scan_cons k f c s t u b rest n m hs hc hl ihc ihl =>
    have first : advance program (some (cfg (some (label (.inl ()))) s)) =
        some (cfg (some (label (.inr c.entry)))
          ⟨f s.state b,Function.update s.tape k rest⟩) := by
      simp only [advance_some,cfg,TM2.step]
      rw [atLabel (.inl ())]
      simp only [compile,TM2.stepAux,hs,
        List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,Option.elim_some]
    rw [iterate_sum,iterate_sum]
    change (advance program)^[m] ((advance program)^[n]
      (advance program (some (cfg (some (label (.inl ()))) s)))) = _
    rw [first,ihc (fun i => label (.inr i)) (some (label (.inl ()))) program
      (fun i => atLabel (.inr i))]
    exact ihl label exit program atLabel

end Code
end DirectedFeedback.StackDSL

namespace DirectedFeedback.StackDSL
open Turing
namespace Code
variable {K S : Type} [DecidableEq K] [Fintype K] [Fintype S]

def ioStore (initial : S) (k : K) (input : List Bool) : Store K S :=
  ⟨initial,fun j => if j = k then input else []⟩

@[reducible] noncomputable def machine (c : Code K S) (initial : S) (input output : K) : FinTM2 where
  K := K
  k₀ := input
  k₁ := output
  Γ := fun _ => Bool
  Λ := c.Label
  main := c.entry
  σ := S × Option Bool
  initialState := (initial,none)
  m := c.compile id none

theorem machine_init (c : Code K S) (initial : S) (input output : K) (bits : List Bool) :
    initList (c.machine initial input output) bits = cfg (some c.entry) (ioStore initial input bits) := by
  rfl

theorem machine_halt (c : Code K S) (initial : S) (input output : K) (bits : List Bool) :
    haltList (c.machine initial input output) bits = cfg none (ioStore initial output bits) := by
  rfl

noncomputable def computation {A B : Type} (ea : A → List Bool) (eb : B → List Bool)
    (f : A → B) (c : Code K S) (initial : S) (input output : K)
    (time : Polynomial Nat) (cost : A → Nat)
    (runs : ∀ a, c.Exec (ioStore initial input (ea a)) (cost a) (ioStore initial output (eb (f a))))
    (bound : ∀ a, cost a ≤ time.eval (ea a).length) :
    TM2ComputableInPolyTime ea eb f where
  tm := c.machine initial input output
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time
  outputsFun a := {
    steps := cost a
    evals_in_steps := by
      simp only [Equiv.refl, List.map_id, Option.map_some]
      change (advance (c.compile id none))^[cost a]
        (some (initList (c.machine initial input output) (ea a))) =
          some (haltList (c.machine initial input output) (eb (f a)))
      rw [machine_init,machine_halt]
      exact (runs a).trace id none (c.compile id none) (fun _ => rfl)
    steps_le_m := bound a }

end Code
end DirectedFeedback.StackDSL

end


namespace DirectedFeedback.StackDSL
open Code
variable {K : Type} [DecidableEq K]

namespace Store

def put (s : Store K Bool) (k : K) (value : List Bool) : Store K Bool :=
  ⟨s.state,Function.update s.tape k value⟩
def flag (s : Store K Bool) (value : Bool) : Store K Bool := ⟨value,s.tape⟩

@[simp] theorem put_tape_same (s : Store K Bool) (k : K) (v : List Bool) : (s.put k v).tape k = v := by
  simp [put]
@[simp] theorem put_tape_other (s : Store K Bool) {k j : K} (h : j ≠ k) (v : List Bool) :
    (s.put k v).tape j = s.tape j := by simp [put,h]
@[simp] theorem put_state (s : Store K Bool) (k : K) (v : List Bool) : (s.put k v).state = s.state := rfl
omit [DecidableEq K] in
@[simp] theorem flag_state (s : Store K Bool) (b : Bool) : (s.flag b).state = b := rfl
omit [DecidableEq K] in
@[simp] theorem flag_tape (s : Store K Bool) (b : Bool) : (s.flag b).tape = s.tape := rfl
@[simp] theorem put_put (s : Store K Bool) (k : K) (v w : List Bool) : (s.put k v).put k w = s.put k w := by
  simp [put]
@[simp] theorem put_self (s : Store K Bool) (k : K) : s.put k (s.tape k) = s := by
  cases s
  simp [put]
omit [DecidableEq K] in
@[simp] theorem flag_flag (s : Store K Bool) (b c : Bool) : (s.flag b).flag c = s.flag c := rfl
omit [DecidableEq K] in
@[simp] theorem flag_self (s : Store K Bool) : s.flag s.state = s := by cases s; rfl
@[simp] theorem put_flag (s : Store K Bool) (k : K) (v : List Bool) (b : Bool) :
    (s.flag b).put k v = (s.put k v).flag b := rfl

theorem put_comm (s : Store K Bool) {k j : K} (h : k ≠ j) (v w : List Bool) :
    (s.put k v).put j w = (s.put j w).put k v := by
  simp [put,Function.update_comm h]

omit [DecidableEq K] in
@[ext] theorem ext (s t : Store K Bool) (hs : s.state = t.state) (ht : s.tape = t.tape) : s=t := by
  cases s; cases t; simp_all

end Store

namespace Ops

@[reducible] def idle : Code K Bool := .atom (.load id)
@[reducible] def reset : Code K Bool := .atom (.load fun _ => false)
@[reducible] def push (k : K) (b : Bool) : Code K Bool := .atom (.push k fun _ => b)
@[reducible] def pop (k : K) : Code K Bool := .atom (.pop k fun s _ => s)
@[reducible] def clear (k : K) : Code K Bool := .scan k (fun s _ => s) idle

theorem idle_run (s : Store K Bool) : idle.Exec s 1 s := by
  exact Exec.atom (.load id) s

theorem reset_run (s : Store K Bool) : reset.Exec s 1 (s.flag false) := by
  exact Exec.atom (.load fun _ => false) s

theorem push_run (s : Store K Bool) (k : K) (b : Bool) :
    (push k b).Exec s 1 (s.put k (b::s.tape k)) := by
  exact Exec.atom (.push k fun _ => b) s

theorem pop_run (s : Store K Bool) (k : K) :
    (pop k).Exec s 1 (s.put k (s.tape k).tail) := by
  exact Exec.atom (.pop k fun s _ => s) s

theorem clear_list (k : K) (s : Store K Bool) (l : List Bool) :
    (clear k).Exec (s.put k l) (2*l.length+1) (s.put k []) := by
  induction l with
  | nil => simpa using (Exec.scan_nil (c := idle) (f := fun s _ => s)
      (s := s.put k []) (by simp))
  | cons b l ih =>
    have h : (clear k).Exec (s.put k (b::l)) (1+1+(2*l.length+1)) (s.put k []) := by
      apply Exec.scan_cons (b := b) (rest := l) (by simp)
      · change idle.Exec ((s.put k (b::l)).put k l) 1 (s.put k l)
        simpa using idle_run (s.put k l)
      · exact ih
    convert h using 1; simp; omega

theorem clear_run (k : K) (s : Store K Bool) :
    (clear k).Exec s (2*(s.tape k).length+1) (s.put k []) := by
  simpa using clear_list k s (s.tape k)

@[reducible] def transferScan (src dst : K) : Code K Bool := .scan src (fun _ b => b) (.atom (.push dst id))
@[reducible] def transfer (src dst : K) : Code K Bool := .seq (transferScan src dst) reset

theorem transferScan_run (src dst : K) (hne : src ≠ dst) (l d : List Bool) (s : Store K Bool) :
    ∃ b, (transferScan src dst).Exec ((s.put src l).put dst d) (2*l.length+1)
      (((s.put src []).put dst (l.reverse++d)).flag b) := by
  induction l generalizing d s with
  | nil =>
    refine ⟨s.state,?_⟩
    simpa [transferScan,Store.put,Store.flag] using (Exec.scan_nil (c := .atom (.push dst id)) (f := fun _ b => b)
      (s := (s.put src []).put dst d) (by simp [hne]))
  | cons b l ih =>
    obtain ⟨q,hq⟩ := ih (b::d) (s.flag b)
    refine ⟨q,?_⟩
    have hbody : (.atom (.push dst id) : Code K Bool).Exec
        ⟨b,Function.update (((s.put src (b::l)).put dst d).tape) src l⟩ 1
        (((s.flag b).put src l).put dst (b::d)) := by
      convert Exec.atom (.push dst id)
        (⟨b,Function.update (((s.put src (b::l)).put dst d).tape) src l⟩ : Store K Bool) using 1
      all_goals try with_reducible_and_instances rfl
      refine Store.ext _ _ ?_ ?_
      · rfl
      funext k
      by_cases hs : k = src <;> by_cases hd : k = dst <;>
        simp_all [Prim.run,Store.put,Store.flag,Function.update_apply]
    have h := Exec.scan_cons (k := src) (f := fun _ b => b)
      (c := .atom (.push dst id))
      (s := (s.put src (b::l)).put dst d) (b := b) (rest := l) (by simp [hne]) hbody hq
    convert h using 1 <;> simp [List.reverse_cons,List.append_assoc]; omega

theorem transfer_run (src dst : K) (hne : src ≠ dst) (s : Store K Bool) :
    (transfer src dst).Exec s (2*(s.tape src).length+2)
      (((s.put src []).put dst ((s.tape src).reverse++s.tape dst)).flag false) := by
  obtain ⟨b,h⟩ := transferScan_run src dst hne (s.tape src) (s.tape dst) s
  simp only [Store.put_self] at h
  have hh := Exec.seq h (reset_run _)
  convert hh using 1; simp

@[reducible] def fanScan (src a b : K) (f g : Bool → Bool) : Code K Bool :=
  .scan src (fun _ x => x) (.seq (.atom (.push a f)) (.atom (.push b g)))

theorem fanScan_run (src a b : K) (hsa : src ≠ a) (hsb : src ≠ b) (hab : a ≠ b)
    (f g : Bool → Bool) (l x y : List Bool) (s : Store K Bool) :
    ∃ q, (fanScan src a b f g).Exec (((s.put src l).put a x).put b y) (3*l.length+1)
      ((((s.put src []).put a (l.reverse.map f ++ x)).put b (l.reverse.map g ++ y)).flag q) := by
  induction l generalizing x y s with
  | nil =>
    refine ⟨s.state,?_⟩
    simpa [Store.put,Store.flag] using (Exec.scan_nil
      (c := .seq (.atom (.push a f)) (.atom (.push b g))) (f := fun _ x => x)
      (s := ((s.put src []).put a x).put b y) (by simp [hsa,hsb]))
  | cons v l ih =>
    obtain ⟨q,hq⟩ := ih (f v :: x) (g v :: y) (s.flag v)
    refine ⟨q,?_⟩
    have hbody : (.seq (.atom (.push a f)) (.atom (.push b g)) : Code K Bool).Exec
        ⟨v,Function.update ((((s.put src (v::l)).put a x).put b y).tape) src l⟩ (1+1)
        ((((s.flag v).put src l).put a (f v::x)).put b (g v::y)) := by
      convert Exec.seq (Exec.atom (.push a f) _) (Exec.atom (.push b g) _) using 1
      all_goals try with_reducible_and_instances rfl
      refine Store.ext _ _ ?_ ?_
      · rfl
      funext k
      by_cases h0 : k=src <;> by_cases h1 : k=a <;> by_cases h2 : k=b <;>
        simp_all [Prim.run,Store.put,Store.flag,Function.update_apply]
    have h := Exec.scan_cons (k := src) (f := fun _ v => v)
      (c := .seq (.atom (.push a f)) (.atom (.push b g)))
      (s := ((s.put src (v::l)).put a x).put b y) (b := v) (rest := l)
      (by simp [hsa,hsb]) hbody hq
    convert h using 1 <;> simp [List.reverse_cons,List.append_assoc]; omega

@[reducible] def copyMap (src dst tmp : K) (f : Bool → Bool) : Code K Bool :=
  .seq (transfer src tmp) (.seq (fanScan tmp src dst id f) reset)

theorem copyMap_run (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (f : Bool → Bool) (s : Store K Bool) (ht : s.tape tmp = []) :
    (copyMap src dst tmp f).Exec s (5*(s.tape src).length+4)
      ((s.put dst ((s.tape src).map f ++ s.tape dst)).flag false) := by
  have h1 := transfer_run src tmp hst s
  rw [ht,List.append_nil] at h1
  obtain ⟨q,h2⟩ := fanScan_run tmp src dst (Ne.symm hst) (Ne.symm hdt) hsd id f
    (s.tape src).reverse [] (s.tape dst) (s.flag false)
  have heq : ((((s.flag false).put tmp (s.tape src).reverse).put src []).put dst (s.tape dst)) =
      (((s.put src []).put tmp (s.tape src).reverse).flag false) := by
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases h0 : k=src <;> by_cases h1 : k=dst <;> by_cases h2 : k=tmp <;>
      simp_all [Store.put,Store.flag]
  rw [heq] at h2
  have h3 := Exec.seq h1 (Exec.seq h2 (reset_run _))
  have hend : (((((s.flag false).put tmp []).put src
      ((s.tape src).reverse.reverse.map id ++ [])).put dst
      ((s.tape src).reverse.reverse.map f ++ s.tape dst)).flag q).flag false =
      (s.put dst ((s.tape src).map f ++ s.tape dst)).flag false := by
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases h0 : k=src <;> by_cases h1 : k=dst <;> by_cases h2 : k=tmp <;>
      simp_all [Store.put,Store.flag]
  rw [hend] at h3
  convert h3 using 1; simp; omega

@[reducible] def copy (src dst tmp : K) : Code K Bool := copyMap src dst tmp id
@[reducible] def count (src dst tmp : K) : Code K Bool := copyMap src dst tmp (fun _ => true)

theorem copy_run (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (s : Store K Bool) (ht : s.tape tmp = []) :
    (copy src dst tmp).Exec s (5*(s.tape src).length+4)
      ((s.put dst (s.tape src ++ s.tape dst)).flag false) := by
  simpa using copyMap_run src dst tmp hsd hst hdt id s ht

theorem count_run (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (s : Store K Bool) (ht : s.tape tmp = []) :
    (count src dst tmp).Exec s (5*(s.tape src).length+4)
      ((s.put dst (List.replicate (s.tape src).length true ++ s.tape dst)).flag false) := by
  simpa using copyMap_run src dst tmp hsd hst hdt (fun _ => true) s ht

end Ops
end DirectedFeedback.StackDSL


namespace DirectedFeedback.StackDSL
open Code
variable {K : Type} [DecidableEq K]
namespace Ops

theorem scan_indexed (counter : K) (c : Code K Bool) (n : Nat)
    (states : Nat → Store K Bool) (cost : Nat → Nat)
    (hc : ∀ i, i ≤ n → (states i).tape counter = List.replicate (n-i) true)
    (hb : ∀ i, i < n → c.Exec ((states i).put counter (List.replicate (n-(i+1)) true))
      (cost i) (states (i+1))) :
    (Code.scan counter (fun s _ => s) c).Exec (states 0)
      (n+1+∑ i ∈ Finset.range n, cost i) (states n) := by
  induction n generalizing states cost with
  | zero =>
    simpa using (Exec.scan_nil (c := c) (f := fun s _ => s) (s := states 0)
      (by simpa using hc 0 (by omega)))
  | succ n ih =>
    have hh := ih (fun i => states (i+1)) (fun i => cost (i+1))
      (by intro i hi; simpa [Nat.add_sub_add_right] using hc (i+1) (by omega))
      (by intro i hi; simpa [Nat.add_assoc] using hb (i+1) (by omega))
    have h := Exec.scan_cons (k := counter) (f := fun s _ => s) (c := c)
      (s := states 0) (b := true) (rest := List.replicate n true)
      (by simpa [List.replicate_succ] using hc 0 (by omega))
      (by simpa [Store.put] using hb 0 (by omega)) hh
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rw [Finset.sum_range_succ']
    omega

@[reducible] def pushN (k : K) : Nat → Code K Bool
  | 0 => reset
  | n+1 => .seq (push k true) (pushN k n)

theorem pushN_run (k : K) (n : Nat) (s : Store K Bool) :
    (pushN k n).Exec s (n+1)
      ((s.put k (List.replicate n true ++ s.tape k)).flag false) := by
  induction n generalizing s with
  | zero => simpa using reset_run s
  | succ n ih =>
    have h := Exec.seq (push_run s k true) (ih (s.put k (true::s.tape k)))
    convert h using 1 <;> first | omega | simp [List.replicate_succ',List.append_assoc]

theorem subtract_run (src counter : K) (hne : src ≠ counter) (a b : Nat) (s : Store K Bool) :
    (Code.scan counter (fun s _ => s) (pop src)).Exec
      ((s.put src (List.replicate a true)).put counter (List.replicate b true))
      (2*b+1) ((s.put src (List.replicate (a-b) true)).put counter []) := by
  let states := fun i => (s.put src (List.replicate (a-i) true)).put counter (List.replicate (b-i) true)
  have h := scan_indexed counter (pop src) b states (fun _ => 1)
    (by intro i hi; simp [states]) (by
      intro i hi
      convert pop_run ((states i).put counter (List.replicate (b-(i+1)) true)) src using 1
      all_goals try with_reducible_and_instances rfl
      refine Store.ext _ _ rfl ?_
      funext k
      by_cases hs : k=src <;> by_cases hc : k=counter <;>
        simp_all [states,Store.put,List.tail_replicate]
      omega)
  convert h using 1 <;> simp [states]; omega

theorem drop_run (src counter : K) (hne : src ≠ counter) (l : List Bool) (b : Nat) (s : Store K Bool) :
    (Code.scan counter (fun s _ => s) (pop src)).Exec
      ((s.put src l).put counter (List.replicate b true))
      (2*b+1) ((s.put src (l.drop b)).put counter []) := by
  let states := fun i => (s.put src (l.drop i)).put counter (List.replicate (b-i) true)
  have h := scan_indexed counter (pop src) b states (fun _ => 1)
    (by intro i hi; simp [states]) (by
      intro i hi
      convert pop_run ((states i).put counter (List.replicate (b-(i+1)) true)) src using 1
      all_goals try with_reducible_and_instances rfl
      refine Store.ext _ _ rfl ?_
      funext k
      by_cases hs : k=src <;> by_cases hc : k=counter <;>
        simp_all [states,Store.put])
  convert h using 1 <;> simp [states]; omega

end Ops
end DirectedFeedback.StackDSL


namespace DirectedFeedback.BoundedExpr
open scoped BigOperators

inductive Expr : Nat → Type
  | lit {r : Nat} (value : Nat) : Expr r
  | arg {r : Nat} (index : Fin r) : Expr r
  | length {r : Nat} : Expr r
  | bit {r : Nat} (index : Expr r) : Expr r
  | add {r : Nat} (a b : Expr r) : Expr r
  | mul {r : Nat} (a b : Expr r) : Expr r
  | sub {r : Nat} (a b : Expr r) : Expr r
  | zero {r : Nat} (a : Expr r) : Expr r
  | sum {r : Nat} (bound : Expr r) (body : Expr (r+1)) : Expr r

namespace Expr

def eval {r : Nat} (e : Expr r) (input : List Bool) (args : Fin r → Nat) : Nat :=
  match e with
  | .lit n => n
  | .arg i => args i
  | .length => input.length
  | .bit i => if input[i.eval input args]?.getD false then 1 else 0
  | .add a b => a.eval input args + b.eval input args
  | .mul a b => a.eval input args * b.eval input args
  | .sub a b => a.eval input args - b.eval input args
  | .zero a => if a.eval input args = 0 then 1 else 0
  | .sum b e => ∑ i ∈ Finset.range (b.eval input args), e.eval input (Fin.cons i args)

noncomputable def bound {r : Nat} : Expr r → Polynomial Nat
  | .lit n => Polynomial.C n
  | .arg _ | .length => Polynomial.X
  | .bit _ | .zero _ => 1
  | .add a b => a.bound + b.bound
  | .mul a b => a.bound * b.bound
  | .sub a _ => a.bound
  | .sum b e => b.bound * e.bound.comp (Polynomial.X + b.bound)

theorem eval_le_bound {r : Nat} (e : Expr r) (input : List Bool) (args : Fin r → Nat)
    (n : Nat) (hi : input.length ≤ n) (ha : ∀ i, args i ≤ n) : e.eval input args ≤ e.bound.eval n := by
  induction e generalizing input n with
  | lit k => simp [eval,bound]
  | arg i => simpa [eval,bound] using ha i
  | length => simpa [eval,bound] using hi
  | bit i ih => simp only [eval,bound,Polynomial.eval_one]; split <;> omega
  | add a b iha ihb =>
    simpa only [eval,bound,Polynomial.eval_add] using
      Nat.add_le_add (iha input args n hi ha) (ihb input args n hi ha)
  | mul a b iha ihb =>
    simpa only [eval,bound,Polynomial.eval_mul] using
      Nat.mul_le_mul (iha input args n hi ha) (ihb input args n hi ha)
  | sub a b iha ihb => exact (Nat.sub_le ..).trans (iha input args n hi ha)
  | zero a iha => simp only [eval,bound,Polynomial.eval_one]; split <;> omega
  | @sum r b e ihb ihe =>
    have hb := ihb input args n hi ha
    have heach : ∀ i ∈ Finset.range (b.eval input args),
        e.eval input (Fin.cons i args) ≤ e.bound.eval (n+b.bound.eval n) := by
      intro i hm
      have hsmall : i < b.eval input args := Finset.mem_range.mp hm
      apply ihe input (Fin.cons i args) (n+b.bound.eval n) (by omega)
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using (show i ≤ n+b.bound.eval n by omega)
      · simpa using (ha j).trans (Nat.le_add_right n _)
    simp only [eval,bound,Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_X]
    calc
      _ ≤ ∑ _i ∈ Finset.range (b.eval input args), e.bound.eval (n+b.bound.eval n) :=
        Finset.sum_le_sum heach
      _ = b.eval input args * e.bound.eval (n+b.bound.eval n) := by simp
      _ ≤ b.bound.eval n * e.bound.eval (n+b.bound.eval n) := Nat.mul_le_mul_right _ hb

end Expr
end DirectedFeedback.BoundedExpr


namespace DirectedFeedback.BoundedExpr
open StackDSL StackDSL.Code StackDSL.Ops
open scoped BigOperators

namespace Expr

@[reducible] def compile {r : Nat} (e : Expr r) (input : Nat) (args : Fin r → Nat)
    (out fresh : Nat) : Code Nat Bool :=
  match e with
  | .lit n => pushN out n
  | .arg i => copy (args i) out fresh
  | .length => count input out fresh
  | .add a b => .seq (a.compile input args out fresh) (b.compile input args out fresh)
  | .mul a b =>
    .seq (a.compile input args fresh (fresh+2))
      (.seq (b.compile input args (fresh+1) (fresh+2))
        (.seq (.scan fresh (fun s _ => s) (copy (fresh+1) out (fresh+2))) (clear (fresh+1))))
  | .sub a b =>
    .seq (a.compile input args fresh (fresh+2))
      (.seq (b.compile input args (fresh+1) (fresh+2))
        (.seq (.scan (fresh+1) (fun s _ => s) (pop fresh)) (transfer fresh out)))
  | .zero a =>
    .seq (a.compile input args fresh (fresh+1))
      (.seq (.atom (.peek fresh (fun _ x => x.isNone)))
        (.seq (clear fresh) (.seq (.branch id (push out true) idle) reset)))
  | .bit i =>
    .seq (i.compile input args fresh (fresh+1))
      (.seq (copy input (fresh+1) (fresh+2))
        (.seq (.scan fresh (fun s _ => s) (pop (fresh+1)))
          (.seq (.atom (.peek (fresh+1) (fun _ x => x.getD false)))
            (.seq (clear (fresh+1)) (.seq (.branch id (push out true) idle) reset)))))
  | .sum b e =>
    .seq (b.compile input args fresh (fresh+2))
      (.seq (.scan fresh (fun s _ => s)
        (.seq (e.compile input (Fin.cons (fresh+1) args) out (fresh+2)) (push (fresh+1) true)))
        (clear (fresh+1)))

def cost {r : Nat} (e : Expr r) (input : List Bool) (args : Fin r → Nat) : Nat :=
  match e with
  | .lit n => n+1
  | .arg i => 5*args i+4
  | .length => 5*input.length+4
  | .add a b => a.cost input args + b.cost input args
  | .mul a b => a.cost input args + b.cost input args +
      a.eval input args * (5*b.eval input args+5) + 2*b.eval input args+2
  | .sub a b => a.cost input args + b.cost input args +
      2*b.eval input args + 2*(a.eval input args-b.eval input args)+3
  | .zero a => a.cost input args + 2*a.eval input args+5
  | .bit i => i.cost input args + 5*input.length + 2*i.eval input args +
      2*(input.length-i.eval input args)+10
  | .sum b e => b.cost input args +
      (∑ i ∈ Finset.range (b.eval input args), e.cost input (Fin.cons i args))+4*b.eval input args+2

noncomputable def costBound {r : Nat} : Expr r → Polynomial Nat
  | .lit n => Polynomial.C (n+1)
  | .arg _ | .length => 5*Polynomial.X+4
  | .add a b => a.costBound+b.costBound
  | .mul a b => a.costBound+b.costBound+a.bound*(5*b.bound+5)+2*b.bound+2
  | .sub a b => a.costBound+b.costBound+2*b.bound+2*a.bound+3
  | .zero a => a.costBound+2*a.bound+5
  | .bit i => i.costBound+7*Polynomial.X+2*i.bound+10
  | .sum b e => b.costBound+b.bound*e.costBound.comp (Polynomial.X+b.bound)+4*b.bound+2

theorem cost_le_bound {r : Nat} (e : Expr r) (input : List Bool) (args : Fin r → Nat)
    (n : Nat) (hi : input.length ≤ n) (ha : ∀ i, args i ≤ n) : e.cost input args ≤ e.costBound.eval n := by
  induction e generalizing input n with
  | lit k => simp [cost,costBound]
  | arg i =>
    have hai := ha i
    simp only [cost,costBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_X]; omega
  | length => simp only [cost,costBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_X]; omega
  | add a b iha ihb =>
    simpa [cost,costBound] using Nat.add_le_add (iha input args n hi ha) (ihb input args n hi ha)
  | mul a b iha ihb =>
    have h1 := iha input args n hi ha
    have h2 := ihb input args n hi ha
    have h3 := a.eval_le_bound input args n hi ha
    have h4 := b.eval_le_bound input args n hi ha
    have hm := Nat.mul_le_mul h3 (Nat.add_le_add_right (Nat.mul_le_mul_left 5 h4) 5)
    simp only [cost,costBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
    omega
  | sub a b iha ihb =>
    have h1 := iha input args n hi ha
    have h2 := ihb input args n hi ha
    have h3 := a.eval_le_bound input args n hi ha
    have h4 := b.eval_le_bound input args n hi ha
    simp only [cost,costBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
    omega
  | zero a iha =>
    have h1 := iha input args n hi ha
    have h2 := a.eval_le_bound input args n hi ha
    simp only [cost,costBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
    omega
  | bit i ih =>
    have h1 := ih input args n hi ha
    have h2 := i.eval_le_bound input args n hi ha
    simp only [cost,costBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    omega
  | @sum r b e ihb ihe =>
    have hb := b.eval_le_bound input args n hi ha
    have hbc := ihb input args n hi ha
    have heach : ∀ i ∈ Finset.range (b.eval input args),
        e.cost input (Fin.cons i args) ≤ e.costBound.eval (n+b.bound.eval n) := by
      intro i hm
      have hsmall : i < b.eval input args := Finset.mem_range.mp hm
      apply ihe input (Fin.cons i args) (n+b.bound.eval n) (by omega)
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using (show i ≤ n+b.bound.eval n by omega)
      · simpa using (ha j).trans (Nat.le_add_right n _)
    have hsum : (∑ i ∈ Finset.range (b.eval input args), e.cost input (Fin.cons i args)) ≤
        b.bound.eval n * e.costBound.eval (n+b.bound.eval n) := by
      calc
        _ ≤ ∑ _i ∈ Finset.range (b.eval input args), e.costBound.eval (n+b.bound.eval n) :=
          Finset.sum_le_sum heach
        _ = b.eval input args * e.costBound.eval (n+b.bound.eval n) := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ hb
    simp only [cost,costBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_comp,Polynomial.eval_X]
    omega

end Expr
end DirectedFeedback.BoundedExpr

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_ExprLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DirectedFeedback.BoundedExpr
open StackDSL StackDSL.Code StackDSL.Ops

structure Layout (r : Nat) where
  input : Nat
  args : Fin r → Nat
  output : Nat
  fresh : Nat
  input_lt : input < fresh
  args_lt : ∀ i, args i < fresh
  output_lt : output < fresh
  input_ne : input ≠ output
  args_ne : ∀ i, args i ≠ output

namespace Layout
variable {r : Nat} (L : Layout r)

def temp (j d : Nat) (h : j < d) : Layout r where
  input := L.input
  args := L.args
  output := L.fresh+j
  fresh := L.fresh+d
  input_lt := by have := L.input_lt; omega
  args_lt := by intro i; have := L.args_lt i; omega
  output_lt := by omega
  input_ne := by have := L.input_lt; omega
  args_ne := by intro i; have := L.args_lt i; omega

def sumBody : Layout (r+1) where
  input := L.input
  args := Fin.cons (L.fresh+1) L.args
  output := L.output
  fresh := L.fresh+2
  input_lt := by have := L.input_lt; omega
  args_lt := by intro i; refine Fin.cases ?_ (fun i => ?_) i
                · simp
                · simpa using (L.args_lt i).trans (by omega : L.fresh < L.fresh+2)
  output_lt := by have := L.output_lt; omega
  input_ne := L.input_ne
  args_ne := by intro i; refine Fin.cases ?_ (fun i => ?_) i
                · simp; have := L.output_lt; omega
                · simpa using L.args_ne i

structure Ready (s : Store Nat Bool) (input : List Bool) (args : Fin r → Nat) : Prop where
  input_eq : s.tape L.input = input
  args_eq : ∀ i, s.tape (L.args i) = List.replicate (args i) true
  clean : ∀ k, L.fresh ≤ k → s.tape k = []

namespace Ready
variable {L : Layout r} {s : Store Nat Bool} {x : List Bool} {a : Fin r → Nat}

 theorem flag (h : L.Ready s x a) (b : Bool) : L.Ready (s.flag b) x a := ⟨h.input_eq,h.args_eq,h.clean⟩

 theorem temp (h : L.Ready s x a) (j d : Nat) (hjd : j<d) : (L.temp j d hjd).Ready s x a where
  input_eq := h.input_eq
  args_eq := h.args_eq
  clean := by intro k hk; apply h.clean; change L.fresh+d ≤ k at hk; omega

 theorem put (h : L.Ready s x a) (k : Nat) (v : List Bool) (hk : k<L.fresh)
    (hki : L.input ≠ k) (hka : ∀ i, L.args i ≠ k) : L.Ready (s.put k v) x a where
  input_eq := by simpa [hki] using h.input_eq
  args_eq := by intro i; simpa [hka i] using h.args_eq i
  clean := by intro j hj; rw [Store.put_tape_other _ (by omega)]; exact h.clean j hj

 theorem output (h : L.Ready s x a) (v : List Bool) : L.Ready (s.put L.output v) x a :=
  h.put L.output v L.output_lt L.input_ne L.args_ne

 theorem temp_put (h : L.Ready s x a) (j d k : Nat) (hjd : j<d) (hkd : k<d) (v : List Bool) :
    (L.temp j d hjd).Ready (s.put (L.fresh+k) v) x a := by
  apply (h.temp j d hjd).put (L.fresh+k) v
  · change L.fresh+k < L.fresh+d; omega
  · change L.input ≠ L.fresh+k; have := L.input_lt; omega
  · intro i; change L.args i ≠ L.fresh+k; have := L.args_lt i; omega

end Ready
end Layout

namespace Expr

def Correct {r : Nat} (e : Expr r) : Prop :=
  ∀ (L : Layout r) (x : List Bool) (a : Fin r → Nat) (s : Store Nat Bool), L.Ready s x a →
    (e.compile L.input L.args L.output L.fresh).Exec s (e.cost x a)
      ((s.put L.output (List.replicate (e.eval x a) true ++ s.tape L.output)).flag false)

theorem correct_lit {r : Nat} (n : Nat) : Correct (Expr.lit (r := r) n) := by
  intro L x a s h
  exact pushN_run L.output n s

theorem correct_arg {r : Nat} (i : Fin r) : Correct (Expr.arg i) := by
  intro L x a s h
  have ht := h.clean L.fresh (by omega)
  have hr := copy_run (L.args i) L.output L.fresh (L.args_ne i)
    (Nat.ne_of_lt (L.args_lt i)) (Nat.ne_of_lt L.output_lt) s ht
  simpa [h.args_eq i,eval,cost] using hr

theorem correct_length {r : Nat} : Correct (Expr.length (r := r)) := by
  intro L x a s h
  have ht := h.clean L.fresh (by omega)
  have hr := count_run L.input L.output L.fresh L.input_ne
    (Nat.ne_of_lt L.input_lt) (Nat.ne_of_lt L.output_lt) s ht
  simpa [h.input_eq,eval,cost] using hr

theorem correct_add {r : Nat} {e f : Expr r} (he : e.Correct) (hf : f.Correct) : (e.add f).Correct := by
  intro L x a s h
  have h1 := he L x a s h
  have h2 := hf L x a _ ((h.output (List.replicate (e.eval x a) true ++ s.tape L.output)).flag false)
  have hh := Exec.seq h1 h2
  convert hh using 1 <;> try rfl
  simp only [eval,Store.put_tape_same,Store.flag_tape,Store.put_flag,Store.put_put,Store.flag_flag]
  rw [← List.append_assoc,← List.replicate_add, Nat.add_comm]

end Expr
end DirectedFeedback.BoundedExpr


namespace DirectedFeedback.BoundedExpr.Expr
open StackDSL StackDSL.Code StackDSL.Ops
open scoped BigOperators

theorem correct_mul {r : Nat} {e g : Expr r} (he : e.Correct) (hg : g.Correct) : (e.mul g).Correct := by
  intro L x a s h
  let u := e.eval x a
  let v := g.eval x a
  have hfo : L.fresh ≠ L.output := (Nat.ne_of_lt L.output_lt).symm
  have h1o : L.fresh+1 ≠ L.output := by have := L.output_lt; omega
  have h2o : L.fresh+2 ≠ L.output := by have := L.output_lt; omega
  have hs0 := h.clean L.fresh (by omega)
  have hs1 := h.clean (L.fresh+1) (by omega)
  have hs2 := h.clean (L.fresh+2) (by omega)
  have h1 := he (L.temp 0 2 (by omega)) x a s (h.temp 0 2 (by omega))
  simp only [Layout.temp,Nat.add_zero,hs0,List.append_nil] at h1
  have h2 := hg (L.temp 1 2 (by omega)) x a
    ((s.put L.fresh (List.replicate u true)).flag false)
    ((h.temp_put 1 2 0 (by omega) (by omega) (List.replicate u true)).flag false)
  simp only [Layout.temp,Store.flag_tape,Store.put_tape_other _ (by omega : L.fresh+1 ≠ L.fresh),
    hs1,List.append_nil,Store.put_flag,Store.flag_flag] at h2
  let states := fun i : Nat =>
    ((((s.put (L.fresh+1) (List.replicate v true)).put L.fresh (List.replicate (u-i) true)).put
      L.output (List.replicate (i*v) true ++ s.tape L.output)).flag false)
  have hp : ∀ i, (copy (L.fresh+1) L.output (L.fresh+2)).Exec
      ((states i).put L.fresh (List.replicate (u-(i+1)) true)) (5*v+4) (states (i+1)) := by
    intro i
    have hr := copy_run (L.fresh+1) L.output (L.fresh+2) h1o (by omega) (by omega : L.output ≠ L.fresh+2)
      ((states i).put L.fresh (List.replicate (u-(i+1)) true)) (by simp [states,hs2,h2o])
    have hb : (((states i).put L.fresh (List.replicate (u-(i+1)) true)).tape (L.fresh+1)) =
        List.replicate v true := by simp [states,h1o]
    rw [hb,List.length_replicate] at hr
    convert hr using 1
    all_goals try with_reducible_and_instances rfl
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hk : k=L.output
    · subst k
      simp only [states,Store.flag_tape,Store.put_tape_same,Store.put_tape_other _ (Ne.symm hfo)]
      rw [← List.append_assoc,← List.replicate_add]
      congr 2
      ring
    · by_cases h0 : k=L.fresh <;> by_cases h1 : k=L.fresh+1 <;>
        simp_all [states,Store.put,Store.flag]
  have hlo := scan_indexed L.fresh (copy (L.fresh+1) L.output (L.fresh+2)) u states
    (fun _ => 5*v+4) (by intro i hi; simp [states,hfo]) (by intro i hi; exact hp i)
  have hstart : states 0 = (((s.put L.fresh (List.replicate u true)).put
      (L.fresh+1) (List.replicate v true)).flag false) := by
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hk : k=L.output <;> by_cases h0 : k=L.fresh <;> by_cases h1 : k=L.fresh+1 <;>
      simp_all [states,Store.put,Store.flag]
  rw [hstart] at hlo
  have hc := clear_run (L.fresh+1) (states u)
  have hcval : (states u).tape (L.fresh+1) = List.replicate v true := by simp [states,h1o]
  rw [hcval,List.length_replicate] at hc
  have hend : (states u).put (L.fresh+1) [] =
      (s.put L.output (List.replicate (u*v) true ++ s.tape L.output)).flag false := by
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hk : k=L.output <;> by_cases h0 : k=L.fresh <;> by_cases h1 : k=L.fresh+1 <;>
      simp_all [states,Store.put,Store.flag]
  rw [hend] at hc
  have hh := Exec.seq h1 (Exec.seq h2 (Exec.seq hlo hc))
  convert hh using 1 <;> try rfl
  simp only [cost,Finset.sum_const,Finset.card_range,smul_eq_mul]
  dsimp [u,v]
  ring

end DirectedFeedback.BoundedExpr.Expr


namespace DirectedFeedback.BoundedExpr.Expr
open StackDSL StackDSL.Code StackDSL.Ops

theorem correct_sub {r : Nat} {e g : Expr r} (he : e.Correct) (hg : g.Correct) : (e.sub g).Correct := by
  intro L x a s h
  let u := e.eval x a
  let v := g.eval x a
  have hfo : L.fresh ≠ L.output := (Nat.ne_of_lt L.output_lt).symm
  have h1o : L.fresh+1 ≠ L.output := by have := L.output_lt; omega
  have hs0 := h.clean L.fresh (by omega)
  have hs1 := h.clean (L.fresh+1) (by omega)
  have h1 := he (L.temp 0 2 (by omega)) x a s (h.temp 0 2 (by omega))
  simp only [Layout.temp,Nat.add_zero,hs0,List.append_nil] at h1
  have h2 := hg (L.temp 1 2 (by omega)) x a
    ((s.put L.fresh (List.replicate u true)).flag false)
    ((h.temp_put 1 2 0 (by omega) (by omega) (List.replicate u true)).flag false)
  simp only [Layout.temp,Store.flag_tape,Store.put_tape_other _ (by omega : L.fresh+1 ≠ L.fresh),
    hs1,List.append_nil,Store.put_flag,Store.flag_flag] at h2
  have hr := subtract_run L.fresh (L.fresh+1) (by omega) u v (s.flag false)
  simp only [Store.put_flag] at hr
  have ht := transfer_run L.fresh L.output hfo
    (((s.put L.fresh (List.replicate (u-v) true)).put (L.fresh+1) []).flag false)
  have hv : (((s.put L.fresh (List.replicate (u-v) true)).put (L.fresh+1) []).flag false).tape L.fresh =
      List.replicate (u-v) true := by simp
  rw [hv,List.length_replicate,List.reverse_replicate] at ht
  have hend : (((((s.put L.fresh (List.replicate (u-v) true)).put (L.fresh+1) []).flag false).put L.fresh []).put
      L.output (List.replicate (u-v) true ++
        (((s.put L.fresh (List.replicate (u-v) true)).put (L.fresh+1) []).flag false).tape L.output)).flag false =
      (s.put L.output (List.replicate (u-v) true ++ s.tape L.output)).flag false := by
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hk : k=L.output <;> by_cases h0 : k=L.fresh <;> by_cases h1 : k=L.fresh+1 <;>
      simp_all [Store.put,Store.flag]
  rw [hend] at ht
  have hh := Exec.seq h1 (Exec.seq h2 (Exec.seq hr ht))
  convert hh using 1 <;> try rfl
  dsimp [cost,u,v]
  omega

end DirectedFeedback.BoundedExpr.Expr


namespace DirectedFeedback.BoundedExpr.Expr
open StackDSL StackDSL.Code StackDSL.Ops
open scoped BigOperators

theorem correct_sum {r : Nat} {b : Expr r} {e : Expr (r+1)}
    (hb : b.Correct) (he : e.Correct) : (b.sum e).Correct := by
  intro L x a s h
  let n := b.eval x a
  let sums := fun i => ∑ j ∈ Finset.range i, e.eval x (Fin.cons j a)
  have hfo : L.fresh ≠ L.output := (Nat.ne_of_lt L.output_lt).symm
  have h1o : L.fresh+1 ≠ L.output := by have := L.output_lt; omega
  have hfi : L.input ≠ L.fresh := Nat.ne_of_lt L.input_lt
  have h1i : L.input ≠ L.fresh+1 := by have := L.input_lt; omega
  have hfa : ∀ j, L.args j ≠ L.fresh := fun j => Nat.ne_of_lt (L.args_lt j)
  have h1a : ∀ j, L.args j ≠ L.fresh+1 := by intro j; have := L.args_lt j; omega
  have hs0 := h.clean L.fresh (by omega)
  have hs1 := h.clean (L.fresh+1) (by omega)
  have h1 := hb (L.temp 0 2 (by omega)) x a s (h.temp 0 2 (by omega))
  simp only [Layout.temp,Nat.add_zero,hs0,List.append_nil] at h1
  let states := fun i =>
    ((((s.put (L.fresh+1) (List.replicate i true)).put L.fresh (List.replicate (n-i) true)).put
      L.output (List.replicate (sums i) true ++ s.tape L.output)).flag false)
  have hrdy : ∀ i, L.sumBody.Ready ((states i).put L.fresh (List.replicate (n-(i+1)) true))
      x (Fin.cons i a) := by
    intro i
    constructor
    · simp [states,Layout.sumBody,hfi,h1i,L.input_ne,h.input_eq]
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [states,Layout.sumBody,h1o]
      · simp [states,Layout.sumBody,hfa,h1a,L.args_ne,h.args_eq]
    · intro k hk
      change L.fresh+2 ≤ k at hk
      have hk0 : k≠L.fresh := by omega
      have hk1 : k≠L.fresh+1 := by omega
      have hko : k≠L.output := by have := L.output_lt; omega
      simp [states,hk0,hk1,hko,h.clean k (by omega)]
  have hp : ∀ i, (Code.seq (e.compile L.input (Fin.cons (L.fresh+1) L.args) L.output (L.fresh+2))
      (push (L.fresh+1) true)).Exec
      ((states i).put L.fresh (List.replicate (n-(i+1)) true))
      (e.cost x (Fin.cons i a)+1) (states (i+1)) := by
    intro i
    have hbody := he L.sumBody x (Fin.cons i a)
      ((states i).put L.fresh (List.replicate (n-(i+1)) true)) (hrdy i)
    have hpush := push_run ((((states i).put L.fresh (List.replicate (n-(i+1)) true)).put L.output
      (List.replicate (e.eval x (Fin.cons i a)) true ++
        ((states i).put L.fresh (List.replicate (n-(i+1)) true)).tape L.output)).flag false)
      (L.fresh+1) true
    have hh := Exec.seq hbody hpush
    convert hh using 1 <;> try rfl
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hko : k=L.output
    · subst k
      simp only [states,Store.flag_tape,Store.put_tape_same,Store.put_tape_other _ (Ne.symm hfo),
        Store.put_tape_other _ (Ne.symm h1o)]
      rw [← List.append_assoc,← List.replicate_add]
      congr 2
      simp only [sums,Finset.sum_range_succ]
      omega
    · by_cases hk0 : k=L.fresh <;> by_cases hk1 : k=L.fresh+1 <;>
        simp_all [states,Store.put,Store.flag,List.replicate_succ]
  have hlo := scan_indexed L.fresh
    (Code.seq (e.compile L.input (Fin.cons (L.fresh+1) L.args) L.output (L.fresh+2)) (push (L.fresh+1) true))
    n states (fun i => e.cost x (Fin.cons i a)+1)
    (by intro i hi; simp [states,hfo]) (by intro i hi; exact hp i)
  have hstart : states 0 = (s.put L.fresh (List.replicate n true)).flag false := by
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hko : k=L.output <;> by_cases hk0 : k=L.fresh <;> by_cases hk1 : k=L.fresh+1 <;>
      simp_all [states,sums,Store.put,Store.flag]
  rw [hstart] at hlo
  have hc := clear_run (L.fresh+1) (states n)
  have hcval : (states n).tape (L.fresh+1) = List.replicate n true := by simp [states,h1o]
  rw [hcval,List.length_replicate] at hc
  have hend : (states n).put (L.fresh+1) [] =
      (s.put L.output (List.replicate (sums n) true ++ s.tape L.output)).flag false := by
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hko : k=L.output <;> by_cases hk0 : k=L.fresh <;> by_cases hk1 : k=L.fresh+1 <;>
      simp_all [states,Store.put,Store.flag]
  rw [hend] at hc
  have hh := Exec.seq h1 (Exec.seq hlo hc)
  convert hh using 1 <;> try rfl
  simp only [cost,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]
  dsimp [n]
  omega

end DirectedFeedback.BoundedExpr.Expr


namespace DirectedFeedback.BoundedExpr.Expr
open StackDSL StackDSL.Code StackDSL.Ops

theorem terminal_run (output : Nat) (s : Store Nat Bool) :
    (Code.seq (.branch id (push output true) idle) reset).Exec s 3
      ((s.put output (List.replicate (if s.state then 1 else 0) true ++ s.tape output)).flag false) := by
  cases hb : s.state with
  | false =>
    have h1 := Exec.branch_false (f := id) (c := push output true) (d := idle) hb (idle_run s)
    have h2 := Exec.seq h1 (reset_run s)
    simpa [hb] using h2
  | true =>
    have h1 := Exec.branch_true (f := id) (c := push output true) (d := idle) hb (push_run s output true)
    have h2 := Exec.seq h1 (reset_run _)
    simpa [hb] using h2

theorem correct_zero {r : Nat} {e : Expr r} (he : e.Correct) : e.zero.Correct := by
  intro L x a s h
  let u := e.eval x a
  have hfo : L.fresh ≠ L.output := (Nat.ne_of_lt L.output_lt).symm
  have hs0 := h.clean L.fresh (by omega)
  have h1 := he (L.temp 0 1 (by omega)) x a s (h.temp 0 1 (by omega))
  simp only [Layout.temp,Nat.add_zero,hs0,List.append_nil] at h1
  let s1 := (s.put L.fresh (List.replicate u true)).flag false
  have hp : (Code.atom (.peek L.fresh (fun _ x => x.isNone))).Exec s1 1
      ((s.put L.fresh (List.replicate u true)).flag (decide (u=0))) := by
    convert Exec.atom (.peek L.fresh (fun _ x => x.isNone)) s1 using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [s1,Prim.run,Store.put,Store.flag]
    cases u <;> simp
  have hc := clear_run L.fresh ((s.put L.fresh (List.replicate u true)).flag (decide (u=0)))
  simp only [Store.flag_tape,Store.put_tape_same,List.length_replicate,Store.put_flag,Store.put_put] at hc
  have hz : s.put L.fresh [] = s := by rw [← hs0,Store.put_self]
  rw [hz] at hc
  have ht := terminal_run L.output (s.flag (decide (u=0)))
  have hh := Exec.seq h1 (Exec.seq hp (Exec.seq hc ht))
  convert hh using 1 <;> try rfl
  · dsimp [cost,u]; omega
  · simp [eval,u]

end DirectedFeedback.BoundedExpr.Expr


namespace DirectedFeedback.BoundedExpr.Expr
open StackDSL StackDSL.Code StackDSL.Ops

theorem correct_bit {r : Nat} {e : Expr r} (he : e.Correct) : e.bit.Correct := by
  intro L x a s h
  let u := e.eval x a
  have hfi : L.input ≠ L.fresh := Nat.ne_of_lt L.input_lt
  have h1i : L.input ≠ L.fresh+1 := by have := L.input_lt; omega
  have h2i : L.input ≠ L.fresh+2 := by have := L.input_lt; omega
  have hs0 := h.clean L.fresh (by omega)
  have hs1 := h.clean (L.fresh+1) (by omega)
  have hs2 := h.clean (L.fresh+2) (by omega)
  have h1 := he (L.temp 0 1 (by omega)) x a s (h.temp 0 1 (by omega))
  simp only [Layout.temp,Nat.add_zero,hs0,List.append_nil] at h1
  have hcopy := copy_run L.input (L.fresh+1) (L.fresh+2) h1i h2i (by omega)
    ((s.put L.fresh (List.replicate u true)).flag false) (by simp [hs2])
  simp only [Store.flag_tape,Store.put_tape_other _ hfi,h.input_eq,
    Store.put_tape_other _ (by omega : L.fresh+1 ≠ L.fresh),hs1,List.append_nil,
    Store.put_flag,Store.flag_flag] at hcopy
  have hr := drop_run (L.fresh+1) L.fresh (by omega) x u (s.flag false)
  simp only [Store.put_flag] at hr
  rw [Store.put_comm _ (by omega : L.fresh+1 ≠ L.fresh)] at hr
  let s2 := ((s.put (L.fresh+1) (x.drop u)).put L.fresh []).flag false
  have hp : (Code.atom (.peek (L.fresh+1) (fun _ x => x.getD false))).Exec s2 1
      (((s.put (L.fresh+1) (x.drop u)).put L.fresh []).flag (x[u]?.getD false)) := by
    convert Exec.atom (.peek (L.fresh+1) (fun _ x => x.getD false)) s2 using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [s2,Prim.run,Store.put,Store.flag]
    simp
  have hc := clear_run (L.fresh+1)
    (((s.put (L.fresh+1) (x.drop u)).put L.fresh []).flag (x[u]?.getD false))
  have htape : (((s.put (L.fresh+1) (x.drop u)).put L.fresh []).flag (x[u]?.getD false)).tape
      (L.fresh+1) = x.drop u := by simp
  rw [htape,List.length_drop] at hc
  have hz : ((((s.put (L.fresh+1) (x.drop u)).put L.fresh []).flag (x[u]?.getD false)).put
      (L.fresh+1) []) = s.flag (x[u]?.getD false) := by
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hk0 : k=L.fresh <;> by_cases hk1 : k=L.fresh+1 <;>
      simp_all [Store.put,Store.flag]
  rw [hz] at hc
  have ht := terminal_run L.output (s.flag (x[u]?.getD false))
  have hh := Exec.seq h1 (Exec.seq hcopy (Exec.seq hr (Exec.seq hp (Exec.seq hc ht))))
  convert hh using 1 <;> try rfl
  dsimp [cost,u]
  omega

end DirectedFeedback.BoundedExpr.Expr


namespace DirectedFeedback.BoundedExpr.Expr

theorem correct {r : Nat} (e : Expr r) : e.Correct := by
  induction e with
  | lit n => exact correct_lit n
  | arg i => exact correct_arg i
  | length => exact correct_length
  | add e f ihe ihf => exact correct_add ihe ihf
  | mul e f ihe ihf => exact correct_mul ihe ihf
  | sub e f ihe ihf => exact correct_sub ihe ihf
  | zero e ih => exact correct_zero ih
  | bit e ih => exact correct_bit ih
  | sum b e ihb ihe => exact correct_sum ihb ihe

end DirectedFeedback.BoundedExpr.Expr


namespace DirectedFeedback.BoundedExpr
open StackDSL StackDSL.Code StackDSL.Ops
open scoped BigOperators

inductive Output : Nat → Type
  | nil {r : Nat} : Output r
  | bit {r : Nat} (b : Bool) : Output r
  | nat {r : Nat} (e : Expr r) : Output r
  | append {r : Nat} (a b : Output r) : Output r
  | loop {r : Nat} (bound : Expr r) (body : Output (r+1)) : Output r
  | when {r : Nat} (test : Expr r) (body : Output r) : Output r

namespace Output

def eval {r : Nat} (o : Output r) (input : List Bool) (args : Fin r → Nat) : List Bool :=
  match o with
  | .nil => []
  | .bit b => [b]
  | .nat e => List.replicate (e.eval input args) true ++ [false]
  | .append a b => a.eval input args ++ b.eval input args
  | .loop b e => (List.range (b.eval input args)).flatMap (fun i => e.eval input (Fin.cons i args))
  | .when t b => if t.eval input args = 0 then [] else b.eval input args

@[reducible] def compile {r : Nat} (o : Output r) (input : Nat) (args : Fin r → Nat)
    (out fresh : Nat) : Code Nat Bool :=
  match o with
  | .nil => reset
  | .bit b => .seq (push out b) reset
  | .nat e => .seq (e.compile input args out fresh) (push out false)
  | .append a b => .seq (a.compile input args out fresh) (b.compile input args out fresh)
  | .loop b e =>
    .seq (b.compile input args fresh (fresh+2))
      (.seq (.scan fresh (fun s _ => s)
        (.seq (e.compile input (Fin.cons (fresh+1) args) out (fresh+2)) (push (fresh+1) true)))
        (clear (fresh+1)))
  | .when t b =>
    .seq (t.compile input args fresh (fresh+1))
      (.seq (.atom (.peek fresh (fun _ x => x.isSome)))
        (.seq (clear fresh) (.branch id (b.compile input args out fresh) reset)))

def cost {r : Nat} (o : Output r) (input : List Bool) (args : Fin r → Nat) : Nat :=
  match o with
  | .nil => 1
  | .bit _ => 2
  | .nat e => e.cost input args+1
  | .append a b => a.cost input args+b.cost input args
  | .loop b e => b.cost input args+
      (∑ i ∈ Finset.range (b.eval input args), e.cost input (Fin.cons i args))+4*b.eval input args+2
  | .when t b => t.cost input args+2*t.eval input args+3+
      (if t.eval input args=0 then 1 else b.cost input args)

noncomputable def bound {r : Nat} : Output r → Polynomial Nat
  | .nil => 0
  | .bit _ => 1
  | .nat e => e.bound+1
  | .append a b => a.bound+b.bound
  | .loop b e => b.bound*e.bound.comp (Polynomial.X+b.bound)
  | .when _ b => b.bound

noncomputable def costBound {r : Nat} : Output r → Polynomial Nat
  | .nil => 1
  | .bit _ => 2
  | .nat e => e.costBound+1
  | .append a b => a.costBound+b.costBound
  | .loop b e => b.costBound+b.bound*e.costBound.comp (Polynomial.X+b.bound)+4*b.bound+2
  | .when t b => t.costBound+2*t.bound+4+b.costBound

theorem length_range_flatMap {α : Type} (n : Nat) (f : Nat → List α) :
    ((List.range n).flatMap f).length = ∑ i ∈ Finset.range n, (f i).length := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,Finset.sum_range_succ,List.flatMap_append,ih]

theorem length_le_bound {r : Nat} (o : Output r) (x : List Bool) (args : Fin r → Nat)
    (n : Nat) (hi : x.length ≤ n) (ha : ∀ i, args i ≤ n) : (o.eval x args).length ≤ o.bound.eval n := by
  induction o generalizing x n with
  | nil => simp [eval,bound]
  | bit b => simp [eval,bound]
  | nat e => simpa [eval,bound] using Nat.add_le_add_right (e.eval_le_bound x args n hi ha) 1
  | append a b iha ihb => simpa [eval,bound] using Nat.add_le_add (iha x args n hi ha) (ihb x args n hi ha)
  | when t b ih =>
    have hb := ih x args n hi ha
    simp only [eval,bound]
    split <;> simp_all
  | @loop r b e ihe =>
    have hb := b.eval_le_bound x args n hi ha
    have heach : ∀ i ∈ Finset.range (b.eval x args),
        (e.eval x (Fin.cons i args)).length ≤ e.bound.eval (n+b.bound.eval n) := by
      intro i hm
      have hsmall : i < b.eval x args := Finset.mem_range.mp hm
      apply ihe x (Fin.cons i args) (n+b.bound.eval n) (by omega)
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using (show i ≤ n+b.bound.eval n by omega)
      · simpa using (ha j).trans (Nat.le_add_right n _)
    simp only [eval,bound,Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_X,
      length_range_flatMap]
    calc
      _ ≤ ∑ _i ∈ Finset.range (b.eval x args), e.bound.eval (n+b.bound.eval n) := Finset.sum_le_sum heach
      _ = b.eval x args * e.bound.eval (n+b.bound.eval n) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hb

theorem cost_le_bound {r : Nat} (o : Output r) (x : List Bool) (args : Fin r → Nat)
    (n : Nat) (hi : x.length ≤ n) (ha : ∀ i, args i ≤ n) : o.cost x args ≤ o.costBound.eval n := by
  induction o generalizing x n with
  | nil => simp [cost,costBound]
  | bit b => simp [cost,costBound]
  | nat e => simpa [cost,costBound] using Nat.add_le_add_right (e.cost_le_bound x args n hi ha) 1
  | append a b iha ihb => simpa [cost,costBound] using Nat.add_le_add (iha x args n hi ha) (ihb x args n hi ha)
  | when t b ih =>
    have h1 := t.cost_le_bound x args n hi ha
    have h2 := t.eval_le_bound x args n hi ha
    have h3 := ih x args n hi ha
    simp only [cost,costBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
    split <;> omega
  | @loop r b e ihe =>
    have hb := b.eval_le_bound x args n hi ha
    have hbc := b.cost_le_bound x args n hi ha
    have heach : ∀ i ∈ Finset.range (b.eval x args),
        e.cost x (Fin.cons i args) ≤ e.costBound.eval (n+b.bound.eval n) := by
      intro i hm
      have hsmall : i < b.eval x args := Finset.mem_range.mp hm
      apply ihe x (Fin.cons i args) (n+b.bound.eval n) (by omega)
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using (show i ≤ n+b.bound.eval n by omega)
      · simpa using (ha j).trans (Nat.le_add_right n _)
    have hs : (∑ i ∈ Finset.range (b.eval x args), e.cost x (Fin.cons i args)) ≤
        b.bound.eval n * e.costBound.eval (n+b.bound.eval n) := by
      calc
        _ ≤ ∑ _i ∈ Finset.range (b.eval x args), e.costBound.eval (n+b.bound.eval n) := Finset.sum_le_sum heach
        _ = b.eval x args * e.costBound.eval (n+b.bound.eval n) := by simp
        _ ≤ _ := Nat.mul_le_mul_right _ hb
    simp only [cost,costBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_comp,Polynomial.eval_X]
    omega

end Output
end DirectedFeedback.BoundedExpr


namespace DirectedFeedback.BoundedExpr.Output
open StackDSL StackDSL.Code StackDSL.Ops
open scoped BigOperators

def Correct {r : Nat} (e : Output r) : Prop :=
  ∀ (L : Layout r) (x : List Bool) (a : Fin r → Nat) (s : Store Nat Bool), L.Ready s x a →
    (e.compile L.input L.args L.output L.fresh).Exec s (e.cost x a)
      ((s.put L.output ((e.eval x a).reverse ++ s.tape L.output)).flag false)

theorem correct_nil {r : Nat} : Correct (Output.nil (r := r)) := by
  intro L x a s h
  simpa [cost,eval] using reset_run s

theorem correct_bit {r : Nat} (b : Bool) : Correct (Output.bit (r := r) b) := by
  intro L x a s h
  have hh := Exec.seq (push_run s L.output b) (reset_run _)
  simpa [cost,eval] using hh

theorem correct_nat {r : Nat} (e : Expr r) : Correct (Output.nat e) := by
  intro L x a s h
  have he := e.correct L x a s h
  have hh := Exec.seq he (push_run _ L.output false)
  convert hh using 1 <;> try rfl
  simp [eval,List.reverse_append]

theorem correct_append {r : Nat} {e f : Output r} (he : e.Correct) (hf : f.Correct) : (e.append f).Correct := by
  intro L x a s h
  have h1 := he L x a s h
  have h2 := hf L x a _ ((h.output ((e.eval x a).reverse ++ s.tape L.output)).flag false)
  have hh := Exec.seq h1 h2
  convert hh using 1 <;> try rfl
  simp [eval,List.reverse_append,List.append_assoc]

theorem correct_when {r : Nat} (t : Expr r) {o : Output r} (ho : o.Correct) : (Output.when t o).Correct := by
  intro L x a s h
  let u := t.eval x a
  have hs0 := h.clean L.fresh (by omega)
  have h1 := t.correct (L.temp 0 1 (by omega)) x a s (h.temp 0 1 (by omega))
  simp only [Layout.temp,Nat.add_zero,hs0,List.append_nil] at h1
  let s1 := (s.put L.fresh (List.replicate u true)).flag false
  have hp : (Code.atom (.peek L.fresh (fun _ x => x.isSome))).Exec s1 1
      ((s.put L.fresh (List.replicate u true)).flag (decide (u≠0))) := by
    convert Exec.atom (.peek L.fresh (fun _ x => x.isSome)) s1 using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [s1,Prim.run,Store.put,Store.flag]
    cases u <;> simp
  have hc := clear_run L.fresh ((s.put L.fresh (List.replicate u true)).flag (decide (u≠0)))
  simp only [Store.flag_tape,Store.put_tape_same,List.length_replicate,Store.put_flag,Store.put_put] at hc
  have hz : s.put L.fresh [] = s := by rw [← hs0,Store.put_self]
  rw [hz] at hc
  have hbranch : (Code.branch id (o.compile L.input L.args L.output L.fresh) reset).Exec
      (s.flag (decide (u≠0))) (1+(if u=0 then 1 else o.cost x a))
      ((s.put L.output (((Output.when t o).eval x a).reverse ++ s.tape L.output)).flag false) := by
    by_cases hu : u=0
    · have hh := Exec.branch_false (f := id) (c := o.compile L.input L.args L.output L.fresh)
        (d := reset) (s := s.flag (decide (u≠0))) (by simp [hu]) (reset_run _)
      simpa [eval,show t.eval x a = u from rfl,hu] using hh
    · have hh := Exec.branch_true (f := id) (c := o.compile L.input L.args L.output L.fresh)
        (d := reset) (s := s.flag (decide (u≠0))) (by simp [hu]) (ho L x a _ (h.flag _))
      simpa [eval,show t.eval x a = u from rfl,hu] using hh
  have hh := Exec.seq h1 (Exec.seq hp (Exec.seq hc hbranch))
  convert hh using 1; try rfl
  dsimp [cost,u]
  omega

theorem correct_loop {r : Nat} (b : Expr r) {e : Output (r+1)}
    (he : e.Correct) : (Output.loop b e).Correct := by
  intro L x a s h
  let n := b.eval x a
  let outputs := fun i => (List.range i).flatMap (fun j => e.eval x (Fin.cons j a))
  have hfo : L.fresh ≠ L.output := (Nat.ne_of_lt L.output_lt).symm
  have h1o : L.fresh+1 ≠ L.output := by have := L.output_lt; omega
  have hfi : L.input ≠ L.fresh := Nat.ne_of_lt L.input_lt
  have h1i : L.input ≠ L.fresh+1 := by have := L.input_lt; omega
  have hfa : ∀ j, L.args j ≠ L.fresh := fun j => Nat.ne_of_lt (L.args_lt j)
  have h1a : ∀ j, L.args j ≠ L.fresh+1 := by intro j; have := L.args_lt j; omega
  have hs0 := h.clean L.fresh (by omega)
  have hs1 := h.clean (L.fresh+1) (by omega)
  have h1 := b.correct (L.temp 0 2 (by omega)) x a s (h.temp 0 2 (by omega))
  simp only [Layout.temp,Nat.add_zero,hs0,List.append_nil] at h1
  let states := fun i =>
    ((((s.put (L.fresh+1) (List.replicate i true)).put L.fresh (List.replicate (n-i) true)).put
      L.output ((outputs i).reverse ++ s.tape L.output)).flag false)
  have hrdy : ∀ i, L.sumBody.Ready ((states i).put L.fresh (List.replicate (n-(i+1)) true))
      x (Fin.cons i a) := by
    intro i
    constructor
    · simp [states,Layout.sumBody,hfi,h1i,L.input_ne,h.input_eq]
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [states,Layout.sumBody,h1o]
      · simp [states,Layout.sumBody,hfa,h1a,L.args_ne,h.args_eq]
    · intro k hk
      change L.fresh+2 ≤ k at hk
      have hk0 : k≠L.fresh := by omega
      have hk1 : k≠L.fresh+1 := by omega
      have hko : k≠L.output := by have := L.output_lt; omega
      simp [states,hk0,hk1,hko,h.clean k (by omega)]
  have hp : ∀ i, (Code.seq (e.compile L.input (Fin.cons (L.fresh+1) L.args) L.output (L.fresh+2))
      (push (L.fresh+1) true)).Exec
      ((states i).put L.fresh (List.replicate (n-(i+1)) true))
      (e.cost x (Fin.cons i a)+1) (states (i+1)) := by
    intro i
    have hbody := he L.sumBody x (Fin.cons i a)
      ((states i).put L.fresh (List.replicate (n-(i+1)) true)) (hrdy i)
    have hpush := push_run ((((states i).put L.fresh (List.replicate (n-(i+1)) true)).put L.output
      ((e.eval x (Fin.cons i a)).reverse ++
        ((states i).put L.fresh (List.replicate (n-(i+1)) true)).tape L.output)).flag false)
      (L.fresh+1) true
    have hh := Exec.seq hbody hpush
    convert hh using 1 <;> try rfl
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hko : k=L.output
    · subst k
      simp only [states,Store.flag_tape,Store.put_tape_same,Store.put_tape_other _ (Ne.symm hfo),
        Store.put_tape_other _ (Ne.symm h1o)]
      simp [outputs,List.range_succ,List.flatMap_append,List.reverse_append,List.append_assoc]
    · by_cases hk0 : k=L.fresh <;> by_cases hk1 : k=L.fresh+1 <;>
        simp_all [states,Store.put,Store.flag,List.replicate_succ]
  have hlo := scan_indexed L.fresh
    (Code.seq (e.compile L.input (Fin.cons (L.fresh+1) L.args) L.output (L.fresh+2)) (push (L.fresh+1) true))
    n states (fun i => e.cost x (Fin.cons i a)+1)
    (by intro i hi; simp [states,hfo]) (by intro i hi; exact hp i)
  have hstart : states 0 = (s.put L.fresh (List.replicate n true)).flag false := by
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hko : k=L.output <;> by_cases hk0 : k=L.fresh <;> by_cases hk1 : k=L.fresh+1 <;>
      simp_all [states,outputs,Store.put,Store.flag]
  rw [hstart] at hlo
  have hc := clear_run (L.fresh+1) (states n)
  have hcval : (states n).tape (L.fresh+1) = List.replicate n true := by simp [states,h1o]
  rw [hcval,List.length_replicate] at hc
  have hend : (states n).put (L.fresh+1) [] =
      (s.put L.output ((outputs n).reverse ++ s.tape L.output)).flag false := by
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hko : k=L.output <;> by_cases hk0 : k=L.fresh <;> by_cases hk1 : k=L.fresh+1 <;>
      simp_all [states,Store.put,Store.flag]
  rw [hend] at hc
  have hh := Exec.seq h1 (Exec.seq hlo hc)
  convert hh using 1 <;> try rfl
  simp only [cost,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one]
  dsimp [n]
  omega

theorem correct {r : Nat} (o : Output r) : o.Correct := by
  induction o with
  | nil => exact correct_nil
  | bit b => exact correct_bit b
  | nat e => exact correct_nat e
  | append a b iha ihb => exact correct_append iha ihb
  | loop b e ihe => exact correct_loop b ihe
  | when t b ih => exact correct_when t ih

end DirectedFeedback.BoundedExpr.Output

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_StackFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DirectedFeedback.StackDSL
open Turing
variable {K S : Type} [DecidableEq K]
namespace Prim

def support : Prim K S → Finset K
  | .push k _ | .pop k _ | .peek k _ => {k}
  | .load _ => ∅

def restrict (p : Prim K S) (scope : Finset K) (h : p.support ⊆ scope) :
    Prim {k // k ∈ scope} S :=
  match p with
  | .push k f => .push ⟨k,h (by simp [support])⟩ f
  | .pop k f => .pop ⟨k,h (by simp [support])⟩ f
  | .peek k f => .peek ⟨k,h (by simp [support])⟩ f
  | .load f => .load f

end Prim

namespace Store

def restrict (s : Store K S) (scope : Finset K) : Store {k // k ∈ scope} S :=
  ⟨s.state,fun k => s.tape k.val⟩

theorem restrict_update (s : K → List Bool) (scope : Finset K) (k : K) (hk : k ∈ scope)
    (l : List Bool) :
    (fun j : {k // k ∈ scope} => Function.update s k l j.val) =
      Function.update (fun j : {k // k ∈ scope} => s j.val) ⟨k,hk⟩ l := by
  funext j
  by_cases h : j.val = k
  · have hj : j = ⟨k,hk⟩ := Subtype.ext h
    simp [hj]
  · have hj : j ≠ ⟨k,hk⟩ := fun he => h (congrArg Subtype.val he)
    simp [h,hj]

end Store

namespace Prim

theorem restrict_run (p : Prim K S) (scope : Finset K) (h : p.support ⊆ scope) (s : Store K S) :
    (p.restrict scope h).run (s.restrict scope) = (p.run s).restrict scope := by
  cases p <;> simp only [restrict,run,Store.restrict]
  · congr 1
    exact (Store.restrict_update ..).symm
  · congr 1
    exact (Store.restrict_update ..).symm

end Prim

namespace Code

def support : Code K S → Finset K
  | .atom p => p.support
  | .seq c d | .branch _ c d => c.support ∪ d.support
  | .scan k _ c => insert k c.support

def restrict (c : Code K S) (scope : Finset K) (h : c.support ⊆ scope) :
    Code {k // k ∈ scope} S :=
  match c with
  | .atom p => .atom (p.restrict scope h)
  | .seq c d => .seq (c.restrict scope (fun _ hm => h (by simp [support,hm])))
    (d.restrict scope (fun _ hm => h (by simp [support,hm])))
  | .branch f c d => .branch f (c.restrict scope (fun _ hm => h (by simp [support,hm])))
    (d.restrict scope (fun _ hm => h (by simp [support,hm])))
  | .scan k f c => .scan ⟨k,h (by simp [support])⟩ f
    (c.restrict scope (fun _ hm => h (by simp [support,hm])))

theorem Exec.restrict {c : Code K S} {s t : Store K S} {n : Nat} (h : c.Exec s n t)
    (scope : Finset K) (hc : c.support ⊆ scope) :
    (c.restrict scope hc).Exec (s.restrict scope) n (t.restrict scope) := by
  induction h with
  | atom p s =>
    rw [Code.restrict,← Prim.restrict_run p scope hc s]
    exact Exec.atom _ _
  | seq h1 h2 ih1 ih2 => exact Exec.seq (ih1 _) (ih2 _)
  | branch_true hb h ih => exact Exec.branch_true hb (ih _)
  | branch_false hb h ih => exact Exec.branch_false hb (ih _)
  | scan_nil hs =>
    apply Exec.scan_nil
    exact hs
  | @scan_cons k f c s t u b rest n m hs hb hl ihb ihl =>
    dsimp only [Code.restrict]
    apply Exec.scan_cons (s := s.restrict scope) (b := b) (rest := rest)
      (k := ⟨k,hc (by simp [support])⟩) (by exact hs)
    · have hh := ihb (fun _ hm => hc (by simp [support,hm]))
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      simp only [Store.restrict]
      congr 1
      exact (Store.restrict_update ..).symm
    · exact ihl hc

theorem restrict_ioStore (initial : S) (k : K) (bits : List Bool)
    (scope : Finset K) (hk : k ∈ scope) :
    (ioStore initial k bits).restrict scope = ioStore initial ⟨k,hk⟩ bits := by
  unfold Store.restrict ioStore
  congr 1
  funext j
  simp only [Subtype.ext_iff]

noncomputable def supportedComputation [Fintype S] {A B : Type}
    (ea : A → List Bool) (eb : B → List Bool) (f : A → B)
    (c : Code K S) (initial : S) (input output : K)
    (time : Polynomial Nat) (cost : A → Nat)
    (runs : ∀ a, c.Exec (ioStore initial input (ea a)) (cost a) (ioStore initial output (eb (f a))))
    (bound : ∀ a, cost a ≤ time.eval (ea a).length) :
    TM2ComputableInPolyTime ea eb f := by
  let scope := c.support ∪ {input,output}
  have hin : input ∈ scope := by simp [scope]
  have hout : output ∈ scope := by simp [scope]
  let d := c.restrict scope Finset.subset_union_left
  exact computation ea eb f d initial ⟨input,hin⟩ ⟨output,hout⟩ time cost (fun a => by
    have hh := (runs a).restrict scope Finset.subset_union_left
    simpa only [restrict_ioStore _ _ _ _ hin,restrict_ioStore _ _ _ _ hout] using hh) bound

end Code
end DirectedFeedback.StackDSL


namespace DirectedFeedback.BoundedExpr.Output
open StackDSL StackDSL.Code StackDSL.Ops
open Turing

def layout : Layout 0 where
  input := 0
  args := Fin.elim0
  output := 1
  fresh := 2
  input_lt := by omega
  args_lt := fun i => i.elim0
  output_lt := by omega
  input_ne := by omega
  args_ne := fun i => i.elim0

@[reducible] def program (o : Output 0) : Code Nat Bool :=
  .seq (o.compile 0 Fin.elim0 1 2) (.seq (clear 0) (transfer 1 0))

def steps (o : Output 0) (x : List Bool) : Nat :=
  o.cost x Fin.elim0+2*x.length+1+2*(o.eval x Fin.elim0).length+2

noncomputable def time (o : Output 0) : Polynomial Nat :=
  o.costBound+2*Polynomial.X+2*o.bound+3

theorem program_run (o : Output 0) (x : List Bool) :
    o.program.Exec (ioStore false 0 x) (o.steps x) (ioStore false 0 (o.eval x Fin.elim0)) := by
  let s := ioStore false (0 : Nat) x
  have hs : layout.Ready s x Fin.elim0 := by
    constructor
    · simp [layout,s,ioStore]
    · exact fun i => i.elim0
    · intro k hk
      change 2≤k at hk
      simp [s,ioStore,show k≠0 by omega]
  have h1 := o.correct layout x Fin.elim0 s hs
  simp only [layout] at h1
  have hs1 : s.tape 1 = [] := by simp [s,ioStore]
  rw [hs1,List.append_nil] at h1
  have hc := clear_run 0 ((s.put 1 (o.eval x Fin.elim0).reverse).flag false)
  have hcval : ((s.put 1 (o.eval x Fin.elim0).reverse).flag false).tape 0=x := by simp [s,ioStore]
  rw [hcval] at hc
  have ht := transfer_run (1 : Nat) 0 (by omega)
    (((s.put 1 (o.eval x Fin.elim0).reverse).flag false).put 0 [])
  have htv : (((s.put 1 (o.eval x Fin.elim0).reverse).flag false).put 0 []).tape 1 =
      (o.eval x Fin.elim0).reverse := by simp
  have ht0 : (((s.put 1 (o.eval x Fin.elim0).reverse).flag false).put 0 []).tape 0=[] := by simp
  rw [htv,ht0,List.length_reverse,List.reverse_reverse,List.append_nil] at ht
  have hend : (((((s.put 1 (o.eval x Fin.elim0).reverse).flag false).put 0 []).put 1 []).put
      0 (o.eval x Fin.elim0)).flag false = ioStore false 0 (o.eval x Fin.elim0) := by
    refine Store.ext _ _ rfl ?_
    funext k
    by_cases hk0 : k=0 <;> by_cases hk1 : k=1 <;> simp_all [Store.put,Store.flag,s,ioStore]
  rw [hend] at ht
  have hh := Exec.seq h1 (Exec.seq hc ht)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [steps]
  omega

theorem steps_le_time (o : Output 0) (x : List Bool) : o.steps x ≤ o.time.eval x.length := by
  have h1 := o.cost_le_bound x Fin.elim0 x.length (by omega) (fun i => i.elim0)
  have h2 := o.length_le_bound x Fin.elim0 x.length (by omega) (fun i => i.elim0)
  simp only [steps,time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  omega

noncomputable def computation (o : Output 0) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) id (fun x => o.eval x Fin.elim0) :=
  Code.supportedComputation id id (fun x => o.eval x Fin.elim0) o.program false 0 0
    o.time o.steps o.program_run o.steps_le_time

theorem computation_alphabet (o : Output 0) (k : o.computation.tm.K) : Finite (o.computation.tm.Γ k) := by
  change Finite Bool
  infer_instance

noncomputable def realizes {B : Type} (eb : B → List Bool) (f : List Bool → B)
    (o : Output 0) (h : ∀ x, o.eval x Fin.elim0 = eb (f x)) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) eb f where
  tm := o.computation.tm
  inputAlphabet := o.computation.inputAlphabet
  outputAlphabet := o.computation.outputAlphabet
  time := o.computation.time
  outputsFun x := by
    have hh := o.computation.outputsFun x
    simpa only [id_eq,h x] using hh

theorem realizes_alphabet {B : Type} (eb : B → List Bool) (f : List Bool → B)
    (o : Output 0) (h : ∀ x, o.eval x Fin.elim0 = eb (f x))
    (k : (realizes eb f o h).tm.K) : Finite ((realizes eb f o h).tm.Γ k) :=
  computation_alphabet o k

end DirectedFeedback.BoundedExpr.Output


namespace DirectedFeedback.BoundedExpr
open scoped BigOperators
namespace Expr

def rename {r s : Nat} (ρ : Fin r → Fin s) : Expr r → Expr s
  | .lit n => .lit n
  | .arg i => .arg (ρ i)
  | .length => .length
  | .bit i => .bit (rename ρ i)
  | .add a b => .add (rename ρ a) (rename ρ b)
  | .mul a b => .mul (rename ρ a) (rename ρ b)
  | .sub a b => .sub (rename ρ a) (rename ρ b)
  | .zero a => .zero (rename ρ a)
  | .sum b e => .sum (rename ρ b) (rename (Fin.cons 0 (fun i => (ρ i).succ)) e)

theorem eval_rename {r s : Nat} (ρ : Fin r → Fin s) (e : Expr r) (x : List Bool) (a : Fin s → Nat) :
    (e.rename ρ).eval x a = e.eval x (a ∘ ρ) := by
  induction e generalizing s with
  | lit n => rfl
  | arg i => rfl
  | length => rfl
  | bit i ih => simp [rename,eval,ih]
  | add a b iha ihb => simp [rename,eval,iha,ihb]
  | mul a b iha ihb => simp [rename,eval,iha,ihb]
  | sub a b iha ihb => simp [rename,eval,iha,ihb]
  | zero a ih => simp [rename,eval,ih]
  | sum b e ihb ihe =>
    simp only [rename,eval,ihb,ihe]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [Function.comp_def]

end Expr

def Def {r : Nat} (f : List Bool → (Fin r → Nat) → Nat) : Prop :=
  ∃ e : Expr r, ∀ x a, e.eval x a = f x a

namespace Def
variable {r : Nat} {f g h : List Bool → (Fin r → Nat) → Nat}

theorem congr (hf : Def f) (he : ∀ x a, f x a = g x a) : Def g := by
  obtain ⟨e,he'⟩ := hf
  exact ⟨e,fun x a => (he' x a).trans (he x a)⟩

theorem lit (n : Nat) : Def (fun (_ : List Bool) (_ : Fin r → Nat) => n) := ⟨.lit n,fun _ _ => rfl⟩
theorem arg (i : Fin r) : Def (fun (_ : List Bool) a => a i) := ⟨.arg i,fun _ _ => rfl⟩
theorem length : Def (fun (x : List Bool) (_ : Fin r → Nat) => x.length) := ⟨.length,fun _ _ => rfl⟩
theorem bit (hf : Def f) : Def (fun x a => if x[f x a]?.getD false then 1 else 0) := by
  obtain ⟨e,he⟩ := hf
  exact ⟨.bit e,by intro x a; simp only [Expr.eval,he]⟩
theorem add (hf : Def f) (hg : Def g) : Def (fun x a => f x a + g x a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg
  exact ⟨.add e d,by intro x a; simp only [Expr.eval,he,hd]⟩
theorem mul (hf : Def f) (hg : Def g) : Def (fun x a => f x a * g x a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg
  exact ⟨.mul e d,by intro x a; simp only [Expr.eval,he,hd]⟩
theorem sub (hf : Def f) (hg : Def g) : Def (fun x a => f x a - g x a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg
  exact ⟨.sub e d,by intro x a; simp only [Expr.eval,he,hd]⟩
theorem zero (hf : Def f) : Def (fun x a => if f x a=0 then 1 else 0) := by
  obtain ⟨e,he⟩ := hf
  exact ⟨.zero e,by intro x a; simp only [Expr.eval,he]⟩

theorem rename {s : Nat} (hf : Def f) (ρ : Fin r → Fin s) : Def (fun x a => f x (a ∘ ρ)) := by
  obtain ⟨e,he⟩ := hf
  exact ⟨e.rename ρ,fun x a => (e.eval_rename ρ x a).trans (he x _)⟩

theorem sum (hb : Def f) {e : List Bool → (Fin (r+1) → Nat) → Nat} (he : Def e) :
    Def (fun x a => ∑ i ∈ Finset.range (f x a), e x (Fin.cons i a)) := by
  obtain ⟨b,hb⟩ := hb; obtain ⟨e,he⟩ := he
  exact ⟨.sum b e,by intro x a; simp only [Expr.eval,hb,he]⟩

theorem eq (hf : Def f) (hg : Def g) : Def (fun x a => if f x a = g x a then 1 else 0) := by
  apply ((hf.sub hg).add (hg.sub hf)).zero.congr
  intro x a
  by_cases he : f x a = g x a
  · simp [he]
  · have hn : f x a - g x a + (g x a - f x a) ≠ 0 := by omega
    simp only [he,hn,ite_false]

theorem le (hf : Def f) (hg : Def g) : Def (fun x a => if f x a ≤ g x a then 1 else 0) := by
  apply (hf.sub hg).zero.congr
  intro x a
  simp only [Nat.sub_eq_zero_iff_le]

theorem lt (hf : Def f) (hg : Def g) : Def (fun x a => if f x a < g x a then 1 else 0) := by
  apply (hf.add (lit 1)).le hg |>.congr
  intro x a
  simp

theorem finset_sum {I : Type} (s : Finset I) (f : I → List Bool → (Fin r → Nat) → Nat)
    (hf : ∀ i ∈ s, Def (f i)) : Def (fun x a => ∑ i ∈ s, f i x a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lit (r := r) 0
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hf i (by simp)).add (ih (fun j hj => hf j (by simp [hj])))

end Def
end DirectedFeedback.BoundedExpr


noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.BoundedExpr

def FDef {r : Nat} {A : Type} (f : List Bool → (Fin r → Nat) → A) : Prop :=
  ∀ v, Def (fun x a => if f x a=v then 1 else 0)

end DirectedFeedback.BoundedExpr

end


noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.BoundedExpr

def PDef {r : Nat} (p : List Bool → (Fin r → Nat) → Prop) : Prop :=
  Def (fun x a => if p x a then 1 else 0)

namespace PDef
variable {r : Nat} {p q : List Bool → (Fin r → Nat) → Prop}

theorem not (hp : PDef p) : PDef (fun x a => ¬p x a) := by
  apply Def.congr (Def.zero hp)
  intro x a
  by_cases h : p x a <;> simp [h]

end PDef

namespace FDef
variable {r : Nat} {A : Type} [Fintype A]

theorem bool_true {f : List Bool → (Fin r → Nat) → Bool} (hf : FDef f) :
    PDef (fun x a => f x a=true) := hf true

end FDef
end DirectedFeedback.BoundedExpr

end


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KernelCardinality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Soundness.ZeroInformation

noncomputable def decodeIndex {O N : Type} (name : O → Fin 3 → N)
    (occurrence : O) (n : N) : Fin 3 := by
  classical
  exact if h : ∃ i, name occurrence i = n then Classical.choose h else 0

def reconstructQuestion {P X : Type} (hidden : P → Bool) (inside outside : P → X) : P → X :=
  fun j => if hidden j then inside j else outside j

end DFVSGames.Soundness.ZeroInformation

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ConditionalIncidences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators

namespace DFVSGames.Soundness.ConditionalIncidences

noncomputable section

def incidence {O N : Type} (name : O → Fin 3 → N) (draw : O × Fin 3) : O × N :=
  (draw.1, name draw.1 draw.2)

end

end DFVSGames.Soundness.ConditionalIncidences
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ActualCanonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Reduction.ActualCanonical

open scoped BigOperators

universe u v w
variable {k : Nat}
variable {Name : Type u} {Id : Type v} {R : Type w}
variable [AddCommGroup R]
  [DecidableEq R]

def singletonTriple (i : Fin 3) (c : R) : Fin 3 → R := Pi.single i c

end DFVSGames.Reduction.ActualCanonical

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_RepeatedGameBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Soundness.ConditionalIncidences
open scoped BigOperators

def coordinateReindex {A B X : Type} (e : B ≃ A) : (A → X) ≃ (B → X) where
  toFun f := fun b => f (e b)
  invFun g := fun a => g (e.symm a)
  left_inv f := by
    funext a
    exact congrArg f (e.apply_symm_apply a)
  right_inv g := by
    funext b
    exact congrArg g (e.symm_apply_apply b)

end DFVSGames.Soundness.ConditionalIncidences

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_PartnerFullSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Soundness.PartnerFullSampling

open scoped BigOperators

noncomputable section

def restrictIndices {P X : Type*} (J : Finset P) (indices : P → X) : ↥J → X :=
  fun j => indices j.val

def restrictionProductEquiv {P X : Type*} [DecidableEq P] (J : Finset P) :
    (P → X) ≃ ((↥J → X) × ({j : P // j ∉ J} → X)) where
  toFun indices := (restrictIndices J indices, fun j => indices j.val)
  invFun parts := fun j =>
    if hj : j ∈ J then parts.1 ⟨j, hj⟩ else parts.2 ⟨j, hj⟩
  left_inv indices := by
    funext j
    by_cases hj : j ∈ J <;> simp [restrictIndices, hj]
  right_inv parts := by
    apply Prod.ext
    · funext j
      simp [restrictIndices, j.property]
    · funext j
      simp [j.property]

end

end DFVSGames.Soundness.PartnerFullSampling


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_PositiveMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.RowErasure

open scoped BigOperators

noncomputable section

def replaceOn {X Y : Type*} (B : X → Prop) (f replacement : X → Y) : X → Y := by
  classical
  exact fun x => if B x then replacement x else f x

def goodUnion {A X : Type*} (good : A → X → Prop) (x : X) : Prop :=
  ∃ a, good a x

end
end DFVSGames.Inverse.RowErasure

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_ActualGoodRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.RowErasure.SelectionPartition

open scoped BigOperators Classical

noncomputable section

variable {X S : Type*} [Fintype X] [Fintype S]

def fiber (observe : X → S) (s : S) : Finset X :=
  Finset.univ.filter fun x => observe x = s

end
end DFVSGames.Inverse.RowErasure.SelectionPartition

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_BlockOrientations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Quadratic

open Module
open scoped BigOperators Matrix

noncomputable section

variable {R F V ι n E : Type*}
variable [Field R] [Field F] [Algebra R F]
variable [AddCommGroup V] [Module R V]
variable [Fintype ι] [Fintype n]

def alignmentMatrix (b : Basis ι R V) (point : E → V) (z : V → n → F) :
    Matrix E (n × ι) F :=
  fun e ij => algebraMap R F (b.repr (point e) ij.2) * z (point e) ij.1

end

end DFVSGames.Quadratic

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Genericity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Quadratic

noncomputable section

variable {R V W I : Type*} [Field R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

variable [Fintype V] [Fintype I] [DecidableEq I]

def lossIndices (f : I → V →ₗ[R] W) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => ∃ v : V, v ≠ 0 ∧ f i v = 0)

def alignedCharacters (aligned : V → Prop) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => v ≠ 0 ∧ aligned v)

end

end DFVSGames.Quadratic

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_NonlinearRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Quadratic

open MvPolynomial
open scoped BigOperators

variable {σ ι R : Type*} [CommSemiring R]

def SquarefreeExponent (a : σ →₀ ℕ) : Prop := ∀ k, a k < 2

noncomputable def blockExponent {κ J : Type*} [Finite κ] [Finite J]
    (v : κ → J) : (κ × J) →₀ ℕ := by
  classical
  exact Finsupp.equivFunOnFinite.symm (fun x => if x.2 = v x.1 then 1 else 0)

@[simp] theorem blockExponent_apply {κ J : Type*} [Finite κ] [Finite J] [DecidableEq J]
    (v : κ → J) (x : κ × J) :
    blockExponent v x = if x.2 = v x.1 then 1 else 0 := by
  classical
  by_cases h : x.2 = v x.1 <;> simp [blockExponent, h]

end DFVSGames.Quadratic

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_GenericPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Quadratic

open MvPolynomial
open scoped BigOperators
open scoped nonZeroDivisors

variable {σ : Type*}

variable {J X : Type*} [Fintype J] [Fintype X]

noncomputable def universalLinearForm (t : J → ZMod 2) (i : Fin 3) :
    MvPolynomial (Fin 3 × J) (ZMod 2) :=
  ∑ j, C (t j) * MvPolynomial.X (i, j)

noncomputable def universalAlignmentColumn (t : X → J → ZMod 2)
    (ij : Fin 3 × J) (x : X) : MvPolynomial (Fin 3 × J) (ZMod 2) :=
  C (t x ij.2) * universalLinearForm (t x) ij.1

noncomputable def cubicPairing (t : X → J → ZMod 2)
    (p : X → MvPolynomial (Fin 3 × J) (ZMod 2)) (v : Fin 3 → J) :
    MvPolynomial (Fin 3 × J) (ZMod 2) :=
  ∑ x, p x * C (∏ i, t x (v i))

noncomputable def alignmentObstruction (t : X → J → ZMod 2)
    (p : X → MvPolynomial (Fin 3 × J) (ZMod 2)) :
    MvPolynomial (Fin 3 × J) (ZMod 2) :=
  ∑ x, p x ^ 2 * ∏ i, universalLinearForm (t x) i

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

open scoped BigOperators

def quadraticEvaluationSpan {F X I : Type*} [Field F]
    (c : I → X → F) : Submodule F (X → F) :=
  Submodule.span F (Set.range fun ij : I × I => fun x => c ij.1 x * c ij.2 x)

def cubicEvaluationSpan {F X I : Type*} [Field F]
    (c : I → X → F) : Submodule F (X → F) :=
  Submodule.span F
    (Set.range fun ijk : I × I × I => fun x => c ijk.1 x * c ijk.2.1 x * c ijk.2.2 x)

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

open Module
open scoped BigOperators

noncomputable section

variable {F J : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F] [Fintype J]

def parameterMap (x : (Fin 3 × J) → F) : (J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F) :=
  (Pi.basisFun (ZMod 2) J).constr (ZMod 2) (fun j i => x (i, j))

omit [CharP F 2] in
theorem parameterMap_basis (x : (Fin 3 × J) → F) (j : J) (i : Fin 3) :
    parameterMap x ((Pi.basisFun (ZMod 2) J) j) i = x (i, j) := by
  exact congrFun ((Pi.basisFun (ZMod 2) J).constr_basis (ZMod 2)
    (fun j i => x (i, j)) j) i

end

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

open MvPolynomial

variable {J : Type*} [Fintype J]

noncomputable def selectorAssignment (j k : J) : (Fin 3 × J) → ZMod 2 := by
  classical
  exact fun x => if x.1 = 0 then (if x.2 = j then 1 else 0)
    else if x.1 = 1 then (if x.2 = k then 1 else 0) else 0

noncomputable def universalPairMinor (t u : J → ZMod 2) :
    MvPolynomial (Fin 3 × J) (ZMod 2) :=
  universalLinearForm t 0 * universalLinearForm u 1 +
    universalLinearForm t 1 * universalLinearForm u 0

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

open MvPolynomial
open scoped BigOperators

noncomputable section

variable (J : Type*) [Fintype J]

def nonzeroBinaryInputs : Finset (J → ZMod 2) := by
  classical
  exact Finset.univ.erase 0

def distinctNonzeroBinaryPairs : Finset ((J → ZMod 2) × (J → ZMod 2)) := by
  classical
  exact Finset.univ.filter (fun tu => tu.1 ≠ 0 ∧ tu.2 ≠ 0 ∧ tu.1 ≠ tu.2)

def separationPolynomial : MvPolynomial (Fin 3 × J) (ZMod 2) :=
  (∏ t ∈ nonzeroBinaryInputs J, universalLinearForm t 0) *
    ∏ tu ∈ distinctNonzeroBinaryPairs J, universalPairMinor tu.1 tu.2

end

end DFVSGames.Quadratic

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_PolynomialProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Quadratic

open scoped BigOperators

noncomputable section

variable {K F : Type*} [Field K] [Field F] [Fintype F]

def assignmentProbability {n : ℕ} (event : (Fin n → F) → Prop) : ℚ≥0 := by
  classical
  exact ((Finset.univ.filter event).card : ℚ≥0) / (Fintype.card F : ℚ≥0) ^ n

end

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

open scoped BigOperators

noncomputable section

variable {σ τ K F : Type*} [Field K] [Field F] [Fintype F]

def reindexAssignments (e : σ ≃ τ) : (σ → F) ≃ (τ → F) where
  toFun x := fun t => x (e.symm t)
  invFun y := fun s => y (e s)
  left_inv x := by funext s; simp
  right_inv y := by funext t; simp

def finiteAssignmentProbability [Fintype σ] (event : (σ → F) → Prop) : ℚ≥0 := by
  classical
  exact ((Finset.univ.filter event).card : ℚ≥0) /
    (Fintype.card F : ℚ≥0) ^ Fintype.card σ

end

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

noncomputable section

variable {F J : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F] [Fintype J]

def parameterMapEquiv : ((Fin 3 × J) → F) ≃
    ((J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F)) where
  toFun := parameterMap
  invFun g ij := g ((Pi.basisFun (ZMod 2) J) ij.2) ij.1
  left_inv x := by
    funext ij
    exact parameterMap_basis x ij.2 ij.1
  right_inv g := by
    apply (Pi.basisFun (ZMod 2) J).ext
    intro j
    funext i
    exact parameterMap_basis _ j i

end

end DFVSGames.Quadratic

noncomputable section

open scoped BigOperators
open Module

namespace DFVSGames.Quadratic.UniformSubspaces

variable {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]

def Injection (K V W : Type*) [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] :=
  {J : V →ₗ[K] W // Function.Injective J}

instance injectionAction : MulAction (W ≃ₗ[K] W) (Injection K V W) where
  smul a J := ⟨a.toLinearMap.comp J.val, a.injective.comp J.property⟩
  one_smul J := by
    apply Subtype.ext
    ext x
    rfl
  mul_smul a b J := by
    apply Subtype.ext
    ext x
    rfl

end DFVSGames.Quadratic.UniformSubspaces
end

namespace DFVSGames.Quadratic

def fieldDegree (cardThreshold rankThreshold : ℕ) : ℕ :=
  cardThreshold + rankThreshold + 1

end DFVSGames.Quadratic

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_MatrixChartDegreeNeighbors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.MatrixChart

open Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

theorem inf_eq_base_of_distinct_extensions [FiniteDimensional K E]
    (H L W : Submodule K E) (hHL : H ≤ L) (hHW : H ≤ W)
    (hL : finrank K L = finrank K H + 1)
    (hW : finrank K W = finrank K H + 1) (hWL : W ≠ L) :
    L ⊓ W = H := by
  apply le_antisymm
  · by_contra hn
    have hlt : H < L ⊓ W := lt_of_le_of_ne (le_inf hHL hHW) (by
      intro heq
      exact hn heq.ge)
    have hd := Submodule.finrank_lt_finrank_of_lt hlt
    have hi := Submodule.finrank_mono (show L ⊓ W ≤ L from inf_le_left)
    have heq : L ⊓ W = L := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
    have hLW : L ≤ W := by rw [← heq]; exact inf_le_right
    exact hWL (Submodule.eq_of_le_of_finrank_eq hLW (hL.trans hW.symm)).symm
  · exact le_inf hHL hHW

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.MatrixChart

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

def lowerRows {ι : Type*} (d : ι → X) (s : ι → Y) : Submodule K (X × Y) :=
  Submodule.span K (Set.range fun i => (d i, s i))

def upperColumns {ι : Type*} (t : ι → X →ₗ[K] K) (q : ι → Y →ₗ[K] K) :
    Submodule K (X × Y) :=
  ⨅ i, LinearMap.ker ((q i).comp (LinearMap.snd K X Y) -
    (t i).comp (LinearMap.fst K X Y))

end DFVSGames.Inverse.MatrixChart

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSBasisComparisonRetention
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped Classical
open MatrixChart

def zeroFactorMass (ell m : ℕ) : ℝ :=
  ((2 : ℝ) ^ ell)⁻¹ + ((2 : ℝ) ^ m)⁻¹ - ((2 : ℝ) ^ (ell + m))⁻¹

end
end DFVSGames.Inverse.ShortcodeFromGrassmann

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_UnweightedIntegrated
attribute [-instance] _root_.OAI.DirectedFeedback.StackDSL.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace DirectedFeedback.RankGraph

variable (U V X Y : Type) (T N : ℕ)

abbrev Tuple := (Σ t : Fin (T + 1), Fin t.val → U) ⊕
  (Σ t : Fin T, (Fin t.val → U) × V)

abbrev Domain : Tuple U V T → Type
  | .inl ⟨t, _⟩ => Fin t.val → X
  | .inr ⟨t, _⟩ => (Fin t.val → X) × Y

instance instFintypeDomain [Fintype X] [Fintype Y] (d : Tuple U V T) : Fintype (Domain U V X Y T d) := by
  cases d with
  | inl d => rcases d with ⟨t, s⟩; exact inferInstanceAs (Fintype (Fin t.val → X))
  | inr d => rcases d with ⟨t, s⟩; exact inferInstanceAs (Fintype ((Fin t.val → X) × Y))

abbrev Formal := Σ d : Tuple U V T, Domain U V X Y T d → Fin N

inductive PrefixStep : Formal U V X Y T N → Formal U V X Y T N → Prop
  | big (t : ℕ) (ht : t < T) (s : Fin (t + 1) → U)
      (x : (Fin t → X) → Fin N) :
      PrefixStep
        ⟨.inl ⟨⟨t, by omega⟩, Fin.init s⟩, x⟩
        ⟨.inl ⟨⟨t + 1, by omega⟩, s⟩, fun a => x (Fin.init a)⟩
  | small (t : Fin T) (s : Fin t.val → U) (v : V)
      (x : (Fin t.val → X) → Fin N) :
      PrefixStep
        ⟨.inl ⟨⟨t.val, by omega⟩, s⟩, x⟩
        ⟨.inr ⟨t, s, v⟩, fun a => x a.1⟩

abbrev Rank := Quot (PrefixStep U V X Y T N)

instance instFiniteRank [Finite U] [Finite V] [Finite X] [Finite Y] : Finite (Rank U V X Y T N) := by
  let := Fintype.ofFinite U
  let := Fintype.ofFinite V
  let := Fintype.ofFinite X
  let := Fintype.ofFinite Y
  exact Quot.finite _

variable {U V X Y T N}

def vertex (d : Tuple U V T) (x : Domain U V X Y T d → Fin N) : Rank U V X Y T N :=
  Quot.mk _ ⟨d, x⟩

def labels (ellU : U → X) (ellV : V → Y) :
    (d : Tuple U V T) → Domain U V X Y T d
  | .inl ⟨_, s⟩ => fun i => ellU (s i)
  | .inr ⟨_, s, v⟩ => (fun i => ellU (s i), ellV v)

def eval (ellU : U → X) (ellV : V → Y) : Rank U V X Y T N → Fin N :=
  Quot.lift (fun z => z.2 (labels ellU ellV z.1)) (by
    intro a b hab
    cases hab <;> rfl)

@[simp] theorem eval_vertex (ellU : U → X) (ellV : V → Y)
    (d : Tuple U V T) (x : Domain U V X Y T d → Fin N) :
    eval ellU ellV (vertex d x) = x (labels ellU ellV d) := rfl

def Arc (a b : Rank U V X Y T N) : Prop :=
  ∃ (d : Tuple U V T) (x y : Domain U V X Y T d → Fin N),
    a = vertex d x ∧ b = vertex d y ∧ ∀ lambda, x lambda < y lambda

theorem eval_arc (ellU : U → X) (ellV : V → Y)
    {a b : Rank U V X Y T N} (h : Arc a b) : eval ellU ellV a < eval ellU ellV b := by
  obtain ⟨d, x, y, rfl, rfl, h⟩ := h
  exact h (labels ellU ellV d)

def emptyTuple : Tuple U V T := .inl ⟨⟨0, Nat.zero_lt_succ _⟩, Fin.elim0⟩

def marker (j : Fin N) : Rank U V X Y T N := vertex emptyTuple (fun _ => j)

@[simp] theorem eval_marker (ellU : U → X) (ellV : V → Y) (j : Fin N) :
    eval ellU ellV (marker j : Rank U V X Y T N) = j := rfl

theorem marker_arc {i j : Fin N} (h : i < j) :
    Arc (marker i : Rank U V X Y T N) (marker j) :=
  ⟨emptyTuple, (fun _ => i), (fun _ => j), rfl, rfl, fun _ => h⟩

theorem prefix_big (t : ℕ) (ht : t < T) (s : Fin (t + 1) → U)
    (x : (Fin t → X) → Fin N) :
    (vertex (.inl ⟨⟨t, by omega⟩, Fin.init s⟩) x : Rank U V X Y T N) =
      vertex (.inl ⟨⟨t + 1, by omega⟩, s⟩) (fun a => x (Fin.init a)) :=
  Quot.sound (.big t ht s x)

theorem prefix_small (t : Fin T) (s : Fin t.val → U) (v : V)
    (x : (Fin t.val → X) → Fin N) :
    (vertex (.inl ⟨⟨t.val, by omega⟩, s⟩) x : Rank U V X Y T N) =
      vertex (.inr ⟨t, s, v⟩) (fun a => x a.1) :=
  Quot.sound (.small t s v x)

theorem constant_pure (t : ℕ) (ht : t ≤ T) (s : Fin t → U) (j : Fin N) :
    (vertex (.inl ⟨⟨t, by omega⟩, s⟩) (fun _ => j) : Rank U V X Y T N) = marker j := by
  induction t with
  | zero =>
      have hs : s = Fin.elim0 := funext (fun i => Fin.elim0 i)
      subst s
      rfl
  | succ t ih =>
      rw [← prefix_big t (by omega) s (fun _ => j)]
      exact ih (by omega) (Fin.init s)

theorem constant_vertex (d : Tuple U V T) (j : Fin N) :
    (vertex d (fun _ => j) : Rank U V X Y T N) = marker j := by
  cases d with
  | inl d => rcases d with ⟨t, s⟩; exact constant_pure t.val (by omega) s j
  | inr d =>
      rcases d with ⟨t, s, v⟩
      rw [← prefix_small t s v (fun _ => j)]
      exact constant_pure t.val (by omega) s j

end DirectedFeedback.RankGraph

namespace DirectedFeedback.RankGraph
variable {U V X Y : Type} {T N L : ℕ}
variable (ord : Rank U V X Y T N → ℕ)
variable (ψ : Fin L → Fin N)

def twoLevel (d : Tuple U V T) (E : Set (Domain U V X Y T d))
    (a h : Fin L) : Rank U V X Y T N := by
  classical
  exact vertex d (fun lambda => if lambda ∈ E then ψ a else ψ h)

def compareBit (d : Tuple U V T) (E : Set (Domain U V X Y T d))
    (a c h : Fin L) : Bool :=
  decide (ord (twoLevel ψ d E a h) < ord (marker (ψ c)))

def referenceBit (hL : 30 ≤ L) (d : Tuple U V T)
    (E : Set (Domain U V X Y T d)) : Bool :=
  compareBit ord ψ d E ⟨1, by omega⟩ ⟨14, by omega⟩ ⟨L - 2, by omega⟩

variable {ord ψ}

@[simp] theorem reference_empty (hL : 30 ≤ L) (hψ : StrictMono ψ)
    (hord : ∀ {a b}, Arc a b → ord a < ord b) (d : Tuple U V T) :
    referenceBit ord ψ hL d ∅ = false := by
  classical
  have hx : twoLevel (X := X) (Y := Y) ψ d ∅ (⟨1, by omega⟩ : Fin L) ⟨L - 2, by omega⟩ =
      marker (ψ ⟨L - 2, by omega⟩) := by
    simpa [twoLevel] using constant_vertex (X := X) (Y := Y) d (ψ ⟨L - 2, by omega⟩)
  have hlt := hord (marker_arc (U := U) (V := V) (X := X) (Y := Y) (T := T)
    (hψ (show (⟨14, by omega⟩ : Fin L) < ⟨L - 2, by omega⟩ from by simp; omega)))
  simp only [referenceBit, compareBit, hx, decide_eq_false_iff_not]
  exact not_lt_of_gt hlt

@[simp] theorem reference_univ (hL : 30 ≤ L) (hψ : StrictMono ψ)
    (hord : ∀ {a b}, Arc a b → ord a < ord b) (d : Tuple U V T) :
    referenceBit ord ψ hL d Set.univ = true := by
  classical
  have hx : twoLevel (X := X) (Y := Y) ψ d Set.univ (⟨1, by omega⟩ : Fin L) ⟨L - 2, by omega⟩ =
      marker (ψ ⟨1, by omega⟩) := by
    simpa [twoLevel] using constant_vertex (X := X) (Y := Y) d (ψ ⟨1, by omega⟩)
  simp only [referenceBit, compareBit, hx, decide_eq_true_eq]
  exact hord (marker_arc (hψ (by simp)))

end DirectedFeedback.RankGraph

namespace DirectedFeedback.RankGraph
variable {U V X Y : Type} {T N L k K : ℕ}
variable (ψ : Fin L → Fin N) (d : Tuple U V T)

def belowWildcard (cell : Domain U V X Y T d → Fin k)
    (Z : Set (Domain U V X Y T d)) (level : Fin k → Fin N)
    (x : Domain U V X Y T d → Fin N) : Prop :=
  ∀ lambda, lambda ∉ Z → x lambda < level (cell lambda)

def aboveWildcard (cell : Domain U V X Y T d → Fin k)
    (Z : Set (Domain U V X Y T d)) (level : Fin k → Fin N)
    (x : Domain U V X Y T d → Fin N) : Prop :=
  ∀ lambda, lambda ∉ Z → level (cell lambda) < x lambda

end DirectedFeedback.RankGraph

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.TestGraph
open RankGraph
variable {U V X Y W C : Type} {T N : ℕ}

structure Wildcard where
  tuple : Tuple U V T
  cells : ℕ
  cell : Domain U V X Y T tuple → Fin cells
  stars : Set (Domain U V X Y T tuple)
  level : Fin cells → Fin N

structure Comparison where
  source : Rank U V X Y T N
  target : Rank U V X Y T N

abbrev Vertex (U V X Y W C : Type) (T N : ℕ) := Rank U V X Y T N ⊕ (W ⊕ C)

inductive Arc (wild : W → Wildcard (U := U) (V := V) (X := X) (Y := Y) (T := T) (N := N))
    (comp : C → Comparison (U := U) (V := V) (X := X) (Y := Y) (T := T) (N := N)) :
    Vertex U V X Y W C T N → Vertex U V X Y W C T N → Prop
  | rank {a b} (h : RankGraph.Arc a b) : Arc wild comp (.inl a) (.inl b)
  | wild_in (w : W) (x : Domain U V X Y T (wild w).tuple → Fin N)
      (h : belowWildcard (wild w).tuple (wild w).cell (wild w).stars (wild w).level x) :
      Arc wild comp (.inl (vertex (wild w).tuple x)) (.inr (.inl w))
  | wild_out (w : W) (x : Domain U V X Y T (wild w).tuple → Fin N)
      (h : aboveWildcard (wild w).tuple (wild w).cell (wild w).stars (wild w).level x) :
      Arc wild comp (.inr (.inl w)) (.inl (vertex (wild w).tuple x))
  | comp_in (c : C) : Arc wild comp (.inl (comp c).source) (.inr (.inr c))
  | comp_out (c : C) : Arc wild comp (.inr (.inr c)) (.inl (comp c).target)

variable (wild : W → Wildcard (U := U) (V := V) (X := X) (Y := Y) (T := T) (N := N))
    (comp : C → Comparison (U := U) (V := V) (X := X) (Y := Y) (T := T) (N := N))

def LabelDeleted (ellU : U → X) (ellV : V → Y) : Vertex U V X Y W C T N → Prop
  | .inl _ => False
  | .inr (.inl w) => labels ellU ellV (wild w).tuple ∈ (wild w).stars
  | .inr (.inr c) => eval ellU ellV (comp c).target ≤ eval ellU ellV (comp c).source

def labelPotential (ellU : U → X) (ellV : V → Y) : Vertex U V X Y W C T N → ℚ
  | .inl r => (eval ellU ellV r).val
  | .inr (.inl w) => ((wild w).level ((wild w).cell (labels ellU ellV (wild w).tuple))).val
  | .inr (.inr c) => ((eval ellU ellV (comp c).source).val +
      (eval ellU ellV (comp c).target).val : ℚ) / 2

theorem labelPotential_increases (ellU : U → X) (ellV : V → Y)
    {a b : Vertex U V X Y W C T N} (hab : Arc wild comp a b)
    (ha : ¬LabelDeleted wild comp ellU ellV a) (hb : ¬LabelDeleted wild comp ellU ellV b) :
    labelPotential wild comp ellU ellV a < labelPotential wild comp ellU ellV b := by
  cases hab with
  | rank h =>
      dsimp [labelPotential]
      exact_mod_cast (eval_arc ellU ellV h : (eval ellU ellV _).val < (eval ellU ellV _).val)
  | wild_in w x h =>
      dsimp [labelPotential, eval_vertex]
      exact_mod_cast (h _ hb : (x _).val < ((wild w).level _).val)
  | wild_out w x h =>
      dsimp [labelPotential, eval_vertex]
      exact_mod_cast (h _ ha : ((wild w).level _).val < (x _).val)
  | comp_in c =>
      have hh : (eval ellU ellV (comp c).source).val < (eval ellU ellV (comp c).target).val :=
        not_le.mp hb
      dsimp [labelPotential]
      have hh' : ((eval ellU ellV (comp c).source).val : ℚ) < (eval ellU ellV (comp c).target).val :=
        by exact_mod_cast hh
      linarith
  | comp_out c =>
      have hh : (eval ellU ellV (comp c).source).val < (eval ellU ellV (comp c).target).val :=
        not_le.mp ha
      dsimp [labelPotential]
      have hh' : ((eval ellU ellV (comp c).source).val : ℚ) < (eval ellU ellV (comp c).target).val :=
        by exact_mod_cast hh
      linarith

end DirectedFeedback.TestGraph

noncomputable section
open scoped Classical
namespace DirectedFeedback.Prefix
variable {S X : Type*} {k : ℕ}

def boundary (cell : S → Fin k) (r : ℕ) : Set S := {a | (cell a).val < r}

@[simp] theorem boundary_zero (cell : S → Fin k) : boundary cell 0 = ∅ := by
  ext a; simp [boundary]

@[simp] theorem boundary_top (cell : S → Fin k) : boundary cell k = Set.univ := by
  ext a; simp [boundary]

def conditionedSet (cell : S → Fin k) (r : Fin k) (R : Set X) : Set (S × X) :=
  {a | (cell a.1).val < r.val ∨ cell a.1 = r ∧ a.2 ∈ R}

@[simp] theorem conditionedSet_empty (cell : S → Fin k) (r : Fin k) :
    conditionedSet (X := X) cell r ∅ = Prod.fst ⁻¹' boundary cell r.val := by
  ext a; simp [conditionedSet, boundary]

@[simp] theorem conditionedSet_univ (cell : S → Fin k) (r : Fin k) :
    conditionedSet (X := X) cell r Set.univ = Prod.fst ⁻¹' boundary cell (r.val + 1) := by
  ext a
  simp only [conditionedSet, Set.mem_ofPred_eq, Set.mem_univ, and_true,
    Set.mem_preimage, boundary, Fin.ext_iff]
  omega

def refineCell (cell : S → Fin k) (P : Set X) (a : S × X) : Fin (2 * k) := by
  classical
  exact ⟨2 * (cell a.1).val + if a.2 ∈ P then 0 else 1, by
    have := (cell a.1).isLt
    split_ifs <;> omega⟩

end DirectedFeedback.Prefix
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_CellCount
attribute [-instance] _root_.OAI.DirectedFeedback.StackDSL.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical

noncomputable section
open scoped Classical
namespace DirectedFeedback.Prefix
variable {X : Type*}

def cellCount : ℕ → ℕ
  | 0 => 1
  | t+1 => 2 * cellCount t

theorem cellCount_eq (t : ℕ) : cellCount t = 2^t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [cellCount, ih, pow_succ, mul_comm]

def prefixCell : (t : ℕ) → (ℕ → Set X) → (Fin t → X) → Fin (cellCount t)
  | 0, _, _ => ⟨0, by decide⟩
  | t+1, P, a => refineCell (prefixCell t P) (P t) (Fin.init a, a (Fin.last t))

def splitLast (t : ℕ) : (Fin (t+1) → X) ≃ ((Fin t → X) × X) where
  toFun a := (Fin.init a, a (Fin.last t))
  invFun a := Fin.snoc a.1 a.2
  left_inv a := by funext i; exact Fin.lastCases (by simp) (fun j => by simp [Fin.init]) i
  right_inv a := by rcases a with ⟨a,x⟩; simp

end DirectedFeedback.Prefix

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Prefix
variable {S X : Type*} {k n : ℕ}

def orderedCell (cell : S → Fin k) (order : X ≃ Fin n) (a : S × X) : Fin (k*n) :=
  ⟨n*(cell a.1).val + (order a.2).val, by
    have h := Nat.mul_le_mul_left n (cell a.1).isLt
    have h' := (order a.2).isLt
    simp only [Nat.mul_succ] at h
    rw [Nat.mul_comm k n]
    omega⟩

end DirectedFeedback.Prefix

noncomputable section
open scoped BigOperators
namespace DirectedFeedback.SourceProbability
structure FiniteDistribution (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonnegative : ∀ x, 0 ≤ weight x
  normalized : ∑ x, weight x = 1

namespace FiniteDistribution

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

def expectation (μ : FiniteDistribution Ω) (f : Ω → ℝ) : ℝ :=
  ∑ x, μ.weight x * f x

def probability (μ : FiniteDistribution Ω) (event : Ω → Bool) : ℝ :=
  ∑ x, if event x then μ.weight x else 0

@[simp] theorem probability_true (μ : FiniteDistribution Ω) :
    μ.probability (fun _ => true) = 1 := by
  simpa [probability] using μ.normalized

@[simp] theorem probability_false (μ : FiniteDistribution Ω) :
    μ.probability (fun _ => false) = 0 := by
  simp [probability]

theorem probability_mono (μ : FiniteDistribution Ω) {event event' : Ω → Bool}
    (h : ∀ x, event x = true → event' x = true) :
    μ.probability event ≤ μ.probability event' := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : event x = true
  · simp [hx, h x hx]
  · simp [hx]
    split
    · exact μ.nonnegative x
    · exact le_rfl

def pushforward (μ : FiniteDistribution Ω) (f : Ω → Γ) : FiniteDistribution Γ := by
  classical
  exact
    { weight := fun y => ∑ x, if f x = y then μ.weight x else 0
      nonnegative := fun y => Finset.sum_nonneg fun x _ => by
        split
        · exact μ.nonnegative x
        · exact le_rfl
      normalized := by
        rw [Finset.sum_comm]
        simpa using μ.normalized }

theorem probability_pushforward (μ : FiniteDistribution Ω) (f : Ω → Γ)
    (event : Γ → Bool) :
    (μ.pushforward f).probability event = μ.probability (fun x => event (f x)) := by
  classical
  simp only [probability, pushforward]
  calc
    _ = ∑ y, ∑ x, if f x = y then (if event y then μ.weight x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : event y = true <;> simp [hy]
    _ = _ := by rw [Finset.sum_comm]; simp

def iid (μ : FiniteDistribution Ω) (n : Nat) : FiniteDistribution (Fin n → Ω) where
  weight x := ∏ i, μ.weight (x i)
  nonnegative x := Finset.prod_nonneg fun i _ => μ.nonnegative (x i)
  normalized := by rw [← Fintype.sum_pow, μ.normalized, one_pow]

end FiniteDistribution
namespace FiniteDistribution
variable {Ω Γ Q A : Type*} [Fintype Ω] [Fintype Γ] [Fintype Q] [Fintype A]
theorem eq_of_weight_eq {μ ν : FiniteDistribution Ω}
    (h : ∀ x, μ.weight x = ν.weight x) : μ = ν := by
  cases μ with
  | mk w hw hs =>
    cases ν with
    | mk w' hw' hs' =>
      have he : w = w' := funext h
      cases he
      rfl

def table [DecidableEq Q] (responses : Q → FiniteDistribution A) :
    FiniteDistribution (Q → A) := by
  classical
  exact
    { weight := fun answers => ∏ q, (responses q).weight (answers q)
      nonnegative := fun answers => Finset.prod_nonneg fun q _ =>
        (responses q).nonnegative (answers q)
      normalized := by
        rw [← Fintype.prod_sum]
        simp only [FiniteDistribution.normalized, Finset.prod_const_one] }

theorem expectation_table_eval [DecidableEq Q] (responses : Q → FiniteDistribution A)
    (q₀ : Q) (h : A → ℝ) :
    (table responses).expectation (fun answers => h (answers q₀)) =
      (responses q₀).expectation h := by
  classical
  change (∑ answers : Q → A,
    (∏ q, (responses q).weight (answers q)) * h (answers q₀)) =
      ∑ a, (responses q₀).weight a * h a
  calc
    _ = ∑ answers : Q → A,
        ∏ q, (responses q).weight (answers q) *
          (if q = q₀ then h (answers q) else 1) := by
      apply Finset.sum_congr rfl
      intro answers _
      rw [Finset.prod_mul_distrib]
      simp
    _ = ∏ q, ∑ a, (responses q).weight a * (if q = q₀ then h a else 1) :=
      (Fintype.prod_sum (fun q a =>
        (responses q).weight a * (if q = q₀ then h a else 1))).symm
    _ = ∏ q : Q, if q = q₀ then (∑ a, (responses q₀).weight a * h a) else 1 := by
      apply Finset.prod_congr rfl
      intro q _
      by_cases hq : q = q₀
      · subst q
        simp
      · simp [hq, (responses q).normalized]
    _ = _ := by simp

def product (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ) :
    FiniteDistribution (Ω × Γ) where
  weight x := μ.weight x.1 * ν.weight x.2
  nonnegative x := mul_nonneg (μ.nonnegative _) (ν.nonnegative _)
  normalized := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ν.normalized, mul_one]
    exact μ.normalized

theorem expectation_product (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω × Γ → ℝ) :
    (μ.product ν).expectation f =
      μ.expectation (fun x => ν.expectation (fun y => f (x,y))) := by
  simp only [expectation, product, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem expectation_congr (μ : FiniteDistribution Ω) {f g : Ω → ℝ}
    (h : ∀ x, f x = g x) : μ.expectation f = μ.expectation g := by
  unfold expectation
  apply Finset.sum_congr rfl
  intro x _
  rw [h x]

def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteDistribution Ω where
  weight _ := 1 / (Fintype.card Ω : ℝ)
  nonnegative _ := div_nonneg zero_le_one (Nat.cast_nonneg _)
  normalized := by
    have hn : (Fintype.card Ω : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_div]
    exact mul_inv_cancel₀ hn

theorem expectation_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    (uniform Ω).expectation f = (∑ x, f x) / (Fintype.card Ω : ℝ) := by
  unfold expectation uniform
  rw [← Finset.mul_sum]
  simp [div_eq_mul_inv, mul_comm]

end FiniteDistribution
end DirectedFeedback.SourceProbability

namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {I J : Type*} [Fintype I] [Fintype J]

@[simp] theorem expectation_const (μ : FiniteDistribution I) (a : ℝ) :
    μ.expectation (fun _ => a) = a := by
  simp [expectation, ← Finset.sum_mul, μ.normalized]

theorem expectation_mono (μ : FiniteDistribution I) {f g : I → ℝ}
    (h : ∀ i, f i ≤ g i) : μ.expectation f ≤ μ.expectation g :=
  Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) (μ.nonnegative i))

@[simp] theorem expectation_add (μ : FiniteDistribution I) (f g : I → ℝ) :
    μ.expectation (fun i => f i + g i) = μ.expectation f + μ.expectation g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

@[simp] theorem expectation_mul_left (μ : FiniteDistribution I) (a : ℝ) (f : I → ℝ) :
    μ.expectation (fun i => a * f i) = a * μ.expectation f := by
  simp [expectation, Finset.mul_sum, mul_left_comm]

end DirectedFeedback.SourceProbability.FiniteDistribution

noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
namespace DirectedFeedback.Pivotal

variable {I : Type*} [Fintype I] [DecidableEq I]

def coin (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteDistribution Bool where
  weight b := if b then p else 1 - p
  nonnegative b := by cases b <;> simp [hp0, sub_nonneg.mpr hp1]
  normalized := by simp

def law (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteDistribution (I → Bool) :=
  FiniteDistribution.table (fun _ => coin p hp0 hp1)

def relabel (σ : Equiv.Perm I) : (I → Bool) ≃ (I → Bool) where
  toFun b i := b (σ.symm i)
  invFun b i := b (σ i)
  left_inv b := by ext i; simp
  right_inv b := by ext i; simp

omit [Fintype I] [DecidableEq I] in
@[simp] theorem relabel_apply (σ : Equiv.Perm I) (b : I → Bool) (i : I) :
    relabel σ b i = b (σ.symm i) := rfl

omit [Fintype I] [DecidableEq I] in
@[simp] theorem relabel_trans (σ τ : Equiv.Perm I) (b : I → Bool) :
    relabel τ (relabel σ b) = relabel (σ.trans τ) b := rfl

def chainPrefix (I : Type*) [Fintype I] (r : ℕ) : I → Bool :=
  fun i => decide ((Fintype.equivFin I i).val < r)

def chainHit (event : (I → Bool) → Bool) (σ : Equiv.Perm I) : Bool :=
  decide (∃ r ≤ Fintype.card I, event (relabel σ (chainPrefix I r)) = true)

def chainBudget (event : (I → Bool) → Bool) : ℝ :=
  (FiniteDistribution.uniform (Equiv.Perm I)).probability (chainHit event)

@[simp] theorem uniform_comp_right (σ : Equiv.Perm I) (f : Equiv.Perm I → ℝ) :
    (FiniteDistribution.uniform (Equiv.Perm I)).expectation (fun τ => f (σ.trans τ)) =
      (FiniteDistribution.uniform (Equiv.Perm I)).expectation f := by
  classical
  rw [FiniteDistribution.expectation_uniform, FiniteDistribution.expectation_uniform]
  congr 1
  let e : Equiv.Perm I ≃ Equiv.Perm I :=
    { toFun := fun τ => σ.trans τ
      invFun := fun τ => σ.symm.trans τ
      left_inv := by intro τ; ext i; simp
      right_inv := by intro τ; ext i; simp }
  exact e.sum_comp f

end DirectedFeedback.Pivotal

namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

def bitValue (b : Bool) : ℝ := if b then 1 else 0

def insertBit (j : I) (b : Bool) (x : {i : I // i ≠ j} → Bool) : I → Bool :=
  (Equiv.funSplitAt j Bool).symm (b, x)

omit [Fintype I] in
@[simp] theorem insertBit_self (j : I) (b : Bool) (x : {i : I // i ≠ j} → Bool) :
    insertBit j b x j = b := by simp [insertBit]

omit [Fintype I] in
@[simp] theorem insertBit_other (j : I) (b : Bool) (x : {i : I // i ≠ j} → Bool)
    (i : {i : I // i ≠ j}) : insertBit j b x i = x i := by
  simp [insertBit, i.property]

def pivotalEvent (f : (I → Bool) → Bool) (j : I)
    (x : {i : I // i ≠ j} → Bool) : Bool :=
  decide (f (insertBit j false x) = false ∧ f (insertBit j true x) = true)

def budget (f : (I → Bool) → Bool) : ℝ :=
  ∑ j, chainBudget (pivotalEvent f j)

end DirectedFeedback.Pivotal
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_Point
attribute [-instance] _root_.OAI.DirectedFeedback.StackDSL.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability

namespace DirectedFeedback.SourceProbability.FiniteDistribution
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]

theorem probability_exists_le_sum (μ : FiniteDistribution I) (p : J → I → Bool) :
    μ.probability (fun i => decide (∃ j, p j i = true)) ≤ ∑ j, μ.probability (p j) := by
  classical
  unfold probability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  by_cases h : ∃ j, p j i = true
  · obtain ⟨j, hj⟩ := h
    have he : ∃ j, p j i = true := ⟨j, hj⟩
    simp only [decide_eq_true_eq, he, ↓reduceIte]
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => if p j i then μ.weight i else 0)
      (fun j _ => by split_ifs <;> simp [μ.nonnegative]) (Finset.mem_univ j)
    simpa [hj] using hh
  · simp only [decide_eq_true_eq, h, ↓reduceIte]
    exact Finset.sum_nonneg (fun j _ => by split_ifs <;> simp [μ.nonnegative])

theorem probability_not (μ : FiniteDistribution I) (p : I → Bool) :
    μ.probability (fun i => !(p i)) = 1 - μ.probability p := by
  rw [← μ.normalized]
  unfold probability
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hp : p i <;> simp [hp]

end DirectedFeedback.SourceProbability.FiniteDistribution

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

def point (a : I) : FiniteDistribution I where
  weight x := if x = a then 1 else 0
  nonnegative x := by split_ifs <;> norm_num
  normalized := by simp

@[simp] theorem expectation_point (a : I) (f : I → ℝ) :
    (point a).expectation f = f a := by simp [expectation, point]

@[simp] theorem expectation_sub (μ : FiniteDistribution I) (f g : I → ℝ) :
    μ.expectation (fun x => f x - g x) = μ.expectation f - μ.expectation g := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem expectation_mul_right (μ : FiniteDistribution I) (f : I → ℝ) (c : ℝ) :
    μ.expectation (fun x => f x * c) = μ.expectation f * c := by
  simpa only [mul_comm] using expectation_mul_left μ c f

@[simp] theorem probability_eq_expect (μ : FiniteDistribution I) (p : I → Bool) :
    μ.probability p = μ.expectation (fun x => if p x then 1 else 0) := by
  simp [probability, expectation, mul_ite]

def sigma {F : I → Type*} [∀ i, Fintype (F i)] (μ : FiniteDistribution I)
    (ν : ∀ i, FiniteDistribution (F i)) : FiniteDistribution (Σ i, F i) where
  weight x := μ.weight x.1 * (ν x.1).weight x.2
  nonnegative x := mul_nonneg (μ.nonnegative _) ((ν _).nonnegative _)
  normalized := by
    rw [Fintype.sum_sigma]
    simp only [← Finset.mul_sum, (ν _).normalized, mul_one, μ.normalized]

theorem expectation_sigma {F : I → Type*} [∀ i, Fintype (F i)] (μ : FiniteDistribution I)
    (ν : ∀ i, FiniteDistribution (F i)) (f : (Σ i, F i) → ℝ) :
    (μ.sigma ν).expectation f = μ.expectation (fun i => (ν i).expectation (fun x => f ⟨i, x⟩)) := by
  simp only [expectation, sigma, Fintype.sum_sigma, Finset.mul_sum, mul_assoc]

end DirectedFeedback.SourceProbability.FiniteDistribution

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability FiniteDistribution
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}

def insertOrder (j : I) (r : Fin (n+1)) (e : {i : I // i ≠ j} ≃ Fin n) : I ≃ Fin (n+1) :=
  (Equiv.optionSubtypeNe j).symm |>.trans (Equiv.optionCongr e) |>.trans (finSuccEquiv' r).symm

omit [Fintype I] in
@[simp] theorem insertOrder_self (j : I) (r : Fin (n+1)) (e : {i : I // i ≠ j} ≃ Fin n) :
    insertOrder j r e j = r := by
  simp [insertOrder]

omit [Fintype I] in
@[simp] theorem insertOrder_other (j : I) (r : Fin (n+1)) (e : {i : I // i ≠ j} ≃ Fin n)
    (x : {i : I // i ≠ j}) : insertOrder j r e x = r.succAbove (e x) := by
  simp [insertOrder, Equiv.optionSubtypeNe_symm_of_ne x.property]

def deleteOrder (j : I) (e : I ≃ Fin (n+1)) : {i : I // i ≠ j} ≃ Fin n :=
  (e.subtypeEquiv (fun _ => not_congr e.injective.eq_iff.symm)).trans (finSuccAboveEquiv (e j)).symm

omit [Fintype I] [DecidableEq I] in
theorem deleteOrder_spec (j : I) (e : I ≃ Fin (n+1)) (x : {i : I // i ≠ j}) :
    (e j).succAbove (deleteOrder j e x) = e x := by
  have h := (finSuccAboveEquiv (e j)).apply_symm_apply
    (⟨e x, fun h => x.property (e.injective h)⟩ : {y : Fin (n+1) // y ≠ e j})
  exact congrArg Subtype.val h

omit [Fintype I] in
@[simp] theorem insert_delete_order (j : I) (e : I ≃ Fin (n+1)) :
    insertOrder j (e j) (deleteOrder j e) = e := by
  apply Equiv.ext
  intro x
  by_cases hx : x = j
  · subst x; simp
  · exact (insertOrder_other j (e j) (deleteOrder j e) ⟨x,hx⟩).trans (deleteOrder_spec j e ⟨x,hx⟩)

omit [Fintype I] in
@[simp] theorem delete_insert_order (j : I) (r : Fin (n+1)) (e : {i : I // i ≠ j} ≃ Fin n) :
    deleteOrder j (insertOrder j r e) = e := by
  apply Equiv.ext
  intro x
  have h := deleteOrder_spec j (insertOrder j r e) x
  simp only [insertOrder_self, insertOrder_other] at h
  exact Fin.succAbove_right_injective h

end DirectedFeedback.Pivotal

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability FiniteDistribution
variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Ω]

abbrev LabelOrder (I : Type*) [Fintype I] [DecidableEq I] :=
  Σ j : I, I ≃ Fin (Fintype.card {i : I // i ≠ j}+1)

instance labelOrderNonempty (j : I) : Nonempty (I ≃ Fin (Fintype.card {i : I // i ≠ j}+1)) :=
  ⟨insertOrder j 0 (Fintype.equivFin _)⟩

def labelOrderLaw : FiniteDistribution (LabelOrder I) :=
  (uniform I).sigma (fun _ => uniform _)

end DirectedFeedback.Pivotal

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {I : Type*} [Fintype I]

def takePrefix {t T : ℕ} (h : t ≤ T) (a : Fin T → I) : Fin t → I :=
  fun i => a ⟨i.val, lt_of_lt_of_le i.isLt h⟩

omit [Fintype I] in
@[simp] theorem takePrefix_self {t : ℕ} (a : Fin t → I) : takePrefix le_rfl a = a := rfl

end DirectedFeedback.SourceProbability.FiniteDistribution

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.PrefixExperiment
open DirectedFeedback.SourceProbability FiniteDistribution
variable {U I P Ω : Type*} [Fintype U] [Fintype I] [Nonempty I] [Fintype P] [Fintype Ω]

abbrev Atom (U I P : Type*) := U × (Σ _ : I, P)

def atomLaw (μ : FiniteDistribution U) (ν : I → FiniteDistribution P) :
    FiniteDistribution (Atom U I P) := μ.product ((uniform I).sigma ν)

theorem fresh_index_expectation (μ : FiniteDistribution U) (ν : I → FiniteDistribution P)
    (i : I) (f : U → P → ℝ) :
    (atomLaw μ ν).expectation (fun a => if a.2.1 = i then f a.1 a.2.2 else 0) =
      (1 / Fintype.card I) * μ.expectation (fun u => (ν i).expectation (f u)) := by
  rw [atomLaw, expectation_product]
  simp_rw [expectation_sigma, expectation_uniform]
  have hh (u : U) : (∑ j : I, (ν j).expectation (fun p => if j = i then f u p else 0)) =
      (ν i).expectation (f u) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  simp_rw [hh]
  rw [← expectation_mul_left]
  apply congrArg (expectation μ)
  funext u
  ring

def commonLaw (μΩ : FiniteDistribution Ω) (μ : FiniteDistribution U)
    (ν : I → FiniteDistribution P) (T : ℕ) [NeZero T] :
    FiniteDistribution (Ω × (Σ t : Fin T, Fin t.val → Atom U I P)) :=
  μΩ.product ((uniform (Fin T)).sigma (fun t => (atomLaw μ ν).iid t.val))

end DirectedFeedback.PrefixExperiment

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Coupling
open DirectedFeedback.SourceProbability FiniteDistribution
open Pivotal
variable {X Y : Type*} [Fintype X] [Fintype Y]

abbrev Block := (Bool × Bool) × Bool

def blockWeight (p : ℝ) : Block → ℝ
  | ((false, false), false) => 1 - 2*p
  | ((false, false), true) => p^2
  | ((false, true), true) => p*(1-p)
  | ((true, false), true) => p*(1-p)
  | ((true, true), true) => p^2
  | _ => 0

def block (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2) : FiniteDistribution Block where
  weight := blockWeight p
  nonnegative z := by
    rcases z with ⟨⟨a,b⟩,c⟩
    have h1 : 0 ≤ 1-p := by linarith
    cases a <;> cases b <;> cases c <;> simp [blockWeight] <;> nlinarith [mul_nonneg hp0 h1]
  normalized := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, blockWeight]
    ring

theorem block_inclusion (p : ℝ) (z : Block) (hz : blockWeight p z ≠ 0) :
    z.1.1 = true ∨ z.1.2 = true → z.2 = true := by
  rcases z with ⟨⟨a,b⟩,c⟩
  cases a <;> cases b <;> cases c <;> simp_all [blockWeight]

def flatten (e : X ≃ Y × Bool) : (Y → Bool × Bool) ≃ (X → Bool) where
  toFun z x := if (e x).2 then (z (e x).1).2 else (z (e x).1).1
  invFun a y := (a (e.symm (y,false)), a (e.symm (y,true)))
  left_inv z := by ext y <;> simp
  right_inv a := by
    ext x
    generalize hx : e x = z
    rcases z with ⟨y,b⟩
    have hh : e.symm (y,b) = x := by rw [← hx]; simp
    dsimp only
    rw [hx]
    cases b <;> simpa using congrArg a hh

def bigBits (e : X ≃ Y × Bool) (z : Y → Block) : X → Bool :=
  flatten e (fun y => (z y).1)

def smallBits (z : Y → Block) : Y → Bool := fun y => (z y).2

def law (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2) : FiniteDistribution (Y → Block) :=
  table (fun _ => block p hp0 hp)

end DirectedFeedback.Coupling

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Games
open DirectedFeedback.SourceProbability
open FiniteDistribution
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

structure Game (U V E X Y : Type) [Fintype E] where
  edgeLaw : FiniteDistribution E
  left : E → U
  right : E → V
  project : E → X → Y

def Game.score (G : Game U V E X Y) (lu : U → X) (lv : V → Y) : ℝ :=
  G.edgeLaw.probability (fun e => decide (G.project e (lu (G.left e)) = lv (G.right e)))

end DirectedFeedback.Games
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_Bias
attribute [-instance] _root_.OAI.DirectedFeedback.StackDSL.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]

def bias (i : Fin M) : ℝ := (2:ℝ)⁻¹ ^ (i.val+2)

omit [NeZero M] in
theorem bias_pos (i : Fin M) : 0 < bias i := by unfold bias; positivity

omit [NeZero M] in
theorem bias_le_quarter (i : Fin M) : bias i ≤ 1/4 := by
  unfold bias
  rw [pow_add]
  have h : (2:ℝ)⁻¹ ^ i.val ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  norm_num at *
  linarith

def subsetLaw (i : Fin M) : FiniteDistribution (X → Bool) :=
  Pivotal.law (bias i) (bias_pos i).le (by linarith [bias_le_quarter i])

abbrev Slot (U X : Type) (M : ℕ) := Atom U (Fin M) (X → Bool)
abbrev PrefixData (U X : Type) (M t : ℕ) := Fin t → Slot U X M

def sets {t : ℕ} (a : PrefixData U X M t) (j : ℕ) : Set X :=
  if h : j < t then {x | (a ⟨j,h⟩).2.2 x = true} else ∅

def cell {t : ℕ} (a : PrefixData U X M t) : (Fin t → X) → Fin (cellCount t) :=
  prefixCell t (sets a)

def vertices {t : ℕ} (a : PrefixData U X M t) : Fin t → U := fun j => (a j).1

abbrev Emb (L N : ℕ) := {ψ : Fin L → Fin N // StrictMono ψ}
def maxCells (X : Type) [Fintype X] (T : ℕ) := cellCount T * Fintype.card X
def rankLength (X : Type) [Fintype X] (T : ℕ) := 10 * maxCells X T + 30

abbrev Common (U X : Type) [Fintype X] (M T N : ℕ) :=
  Emb (rankLength X T) N × (Σ t : Fin T, PrefixData U X M t.val)
abbrev Full (U X : Type) [Fintype X] (M T N : ℕ) :=
  Emb (rankLength X T) N × PrefixData U X M T
abbrev Big (U X : Type) [Fintype X] (M T N : ℕ) :=
  Common U X M T N × (U × Pivotal.LabelOrder X)
abbrev Small (U V X Y : Type) [Fintype X] [Fintype Y] (M T N : ℕ) :=
  Common U X M T N × (V × Pivotal.LabelOrder Y)
abbrev Compare (U E X Y : Type) [Fintype X] (M T N : ℕ) :=
  Σ d : Common U X M T N, E × (Σ _ : Fin M, Fin (cellCount d.2.1.val) × (Y → Coupling.Block))

abbrev Wild (U V X Y : Type) [Fintype X] [Fintype Y]
    (M T N : ℕ) := Full U X M T N ⊕ (Big U X M T N ⊕ Small U V X Y M T N)

def bigMarginal (G : Game U V E X Y) := G.edgeLaw.pushforward G.left
def smallMarginal (G : Game U V E X Y) := G.edgeLaw.pushforward G.right

def common (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N)) :
    FiniteDistribution (Common U X M T N) := commonLaw ψLaw (bigMarginal G) subsetLaw T

def fullLaw (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N)) :
    FiniteDistribution (Full U X M T N) := ψLaw.product ((atomLaw (bigMarginal G) subsetLaw).iid T)

def bigLaw (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N)) :
    FiniteDistribution (Big U X M T N) := (common G ψLaw).product
      ((bigMarginal G).product Pivotal.labelOrderLaw)

def smallLaw (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N)) :
    FiniteDistribution (Small U V X Y M T N) := (common G ψLaw).product
      ((smallMarginal G).product Pivotal.labelOrderLaw)

instance cellCountNeZero (t : ℕ) : NeZero (cellCount t) :=
  ⟨by rw [cellCount_eq]; positivity⟩

def comparisonLaw (G : Game U V E X Y)
    (ψLaw : FiniteDistribution (Emb (rankLength X T) N)) :
    FiniteDistribution (Compare U E X Y M T N) :=
  (common G ψLaw).sigma (fun d => G.edgeLaw.product ((uniform (Fin M)).sigma (fun i =>
    (uniform (Fin (cellCount d.2.1.val))).product
      (Coupling.law (bias i) (bias_pos i).le (by linarith [bias_le_quarter i])))))

theorem cellCount_mono {s t : ℕ} (h : s ≤ t) : cellCount s ≤ cellCount t := by
  simp only [cellCount_eq]
  exact Nat.pow_le_pow_right (by decide) h

omit [NeZero T] in
theorem full_cells_bound : cellCount T ≤ maxCells X T := by
  have h : 1 ≤ Fintype.card X := Fintype.card_pos
  simpa [maxCells] using Nat.mul_le_mul_left (cellCount T) h

omit [Nonempty X] [NeZero T] in
theorem ordered_cells_bound {I : Type} [Fintype I] [DecidableEq I]
    (hI : Fintype.card I ≤ Fintype.card X) (t : Fin T) (o : Pivotal.LabelOrder I) :
    cellCount t.val * (Fintype.card {i : I // i ≠ o.1} + 1) ≤ maxCells X T := by
  have he : Fintype.card I = Fintype.card {i : I // i ≠ o.1} + 1 := by
    simpa using Fintype.card_congr o.2
  rw [← he]
  exact Nat.mul_le_mul (cellCount_mono (Nat.le_of_lt t.isLt)) hI

def level (ψ : Emb (rankLength X T) N) {k : ℕ} (hk : k ≤ maxCells X T) (j : Fin k) : Fin N :=
  ψ.val ⟨10*j.val+19, by have := j.isLt; unfold rankLength; omega⟩

def fullCount (a : PrefixData U X M T) (i : Fin M) (x : Fin T → X) : ℕ :=
  (Finset.univ.filter (fun j => (a j).2.1 = i ∧ (a j).2.2 (x j) = true)).card

def fullStars (a : PrefixData U X M T) : Set (Fin T → X) :=
  {x | ∃ i : Fin M, (fullCount a i x : ℝ) < bias i * T / (2*M)}

def fullWildcard (d : Full U X M T N) :
    TestGraph.Wildcard (U := U) (V := V) (X := X) (Y := Y) (T := T) (N := N) where
  tuple := .inl ⟨⟨T, by omega⟩, vertices d.2⟩
  cells := cellCount T
  cell := cell d.2
  stars := fullStars d.2
  level := level d.1 full_cells_bound

def bigWildcard (d : Big U X M T N) :
    TestGraph.Wildcard (U := U) (V := V) (X := X) (Y := Y) (T := T) (N := N) where
  tuple := .inl ⟨⟨d.1.2.1.val+1, by have := d.1.2.1.isLt; omega⟩,
    Fin.snoc (vertices d.1.2.2) d.2.1⟩
  cells := cellCount d.1.2.1.val * (Fintype.card {x : X // x ≠ d.2.2.1}+1)
  cell := fun a => orderedCell (cell d.1.2.2) d.2.2.2 (splitLast d.1.2.1.val a)
  stars := {a | a (Fin.last d.1.2.1.val) = d.2.2.1}
  level := level d.1.1 (ordered_cells_bound le_rfl d.1.2.1 d.2.2)

def smallWildcard (hYX : Fintype.card Y ≤ Fintype.card X) (d : Small U V X Y M T N) :
    TestGraph.Wildcard (U := U) (V := V) (X := X) (Y := Y) (T := T) (N := N) where
  tuple := .inr ⟨d.1.2.1, vertices d.1.2.2, d.2.1⟩
  cells := cellCount d.1.2.1.val * (Fintype.card {y : Y // y ≠ d.2.2.1}+1)
  cell := orderedCell (cell d.1.2.2) d.2.2.2
  stars := {a | a.2 = d.2.2.1}
  level := level d.1.1 (ordered_cells_bound hYX d.1.2.1 d.2.2)

def wildcard (hYX : Fintype.card Y ≤ Fintype.card X) : Wild U V X Y M T N →
    TestGraph.Wildcard (U := U) (V := V) (X := X) (Y := Y) (T := T) (N := N)
  | .inl d => fullWildcard d
  | .inr (.inl d) => bigWildcard d
  | .inr (.inr d) => smallWildcard hYX d

def comparison (G : Game U V E X Y) (fiber : E → X ≃ Y × Bool)
    (d : Compare U E X Y M T N) :
    TestGraph.Comparison (U := U) (V := V) (X := X) (Y := Y) (T := T) (N := N) :=
  let t := d.1.2.1
  let a := d.1.2.2
  let e := d.2.1
  let r := d.2.2.2.1
  let z := d.2.2.2.2
  { source := twoLevel d.1.1.val (.inr ⟨t, vertices a, G.right e⟩)
      (conditionedSet (cell a) r {y | Coupling.smallBits z y = true})
      ⟨1, by unfold rankLength; omega⟩ ⟨16, by unfold rankLength; omega⟩
    target := twoLevel d.1.1.val
      (.inl ⟨⟨t.val+1, by have := t.isLt; omega⟩, Fin.snoc (vertices a) (G.left e)⟩)
      (splitLast t.val ⁻¹' conditionedSet (cell a) r {x | Coupling.bigBits (fiber e) z x = true})
      ⟨2, by unfold rankLength; omega⟩ ⟨17, by unfold rankLength; omega⟩ }

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {Ω : Type*} [Fintype Ω]

abbrev Support (μ : FiniteDistribution Ω) := {x : Ω // 0 < μ.weight x}

theorem sum_support (μ : FiniteDistribution Ω) (f : Ω → ℝ) :
    (∑ x : μ.Support, μ.weight x.val * f x.val) = ∑ x, μ.weight x * f x := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun x => 0 < μ.weight x)) (by simp) (fun x => μ.weight x * f x)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : 0 < μ.weight x
  · simp [h]
  · have hz : μ.weight x = 0 := le_antisymm (not_lt.mp h) (μ.nonnegative x)
    simp [hz]

def supported (μ : FiniteDistribution Ω) : FiniteDistribution μ.Support where
  weight x := μ.weight x.val
  nonnegative x := μ.nonnegative x.val
  normalized := by simpa using sum_support μ (fun _ => 1) |>.trans (by simpa using μ.normalized)

@[simp] theorem expectation_supported (μ : FiniteDistribution Ω) (f : Ω → ℝ) :
    μ.supported.expectation (fun x => f x.val) = μ.expectation f := sum_support μ f

@[simp] theorem probability_supported (μ : FiniteDistribution Ω) (f : Ω → Bool) :
    μ.supported.probability (fun x => f x.val) = μ.probability f := by
  simp only [probability_eq_expect]
  exact expectation_supported μ (fun x => if f x then 1 else 0)

def extend (μ : FiniteDistribution Ω) (f : μ.Support → Bool) (x : Ω) : Bool :=
  if h : 0 < μ.weight x then f ⟨x,h⟩ else false

@[simp] theorem extend_at_support (μ : FiniteDistribution Ω) (f : μ.Support → Bool)
    (x : μ.Support) : μ.extend f x.val = f x := by simp [extend,x.property]

theorem probability_extend (μ : FiniteDistribution Ω) (f : μ.Support → Bool) :
    μ.probability (μ.extend f) = μ.supported.probability f := by
  rw [← probability_supported]
  simp only [extend_at_support]

end DirectedFeedback.SourceProbability.FiniteDistribution

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]
omit [NeZero M] [NeZero T] in
instance rankFintype : Fintype (Rank U V X Y T N) := Fintype.ofFinite _

variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))

abbrev WildSupport := (fullLaw (M := M) G ψLaw).Support ⊕
  ((bigLaw (M := M) G ψLaw).Support ⊕ (smallLaw (M := M) G ψLaw).Support)
abbrev ComparisonSupport := (comparisonLaw (M := M) G ψLaw).Support
abbrev OutputVertex := TestGraph.Vertex U V X Y
  (WildSupport (M := M) G ψLaw) (ComparisonSupport (M := M) G ψLaw) T N

def forgetWild : WildSupport (M := M) G ψLaw → Wild U V X Y M T N
  | .inl d => .inl d.val
  | .inr (.inl d) => .inr (.inl d.val)
  | .inr (.inr d) => .inr (.inr d.val)

def wildSupport (hYX : Fintype.card Y ≤ Fintype.card X) (w : WildSupport (M := M) G ψLaw) :=
  wildcard hYX (forgetWild G ψLaw w)

def compSupport (fiber : E → X ≃ Y × Bool) (c : ComparisonSupport (M := M) G ψLaw) :=
  comparison G fiber c.val

def vertexCost (D H K : ℝ) : OutputVertex (M := M) G ψLaw → ℝ
  | .inl _ => D+1
  | .inr (.inl (.inl d)) => H * (fullLaw G ψLaw).weight d.val
  | .inr (.inl (.inr (.inl d))) => Fintype.card X * (bigLaw G ψLaw).weight d.val
  | .inr (.inl (.inr (.inr d))) => Fintype.card Y * (smallLaw G ψLaw).weight d.val
  | .inr (.inr d) => K * (comparisonLaw G ψLaw).weight d.val

instance fullSupportFintype : Fintype ((fullLaw (M := M) G ψLaw).Support) := inferInstance
instance bigSupportFintype : Fintype ((bigLaw (M := M) G ψLaw).Support) := inferInstance
instance smallSupportFintype : Fintype ((smallLaw (M := M) G ψLaw).Support) := inferInstance
instance comparisonSupportFintype : Fintype ((comparisonLaw (M := M) G ψLaw).Support) := inferInstance

instance outputFintype : Fintype (OutputVertex (M := M) G ψLaw) := by
  unfold OutputVertex TestGraph.Vertex WildSupport ComparisonSupport
  infer_instance

def totalDeletionCost (D H K : ℝ) (deleted : OutputVertex (M := M) G ψLaw → Bool) : ℝ :=
  ∑ v, if deleted v then vertexCost G ψLaw D H K v else 0

def fullDeleted (deleted : OutputVertex (M := M) G ψLaw → Bool) : Full U X M T N → Bool :=
  (fullLaw G ψLaw).extend (fun d => deleted (.inr (.inl (.inl d))))
def bigDeleted (deleted : OutputVertex (M := M) G ψLaw → Bool) : Big U X M T N → Bool :=
  (bigLaw G ψLaw).extend (fun d => deleted (.inr (.inl (.inr (.inl d)))))
def smallDeleted (deleted : OutputVertex (M := M) G ψLaw → Bool) : Small U V X Y M T N → Bool :=
  (smallLaw G ψLaw).extend (fun d => deleted (.inr (.inl (.inr (.inr d)))))
def comparisonDeleted (deleted : OutputVertex (M := M) G ψLaw → Bool) : Compare U E X Y M T N → Bool :=
  (comparisonLaw G ψLaw).extend (fun d => deleted (.inr (.inr d)))

theorem deletionCost_decomposition (D H K : ℝ) (deleted : OutputVertex (M := M) G ψLaw → Bool) :
    totalDeletionCost G ψLaw D H K deleted =
      (∑ r : Rank U V X Y T N, if deleted (.inl r) then D+1 else 0) +
      (H * (fullLaw G ψLaw).probability (fullDeleted G ψLaw deleted) +
      (Fintype.card X * (bigLaw G ψLaw).probability (bigDeleted G ψLaw deleted) +
       Fintype.card Y * (smallLaw G ψLaw).probability (smallDeleted G ψLaw deleted))) +
      K * (comparisonLaw G ψLaw).probability (comparisonDeleted G ψLaw deleted) := by
  unfold totalDeletionCost
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  change _ = _ + (H * (fullLaw G ψLaw).probability ((fullLaw G ψLaw).extend _) +
    ((Fintype.card X : ℝ) * (bigLaw G ψLaw).probability ((bigLaw G ψLaw).extend _) +
    (Fintype.card Y : ℝ) * (smallLaw G ψLaw).probability ((smallLaw G ψLaw).extend _))) +
    K * (comparisonLaw G ψLaw).probability ((comparisonLaw G ψLaw).extend _)
  rw [probability_extend, probability_extend, probability_extend, probability_extend]
  simp only [probability, vertexCost, supported, Finset.mul_sum, mul_ite, mul_zero]
  ring

end DirectedFeedback.Construction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_FailureEvent
attribute [-instance] _root_.OAI.DirectedFeedback.StackDSL.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
namespace DirectedFeedback.JuntaSupport

open scoped BigOperators
open Finset

abbrev Cube (I : Type*) := I → Bool

def bitSign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem bitSign_sq (b : Bool) : bitSign b ^ 2 = 1 := by
  cases b <;> norm_num [bitSign]

def walsh {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) : ℝ :=
  ∏ i, bitSign (s i && x i)

@[simp] theorem walsh_sq {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) :
    walsh s x ^ 2 = 1 := by
  simp [walsh, ← Finset.prod_pow]

end DirectedFeedback.JuntaSupport

namespace DFVSMaxCut.Analytic
open Finset DirectedFeedback.JuntaSupport
def degree {I : Type*} [Fintype I] (s : Cube I) : ℕ :=
  (Finset.univ.filter fun i => s i = true).card
end DFVSMaxCut.Analytic

namespace DFVSMaxCut.BooleanFourthMoment
open scoped BigOperators
open Finset DirectedFeedback.JuntaSupport

noncomputable def polynomial {I : Type*} [Fintype I] [DecidableEq I]
    (c : Cube I → ℝ) (x : Cube I) : ℝ := ∑ s, c s * walsh s x

noncomputable def energy {I : Type*} [Fintype I] [DecidableEq I]
    (c : Cube I → ℝ) : ℝ :=
  ∑ s, (∏ i, if s i then (3 : ℝ) else 1) * c s ^ 2

noncomputable def discreteDiff {I : Type*} [Fintype I] [DecidableEq I]
    (f : Cube I → ℝ) (i : I) (x : Cube I) : ℝ := (f x - f (Function.update x i (!x i))) / 2

end DFVSMaxCut.BooleanFourthMoment

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_RoundBoolean
attribute [-instance] _root_.OAI.DirectedFeedback.StackDSL.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability FiniteDistribution

def DyadicJuntaBound (M : ℕ) (B γ : ℝ) (Jmax : ℕ) : Prop :=
  ∀ k : Fin (M+2), ∀ (I : Type) [Fintype I] [DecidableEq I] (f : (I → Bool) → Bool),
    Monotone f → budget f ≤ B →
    ∃ J : Finset I, J.card ≤ Jmax ∧ ∃ g : (I → Bool) → Bool,
      (∀ x y, (∀ i ∈ J, x i = y i) → g x = g y) ∧
      (law ((2:ℝ)⁻¹^k.val) (by positivity)
        (pow_le_one₀ (by norm_num) (by norm_num))).probability
          (fun x => decide (f x ≠ g x)) ≤ γ

end DirectedFeedback.Pivotal

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_PrefixBit
attribute [-instance] _root_.OAI.DirectedFeedback.StackDSL.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators
namespace DirectedFeedback.Ranks

abbrev Triple (n : ℕ) := {s : Finset (Fin n) // s.card = 3}
abbrev Increasing (L N : ℕ) := {f : Fin L → Fin N // StrictMono f}

end DirectedFeedback.Ranks
open scoped Classical
namespace DirectedFeedback.Ranks
open DirectedFeedback.SourceProbability
open DirectedFeedback.SourceProbability.FiniteDistribution

def Spreads {L N : ℕ} (μ : FiniteDistribution (Increasing L N)) (η : ℝ) : Prop :=
  ∀ I I' : Triple L, ∀ A : Finset (Finset (Fin N)),
    |μ.probability (fun ψ => decide (I.val.image ψ.val ∈ A)) -
      μ.probability (fun ψ => decide (I'.val.image ψ.val ∈ A))| ≤ η

end DirectedFeedback.Ranks

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_LastBias
attribute [-instance] _root_.OAI.DirectedFeedback.StackDSL.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open PrefixExperiment Pivotal Games
variable {M : ℕ} [NeZero M]

def lastBias (M : ℕ) : ℝ := (2:ℝ)⁻¹^(M+1)

omit [NeZero M] in
theorem lastBias_le (i : Fin M) : lastBias M ≤ bias i := by
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  have := i.isLt
  omega

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {I : Type*} [Fintype I]

theorem expectation_iid_prod (μ : FiniteDistribution I) (T : ℕ) (f : I → ℝ) :
    (μ.iid T).expectation (fun a => ∏ t, f (a t)) = (μ.expectation f)^T := by
  simp only [expectation, iid]
  simpa only [Finset.prod_mul_distrib] using
    (Fintype.sum_pow (fun i => μ.weight i * f i) T).symm

theorem probability_sublevel_exp (μ : FiniteDistribution I) (count : I → ℝ) (b : ℝ) :
    μ.probability (fun a => decide (count a < b)) ≤
      Real.exp b * μ.expectation (fun a => Real.exp (-count a)) := by
  rw [probability_eq_expect, ← expectation_mul_left]
  apply expectation_mono
  intro a
  by_cases ha : count a < b
  · simp only [ha, decide_true, ↓reduceIte]
    rw [← Real.exp_add]
    exact Real.one_le_exp_iff.mpr (by linarith)
  · simp only [ha, decide_false, Bool.false_eq_true, ↓reduceIte]
    positivity

end DirectedFeedback.SourceProbability.FiniteDistribution

namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability FiniteDistribution

def countTrue {T : ℕ} (a : Fin T → Bool) : ℝ := ∑ t, bitValue (a t)

theorem exp_neg_count {T : ℕ} (a : Fin T → Bool) :
    Real.exp (-countTrue a) = ∏ t, Real.exp (-bitValue (a t)) := by
  simp only [countTrue, ← Finset.sum_neg_distrib, Real.exp_sum]

theorem expMoment_count (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (T : ℕ) :
    ((coin a ha0 ha1).iid T).expectation (fun x => Real.exp (-countTrue x)) =
      (1-a+a*Real.exp (-1))^T := by
  simp_rw [exp_neg_count]
  rw [expectation_iid_prod (coin a ha0 ha1) T (fun b => Real.exp (-bitValue b))]
  congr 1
  simp [expectation, coin, bitValue]
  ring

theorem expMoment_count_le (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (T : ℕ) :
    ((coin a ha0 ha1).iid T).expectation (fun x => Real.exp (-countTrue x)) ≤
      Real.exp (-(a*T)*(1-Real.exp (-1))) := by
  rw [expMoment_count]
  have hbase : 0 ≤ 1-a+a*Real.exp (-1) := by positivity
  have hbound : 1-a+a*Real.exp (-1) ≤ Real.exp (a*(Real.exp (-1)-1)) := by
    nlinarith [Real.add_one_le_exp (a*(Real.exp (-1)-1))]
  have hp := pow_le_pow_left₀ hbase hbound T
  calc
    _ ≤ (Real.exp (a*(Real.exp (-1)-1)))^T := hp
    _ = Real.exp (-(a*T)*(1-Real.exp (-1))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

theorem exp_neg_one_le : Real.exp (-1) ≤ (3:ℝ)/8 := by
  have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 1 by norm_num) 4
  norm_num [Finset.sum_range_succ] at h
  rw [Real.exp_neg]
  rw [inv_eq_one_div]
  exact (div_le_iff₀ (Real.exp_pos 1)).mpr (by linarith)

theorem bernoulli_lower_tail (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (T : ℕ) :
    ((coin a ha0 ha1).iid T).probability (fun x => decide (countTrue x < (a*T)/2)) ≤
      Real.exp (-(a*T)/8) := by
  calc
    _ ≤ Real.exp ((a*T)/2) *
        ((coin a ha0 ha1).iid T).expectation (fun x => Real.exp (-countTrue x)) :=
      probability_sublevel_exp _ _ _
    _ ≤ Real.exp ((a*T)/2) * Real.exp (-(a*T)*(1-Real.exp (-1))) :=
      mul_le_mul_of_nonneg_left (expMoment_count_le a ha0 ha1 T) (Real.exp_nonneg _)
    _ ≤ Real.exp (-(a*T)/8) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hμ : 0 ≤ a*T := mul_nonneg ha0 (Nat.cast_nonneg _)
      nlinarith [mul_le_mul_of_nonneg_left exp_neg_one_le hμ]

end DirectedFeedback.Pivotal

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {Ω : Type*} [Fintype Ω]

theorem pushforward_bool (μ : FiniteDistribution Ω) (event : Ω → Bool) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (he : μ.probability event = p) :
    μ.pushforward event = DirectedFeedback.Pivotal.coin p hp0 hp1 := by
  apply eq_of_weight_eq
  intro b
  have ht : (μ.pushforward event).weight true = p := by
    calc
      _ = μ.probability event := by
        unfold pushforward probability
        apply Finset.sum_congr rfl
        intro x _
        cases event x <;> simp
      _ = p := he
  have hn := (μ.pushforward event).normalized
  simp only [Fintype.sum_bool] at hn
  cases b
  · change (μ.pushforward event).weight false = 1-p
    linarith
  · exact ht

end DirectedFeedback.SourceProbability.FiniteDistribution

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Coupling
open DirectedFeedback.SourceProbability FiniteDistribution
variable {X Y : Type} [Fintype X] [Fintype Y]

omit [Fintype X] in
theorem support_inclusion (e : X ≃ Y × Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (z : Y → Block) (hz : (law p hp0 hp).weight z ≠ 0) (x : X) :
    bigBits e z x = true → smallBits z (e x).1 = true := by
  have hprod : (∏ y, blockWeight p (z y)) ≠ 0 := hz
  have hblock : blockWeight p (z (e x).1) ≠ 0 := by
    exact (Finset.prod_ne_zero_iff.mp hprod) _ (Finset.mem_univ _)
  intro hx
  apply block_inclusion p _ hblock
  change (if (e x).2 = true then (z (e x).1).1.2 else (z (e x).1).1.1) = true at hx
  split at hx
  · exact Or.inr hx
  · exact Or.inl hx

end DirectedFeedback.Coupling

namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]
variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (fiber : E → X ≃ Y × Bool) (hproject : ∀ e x, (fiber e x).1 = G.project e x)

omit [Fintype V] [Nonempty X] [Nonempty Y] in
theorem comparison_support_coupling (d : ComparisonSupport (M := M) G ψLaw) :
    (Coupling.law (Y := Y) (bias d.val.2.2.1) (bias_pos _).le
      (by linarith [bias_le_quarter d.val.2.2.1])).weight d.val.2.2.2.2 ≠ 0 := by
  intro hz
  have he : (comparisonLaw G ψLaw).weight d.val = 0 := by
    simp only [comparisonLaw, sigma, product, hz, mul_zero]
  linarith [d.property]

include hproject in
omit [Fintype V] [Nonempty X] [Nonempty Y] in

theorem comparison_label_increases (ellU : U → X) (ellV : V → Y)
    (d : ComparisonSupport (M := M) G ψLaw)
    (hsat : G.project d.val.2.1 (ellU (G.left d.val.2.1)) = ellV (G.right d.val.2.1)) :
    eval ellU ellV (comparison G fiber d.val).source <
      eval ellU ellV (comparison G fiber d.val).target := by
  let pref : Fin d.val.1.2.1.val → X := fun j => ellU (vertices d.val.1.2.2 j)
  let xu := ellU (G.left d.val.2.1)
  let yv := ellV (G.right d.val.2.1)
  have himp : Coupling.bigBits (fiber d.val.2.1) d.val.2.2.2.2 xu = true →
      Coupling.smallBits d.val.2.2.2.2 yv = true := by
    have he : (fiber d.val.2.1 xu).1 = yv := (hproject _ _).trans hsat
    rw [← he]
    exact Coupling.support_inclusion _ _ _ _ _ (comparison_support_coupling G ψLaw d) _
  have hlabels : labels ellU ellV
      (.inl ⟨⟨d.val.1.2.1.val+1, by exact Nat.succ_lt_succ d.val.1.2.1.isLt⟩,
        Fin.snoc (vertices d.val.1.2.2) (G.left d.val.2.1)⟩) = Fin.snoc pref xu := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [labels, pref, xu]
    · simp [labels, pref, xu]
  simp only [comparison, twoLevel, eval_vertex, hlabels, Set.mem_preimage, splitLast,
    Equiv.coe_fn_mk, Fin.init_snoc, Fin.snoc_last]
  change (if (pref,yv) ∈ conditionedSet (cell d.val.1.2.2) d.val.2.2.2.1
      {y | Coupling.smallBits d.val.2.2.2.2 y = true} then d.val.1.1.val ⟨1,_⟩ else d.val.1.1.val ⟨16,_⟩) <
    (if (pref,xu) ∈ conditionedSet (cell d.val.1.2.2) d.val.2.2.2.1
      {x | Coupling.bigBits (fiber d.val.2.1) d.val.2.2.2.2 x = true} then d.val.1.1.val ⟨2,_⟩ else d.val.1.1.val ⟨17,_⟩)
  by_cases hbefore : (cell d.val.1.2.2 pref).val < d.val.2.2.2.1.val
  · simp only [conditionedSet, Set.mem_ofPred_eq, hbefore, true_or, ↓reduceIte]
    apply d.val.1.1.property; change (1 : ℕ) < 2; omega
  · by_cases heq : cell d.val.1.2.2 pref = d.val.2.2.2.1
    · simp only [conditionedSet, Set.mem_ofPred_eq, heq, lt_self_iff_false, false_or, true_and]
      by_cases hu : Coupling.bigBits (fiber d.val.2.1) d.val.2.2.2.2 xu = true
      · simp only [hu, himp hu, ↓reduceIte]
        apply d.val.1.1.property; change (1 : ℕ) < 2; omega
      · simp only [hu]
        split
        · apply d.val.1.1.property; change (1 : ℕ) < 17; omega
        · apply d.val.1.1.property; change (16 : ℕ) < 17; omega
    · simp only [conditionedSet, Set.mem_ofPred_eq, hbefore, false_or, heq, false_and, ↓reduceIte]
      apply d.val.1.1.property; change (16 : ℕ) < 17; omega

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open PrefixExperiment Pivotal Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]

omit [NeZero M] [Nonempty X] in
theorem subset_eval_probability (i : Fin M) (x : X) :
    (subsetLaw i).probability (fun b => b x) = bias i := by
  rw [probability_eq_expect]
  unfold subsetLaw Pivotal.law
  rw [expectation_table_eval (fun _ : X => coin (bias i) (bias_pos i).le
    (by linarith [bias_le_quarter i])) x (fun b : Bool => if b then 1 else 0)]
  simp [expectation, coin]

omit [Fintype V] [Fintype Y] [Nonempty X] [Nonempty Y] in

theorem slot_label_probability (G : Game U V E X Y) (ell : U → X) (i : Fin M) :
    (atomLaw (bigMarginal G) subsetLaw).probability
      (fun a => decide (a.2.1 = i) && a.2.2 (ell a.1)) = bias i / M := by
  rw [probability_eq_expect]
  have hind (a : Slot U X M) :
      (if decide (a.2.1 = i) && a.2.2 (ell a.1) then (1:ℝ) else 0) =
      if a.2.1 = i then (if a.2.2 (ell a.1) then 1 else 0) else 0 := by
    by_cases hi : a.2.1 = i <;> cases a.2.2 (ell a.1) <;> simp [hi]
  simp_rw [hind]
  have he := fresh_index_expectation (bigMarginal G) subsetLaw i
    (fun u b => if b (ell u) then 1 else 0)
  calc
    _ = (1 / (Fintype.card (Fin M) : ℝ)) * (bigMarginal G).expectation
        (fun u => (subsetLaw i).expectation (fun b => if b (ell u) then 1 else 0)) := by
      convert he using 1
      all_goals try with_reducible_and_instances rfl
      apply expectation_congr
      intro a
      by_cases hi : a.2.1 = i <;> simp [hi]
    _ = bias i / M := by
      simp_rw [← probability_eq_expect, subset_eval_probability, expectation_const]
      simp [div_eq_mul_inv, mul_comm]

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability FiniteDistribution
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

theorem labelOrder_label_probability (x : I) :
    labelOrderLaw.probability (fun o : LabelOrder I => decide (x = o.1)) =
      1 / Fintype.card I := by
  rw [probability_eq_expect, labelOrderLaw, expectation_sigma]
  simp only [expectation_const, decide_eq_true_eq]
  rw [expectation_uniform]
  simp

end DirectedFeedback.Pivotal

namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games Pivotal
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]
variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)
variable (ellU : U → X) (ellV : V → Y)

def labelDeleted : OutputVertex (M := M) G ψLaw → Bool :=
  fun v => decide (TestGraph.LabelDeleted (wildSupport G ψLaw hYX)
    (compSupport G ψLaw fiber) ellU ellV v)

theorem big_label_cost :
    Fintype.card X * (bigLaw (M := M) G ψLaw).probability
      (bigDeleted G ψLaw (labelDeleted (M := M) G ψLaw hYX fiber ellU ellV)) = 1 := by
  rw [bigDeleted, probability_extend]
  have he : (bigLaw (M := M) G ψLaw).supported.probability (fun d =>
      labelDeleted (M := M) G ψLaw hYX fiber ellU ellV (.inr (.inl (.inr (.inl d))))) =
      (bigLaw (M := M) G ψLaw).probability (fun d => decide (ellU d.2.1 = d.2.2.1)) := by
    convert probability_supported (bigLaw (M := M) G ψLaw)
      (fun d => decide (ellU d.2.1 = d.2.2.1)) using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg (fun f => (bigLaw (M := M) G ψLaw).supported.probability f)
    funext d
    apply Bool.eq_iff_iff.mpr
    simp only [labelDeleted, decide_eq_true_eq]
    change (ellU (Fin.snoc (α := fun _ => U) (vertices d.val.1.2.2) d.val.2.1
      (Fin.last d.val.1.2.1.val)) = d.val.2.2.1) ↔ _
    simp only [Fin.snoc_last]
  rw [he, bigLaw, probability_eq_expect]
  simp only [expectation_product]
  simp_rw [← probability_eq_expect, labelOrder_label_probability, expectation_const]
  have hc : (Fintype.card X:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem small_label_cost :
    Fintype.card Y * (smallLaw (M := M) G ψLaw).probability
      (smallDeleted G ψLaw (labelDeleted (M := M) G ψLaw hYX fiber ellU ellV)) = 1 := by
  rw [smallDeleted, probability_extend]
  have he : (smallLaw (M := M) G ψLaw).supported.probability (fun d =>
      labelDeleted (M := M) G ψLaw hYX fiber ellU ellV (.inr (.inl (.inr (.inr d))))) =
      (smallLaw (M := M) G ψLaw).probability (fun d => decide (ellV d.2.1 = d.2.2.1)) := by
    exact probability_supported (smallLaw (M := M) G ψLaw)
      (fun d => decide (ellV d.2.1 = d.2.2.1))
  rw [he, smallLaw, probability_eq_expect]
  simp only [expectation_product]
  simp_rw [← probability_eq_expect, labelOrder_label_probability, expectation_const]
  have hc : (Fintype.card Y:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

include fiber in
theorem comparison_label_cost (hproject : ∀ e x, (fiber e x).1 = G.project e x) :
    (comparisonLaw (M := M) G ψLaw).probability
      (comparisonDeleted G ψLaw (labelDeleted (M := M) G ψLaw hYX fiber ellU ellV)) ≤
      1-G.score ellU ellV := by
  rw [comparisonDeleted, probability_extend]
  have hm := probability_mono (μ := (comparisonLaw (M := M) G ψLaw).supported)
    (event := fun d => labelDeleted (M := M) G ψLaw hYX fiber ellU ellV (.inr (.inr d)))
    (event' := fun d => decide (G.project d.val.2.1 (ellU (G.left d.val.2.1)) ≠ ellV (G.right d.val.2.1))) (by
      intro d hd
      apply decide_eq_true
      intro hs
      have hi := comparison_label_increases G ψLaw fiber hproject ellU ellV d hs
      have hd' : TestGraph.LabelDeleted (wildSupport G ψLaw hYX)
        (compSupport G ψLaw fiber) ellU ellV (.inr (.inr d)) := of_decide_eq_true hd
      exact not_le.mpr hi hd')
  apply hm.trans_eq
  have he := probability_supported (comparisonLaw (M := M) G ψLaw)
    (fun d => decide (G.project d.2.1 (ellU (G.left d.2.1)) ≠ ellV (G.right d.2.1)))
  rw [he, comparisonLaw, probability_eq_expect, expectation_sigma]
  trans (common (M := M) G ψLaw).expectation (fun _ =>
    G.edgeLaw.probability (fun e => decide (G.project e (ellU (G.left e)) ≠ ellV (G.right e))))
  · apply expectation_congr
    intro d
    rw [expectation_product, probability_eq_expect]
    apply expectation_congr
    intro e
    exact expectation_const ((uniform (Fin M)).sigma (fun i =>
      (uniform (Fin (cellCount d.2.1.val))).product
        (Coupling.law (Y := Y) (bias i) (bias_pos i).le (by linarith [bias_le_quarter i]))))
      (if decide (G.project e (ellU (G.left e)) ≠ ellV (G.right e)) then 1 else 0)
  rw [expectation_const]
  have hh := probability_not G.edgeLaw
    (fun e => decide (G.project e (ellU (G.left e)) = ellV (G.right e)))
  simpa only [decide_not, Game.score] using hh

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open Pivotal

structure Parameters (D : ℕ) where
  M : ℕ
  T : ℕ
  K : ℕ
  J : ℕ
  M_eq : M = 128*(D+1)
  T_pos : 0 < T
  K_pos : 0 < K
  J_pos : 1 ≤ J
  theta : ℚ
  theta_pos : 0 < theta
  theta_half : (theta : ℝ) < 1/2
  fullChernoff : (8*((D:ℝ)+1)) * (M * Real.exp (-(lastBias M*T/(8*M)))) ≤ 1
  comparison : (M:ℝ)*2^T*D/K ≤ lastBias M/1000
  junta : DyadicJuntaBound M (((D:ℝ)+1)/(lastBias M/1000)) (lastBias M/1000) J
  Ktheta : (K:ℝ)*theta ≤ 1
  Jtheta : (theta:ℝ)*(J:ℝ)^2 ≤ lastBias M/1000

namespace Parameters
variable {D : ℕ} (P : Parameters D)

instance instNeZeroNatM : NeZero P.M := ⟨by rw [P.M_eq]; omega⟩
instance instNeZeroNatT : NeZero P.T := ⟨ne_of_gt P.T_pos⟩

end Parameters
end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games Pivotal Ranks

structure RankParameters {D : ℕ} (P : Parameters D) (X : Type) [Fintype X] where
  N : ℕ
  law : FiniteDistribution (Emb (rankLength X P.T) N)
  eta : ℝ
  rho : ℝ
  eta_pos : 0 < eta
  rho_nonneg : 0 ≤ rho
  rho_small : rho ≤ lastBias P.M/1000
  rho_alphabet : Fintype.card X * rho ≤ 1
  accuracy : 3*eta*(rankLength X P.T : ℝ)^3*2^((Fintype.card X)^P.T) ≤ rho
  spreads : Spreads law eta
  rational : ∀ ψ, ∃ q : ℚ, law.weight ψ = q

end DirectedFeedback.Construction
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_OutputDef
attribute [-instance] _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
namespace DirectedFeedback.BoundedExpr

def OutDef {r : Nat} (f : List Bool → (Fin r → Nat) → List Bool) : Prop :=
  ∃ e : Output r, ∀ x a, e.eval x a=f x a

namespace OutDef
variable {r : Nat} {f g : List Bool → (Fin r → Nat) → List Bool}

theorem congr (hf : OutDef f) (h : ∀ x a, f x a=g x a) : OutDef g := by
  obtain ⟨e,he⟩ := hf
  exact ⟨e,fun x a => (he x a).trans (h x a)⟩

theorem nil : OutDef (fun (_ : List Bool) (_ : Fin r → Nat) => []) := ⟨.nil,fun _ _ => rfl⟩
theorem bit (b : Bool) : OutDef (fun (_ : List Bool) (_ : Fin r → Nat) => [b]) := ⟨.bit b,fun _ _ => rfl⟩
theorem nat {f : List Bool → (Fin r → Nat) → Nat} (hf : Def f) :
    OutDef (fun x a => (List.replicate (f x a) true ++ [false])) := by
  obtain ⟨e,he⟩ := hf
  exact ⟨.nat e,by intro x a; simp only [Output.eval,he]⟩

theorem append (hf : OutDef f) (hg : OutDef g) : OutDef (fun x a => f x a++g x a) := by
  obtain ⟨e,he⟩ := hf; obtain ⟨d,hd⟩ := hg
  exact ⟨.append e d,by intro x a; simp only [Output.eval,he,hd]⟩

theorem loop {b : List Bool → (Fin r → Nat) → Nat}
    {e : List Bool → (Fin (r+1) → Nat) → List Bool} (hb : Def b) (he : OutDef e) :
    OutDef (fun x a => (List.range (b x a)).flatMap (fun i => e x (Fin.cons i a))) := by
  obtain ⟨b,hb⟩ := hb; obtain ⟨e,he⟩ := he
  exact ⟨.loop b e,by intro x a; simp only [Output.eval,hb,he]⟩

theorem when {p : List Bool → (Fin r → Nat) → Prop} (hp : PDef p) (hf : OutDef f) :
    OutDef (fun x a => if p x a then f x a else []) := by
  obtain ⟨t,ht⟩ := hp; obtain ⟨e,he⟩ := hf
  refine ⟨.when t e,?_⟩
  intro x a
  simp only [Output.eval,ht,he]
  by_cases h : p x a <;> simp [h]

theorem ite {p : List Bool → (Fin r → Nat) → Prop} (hp : PDef p) (hf : OutDef f) (hg : OutDef g) :
    OutDef (fun x a => if p x a then f x a else g x a) := by
  apply ((hf.when hp).append (hg.when hp.not)).congr
  intro x a
  by_cases h : p x a <;> simp [h]

theorem flatMap {I : Type} (l : List I) (f : I → List Bool → (Fin r → Nat) → List Bool)
    (hf : ∀ i ∈ l, OutDef (f i)) : OutDef (fun x a => l.flatMap (fun i => f i x a)) := by
  induction l with
  | nil => exact nil
  | cons i l ih =>
    exact (hf i (by simp)).append (ih (fun j hj => hf j (by simp [hj])))

end OutDef
end DirectedFeedback.BoundedExpr

end

noncomputable section
open scoped Classical
namespace DirectedFeedback.BoundedExpr.CNFPrinter

theorem map_finRange_val (n : Nat) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem range_flatMap {I : Type} {n : Nat} (f : Nat → List I) (g : Fin n → List I)
    (hg : ∀ i, f i.val=g i) : (List.range n).flatMap f=(List.finRange n).flatMap g := by
  rw [← map_finRange_val,List.flatMap_map]
  have he : (fun i : Fin n => f i.val)=g := funext hg
  rw [he]

end DirectedFeedback.BoundedExpr.CNFPrinter

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_AllGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open SourceProbability FiniteDistribution Games RankGraph
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : Nat} [NeZero M] [NeZero T]

abbrev AllVertex (U V E X Y : Type) [Fintype X] [Fintype Y] (M T N : Nat) := TestGraph.Vertex U V X Y (Wild U V X Y M T N) (Compare U E X Y M T N) T N
instance rawFullFintype : Fintype (Full U X M T N) := inferInstance
instance rawSmallFintype : Fintype (Small U V X Y M T N) := inferInstance
instance rawCompareFintype : Fintype (Compare U E X Y M T N) := inferInstance
instance allVertexFintype : Fintype (AllVertex U V E X Y M T N) := by
  unfold AllVertex TestGraph.Vertex Wild
  infer_instance

variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))

def supportEmbed : OutputVertex (M:=M) G ψLaw → AllVertex U V E X Y M T N
  | .inl r => .inl r
  | .inr (.inl w) => .inr (.inl (forgetWild G ψLaw w))
  | .inr (.inr c) => .inr (.inr c.val)

def allCost (D H K : ℝ) : AllVertex U V E X Y M T N → ℝ
  | .inl _ => D+1
  | .inr (.inl (.inl d)) => H*(fullLaw G ψLaw).weight d
  | .inr (.inl (.inr (.inl d))) => Fintype.card X*(bigLaw G ψLaw).weight d
  | .inr (.inl (.inr (.inr d))) => Fintype.card Y*(smallLaw G ψLaw).weight d
  | .inr (.inr d) => K*(comparisonLaw G ψLaw).weight d

def AllArc (hYX : Fintype.card Y≤Fintype.card X) (fiber : E → X ≃ Y × Bool) :=
  TestGraph.Arc (wildcard (M:=M) (T:=T) (N:=N) (U:=U) (V:=V) hYX) (comparison (M:=M) G fiber)

theorem allCost_sum (D H K : ℝ) (f : AllVertex U V E X Y M T N → Bool) :
    (∑ v, if f v then allCost G ψLaw D H K v else 0) =
      totalDeletionCost G ψLaw D H K (fun v => f (supportEmbed G ψLaw v)) := by
  simp only [totalDeletionCost,Fintype.sum_sum_type,allCost,vertexCost,supportEmbed,forgetWild]
  have hs {A : Type} [Fintype A] (μ : FiniteDistribution A) (c : ℝ) (g : A → Bool) :
      (∑ a, if g a then c*μ.weight a else 0) =
      ∑ a : μ.Support, if g a.val then c*μ.weight a.val else 0 := by
    simpa only [Finset.mul_sum,mul_ite,mul_one,mul_zero,mul_assoc] using
      congrArg (fun z => c*z) (μ.sum_support (fun a => if g a then 1 else 0)).symm
  rw [hs (fullLaw G ψLaw),hs (bigLaw G ψLaw),hs (smallLaw G ψLaw),hs (comparisonLaw G ψLaw)]
  congr 3

end DirectedFeedback.Construction

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.LocalPrinter
open BoundedExpr

def Ordered {H : Nat} : Option (Fin H) → Option (Fin H) → Prop
  | some a,some b => a < b
  | _,_ => True

end DirectedFeedback.LocalPrinter

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.AllLabels
open Construction SourceProbability FiniteDistribution Games RankGraph
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : Nat} [NeZero M] [NeZero T]
variable (G : Game U V E X Y) (hYX : Fintype.card Y≤Fintype.card X) (fiber : E → X ≃ Y × Bool)

abbrev deleted (a : U → X) (b : V → Y) : AllVertex U V E X Y M T N → Prop :=
  TestGraph.LabelDeleted (wildcard (M:=M) (T:=T) (N:=N) hYX) (comparison G fiber) a b
abbrev pot (a : U → X) (b : V → Y) : AllVertex U V E X Y M T N → ℚ :=
  TestGraph.labelPotential (wildcard (M:=M) (T:=T) (N:=N) hYX) (comparison G fiber) a b

def height (a : U → X) (b : V → Y) : AllVertex U V E X Y M T N → Nat
  | .inl r => 2*(eval a b r).val
  | .inr (.inl w) => 2*((wildcard hYX w).level ((wildcard hYX w).cell (labels a b (wildcard hYX w).tuple))).val
  | .inr (.inr c) => (eval a b (comparison G fiber c).source).val+(eval a b (comparison G fiber c).target).val

omit [Fintype U] [Fintype V] [Nonempty Y] [NeZero M] [NeZero T] in
theorem height_bound (a : U → X) (b : V → Y) (v : AllVertex U V E X Y M T N) :
    height G hYX fiber a b v<2*N+1 := by
  rcases v with r | (w | c)
  · have := (eval a b r).isLt
    dsimp [height]
    omega
  · have := ((wildcard hYX w).level ((wildcard hYX w).cell (labels a b (wildcard hYX w).tuple))).isLt
    dsimp [height]
    omega
  · have := (eval a b (comparison G fiber c).source).isLt
    have := (eval a b (comparison G fiber c).target).isLt
    dsimp [height]
    omega

def code (a : U → X) (b : V → Y) (v : AllVertex U V E X Y M T N) : Option (Fin (2*N+1)) :=
  if deleted G hYX fiber a b v then none else some ⟨height G hYX fiber a b v,height_bound G hYX fiber a b v⟩

omit [Fintype U] [Fintype V] [Nonempty Y] [NeZero M] [NeZero T] in
theorem code_none (a : U → X) (b : V → Y) (v : AllVertex U V E X Y M T N) :
    code G hYX fiber a b v=none ↔ deleted G hYX fiber a b v := by simp [code]

omit [Fintype U] [Fintype V] [Nonempty Y] [NeZero M] [NeZero T] in
theorem height_potential (a : U → X) (b : V → Y) (v : AllVertex U V E X Y M T N) :
    (height G hYX fiber a b v:ℚ)=2*pot G hYX fiber a b v := by
  rcases v with r | (w | c) <;> simp [height,pot,TestGraph.labelPotential]; ring

omit [Fintype U] [Fintype V] [Nonempty Y] [NeZero M] [NeZero T] in
theorem ordered_arc (a : U → X) (b : V → Y) {v w : AllVertex U V E X Y M T N}
    (h : AllArc G hYX fiber v w) : LocalPrinter.Ordered (code G hYX fiber a b v) (code G hYX fiber a b w) := by
  by_cases hv : deleted G hYX fiber a b v
  · simp [code,hv,LocalPrinter.Ordered]
  by_cases hw : deleted G hYX fiber a b w
  · simp [code,hw,LocalPrinter.Ordered]
  simp only [code,hv,hw,ite_false,LocalPrinter.Ordered]
  change height G hYX fiber a b v<height G hYX fiber a b w
  have hi := TestGraph.labelPotential_increases (wildcard hYX) (comparison G fiber) a b h hv hw
  have hi' : (height G hYX fiber a b v:ℚ)<height G hYX fiber a b w := by
    rw [height_potential,height_potential]
    exact mul_lt_mul_of_pos_left hi (by norm_num)
  exact_mod_cast hi'

theorem embed_deleted (ψLaw : FiniteDistribution (Emb (rankLength X T) N)) (a : U → X) (b : V → Y)
    (v : OutputVertex (M:=M) G ψLaw) :
    decide (deleted G hYX fiber a b (supportEmbed G ψLaw v))=labelDeleted G ψLaw hYX fiber a b v := by
  rcases v with r | (w | c)
  · rfl
  · rcases w with w | (w | w) <;> rfl
  · rfl

end DirectedFeedback.AllLabels

end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical
namespace DirectedFeedback.BinaryEmbed
open DFVSGames

def name : Nat → Nat
  | 0 => 0
  | n+1 => Nat.bit true (name n)

theorem name_bits (n : Nat) : (name n).bits=List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [name,Nat.bits_append_bit _ true (by simp),ih,List.replicate_succ]

theorem name_injective : Function.Injective name := by
  intro i j h
  have hh := congrArg (fun n => n.bits.length) h
  simpa only [name_bits,List.length_replicate] using hh

end DirectedFeedback.BinaryEmbed

end
end

section

noncomputable section
open scoped Classical
namespace DirectedFeedback.BoundedExpr
namespace BinaryCNFPrinter

abbrev Lit := Nat × Bool

def literalBits (l : Lit) : List Bool := l.2 :: (List.replicate (2*l.1) true ++ [false])
def clauseBits (a b c : Lit) : List Bool := true :: (literalBits a ++ literalBits b ++ literalBits c)

def rawSplit : List Lit → List Nat → List Bool
  | [a,b,c], [] => clauseBits a b c
  | a::b::rest, y::ys => clauseBits a b (y,true) ++ rawSplit ((y,false)::rest) ys
  | _, _ => []

theorem literalBits_def {r : Nat} {n : List Bool → (Fin r → Nat) → Nat} (hn : Def n) (b : Bool) :
    OutDef (fun x a => literalBits (n x a,b)) := by
  simpa only [literalBits,List.singleton_append] using
    (OutDef.bit b).append (OutDef.nat ((Def.lit 2).mul hn))

theorem clauseBits_def {r : Nat} {f g h : List Bool → (Fin r → Nat) → Nat}
    (hf : Def f) (hg : Def g) (hh : Def h) (a b c : Bool) :
    OutDef (fun x v => clauseBits (f x v,a) (g x v,b) (h x v,c)) :=
  by
    simpa only [clauseBits,List.singleton_append] using (OutDef.bit true).append
      (((literalBits_def hf a).append (literalBits_def hg b)).append (literalBits_def hh c))

theorem rawSplit_def {r : Nat}
    (ls : List ((List Bool → (Fin r → Nat) → Nat) × Bool))
    (ys : List (List Bool → (Fin r → Nat) → Nat))
    (hls : ∀ l ∈ ls, Def l.1) (hys : ∀ y ∈ ys, Def y) :
    OutDef (fun x a => rawSplit (ls.map (fun l => (l.1 x a,l.2))) (ys.map (fun y => y x a))) := by
  induction ys generalizing ls with
  | nil =>
    match ls with
    | [] => exact OutDef.nil
    | [_] => exact OutDef.nil
    | [_,_] => exact OutDef.nil
    | [a,b,c] => exact clauseBits_def (hls a (by simp)) (hls b (by simp)) (hls c (by simp)) a.2 b.2 c.2
    | _::_::_::_::_ => exact OutDef.nil
  | cons y ys ih =>
    match ls with
    | [] => exact OutDef.nil
    | [_] => exact OutDef.nil
    | a::b::rest =>
      have hy := hys y (by simp)
      have ht := ih ((y,false)::rest) (by
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hy
        · exact hls c (by simp [hc])) (fun z hz => hys z (by simp [hz]))
      simpa only [List.map_cons,rawSplit] using
        (clauseBits_def (hls a (by simp)) (hls b (by simp)) hy a.2 b.2 true).append ht

end BinaryCNFPrinter
end DirectedFeedback.BoundedExpr

end
end

end OAI
end


