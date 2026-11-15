-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_StructuredStackCode
-- name    : QMAPerfectCompleteness_Proof_StructuredStackCode
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:55:38.071196+00:00
-- url     : https://prove2.me/theorems/0903a877-4369-4d5c-9d50-98e085e4de4c
-- title:
--   Structured finite stack-machine programs
-- statement:
--   Defines finite program codes for atomic statements, sequencing, stack-guarded loops and conditional branches. A bounded execution relation and its composition lemmas connect these structured programs to concrete TM2 output computations.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/StructuredStackCode.lean, retained declaration span lines 9–257.

/- Generated from Solutions.StructuredStackCode by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Proof_BinaryComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ConcreteUniformity
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion



/-! Structured finite TM2 programs. Sequencing and stack-guarded loops preserve arbitrary
shared stack data; their execution proofs compose without repeated low-level label bookkeeping. -/
open Turing StateTransition
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Uniformity.StructuredStack

abbrev Data (K : Type) := Option Bool × (K → List Bool)

structure Code (K : Type) where
  Label : Type
  [labelFinite : Fintype Label]
  main : Label
  program : Label → TM2.Stmt (fun _ : K => Bool) Label (Option Bool)
attribute [instance] Code.labelFinite

namespace Code
variable {K : Type} [DecidableEq K]
abbrev Cfg (P : Code K) := TM2.Cfg (fun _ : K => Bool) P.Label (Option Bool)
def step (P : Code K) : P.Cfg → Option P.Cfg := TM2.step P.program

def start (P : Code K) (d : Data K) : P.Cfg := ⟨some P.main,d.1,d.2⟩
def halt (P : Code K) (d : Data K) : P.Cfg := ⟨none,d.1,d.2⟩
def Exec (P : Code K) (d e : Data K) (t : ℕ) : Prop :=
  Nonempty (EvalsToInTime P.step (P.start d) (some (P.halt e)) t)

def atomic (q : TM2.Stmt (fun _ : K => Bool) Unit (Option Bool)) : Code K where
  Label := Unit
  main := ()
  program _ := q

def effect (q : TM2.Stmt (fun _ : K => Bool) Unit (Option Bool)) (d : Data K) : Data K :=
  let c := TM2.stepAux q d.1 d.2
  (c.var,c.stk)

/-- An inline statement ending in halt executes in exactly one global TM2 step. -/
theorem atomic_exec (q : TM2.Stmt (fun _ : K => Bool) Unit (Option Bool)) (d : Data K)
    (hq : (TM2.stepAux q d.1 d.2).l=none) : (atomic q).Exec d (effect q d) 1 := by
  refine ⟨{steps := 1,steps_le_m := le_rfl,evals_in_steps := ?_}⟩
  change some (TM2.stepAux q d.1 d.2) = some ⟨none,(TM2.stepAux q d.1 d.2).var,(TM2.stepAux q d.1 d.2).stk⟩
  congr 1
  generalize hd : TM2.stepAux q d.1 d.2 = c at *
  rcases c with ⟨l,v,S⟩
  simp only at hq
  subst l
  rfl

def push (k : K) (b : Bool) : Code K := atomic (.push k (fun _=>b) .halt)
def pop (k : K) : Code K := atomic (.pop k (fun _ b=>b) .halt)
def load (v : Option Bool) : Code K := atomic (.load (fun _=>v) .halt)

theorem push_exec (k : K) (b : Bool) (d : Data K) :
    (push k b).Exec d (d.1,Function.update d.2 k (b::d.2 k)) 1 := atomic_exec _ _ rfl
theorem pop_exec (k : K) (d : Data K) :
    (pop k).Exec d ((d.2 k).head?,Function.update d.2 k (d.2 k).tail) 1 := atomic_exec _ _ rfl
theorem load_exec (v : Option Bool) (d : Data K) : (load v).Exec d (v,d.2) 1 := atomic_exec _ _ rfl

/-- Relabel a subroutine and redirect each return to a caller's continuation label. -/
def linkStmt {A B : Type} (f : A → B) (finish : B)
    (q : TM2.Stmt (fun _ : K => Bool) A (Option Bool)) :
    TM2.Stmt (fun _ : K => Bool) B (Option Bool) :=
  Statement.continueWith (.goto (fun _=>finish)) (Statement.mapLabels f q)

def linkCfg {A B : Type} (f : A → B) (finish : B)
    (c : TM2.Cfg (fun _ : K => Bool) A (Option Bool)) :
    TM2.Cfg (fun _ : K => Bool) B (Option Bool) :=
  ⟨some (c.l.elim finish f),c.var,c.stk⟩

lemma linkStmt_stepAux {A B : Type} (f : A → B) (finish : B)
    (q : TM2.Stmt (fun _ : K => Bool) A (Option Bool)) (d : Data K) :
    TM2.stepAux (linkStmt f finish q) d.1 d.2 = linkCfg f finish (TM2.stepAux q d.1 d.2) := by
  rw [linkStmt,Statement.stepAux_continueWith,Statement.stepAux_mapLabels]
  generalize hd : TM2.stepAux q d.1 d.2 = c
  rcases c with ⟨l,v,S⟩
  cases l <;> rfl

lemma link_step (P Q : Code K) (f : P.Label → Q.Label) (finish : Q.Label)
    (hm : ∀ l, Q.program (f l)=linkStmt f finish (P.program l))
    (c c' : P.Cfg) (h : P.step c=some c') :
    Q.step (linkCfg f finish c)=some (linkCfg f finish c') := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [step,TM2.step] at h
  | some l =>
    change some (TM2.stepAux (P.program l) v S)=some c' at h
    have hh := Option.some.inj h
    subst c'
    change some (TM2.stepAux (Q.program (f l)) v S)=_
    rw [hm]
    exact congrArg some (linkStmt_stepAux f finish (P.program l) (v,S))

lemma mapped_step (P Q : Code K) (f : P.Label → Q.Label)
    (hm : ∀ l, Q.program (f l)=Statement.mapLabels f (P.program l))
    (c c' : P.Cfg) (h : P.step c=some c') :
    Q.step (Statement.mapCfgLabels f c)=some (Statement.mapCfgLabels f c') := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [step,TM2.step] at h
  | some l =>
    change some (TM2.stepAux (P.program l) v S)=some c' at h
    have hh := Option.some.inj h
    subst c'
    change some (TM2.stepAux (Q.program (f l)) v S)=_
    rw [hm,Statement.stepAux_mapLabels]

abbrev seq (P Q : Code K) : Code K where
  Label := P.Label ⊕ Q.Label
  main := Sum.inl P.main
  program
    | .inl l => linkStmt Sum.inl (.inr Q.main) (P.program l)
    | .inr l => Statement.mapLabels Sum.inr (Q.program l)

/-- Sequential programs share their stacks; no intermediate encoding or copying is needed. -/
theorem seq_exec (P Q : Code K) {d e f : Data K} {m n : ℕ}
    (hp : P.Exec d e m) (hq : Q.Exec e f n) : (seq P Q).Exec d f (m+n) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hq⟩ := hq
  have hs := successful_iterate_simulation P.step (seq P Q).step
    (linkCfg Sum.inl (.inr Q.main)) (link_step P (seq P Q) Sum.inl (.inr Q.main) (fun _=>rfl))
    hp.steps (P.start d) (P.halt e) hp.evals_in_steps
  have ht := successful_iterate_simulation Q.step (seq P Q).step
    (Statement.mapCfgLabels Sum.inr) (mapped_step Q (seq P Q) Sum.inr (fun _=>rfl))
    hq.steps (Q.start e) (Q.halt f) hq.evals_in_steps
  refine ⟨{ steps := hp.steps+hq.steps, steps_le_m := ?_, evals_in_steps := ?_ }⟩
  · rw [show hp.steps+hq.steps=hq.steps+hp.steps by omega,Function.iterate_add_apply]
    change (fun o => o.bind (seq P Q).step)^[hq.steps]
      ((fun o => o.bind (seq P Q).step)^[hp.steps]
        (some (linkCfg Sum.inl (.inr Q.main) (P.start d)))) = _
    rw [hs]
    exact ht
  · have := hp.steps_le_m
    have := hq.steps_le_m
    omega

/-- A stack guard peeks once and runs a body as long as its finite predicate succeeds. -/
abbrev whilePeek (k : K) (p : Option Bool → Bool) (P : Code K) : Code K where
  Label := Option P.Label
  main := none
  program
    | none => .peek k (fun _ b=>b) (.branch p (.goto (fun _=>some P.main)) .halt)
    | some l => linkStmt some none (P.program l)

theorem while_false (k : K) (p : Option Bool → Bool) (P : Code K) (d : Data K)
    (hp : p (d.2 k).head?=false) :
    (whilePeek k p P).Exec d ((d.2 k).head?,d.2) 1 := by
  refine ⟨{steps := 1,steps_le_m := le_rfl,evals_in_steps := ?_}⟩
  change some (TM2.stepAux ((whilePeek k p P).program none) d.1 d.2)=_
  simp [whilePeek,TM2.stepAux,hp,start,halt]

theorem while_true (k : K) (p : Option Bool → Bool) (P : Code K) {d e f : Data K} {m n : ℕ}
    (hp : p (d.2 k).head?=true)
    (hbody : P.Exec ((d.2 k).head?,d.2) e m)
    (htail : (whilePeek k p P).Exec e f n) : (whilePeek k p P).Exec d f (1+m+n) := by
  obtain ⟨hb⟩ := hbody
  obtain ⟨ht⟩ := htail
  have hs := successful_iterate_simulation P.step (whilePeek k p P).step
    (linkCfg some none) (link_step P (whilePeek k p P) some none (fun _=>rfl))
    hb.steps (P.start ((d.2 k).head?,d.2)) (P.halt e) hb.evals_in_steps
  have hg : (whilePeek k p P).step ((whilePeek k p P).start d) =
      some (linkCfg some none (P.start ((d.2 k).head?,d.2))) := by
    simp [step,TM2.step,start,whilePeek,TM2.stepAux,hp,linkCfg]
  refine ⟨{ steps := 1+hb.steps+ht.steps, steps_le_m := ?_, evals_in_steps := ?_ }⟩
  · rw [show 1+hb.steps+ht.steps=ht.steps+(hb.steps+1) by omega,
      Function.iterate_add_apply,Function.iterate_add_apply,Function.iterate_one]
    change (fun o => o.bind (whilePeek k p P).step)^[ht.steps]
      ((fun o => o.bind (whilePeek k p P).step)^[hb.steps]
        ((whilePeek k p P).step ((whilePeek k p P).start d))) = _
    rw [hg,hs]
    exact ht.evals_in_steps
  · have := hb.steps_le_m
    have := ht.steps_le_m
    omega

/-- Increase a proved runtime bound without changing the machine. -/
theorem exec_mono (P : Code K) {d e : Data K} {m n : ℕ}
    (h : P.Exec d e m) (hm : m ≤ n) : P.Exec d e n := by
  obtain ⟨h⟩ := h
  exact ⟨{ steps := h.steps, evals_in_steps := h.evals_in_steps, steps_le_m := h.steps_le_m.trans hm }⟩

abbrev ifPeek (k : K) (p : Option Bool → Bool) (P Q : Code K) : Code K where
  Label := Option (P.Label ⊕ Q.Label)
  main := none
  program
    | none => .peek k (fun _ b=>b) (.branch p
        (.goto (fun _=>some (.inl P.main))) (.goto (fun _=>some (.inr Q.main))))
    | some (.inl l) => Statement.mapLabels (fun l=>some (.inl l)) (P.program l)
    | some (.inr l) => Statement.mapLabels (fun l=>some (.inr l)) (Q.program l)

theorem ifPeek_true (k : K) (p : Option Bool → Bool) (P Q : Code K)
    {d e : Data K} {m : ℕ} (hp : p (d.2 k).head?=true)
    (h : P.Exec ((d.2 k).head?,d.2) e m) : (ifPeek k p P Q).Exec d e (m+1) := by
  obtain ⟨h⟩ := h
  have hs := successful_iterate_simulation P.step (ifPeek k p P Q).step
    (Statement.mapCfgLabels (fun l=>some (.inl l)))
    (mapped_step P (ifPeek k p P Q) (fun l=>some (.inl l)) (fun _=>rfl))
    h.steps (P.start ((d.2 k).head?,d.2)) (P.halt e) h.evals_in_steps
  refine ⟨{ steps := h.steps+1, evals_in_steps := ?_, steps_le_m := by have := h.steps_le_m; omega }⟩
  rw [Function.iterate_succ_apply]
  change (fun o=>o.bind (ifPeek k p P Q).step)^[h.steps]
    ((ifPeek k p P Q).step ((ifPeek k p P Q).start d)) = _
  have hg : (ifPeek k p P Q).step ((ifPeek k p P Q).start d) =
      some (Statement.mapCfgLabels (fun l=>some (.inl l)) (P.start ((d.2 k).head?,d.2))) := by
    simp [step,TM2.step,ifPeek,TM2.stepAux,hp,start,Statement.mapCfgLabels]
  rw [hg]
  exact hs

theorem ifPeek_false (k : K) (p : Option Bool → Bool) (P Q : Code K)
    {d e : Data K} {m : ℕ} (hp : p (d.2 k).head?=false)
    (h : Q.Exec ((d.2 k).head?,d.2) e m) : (ifPeek k p P Q).Exec d e (m+1) := by
  obtain ⟨h⟩ := h
  have hs := successful_iterate_simulation Q.step (ifPeek k p P Q).step
    (Statement.mapCfgLabels (fun l=>some (.inr l)))
    (mapped_step Q (ifPeek k p P Q) (fun l=>some (.inr l)) (fun _=>rfl))
    h.steps (Q.start ((d.2 k).head?,d.2)) (Q.halt e) h.evals_in_steps
  refine ⟨{ steps := h.steps+1, evals_in_steps := ?_, steps_le_m := by have := h.steps_le_m; omega }⟩
  rw [Function.iterate_succ_apply]
  change (fun o=>o.bind (ifPeek k p P Q).step)^[h.steps]
    ((ifPeek k p P Q).step ((ifPeek k p P Q).start d)) = _
  have hg : (ifPeek k p P Q).step ((ifPeek k p P Q).start d) =
      some (Statement.mapCfgLabels (fun l=>some (.inr l)) (Q.start ((d.2 k).head?,d.2))) := by
    simp [step,TM2.step,ifPeek,TM2.stepAux,hp,start,Statement.mapCfgLabels]
  rw [hg]
  exact hs

abbrev toMachine [Fintype K] (P : Code K) (input output : K) : FinTM2 where
  K := K
  k₀ := input
  k₁ := output
  Γ _ := Bool
  Λ := P.Label
  main := P.main
  σ := Option Bool
  initialState := none
  m := P.program

/-- Turn a structured-program proof into the actual bundled machine required by the platform. -/
noncomputable def outputs [Fintype K] (P : Code K) (input output : K) (s t : List Bool) (m : ℕ)
    (h : P.Exec (none,Function.update (fun _=>[]) input s)
      (none,Function.update (fun _=>[]) output t) m) :
    TM2OutputsInTime (toMachine P input output) s (some t) m := by
  let hr := Classical.choice h
  have hi : initList (toMachine P input output) s =
      P.start (none,Function.update (fun _=>[]) input s) := by
    simp only [initList,start,toMachine]
    congr 1
    funext k
    by_cases hk : k=input <;> simp [initList,toMachine,start,hk]
  have ho : haltList (toMachine P input output) t =
      P.halt (none,Function.update (fun _=>[]) output t) := by
    simp only [haltList,halt,toMachine]
    congr 1
    funext k
    by_cases hk : k=output <;> simp [haltList,toMachine,halt,hk]
  unfold TM2OutputsInTime
  simp only [Option.map_some,hi,ho]
  exact hr

end Code
end QMAPerfectCompleteness.Uniformity.StructuredStack


