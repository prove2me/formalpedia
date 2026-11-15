-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerTM
-- name    : QMAPerfectCompleteness_Proof_UnaryNextPowerTM
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:57:10.707339+00:00
-- url     : https://prove2.me/theorems/91c48d04-caa6-4269-926d-884e79644be9
-- title:
--   The unary next-power-of-two machine
-- statement:
--   Defines the finite registers, labels and step functions for repeated comparison and doubling of a unary power counter. The retained parsing and restoration lemmas specify the comparison result while preserving the target needed by the next iteration.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/UnaryNextPowerTM.lean, retained declaration span lines 11–227.

/- Generated from Solutions.UnaryNextPowerTM by authoritative Stage-2 skeleton subtraction.
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
namespace QMAPerfectCompleteness.Uniformity.UnaryNatArithmetic
end QMAPerfectCompleteness.Uniformity.UnaryNatArithmetic



/-! A finite unary doubling machine computing ceiling-log2 and the next power of two. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Turing StateTransition
namespace QMAPerfectCompleteness.Uniformity.UnaryNextPowerTM
open QAlgorithms.Complexity (Str encNat)

inductive Label where
  | init | read | compare | restoreTarget : Bool → Label
  | restorePower : Bool → Label
  | double | restoreDouble | reverseTail | outputTail | outputPower | outputExponent | clearTarget
  deriving DecidableEq, Fintype

abbrev machine : FinTM2 where
  K := Fin 9
  k₀ := 0
  k₁ := 8
  Γ _ := Bool
  Λ := Label
  main := .init
  σ := Option Bool
  initialState := none
  m l := match l with
    | .init => .push 2 (fun _ => true) (.goto (fun _ => .read))
    | .read => .pop 0 (fun _ b => b) (.branch (fun v => v.getD false)
        (.push 1 (fun _ => true) (.goto (fun _ => .read))) (.goto (fun _ => .compare)))
    | .compare => .peek 2 (fun _ b => b) (.branch Option.isSome
        (.peek 1 (fun _ b => b) (.branch Option.isSome
          (.pop 2 (fun v _ => v) (.push 4 (fun _ => true)
            (.pop 1 (fun v _ => v) (.push 3 (fun _ => true) (.goto (fun _ => .compare))))))
          (.goto (fun _ => .restoreTarget false))))
        (.peek 1 (fun _ b => b) (.branch Option.isSome
          (.goto (fun _ => .restoreTarget true)) (.goto (fun _ => .restoreTarget false)))))
    | .restoreTarget b => .peek 3 (fun _ x => x) (.branch Option.isSome
        (.pop 3 (fun v _ => v) (.push 1 (fun _ => true) (.goto (fun _ => .restoreTarget b))))
        (.goto (fun _ => .restorePower b)))
    | .restorePower b => .peek 4 (fun _ x => x) (.branch Option.isSome
        (.pop 4 (fun v _ => v) (.push 2 (fun _ => true) (.goto (fun _ => .restorePower b))))
        (if b then .push 5 (fun _ => true) (.goto (fun _ => .double)) else .goto (fun _ => .reverseTail)))
    | .double => .peek 2 (fun _ b => b) (.branch Option.isSome
        (.pop 2 (fun v _ => v) (.push 6 (fun _ => true) (.push 6 (fun _ => true)
          (.goto (fun _ => .double))))) (.goto (fun _ => .restoreDouble)))
    | .restoreDouble => .peek 6 (fun _ b => b) (.branch Option.isSome
        (.pop 6 (fun v _ => v) (.push 2 (fun _ => true) (.goto (fun _ => .restoreDouble))))
        (.goto (fun _ => .compare)))
    | .reverseTail => .peek 0 (fun _ b => b) (.branch Option.isSome
        (.pop 0 (fun v _ => v) (.push 7 (fun v => v.getD false) (.goto (fun _ => .reverseTail))))
        (.goto (fun _ => .outputTail)))
    | .outputTail => .peek 7 (fun _ b => b) (.branch Option.isSome
        (.pop 7 (fun v _ => v) (.push 8 (fun v => v.getD false) (.goto (fun _ => .outputTail))))
        (.push 8 (fun _ => false) (.pop 2 (fun _ _ => none) (.goto (fun _ => .outputPower)))))
    | .outputPower => .peek 2 (fun _ b => b) (.branch Option.isSome
        (.pop 2 (fun v _ => v) (.push 8 (fun _ => true) (.goto (fun _ => .outputPower))))
        (.push 8 (fun _ => false) (.goto (fun _ => .outputExponent))))
    | .outputExponent => .peek 5 (fun _ b => b) (.branch Option.isSome
        (.pop 5 (fun v _ => v) (.push 8 (fun _ => true) (.goto (fun _ => .outputExponent))))
        (.goto (fun _ => .clearTarget)))
    | .clearTarget => .peek 1 (fun _ b => b) (.branch Option.isSome
        (.pop 1 (fun v _ => v) (.goto (fun _ => .clearTarget))) (.load (fun _ => none) .halt))

structure Data where
  input : Str := []
  target : ℕ := 0
  power : ℕ := 0
  savedTarget : ℕ := 0
  savedPower : ℕ := 0
  exponent : ℕ := 0
  doubled : ℕ := 0
  tail : Str := []
  output : Str := []

def Data.stacks (d : Data) : Fin 9 → Str :=
  ![d.input,List.replicate d.target true,List.replicate d.power true,
    List.replicate d.savedTarget true,List.replicate d.savedPower true,
    List.replicate d.exponent true,List.replicate d.doubled true,d.tail,d.output]

def cfg (l : Label) (v : Option Bool) (d : Data) : machine.Cfg := ⟨some l,v,d.stacks⟩
def run (t : ℕ) (c : Option machine.Cfg) : Option machine.Cfg :=
  (fun o => o.bind machine.step)^[t] c

lemma run_add (m n : ℕ) (c : Option machine.Cfg) : run (m+n) c = run n (run m c) := by
  simp only [run,Nat.add_comm m n,Function.iterate_add_apply]
lemma run_trans {m n : ℕ} {a b c : Option machine.Cfg}
    (h1 : run m a=b) (h2 : run n b=c) : run (m+n) a=c := by rw [run_add,h1,h2]

lemma read_zero_step (v : Option Bool) (d : Data) (s : Str) :
    machine.step (cfg .read v {d with input := false::s}) =
      some (cfg .compare (some false) {d with input := s}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  congr 1; funext k; fin_cases k <;> rfl

lemma read_true_step (v : Option Bool) (d : Data) (s : Str) :
    machine.step (cfg .read v {d with input := true::s}) =
      some (cfg .read (some true) {d with input := s,target := d.target+1}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,List.replicate_succ]
  congr 1; funext k; fin_cases k <;> rfl

lemma compare_both_step (v : Option Bool) (d : Data) (a b : ℕ) :
    machine.step (cfg .compare v {d with target := a+1,power := b+1}) =
      some (cfg .compare (some true)
        {d with target := a,power := b,savedTarget := d.savedTarget+1,savedPower := d.savedPower+1}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,List.replicate_succ]
  congr 1; funext k; fin_cases k <;> rfl

lemma compare_zero_zero (v : Option Bool) (d : Data) :
    machine.step (cfg .compare v {d with target := 0,power := 0}) =
      some (cfg (.restoreTarget false) none {d with target := 0,power := 0}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]

lemma compare_target_zero (v : Option Bool) (d : Data) (b : ℕ) :
    machine.step (cfg .compare v {d with target := 0,power := b+1}) =
      some (cfg (.restoreTarget false) none {d with target := 0,power := b+1}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,List.replicate_succ]

lemma compare_power_zero (v : Option Bool) (d : Data) (a : ℕ) :
    machine.step (cfg .compare v {d with target := a+1,power := 0}) =
      some (cfg (.restoreTarget true) (some true) {d with target := a+1,power := 0}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,List.replicate_succ]

lemma restoreTarget_zero (b : Bool) (v : Option Bool) (d : Data) :
    machine.step (cfg (.restoreTarget b) v {d with savedTarget := 0}) =
      some (cfg (.restorePower b) none {d with savedTarget := 0}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]

lemma restoreTarget_succ (b : Bool) (v : Option Bool) (d : Data) (t : ℕ) :
    machine.step (cfg (.restoreTarget b) v {d with savedTarget := t+1}) =
      some (cfg (.restoreTarget b) (some true) {d with target := d.target+1,savedTarget := t}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,List.replicate_succ]
  congr 1; funext k; fin_cases k <;> rfl

lemma restorePower_zero (b : Bool) (v : Option Bool) (d : Data) :
    machine.step (cfg (.restorePower b) v {d with savedPower := 0}) =
      some (if b then cfg .double none {d with savedPower := 0,exponent := d.exponent+1}
        else cfg .reverseTail none {d with savedPower := 0}) := by
  cases b <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,List.replicate_succ]
  congr 1; funext k; fin_cases k <;> rfl

lemma restorePower_succ (b : Bool) (v : Option Bool) (d : Data) (t : ℕ) :
    machine.step (cfg (.restorePower b) v {d with savedPower := t+1}) =
      some (cfg (.restorePower b) (some true) {d with power := d.power+1,savedPower := t}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,List.replicate_succ]
  congr 1; funext k; fin_cases k <;> rfl

lemma run_succ (t : ℕ) (c : machine.Cfg) : run (t+1) (some c) = run t (machine.step c) := by
  simp only [run,Function.iterate_succ_apply]
  rfl

lemma read_run (v : Option Bool) (d : Data) (t : ℕ) (tail : Str) :
    run (t+1) (some (cfg .read v {d with input := encNat t++tail})) =
      some (cfg .compare (some false) {d with input := tail,target := d.target+t}) := by
  induction t generalizing v d with
  | zero => simpa [encNat,run] using read_zero_step v d tail
  | succ t ih =>
    rw [run_succ]
    change run (t+1) (machine.step (cfg .read v {d with input := true::(encNat t++tail)})) = _
    rw [read_true_step]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ih (some true) {d with target := d.target+1}

lemma restoreTarget_run (b : Bool) (v : Option Bool) (d : Data) (t : ℕ) :
    run (t+1) (some (cfg (.restoreTarget b) v {d with savedTarget := t})) =
      some (cfg (.restorePower b) none {d with target := d.target+t,savedTarget := 0}) := by
  induction t generalizing v d with
  | zero => simpa [run] using restoreTarget_zero b v d
  | succ t ih =>
    rw [run_succ,restoreTarget_succ]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ih (some true) {d with target := d.target+1}

lemma restorePower_run (b : Bool) (v : Option Bool) (d : Data) (t : ℕ) :
    run (t+1) (some (cfg (.restorePower b) v {d with savedPower := t})) =
      some (if b then cfg .double none {d with power := d.power+t,savedPower := 0,exponent := d.exponent+1}
        else cfg .reverseTail none {d with power := d.power+t,savedPower := 0}) := by
  induction t generalizing v d with
  | zero => simpa [run] using restorePower_zero b v d
  | succ t ih =>
    rw [run_succ,restorePower_succ]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ih (some true) {d with power := d.power+1}

/-- The paired unary scan records the strict comparison and saves every consumed symbol. -/
lemma compare_run (v : Option Bool) (d : Data) (a b : ℕ) :
    run (min a b+1) (some (cfg .compare v {d with target := a,power := b})) =
      some (cfg (.restoreTarget (decide (b<a))) (if b<a then some true else none)
        {d with target := a-min a b,power := b-min a b,savedTarget := d.savedTarget+min a b,savedPower := d.savedPower+min a b}) := by
  induction a generalizing b v d with
  | zero =>
    cases b with
    | zero => simpa [run] using compare_zero_zero v d
    | succ b => simpa [run] using compare_target_zero v d b
  | succ a ih =>
    cases b with
    | zero => simpa [run] using compare_power_zero v d a
    | succ b =>
      have hm : min (a+1) (b+1)=min a b+1 := by omega
      have ha : (a+1)-(min a b+1)=a-min a b := by omega
      have hb : (b+1)-(min a b+1)=b-min a b := by omega
      rw [hm,run_succ,compare_both_step]
      simpa only [hm,ha,hb,Nat.add_lt_add_iff_right,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        ih (v := some true) (d := {d with savedTarget := d.savedTarget+1,savedPower := d.savedPower+1}) (b := b)

/-- Comparison restores both source counters completely before doubling or exiting. -/
lemma compare_restore_run (v : Option Bool) (d : Data) (a b : ℕ) :
    run (3*min a b+3) (some (cfg .compare v
      {d with target := a,power := b,savedTarget := 0,savedPower := 0})) =
      some (if b<a then cfg .double none
        {d with target := a,power := b,savedTarget := 0,savedPower := 0,exponent := d.exponent+1}
      else cfg .reverseTail none {d with target := a,power := b,savedTarget := 0,savedPower := 0}) := by
  let q := min a b
  let e : Data := {d with target := a-q,power := b-q,savedTarget := q,savedPower := q}
  let f : Data := {e with target := e.target+q,savedTarget := 0}
  have hc : run (q+1) (some (cfg .compare v
      {d with target := a,power := b,savedTarget := 0,savedPower := 0})) =
      some (cfg (.restoreTarget (decide (b<a))) (if b<a then some true else none) e) := by
    simpa only [q,e,Nat.zero_add] using compare_run v {d with savedTarget := 0,savedPower := 0} a b
  have ht : run (q+1) (some (cfg (.restoreTarget (decide (b<a))) (if b<a then some true else none) e)) =
      some (cfg (.restorePower (decide (b<a))) none f) :=
    restoreTarget_run _ _ e q
  have hp := restorePower_run (decide (b<a)) none f q
  have h := run_trans hc (run_trans ht hp)
  have hlen : (q+1)+((q+1)+(q+1))=3*min a b+3 := by dsimp only [q]; omega
  rw [hlen] at h
  by_cases hb : b<a <;>
    simpa [q,e,f,hb,Nat.sub_add_cancel (Nat.min_le_left a b),Nat.sub_add_cancel (Nat.min_le_right a b)] using h

end QMAPerfectCompleteness.Uniformity.UnaryNextPowerTM


