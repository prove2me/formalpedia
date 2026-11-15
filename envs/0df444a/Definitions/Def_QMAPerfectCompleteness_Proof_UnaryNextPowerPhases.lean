-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerPhases
-- name    : QMAPerfectCompleteness_Proof_UnaryNextPowerPhases
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:58:28.864033+00:00
-- url     : https://prove2.me/theorems/480fa4c5-0e70-472f-866f-80e36498532b
-- title:
--   Timed doubling phases of the clock machine
-- statement:
--   Defines and analyzes the finite phases that double a unary power counter, restore comparison targets and emit the final exponent and power. These execution identities are the internal steps of the next-power-of-two computation.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/UnaryNextPowerPhases.lean, retained declaration span lines 10–166.

/- Generated from Solutions.UnaryNextPowerPhases by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion
namespace QMAPerfectCompleteness.Uniformity.UnaryNatArithmetic
end QMAPerfectCompleteness.Uniformity.UnaryNatArithmetic



/-! Exact timed doubling and output phases of the unary next-power machine. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Turing StateTransition
namespace QMAPerfectCompleteness.Uniformity.UnaryNextPowerTM
open QAlgorithms.Complexity (Str encNat)

lemma double_zero_step (v : Option Bool) (d : Data) :
    machine.step (cfg .double v {d with power := 0}) =
      some (cfg .restoreDouble none {d with power := 0}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]

lemma double_succ_step (v : Option Bool) (d : Data) (p : ℕ) :
    machine.step (cfg .double v {d with power := p+1}) =
      some (cfg .double (some true) {d with power := p,doubled := d.doubled+2}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,List.replicate_succ]
  congr 1; funext k; fin_cases k <;> rfl

lemma restoreDouble_zero_step (v : Option Bool) (d : Data) :
    machine.step (cfg .restoreDouble v {d with doubled := 0}) =
      some (cfg .compare none {d with doubled := 0}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]

lemma restoreDouble_succ_step (v : Option Bool) (d : Data) (p : ℕ) :
    machine.step (cfg .restoreDouble v {d with doubled := p+1}) =
      some (cfg .restoreDouble (some true) {d with power := d.power+1,doubled := p}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,List.replicate_succ]
  congr 1; funext k; fin_cases k <;> rfl

lemma double_run (v : Option Bool) (d : Data) (p : ℕ) :
    run (p+1) (some (cfg .double v {d with power := p})) =
      some (cfg .restoreDouble none {d with power := 0,doubled := d.doubled+2*p}) := by
  induction p generalizing v d with
  | zero => simpa [run] using double_zero_step v d
  | succ p ih =>
    rw [run_succ,double_succ_step]
    simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ih (some true) {d with doubled := d.doubled+2}

lemma restoreDouble_run (v : Option Bool) (d : Data) (p : ℕ) :
    run (p+1) (some (cfg .restoreDouble v {d with doubled := p})) =
      some (cfg .compare none {d with power := d.power+p,doubled := 0}) := by
  induction p generalizing v d with
  | zero => simpa [run] using restoreDouble_zero_step v d
  | succ p ih =>
    rw [run_succ,restoreDouble_succ_step]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ih (some true) {d with power := d.power+1}

lemma doubling_run (v : Option Bool) (d : Data) (p : ℕ) :
    run (3*p+2) (some (cfg .double v {d with power := p,doubled := 0})) =
      some (cfg .compare none {d with power := 2*p,doubled := 0}) := by
  have h1 := double_run v {d with doubled := 0} p
  have h2 := restoreDouble_run none {d with power := 0} (2*p)
  simp only [Nat.zero_add] at h1 h2
  have h := run_trans h1 h2
  have ht : (p+1)+(2*p+1)=3*p+2 := by omega
  rw [ht] at h
  simpa only [Nat.zero_add] using h

lemma reverseTail_zero_step (v : Option Bool) (d : Data) :
    machine.step (cfg .reverseTail v {d with input := []}) =
      some (cfg .outputTail none {d with input := []}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]

lemma reverseTail_cons_step (v : Option Bool) (d : Data) (b : Bool) (s : Str) :
    machine.step (cfg .reverseTail v {d with input := b::s}) =
      some (cfg .reverseTail (some b) {d with input := s,tail := b::d.tail}) := by
  cases b <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  all_goals congr 1; funext k; fin_cases k <;> rfl

lemma reverseTail_run (v : Option Bool) (d : Data) (s : Str) :
    run (s.length+1) (some (cfg .reverseTail v {d with input := s})) =
      some (cfg .outputTail none {d with input := [],tail := s.reverse++d.tail}) := by
  induction s generalizing v d with
  | nil => simpa [run] using reverseTail_zero_step v d
  | cons b s ih =>
    rw [List.length_cons,run_succ,reverseTail_cons_step]
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using
      ih (some b) {d with tail := b::d.tail}

lemma outputTail_zero_step (v : Option Bool) (d : Data) (p : ℕ) :
    machine.step (cfg .outputTail v {d with tail := [],power := p+1}) =
      some (cfg .outputPower none {d with tail := [],power := p,output := false::d.output}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,List.replicate_succ]
  congr 1; funext k; fin_cases k <;> rfl

lemma outputTail_cons_step (v : Option Bool) (d : Data) (b : Bool) (s : Str) :
    machine.step (cfg .outputTail v {d with tail := b::s}) =
      some (cfg .outputTail (some b) {d with tail := s,output := b::d.output}) := by
  cases b <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  all_goals congr 1; funext k; fin_cases k <;> rfl

lemma outputTail_run (v : Option Bool) (d : Data) (s : Str) (p : ℕ) :
    run (s.length+1) (some (cfg .outputTail v {d with tail := s,power := p+1})) =
      some (cfg .outputPower none {d with tail := [],power := p,output := false::(s.reverse++d.output)}) := by
  induction s generalizing v d with
  | nil => simpa [run] using outputTail_zero_step v d p
  | cons b s ih =>
    rw [List.length_cons,run_succ,outputTail_cons_step v {d with power := p+1} b s]
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using
      ih (some b) {d with output := b::d.output}

lemma outputPower_zero_step (v : Option Bool) (d : Data) :
    machine.step (cfg .outputPower v {d with power := 0}) =
      some (cfg .outputExponent none {d with power := 0,output := false::d.output}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  congr 1; funext k; fin_cases k <;> rfl

lemma outputPower_succ_step (v : Option Bool) (d : Data) (p : ℕ) :
    machine.step (cfg .outputPower v {d with power := p+1}) =
      some (cfg .outputPower (some true) {d with power := p,output := true::d.output}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,List.replicate_succ]
  congr 1; funext k; fin_cases k <;> rfl

lemma outputPower_run (v : Option Bool) (d : Data) (p : ℕ) :
    run (p+1) (some (cfg .outputPower v {d with power := p})) =
      some (cfg .outputExponent none {d with power := 0,output := false::(List.replicate p true++d.output)}) := by
  induction p generalizing v d with
  | zero => simpa [run] using outputPower_zero_step v d
  | succ p ih =>
    rw [run_succ,outputPower_succ_step]
    simpa only [List.replicate_add,List.replicate_one,List.append_assoc,List.singleton_append] using
      ih (some true) {d with output := true::d.output}

lemma outputExponent_zero_step (v : Option Bool) (d : Data) :
    machine.step (cfg .outputExponent v {d with exponent := 0}) =
      some (cfg .clearTarget none {d with exponent := 0}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]

lemma outputExponent_succ_step (v : Option Bool) (d : Data) (p : ℕ) :
    machine.step (cfg .outputExponent v {d with exponent := p+1}) =
      some (cfg .outputExponent (some true) {d with exponent := p,output := true::d.output}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,List.replicate_succ]
  congr 1; funext k; fin_cases k <;> rfl

lemma outputExponent_run (v : Option Bool) (d : Data) (p : ℕ) :
    run (p+1) (some (cfg .outputExponent v {d with exponent := p})) =
      some (cfg .clearTarget none {d with exponent := 0,output := List.replicate p true++d.output}) := by
  induction p generalizing v d with
  | zero => simpa [run] using outputExponent_zero_step v d
  | succ p ih =>
    rw [run_succ,outputExponent_succ_step]
    simpa only [List.replicate_add,List.replicate_one,List.append_assoc,List.singleton_append] using
      ih (some true) {d with output := true::d.output}

lemma clearTarget_zero_step (v : Option Bool) (out : Str) :
    machine.step (cfg .clearTarget v {output := out}) = some (haltList machine out) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,haltList]
  congr 1; funext k; fin_cases k <;> rfl

lemma clearTarget_succ_step (v : Option Bool) (d : Data) (t : ℕ) :
    machine.step (cfg .clearTarget v {d with target := t+1}) =
      some (cfg .clearTarget (some true) {d with target := t}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,List.replicate_succ]
  congr 1; funext k; fin_cases k <;> rfl

lemma clearTarget_run (v : Option Bool) (t : ℕ) (out : Str) :
    run (t+1) (some (cfg .clearTarget v {target := t,output := out})) = some (haltList machine out) := by
  induction t generalizing v with
  | zero => simpa [run] using clearTarget_zero_step v out
  | succ t ih =>
    rw [run_succ,clearTarget_succ_step v {output := out} t]
    exact ih (some true)

end QMAPerfectCompleteness.Uniformity.UnaryNextPowerTM


