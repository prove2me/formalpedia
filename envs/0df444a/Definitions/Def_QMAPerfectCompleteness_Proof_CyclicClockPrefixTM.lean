-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CyclicClockPrefixTM
-- name    : QMAPerfectCompleteness_Proof_CyclicClockPrefixTM
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:01:22.503631+00:00
-- url     : https://prove2.me/theorems/3f2cf475-67fc-4df7-9757-de1a6cec1ae3
-- title:
--   Unary clock-prefix preparation machine
-- statement:
--   Defines a finite machine that reads the verifier headers, prepares an affine unary clock-size target and retains the original input stream. The retained execution and runtime lemmas support the subsequent next-power-of-two computation.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CyclicClockPrefixTM.lean, retained declaration span lines 10–179.

/- Generated from Solutions.CyclicClockPrefixTM by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerPhases
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion
namespace QMAPerfectCompleteness.Uniformity.UnaryNatArithmetic
end QMAPerfectCompleteness.Uniformity.UnaryNatArithmetic



/-! A finite unary affine-header stage retaining the complete original input stream. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Turing StateTransition
namespace QMAPerfectCompleteness.Uniformity.CyclicClockPrefixTM
open QAlgorithms.Complexity (Str encNat)

inductive Label where
  | read | reverse | copy | emit
  deriving DecidableEq, Fintype

abbrev machine : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 3
  Γ _ := Bool
  Λ := Label
  main := .read
  σ := Option Bool
  initialState := none
  m l := match l with
    | .read => .pop 0 (fun _ b => b) (.branch (fun v => v.getD false)
      (.push 1 (fun _ => true) (.push 2 (fun _ => true) (.goto (fun _ => .read))))
      (.push 2 (fun _ => false) (.goto (fun _ => .reverse))))
    | .reverse => .peek 0 (fun _ b => b) (.branch Option.isSome
      (.pop 0 (fun v _ => v) (.push 2 (fun v => v.getD false) (.goto (fun _ => .reverse))))
      (.goto (fun _ => .copy)))
    | .copy => .peek 2 (fun _ b => b) (.branch Option.isSome
      (.pop 2 (fun v _ => v) (.push 3 (fun v => v.getD false) (.goto (fun _ => .copy))))
      (Statement.pushMany 3 (encNat 5) (.goto (fun _ => .emit))))
    | .emit => .peek 1 (fun _ b => b) (.branch Option.isSome
      (.pop 1 (fun v _ => v) (Statement.pushMany 3 (List.replicate 4 true) (.goto (fun _ => .emit))))
      (.load (fun _ => none) .halt))

structure Data where
  input : Str := []
  count : ℕ := 0
  tmp : Str := []
  output : Str := []

def Data.stacks (d : Data) : Fin 4 → Str := ![d.input,List.replicate d.count true,d.tmp,d.output]
def cfg (l : Label) (v : Option Bool) (d : Data) : machine.Cfg := ⟨some l,v,d.stacks⟩
def run (t : ℕ) (c : Option machine.Cfg) := (fun o => o.bind machine.step)^[t] c
lemma run_succ (t : ℕ) (c : machine.Cfg) : run (t+1) (some c)=run t (machine.step c) := rfl
lemma run_add (a b : ℕ) (c : Option machine.Cfg) : run (a+b) c=run b (run a c) := by
  simp only [run,Nat.add_comm a b,Function.iterate_add_apply]
lemma run_trans {m n : ℕ} {a b c : Option machine.Cfg}
    (h1 : run m a=b) (h2 : run n b=c) : run (m+n) a=c := by rw [run_add,h1,h2]

lemma read_zero_step (v : Option Bool) (d : Data) (tail : Str) :
    machine.step (cfg .read v {d with input := false::tail}) =
      some (cfg .reverse (some false) {d with input := tail,tmp := false::d.tmp}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  congr 1; funext k; fin_cases k <;> rfl

lemma read_true_step (v : Option Bool) (d : Data) (tail : Str) :
    machine.step (cfg .read v {d with input := true::tail}) =
      some (cfg .read (some true) {d with input := tail,count := d.count+1,tmp := true::d.tmp}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,List.replicate_succ]
  congr 1; funext k; fin_cases k <;> rfl

lemma read_run (v : Option Bool) (d : Data) (m : ℕ) (tail : Str) :
    run (m+1) (some (cfg .read v {d with input := encNat m++tail})) =
      some (cfg .reverse (some false) {d with input := tail,count := d.count+m,tmp := false::(List.replicate m true++d.tmp)}) := by
  induction m generalizing v d with
  | zero => simpa [run,encNat] using read_zero_step v d tail
  | succ m ih =>
    rw [run_succ]
    change run (m+1) (machine.step (cfg .read v {d with input := true::(encNat m++tail)})) = _
    rw [read_true_step]
    simpa only [List.replicate_add,List.replicate_one,List.append_assoc,List.singleton_append,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (some true) {d with count := d.count+1,tmp := true::d.tmp}

lemma reverse_nil_step (v : Option Bool) (d : Data) :
    machine.step (cfg .reverse v {d with input := []}) = some (cfg .copy none {d with input := []}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
lemma reverse_cons_step (v : Option Bool) (d : Data) (b : Bool) (tail : Str) :
    machine.step (cfg .reverse v {d with input := b::tail}) =
      some (cfg .reverse (some b) {d with input := tail,tmp := b::d.tmp}) := by
  cases b <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  all_goals congr 1; funext k; fin_cases k <;> rfl
lemma reverse_run (v : Option Bool) (d : Data) (s : Str) :
    run (s.length+1) (some (cfg .reverse v {d with input := s})) =
      some (cfg .copy none {d with input := [],tmp := s.reverse++d.tmp}) := by
  induction s generalizing v d with
  | nil => simpa [run] using reverse_nil_step v d
  | cons b s ih =>
    rw [List.length_cons,run_succ,reverse_cons_step]
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using ih (some b) {d with tmp := b::d.tmp}

lemma copy_nil_step (v : Option Bool) (d : Data) :
    machine.step (cfg .copy v {d with tmp := []}) =
      some (cfg .emit none {d with tmp := [],output := encNat 5++d.output}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,Statement.stepAux_pushMany]
  congr 1; funext k; fin_cases k <;> rfl
lemma copy_cons_step (v : Option Bool) (d : Data) (b : Bool) (tail : Str) :
    machine.step (cfg .copy v {d with tmp := b::tail}) =
      some (cfg .copy (some b) {d with tmp := tail,output := b::d.output}) := by
  cases b <;> simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux]
  all_goals congr 1; funext k; fin_cases k <;> rfl
lemma copy_run (v : Option Bool) (d : Data) (s : Str) :
    run (s.length+1) (some (cfg .copy v {d with tmp := s})) =
      some (cfg .emit none {d with tmp := [],output := encNat 5++s.reverse++d.output}) := by
  induction s generalizing v d with
  | nil => simpa [run] using copy_nil_step v d
  | cons b s ih =>
    rw [List.length_cons,run_succ,copy_cons_step]
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using ih (some b) {d with output := b::d.output}

lemma emit_zero_step (v : Option Bool) (out : Str) :
    machine.step (cfg .emit v {output := out}) = some (haltList machine out) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,haltList]
  congr 1; funext k; fin_cases k <;> rfl
lemma emit_succ_step (v : Option Bool) (d : Data) (m : ℕ) :
    machine.step (cfg .emit v {d with count := m+1}) =
      some (cfg .emit (some true) {d with count := m,output := List.replicate 4 true++d.output}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,Statement.stepAux_pushMany,List.replicate_succ]
  congr 1; funext k; fin_cases k <;> rfl
lemma emit_run (v : Option Bool) (m : ℕ) (out : Str) :
    run (m+1) (some (cfg .emit v {count := m,output := out})) =
      some (haltList machine (List.replicate (4*m) true++out)) := by
  induction m generalizing v out with
  | zero => simpa [run] using emit_zero_step v out
  | succ m ih =>
    rw [run_succ,emit_succ_step v {output := out} m]
    simpa only [Nat.mul_add,Nat.mul_one,List.replicate_add,List.append_assoc] using
      ih (some true) (List.replicate 4 true++out)

/-- Exact source-preserving affine prefix for the clock threshold T=4m+5. -/
theorem full_run (m : ℕ) (tail : Str) :
    run (3*m+2*tail.length+5) (some (initList machine (encNat m++tail))) =
      some (haltList machine (encNat (4*m+5)++encNat m++tail)) := by
  have h1 : run (m+1) (some (initList machine (encNat m++tail))) =
      some (cfg .reverse (some false) {input := tail,count := m,tmp := false::List.replicate m true}) := by
    have hi : initList machine (encNat m++tail) = cfg .read none {input := encNat m++tail} := by
      simp only [initList,cfg]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hi]
    simpa only [Nat.zero_add,List.append_nil] using read_run none {} m tail
  have h2 := reverse_run (some false) {count := m,tmp := false::List.replicate m true} tail
  have h3 := copy_run none {count := m} (tail.reverse++false::List.replicate m true)
  have h4 := emit_run none m (encNat 5++encNat m++tail)
  have h2' : run (tail.length+1)
      (some (cfg .reverse (some false) {input := tail,count := m,tmp := false::List.replicate m true})) =
      some (cfg .copy none {count := m,tmp := tail.reverse++false::List.replicate m true}) := h2
  have h3' : run (tail.length+m+2)
      (some (cfg .copy none {count := m,tmp := tail.reverse++false::List.replicate m true})) =
      some (cfg .emit none {count := m,output := encNat 5++encNat m++tail}) := by
    simpa [encNat,List.length_append,List.length_reverse,List.length_replicate,List.reverse_append,
      List.reverse_cons,List.reverse_replicate,List.append_assoc,Nat.add_assoc] using h3
  have hr := run_trans h1 (run_trans h2' (run_trans h3' h4))
  have ht : (m+1)+((tail.length+1)+((tail.length+m+2)+(m+1)))=3*m+2*tail.length+5 := by omega
  rw [ht] at hr
  simpa only [encNat,List.replicate_add,List.append_assoc] using hr

def outputCode (m : ℕ) (tail : Str) : Str := encNat (4*m+5)++encNat m++tail
noncomputable def timePolynomial : Polynomial ℕ := 40*(Polynomial.X+1)

lemma time_bound (m : ℕ) (tail : Str) :
    3*m+2*tail.length+5 ≤ timePolynomial.eval (encNat m++tail).length := by
  simp only [timePolynomial,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_one,List.length_append,Main.Encoding.encNat_length]
  omega

noncomputable def outputs (m : ℕ) (tail : Str) :
    TM2OutputsInTime machine (encNat m++tail) (some (outputCode m tail))
      (timePolynomial.eval (encNat m++tail).length) where
  steps := 3*m+2*tail.length+5
  evals_in_steps := full_run m tail
  steps_le_m := time_bound m tail

def prepare (s : Str) : Str :=
  match Main.Encoding.parseNat s with
  | none => []
  | some (m,tail) => outputCode m tail





end QMAPerfectCompleteness.Uniformity.CyclicClockPrefixTM


