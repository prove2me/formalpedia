-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerCorrectness
-- name    : QMAPerfectCompleteness_Proof_UnaryNextPowerCorrectness
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:00:03.09074+00:00
-- url     : https://prove2.me/theorems/41686222-f5d5-4f1c-9051-db21e58efa40
-- title:
--   Ceiling logarithm and next-power correctness
-- statement:
--   Defines the total unary compiler interface for a ceiling logarithm and the corresponding power of two. The complete execution, output encoding and polynomial bound are proved for the finite doubling machine.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/UnaryNextPowerCorrectness.lean, retained declaration span lines 10–169.

/- Generated from Solutions.UnaryNextPowerCorrectness by authoritative Stage-2 skeleton subtraction.
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



/-! Correctness and polynomial execution time of the finite unary ceiling-log2 machine. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Turing StateTransition
namespace QMAPerfectCompleteness.Uniformity.UnaryNextPowerTM
open QAlgorithms.Complexity (Str encNat)

def loopData (d : Data) (a p : ℕ) : Data :=
  {d with target := a,power := p,savedTarget := 0,savedPower := 0,doubled := 0}

def loopTime (a p h : ℕ) : ℕ := 6*p*(2^h-1)+5*h+3*a+3

lemma loopTime_succ (a p h : ℕ) :
    loopTime a p (h+1) = (3*p+3)+((3*p+2)+loopTime a (2*p) h) := by
  have hp : 0<2^h := pow_pos (by decide : 0<2) h
  have he : 2^(h+1)-1 = 2*(2^h-1)+1 := by rw [pow_succ]; omega
  unfold loopTime
  rw [he]
  ring

/-- The bounded doubling loop uses exactly the geometric amount of unary work. -/
lemma loop_run (h a p : ℕ) (v : Option Bool) (d : Data) (hp : 0<p)
    (hbefore : ∀ i, i<h → p*2^i<a) (hdone : a≤p*2^h) :
    run (loopTime a p h) (some (cfg .compare v (loopData d a p))) =
      some (cfg .reverseTail none {loopData d a (p*2^h) with exponent := d.exponent+h}) := by
  induction h generalizing p v d with
  | zero =>
    have ha : a≤p := by simpa using hdone
    have hc := compare_restore_run v {d with doubled := 0} a p
    simpa [loopTime,loopData,Nat.min_eq_left ha,show ¬p<a by omega] using hc
  | succ h ih =>
    have hlt : p<a := by simpa using hbefore 0 (by omega)
    let dc : Data := {loopData d a p with exponent := d.exponent+1}
    let dn : Data := {d with exponent := d.exponent+1}
    have hc : run (3*p+3) (some (cfg .compare v (loopData d a p))) = some (cfg .double none dc) := by
      simpa [loopData,dc,Nat.min_eq_right hlt.le,hlt] using
        compare_restore_run v {d with doubled := 0} a p
    have hd : run (3*p+2) (some (cfg .double none dc)) =
        some (cfg .compare none (loopData dn a (2*p))) := by
      simpa only [dc,dn,loopData] using doubling_run none dc p
    have hi := ih (p := 2*p) (v := none) (d := dn) (by omega)
      (by
        intro i hi
        have h' := hbefore (i+1) (by omega)
        simpa only [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h')
      (by simpa only [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hdone)
    have hr := run_trans hc (run_trans hd hi)
    rw [← loopTime_succ] at hr
    simpa only [dc,dn,loopData,pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hr

lemma finish_run (v : Option Bool) (a p c : ℕ) (tail : Str) :
    run (2*tail.length+p+c+a+5)
      (some (cfg .reverseTail v {input := tail,target := a,power := p+1,exponent := c})) =
      some (haltList machine (encNat c++encNat p++tail)) := by
  let ellCode := encNat p++tail
  let output := encNat c++ellCode
  have h1 : run (tail.length+1)
      (some (cfg .reverseTail v {input := tail,target := a,power := p+1,exponent := c})) =
      some (cfg .outputTail none {target := a,power := p+1,exponent := c,tail := tail.reverse}) := by
    simpa only [List.append_nil] using reverseTail_run v {target := a,power := p+1,exponent := c} tail
  have h2 : run (tail.length+1)
      (some (cfg .outputTail none {target := a,power := p+1,exponent := c,tail := tail.reverse})) =
      some (cfg .outputPower none {target := a,power := p,exponent := c,output := false::tail}) := by
    simpa only [List.length_reverse,List.reverse_reverse,List.append_nil] using
      outputTail_run none {target := a,power := p+1,exponent := c} tail.reverse p
  have h3 : run (p+1)
      (some (cfg .outputPower none {target := a,power := p,exponent := c,output := false::tail})) =
      some (cfg .outputExponent none {target := a,exponent := c,output := false::ellCode}) := by
    simpa only [ellCode,encNat,List.append_assoc,List.singleton_append] using
      outputPower_run none {target := a,exponent := c,output := false::tail} p
  have h4 : run (c+1)
      (some (cfg .outputExponent none {target := a,exponent := c,output := false::ellCode})) =
      some (cfg .clearTarget none {target := a,output := output}) := by
    simpa only [output,encNat,List.append_assoc,List.singleton_append] using
      outputExponent_run none {target := a,output := false::ellCode} c
  have h5 := clearTarget_run none a output
  have hr := run_trans h1 (run_trans h2 (run_trans h3 (run_trans h4 h5)))
  have ht : (tail.length+1)+((tail.length+1)+((p+1)+((c+1)+(a+1)))) = 2*tail.length+p+c+a+5 := by omega
  rw [ht] at hr
  simpa only [output,ellCode,List.append_assoc] using hr

/-- Exact output bytes; the source payload after the first unary field is retained verbatim. -/
def outputCode (a : ℕ) (tail : Str) : Str :=
  encNat (Nat.clog 2 a) ++ encNat (2^(Nat.clog 2 a)-1) ++ tail

def time (a : ℕ) (tail : Str) : ℕ :=
  5*a+7*2^(Nat.clog 2 a)+6*(Nat.clog 2 a)+2*tail.length+3

lemma init_step (s : Str) : machine.step (initList machine s) =
    some (cfg .read none {input := s,power := 1}) := by
  simp [FinTM2.step,TM2.step,machine,cfg,Data.stacks,TM2.stepAux,initList]
  congr 1; funext k; fin_cases k <;> rfl

/-- Actual execution of the finite machine, including cleanup of all eight auxiliary stacks. -/
theorem full_run (a : ℕ) (tail : Str) :
    run (time a tail) (some (initList machine (encNat a++tail))) =
      some (haltList machine (outputCode a tail)) := by
  let c := Nat.clog 2 a
  let p := 2^c
  have hp : 0<p := pow_pos (by decide : 0<2) c
  have h1 : run 1 (some (initList machine (encNat a++tail))) =
      some (cfg .read none {input := encNat a++tail,power := 1}) := init_step _
  have h2 : run (a+1) (some (cfg .read none {input := encNat a++tail,power := 1})) =
      some (cfg .compare (some false) {input := tail,target := a,power := 1}) := by
    simpa only [Nat.zero_add] using read_run none {power := 1} a tail
  have h3 : run (loopTime a 1 c)
      (some (cfg .compare (some false) {input := tail,target := a,power := 1})) =
      some (cfg .reverseTail none {input := tail,target := a,power := p,exponent := c}) := by
    simpa only [loopData,Nat.one_mul,Nat.zero_add,p] using
      loop_run c a 1 (some false) {input := tail} (by decide)
        (fun i hi => by simpa using Nat.pow_lt_of_lt_clog hi)
        (by simpa using Nat.le_pow_clog (by decide : 1<2) a)
  have h4 : run (2*tail.length+(p-1)+c+a+5)
      (some (cfg .reverseTail none {input := tail,target := a,power := p,exponent := c})) =
      some (haltList machine (outputCode a tail)) := by
    simpa only [Nat.sub_add_cancel (by omega : 1≤p),outputCode,c,p] using finish_run none a (p-1) c tail
  have hr := run_trans h1 (run_trans h2 (run_trans h3 h4))
  have ht : 1+((a+1)+(loopTime a 1 c+(2*tail.length+(p-1)+c+a+5))) = time a tail := by
    unfold loopTime time
    change 1+(a+1+(6*1*(2^c-1)+5*c+3*a+3+(2*tail.length+(p-1)+c+a+5))) =
      5*a+7*p+6*c+2*tail.length+3
    have he : 2^c=p := rfl
    rw [he]
    omega
  rw [ht] at hr
  exact hr

lemma clog_bound (a : ℕ) : Nat.clog 2 a ≤ a :=
  Nat.clog_le_of_le_pow (Nat.lt_pow_self (by decide : 1<2)).le

lemma power_bound (a : ℕ) : 2^(Nat.clog 2 a) ≤ 2*a+1 := by
  by_cases hc : Nat.clog 2 a=0
  · simp [hc]
  · have hp : 0<Nat.clog 2 a := by omega
    have hs := Nat.pow_lt_of_lt_clog (show Nat.clog 2 a-1<Nat.clog 2 a by omega)
    have he : 2^(Nat.clog 2 a)=2*2^(Nat.clog 2 a-1) := by
      calc
        2^(Nat.clog 2 a) = 2^((Nat.clog 2 a-1)+1) := by congr 1; omega
        _ = 2*2^(Nat.clog 2 a-1) := by rw [pow_succ]; omega
    rw [he]
    omega

noncomputable def timePolynomial : Polynomial ℕ := 100*(Polynomial.X+1)

lemma time_bound (a : ℕ) (tail : Str) :
    time a tail ≤ timePolynomial.eval (encNat a++tail).length := by
  have hc := clog_bound a
  have hp := power_bound a
  simp only [timePolynomial,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_one,List.length_append,Main.Encoding.encNat_length]
  unfold time
  omega

/-- An actual polynomially timed FinTM2 witness, on every encoded unary field and payload. -/
noncomputable def outputs (a : ℕ) (tail : Str) :
    TM2OutputsInTime machine (encNat a++tail) (some (outputCode a tail))
      (timePolynomial.eval (encNat a++tail).length) where
  steps := time a tail
  evals_in_steps := full_run a tail
  steps_le_m := time_bound a tail

/-- Total string interface; valid source streams use its exact unary-prefix equation below. -/
def compile (s : Str) : Str :=
  match Main.Encoding.parseNat s with
  | none => []
  | some (a,tail) => outputCode a tail







end QMAPerfectCompleteness.Uniformity.UnaryNextPowerTM


