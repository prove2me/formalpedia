-- Prove2me | Definitions.Def_OAIQ081S140
-- name    : OAIQ081S140
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:46:40.765104+00:00
-- url     : https://prove2.me/theorems/3187c2a4-c571-45df-bdf9-325bbecbd289
-- title:
--   Definitions bundle OAIQ081S140 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 6 definitions, 1 inductive type or structure and 17 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan.tripleState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.CachedReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.cachedScaledValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.scanCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.cell`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.row`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramPreparedTable`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarBase`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarInit`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarOutput`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarSemantics`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScan`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramTable`, `SubexponentialSAT_SqrtLog_IdempotentProgramConstants`, `SubexponentialSAT_SqrtLog_IdempotentProgramMachine`, `SubexponentialSAT_SqrtLog_IntegerRingLiftProgram`, `SubexponentialSAT_SqrtLog_IntegerRingLiftProgramCached`, `SubexponentialSAT_SqrtLog_LayoutBinomialProgramCell`, `SubexponentialSAT_UnaryForPrograms`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S116`, `OAIQ081S118`, `OAIQ081S119`, `OAIQ081S120` and `OAIQ081S122` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S153`, `OAIQ081S154` and `OAIQ081S155`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S116
import Definitions.Def_OAIQ081S118
import Definitions.Def_OAIQ081S119
import Definitions.Def_OAIQ081S120
import Definitions.Def_OAIQ081S122

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_UnaryForPrograms
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control unary-counted callbacks

The counter is a Boolean stack whose length is the iteration count. Its bits
are ignored. The controller pops before each callback and tests the presence
flag; callbacks preserve the remaining counter tail and may clobber all
registers. Every observation contains an actual callback evaluation.
-/

namespace SubexponentialSAT.UnaryForPrograms

open BitProgram StructuredProgram
open CounterForPrograms (budgetSum)

variable {R S : ℕ}

theorem visits_exists (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ)
    (stable : FrameStable p I) (spec : BodySpec p body I cost) (word : List Bool) :
    ∀ i d, d.stacks p.counter = word → I i d →
      ∃ costs n e, Visits p body costs n d e ∧ I (i + word.length) e ∧
        costs.sum ≤ budgetSum cost i word.length := by
  induction word with
  | nil =>
      intro i d hw hi
      have hp : I i (popped p d) := stable i d (popped p d)
        (fun j hj => (popped_other p d j hj).symm) hi
      exact ⟨[], 2, popped p d, .done d hw, by simpa using hp, by simp [budgetSum]⟩
  | cons bit word ih =>
      intro i d hw hi
      have hp : I i (popped p d) := stable i d (popped p d)
        (fun j hj => (popped_other p d j hj).symm) hi
      obtain ⟨nb, e, hn, he, hc, hei⟩ := spec i (popped p d) hp
      have hew : e.stacks p.counter = word := by simp only [hc, popped_counter, hw, List.tail_cons]
      obtain ⟨costs, nt, f, ht, hfi, hcost⟩ := ih (i + 1) e hew hei
      refine ⟨nb :: costs, nb + nt + 2, f,
        .step (by simp [hw]) he hc ht, ?_, ?_⟩
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfi
      · simpa only [List.sum_cons, List.length_cons, budgetSum] using Nat.add_le_add hn hcost

end SubexponentialSAT.UnaryForPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarInit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing ModularRingPrograms ModularArithmetic

variable (p t : ℕ) [Fact p.Prime]

omit [Fact (Nat.Prime p)] in
/-- Initialization also tolerates the old binary exponent in cache slot 31. -/
theorem initialize_eval (M : SubexpPreparedQuartic.Modulus p t) (shape : List Bool)
    (slots : List Reg) (d : Data) (W : ℕ) (h : Rest d M.bits)
    (h12:d.stacks 12=shape) (hW:shape.length ≤ W)
    (hslots:∀i,(d.stacks (port i)).length ≤ W) :
    ∃ n e, Eval (initializePool slots) n d e ∧ Rest e M.bits ∧ e.stacks 12=shape ∧
      (∀i,e.stacks (port i)=if i∈slots then padTo shape [] else d.stacks (port i)) ∧
      Frame d e ∧ n ≤ slots.length * (23 * shape.length + 2 * W + 25) := by
  induction slots generalizing d with
  | nil=>exact ⟨0,d,.base (.skip _),h,h12,by simp,fun _ _=>rfl,by simp⟩
  | cons i is ih=>
      obtain ⟨na,a,ha,has,hna⟩:=literal_eval d M.bits shape (port i) [] h h12
        (port_ge i) (port_ne38 i)
      have har:Rest a M.bits := by
        constructor
        · intro j
          have hj:low j≠port i := by
            intro hh; have hv:=congrArg Fin.val hh; have hi:=port_ge i
            dsimp [low] at hv; omega
          simpa [has,hj] using h.1 j
        · simpa [has,Ne.symm (port_ne38 i)] using h.2
      have hi12:port i≠12 := by fin_cases i <;> decide
      have ha12:a.stacks 12=shape := by simp [has,hi12.symm,h12]
      have haw:∀j,(a.stacks (port j)).length ≤ W := by
        intro j
        by_cases hj:j=i
        · subst j; simpa [has,padTo_length] using hW
        · have hp:port j≠port i := fun hh=>hj (port_injective hh)
          simpa [has,hp] using hslots j
      obtain ⟨nb,b,hb,hbr,hb12,hbs,hbf,hnb⟩:=ih a har ha12 haw
      refine ⟨na+nb,b,ha.seq hb,hbr,hb12,?_,?_,?_⟩
      · intro j
        rw [hbs]
        by_cases hj:j∈is
        · simp [hj]
        · by_cases hji:j=i
          · subst j; simp [hj,has]
          · have hp:port j≠port i := fun hh=>hji (port_injective hh)
            simp [hj,hji,has,hp]
      · intro j hj
        rw [hbf j hj,has]
        simp [Ne.symm (hj i)]
      · have hi:=hslots i
        simp only [List.length_nil,mul_zero,add_zero] at hna
        simp only [List.length_cons]
        nlinarith

omit [Fact (Nat.Prime p)] in
theorem initializeAll_eval (M : SubexpPreparedQuartic.Modulus p t) (shape : List Bool)
    (hshape:shape.length=baseWidth p t) (d : Data) (W : ℕ) (h : Rest d M.bits)
    (h12:d.stacks 12=shape) (hW:shape.length ≤ W)
    (hslots:∀i,(d.stacks (port i)).length ≤ W) :
    ∃ n e, Eval initializeAll n d e ∧
      Encoded p t M (fun _=>zeroValue p t shape hshape) e ∧ e.stacks 12=shape ∧
      Frame d e ∧ n ≤ 12 * (23 * shape.length + 2 * W + 25) := by
  obtain ⟨n,e,he,her,he12,hes,hf,hn⟩:=initialize_eval p t M shape (List.finRange 12) d W h h12 hW hslots
  refine ⟨n,e,he,⟨her,?_⟩,he12,hf,by simpa using hn⟩
  intro i
  simpa [zeroValue] using hes i

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing ModularRingPrograms ModularArithmetic BinaryArithmetic

variable (t : ℕ)

theorem baseCommand_eval (M : SubexpPreparedQuartic.Modulus 3 t)
    (shape : List Bool) (hs:shape.length=baseWidth 3 t) (d:Data) (W:ℕ)
    (h:Rest d M.bits) (h12:d.stacks 12=shape) (hW:shape.length ≤ W)
    (hslots:∀i,(d.stacks (port i)).length ≤ W) :
    ∃ n e, Eval baseCommand n d e ∧ Encoded 3 t M (baseValues t M shape hs) e ∧
      Frame d e ∧ n ≤ 400*(baseWidth 3 t+W+1) := by
  obtain ⟨n0,d0,he0,hv0,h12',hf0,hn0⟩:=initializeAll_eval 3 t M shape hs d W h h12 hW hslots
  obtain ⟨n1,d1,he1,hes1,hn1⟩:=literal_eval d0 M.bits shape 18 [true] hv0.1 h12'
    (by decide) (by decide)
  have hu1:=encoded_update 3 t M (fun _=>zeroValue 3 t shape hs) d0 d1 1
    (oneValue t shape hs) hv0 hes1
  have h12'' : d1.stacks 12=shape := by rw [hes1]; simpa using h12'
  have hm : 0 < BinaryArithmetic.toNat M.bits := by rw [M.value]; positivity
  obtain ⟨n2,d2,he2,hes2,hn2⟩:=negativeOne_eval d1 M.bits shape 28 hu1.1.1 h12'' hm
    (by decide) (by decide)
  have hu2:=encoded_update 3 t M _ d1 d2 9 (minusValue t M shape hs) hu1.1 hes2
  refine ⟨n0+(n1+n2),d2,he0.seq (he1.seq he2),hu2.1,?_,?_⟩
  · intro j hj
    exact (hu2.2 j hj).trans ((hu1.2 j hj).trans (hf0 j hj))
  · have h18 : (d0.stacks 18).length=baseWidth 3 t := by
      have hh:=hv0.2 1
      simpa [port,zeroValue,padTo_length,hs] using congrArg List.length hh
    have h28 : (d1.stacks 28).length=baseWidth 3 t := by
      have hh:=hu1.1.2 9
      simpa [port,zeroValue,padTo_length,hs] using congrArg List.length hh
    have hm:=M.length_le
    simp only [List.length_cons,List.length_nil] at hn1
    rw [h18,hs] at hn1
    rw [h28,hs] at hn2
    rw [hs] at hn0
    omega

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open SubexpLiftRing SubexpQuarticRing

variable (p t : ℕ) [Fact p.Prime]

theorem decode_op (M : SubexpPreparedQuartic.Modulus p t) (op : Op) (v : Values p t) :
    decode p t (op.eval p t M v)=op.algebra (decode p t v) := by
  cases op with
  | add o l r =>
      funext i
      by_cases hi:i=o
      · subst i; simp [decode,Op.eval,Op.algebra,SubexpPreparedQuartic.wordAdd_correct]
      · simp [decode,Op.eval,Op.algebra,hi]
  | mul o l r =>
      funext i
      by_cases hi:i=o
      · subst i; simp [decode,Op.eval,Op.algebra,SubexpPreparedQuartic.wordMul_correct]
      · simp [decode,Op.eval,Op.algebra,hi]

theorem decode_run (M : SubexpPreparedQuartic.Modulus p t) (ops : List Op) (v : Values p t) :
    decode p t (run p t M ops v)=algebra ops (decode p t v) := by
  induction ops generalizing v with
  | nil=>rfl
  | cons a as ih=>simp only [run,algebra,ih,decode_op]

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open SubexpLiftRing SubexpQuarticRing BinaryArithmetic

variable (p t : ℕ) [Fact p.Prime]

theorem op_canonical (M:SubexpPreparedQuartic.Modulus p t) (v:Values p t)
    (op:Op) (h:Canonical p t v) : Canonical p t (op.eval p t M v) := by
  intro i
  cases op with
  | add o l r =>
      by_cases hi:i=o
      · subst i; simpa [Op.eval] using SubexpPreparedQuartic.wordAdd_canonical p t M (v l) (v r)
      · simpa [Op.eval,hi] using h i
  | mul o l r =>
      by_cases hi:i=o
      · subst i; simpa [Op.eval] using RingProgram.wordMul_canonical p t M (v l) (v r)
      · simpa [Op.eval,hi] using h i

theorem run_canonical (M:SubexpPreparedQuartic.Modulus p t) (v:Values p t)
    (ops:List Op) (h:Canonical p t v) : Canonical p t (run p t M ops v) := by
  induction ops generalizing v with
  | nil=>exact h
  | cons a as ih=>exact ih _ (op_canonical p t M v a h)

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native descending-index traversal. The remaining unary counter is the
runtime index passed to the callback. Prefixing each generated word therefore
materializes the final array in increasing index order, without a precomputed
array or a value-dependent control table. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan

open BitProgram StructuredCalls

def state (base : Store) (counter output : Fin 41) (regs : Fin 8 → Bool)
    (n : ℕ) (tail : List Bool) : Data :=
  ⟨regs, Function.update (Function.update base counter (List.replicate n true)) output tail⟩

theorem popped_succ (base : Store) (counter output : Fin 41) (hco : counter ≠ output)
    (regs : Fin 8 → Bool) (n : ℕ) (tail : List Bool) :
    UnaryForPrograms.popped (ports counter) (state base counter output regs (n+1) tail) =
      state base counter output (readRegs regs 0 7 (some true)) n tail := by
  apply SubexpScanPrimitives.state_ext
  · simp [UnaryForPrograms.popped, ports, state, hco, List.replicate_succ]
  · funext i
    by_cases hi : i = counter
    · subst i; simp [UnaryForPrograms.popped, ports, state, hco, List.replicate_succ]
    · by_cases hio : i = output
      · subst i; simp [UnaryForPrograms.popped, ports, state, Ne.symm hco]
      · simp [UnaryForPrograms.popped, ports, state, hi, hio]

theorem popped_zero (base : Store) (counter output : Fin 41) (hco : counter ≠ output)
    (regs : Fin 8 → Bool) (tail : List Bool) :
    UnaryForPrograms.popped (ports counter) (state base counter output regs 0 tail) =
      state base counter output (readRegs regs 0 7 none) 0 tail := by
  apply SubexpScanPrimitives.state_ext
  · simp [UnaryForPrograms.popped, ports, state, hco]
  · funext i
    by_cases hi : i = counter
    · subst i; simp [UnaryForPrograms.popped, ports, state, hco]
    · by_cases hio : i = output
      · subst i; simp [UnaryForPrograms.popped, ports, state, Ne.symm hco]
      · simp [UnaryForPrograms.popped, ports, state, hi, hio]

/-- The callback premise is a genuine native trace. It receives index i as
the remaining unary counter and must preserve that counter and the frame. -/
theorem command_eval (base : Store) (counter output : Fin 41) (hco : counter ≠ output)
    (body : Cmd 8 41) (f : ℕ → List Bool) (K n : ℕ)
    (step : ∀ i, i < n → ∀ regs tail, ∃ cost rf, cost ≤ K ∧
      Eval body cost (state base counter output regs i tail)
        (state base counter output rf i (f i ++ tail)))
    (regs : Fin 8 → Bool) (tail : List Bool) :
    ∃ cost rf, cost ≤ n*(K+2)+2 ∧
      Eval (command counter body) cost (state base counter output regs n tail)
        (state base counter output rf 0 (cells f n ++ tail)) := by
  suffices h : ∃ costs cost rf, cost ≤ n*(K+2)+2 ∧
      UnaryForPrograms.Visits (ports counter) body costs cost
        (state base counter output regs n tail)
        (state base counter output rf 0 (cells f n ++ tail)) by
    obtain ⟨costs,cost,rf,hb,he⟩ := h
    exact ⟨cost,rf,hb,he.eval⟩
  induction n generalizing regs tail with
  | zero =>
      refine ⟨[],2,readRegs regs 0 7 none,by simp,?_⟩
      have h := UnaryForPrograms.Visits.done (p := ports counter) (body := body)
        (state base counter output regs 0 tail) (by simp [ports,state,hco])
      simpa only [popped_zero base counter output hco, cells, List.nil_append] using h
  | succ n ih =>
      obtain ⟨nb,rb,hnb,hbody⟩ := step n (by omega) (readRegs regs 0 7 (some true)) tail
      obtain ⟨costs,nt,rt,hnt,ht⟩ := ih (fun i hi => step i (by omega)) rb (f n ++ tail)
      refine ⟨nb::costs,nb+nt+2,rt,by nlinarith,?_⟩
      have he := UnaryForPrograms.Visits.step
        (p := ports counter) (body := body)
        (d := state base counter output regs (n+1) tail)
        (by simp [ports,state,hco,List.replicate_succ])
        (by simpa only [popped_succ base counter output hco] using hbody)
        (by rw [popped_succ base counter output hco]; simp [ports,state,hco]) ht
      simpa only [cells, List.append_assoc] using he

theorem copyAndScan_eval (base : Store) (source counter output scratch : Fin 41)
    (hsc : source ≠ counter) (hst : source ≠ scratch) (htc : scratch ≠ counter)
    (hso : source ≠ output) (hco : counter ≠ output) (hto : scratch ≠ output)
    (body : Cmd 8 41) (f : ℕ → List Bool) (K n : ℕ)
    (hs : base source = List.replicate n true) (hc : base counter = [])
    (ht : base scratch = [])
    (step : ∀ i, i < n → ∀ regs tail, ∃ cost rf, cost ≤ K ∧
      Eval body cost (state base counter output regs i tail)
        (state base counter output rf i (f i ++ tail)))
    (regs : Fin 8 → Bool) (tail : List Bool) :
    ∃ cost rf, cost ≤ scanBudget n K ∧
      Eval (copyAndScan source counter output scratch body) cost
        ⟨regs, Function.update base output tail⟩
        ⟨rf, Function.update base output (cells f n ++ tail)⟩ := by
  let a : Data := ⟨regs, Function.update base output tail⟩
  let b := SubexpScanPrimitives.afterCopy a source counter 0 1
  have he := SubexpScanPrimitives.copy_eval a source counter scratch 0 1
    hsc hst htc (by decide) (by simp [a,hto,ht])
  have hbs : b = state base counter output b.regs n tail := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    simp only [b,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,a,state]
    funext i
    by_cases hio : i = output
    · subst i; simp [Ne.symm hco]
    · by_cases hic : i = counter
      · subst i; simp [hco,hso,hc,hs]
      · simp [hio,hic]
  obtain ⟨nt,rt,hnt,hloop⟩ := command_eval base counter output hco body f K n step b.regs tail
  rw [←hbs] at hloop
  have hfinal : state base counter output rt 0 (cells f n ++ tail) =
      ⟨rt, Function.update base output (cells f n ++ tail)⟩ := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    simp [state,←hc]
  rw [hfinal] at hloop
  refine ⟨(7*n+5)+nt,rt,?_,?_⟩
  · dsimp [scanBudget]; nlinarith
  · have hlen : (a.stacks source).length = n := by simp [a,hso,hs]
    simpa only [copyAndScan,hlen] using he.seq hloop

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramTable
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Three nested finite-control loops enumerate the H-adic multiplication
indices from runtime unary degree. Every entry callback is an actual trace. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan

open BitProgram StructuredCalls

def tripleState (base : Store) (regs : Fin 8 → Bool)
    (i j k : ℕ) (tail : List Bool) : Data :=
  ⟨regs,Function.update (Function.update (Function.update (Function.update base
    24 (List.replicate k true)) 25 (List.replicate i true))
    26 (List.replicate j true)) 22 tail⟩

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramPreparedTable
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpQuarticRing

theorem prepared_zero (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t)
    (d : Data) (hp : Scalar.Prepared t M cache u d) :
    d.stacks 17 = cache.zero.val := by
  exact hp.zero

theorem prepared_source_width (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t)
    (d : Data) (hp : Scalar.Prepared t M cache u d) (c : Fin 6) :
    (d.stacks (entrySource c)).length = SubexpLiftRing.baseWidth 3 t := by
  rw [entrySource_eq_scalar,hp.table]
  exact (IdempotentProgram.integerRun (RingProgram.scalarProgram 3 t M cache)
    (IdempotentTableEntryProgram.codeValue c)).1.property

theorem prepared_tableCells (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t)
    (d : Data) (hp : Scalar.Prepared t M cache u d) :
    Scan.tableCells (cachedEntry d.stacks) (3*t) =
      IdempotentProgram.tableTape (IdempotentProgram.tableCode (t := t) (RingProgram.scalarProgram 3 t M cache)) := by
  apply Scan.tableCells_eq_tableTape
  intro i j k
  rw [cachedEntry,entrySource_eq_scalar,hp.table,IdempotentTableEntryProgram.entryCode_correct]
  simp only [IdempotentProgram.tableCode_apply,IdempotentProgram.tableRun]

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramConstants
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact word identities connecting the padded native preparation arrays
to the finite H-adic implementation. -/

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpQuarticRing

theorem minusOneRun_flat (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hm : BinaryArithmetic.toNat cache.minusOne.val < p^t)
    (height : ℕ) (ht : 0 < height) :
    RingProgram.flat (minusOneRun (RingProgram.scalarProgram p t M cache) height).1 =
      cache.minusOne.val ++ (List.replicate (3*height-1) cache.zero.val).flatten := by
  have hfun : (minusOneRun (RingProgram.scalarProgram p t M cache) height).1 =
      fun i => if i.val = 0 then cache.minusOne else cache.zero := by
    funext i
    exact minusOneRun_apply p t M cache hz hm height i
  rw [hfun]
  exact flat_sparse (by omega) cache.minusOne cache.zero

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramMachine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed four-array Newton machine. Its native services perform full dynamic
vector arithmetic, operand copying, and target replacement. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open BitProgram StructuredCalls SubexpSymbolicCost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem RegistersEncoded.frame {B d : ℕ} {modulus width zero table degree : List Bool}
    {minusOne : RingProgram.Code (Word B) d}
    {regs : Registers (RingProgram.Code (Word B) d)} {state next : RegisterData}
    (hf : CounterForPrograms.OutsideEq newtonPorts state next)
    (h : RegistersEncoded modulus width zero table degree minusOne regs state) :
    RegistersEncoded modulus width zero table degree minusOne regs next := by
  constructor
  · intro i
    have hi39 : servicePorts i ≠ newtonPorts.counter := by
      intro he; have hv := congrArg Fin.val he; have := i.isLt
      dsimp [servicePorts, newtonPorts] at hv; omega
    have hi40 : servicePorts i ≠ newtonPorts.scratch := by
      intro he; have hv := congrArg Fin.val he; have := i.isLt
      dsimp [servicePorts, newtonPorts] at hv; omega
    rw [← hf _ hi39 hi40]
    exact h.context i
  · intro i
    have hi39 : arrayRegister i ≠ newtonPorts.counter := by
      intro he; have hv := congrArg Fin.val he; have := i.isLt
      dsimp [arrayRegister, newtonPorts] at hv; omega
    have hi40 : arrayRegister i ≠ newtonPorts.scratch := by
      intro he; have hv := congrArg Fin.val he; have := i.isLt
      dsimp [arrayRegister, newtonPorts] at hv; omega
    rw [← hf _ hi39 hi40]
    exact h.values i
  · rw [← hf 36 (by decide) (by decide)]
    exact h.negativeUnit
  · rw [← hf 37 (by decide) (by decide)]
    exact h.degree
  · rw [← hf 38 (by decide) (by decide)]
    exact h.copyScratch

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IntegerRingLiftProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed little-endian binary-to-ring scanner.  No natural-number value is
used by the program: each input bit conditionally adds the current place and
then doubles that place.  Arithmetic is supplied by finite native commands;
the concrete RingModel instantiation is in IntegerRingLiftProgramModel. -/
namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec LowFrame lowFrame_update lowFrame_refl
  callAt callAt_run CachePort)

def scanCommand (add : Code) : Code := UnaryForPrograms.forCmd bitPorts (bitStep add)

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IntegerRingLiftProgramCached
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Cache-extensional interface for the same fixed integer-lift programs.
Setup may supply any represented zero, one and minus-one bytes whose decoded
values are correct. This avoids requiring its constant-vector construction
to equal a particular arithmetic expression byte for byte. -/
namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open CRTLocalProgram (lowFrame_refl)

structure CachedReady (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (zero one minusOne : ModelCode t d) (s : Store) : Prop where
  native : HornerProgram.Services.NativeReady 3 t M cache (modelTable t a M cache) s
  clean : Clean s
  zero : s 249 = RingProgram.flat zero
  one : s 250 = RingProgram.flat one
  minusOne : s 251 = RingProgram.flat minusOne
  bits : s 246 = []
  accumulator : s 247 = []
  place : s 248 = []
  output : s 255 = []

def cachedScaledValue (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (zero one minusOne invDenom : ModelCode t d) (positive negative : List Bool) : ModelCode t d :=
  let ops := RingProgram.modelProgram t a M cache
  scaledValue (fun x y => (ops.mulRun x y).1) (fun x y => (ops.addRun x y).1)
    zero one minusOne invDenom positive negative

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutBinomialProgramCell
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Consolidated fixed-control binomial-cache implementation. Component module
paths re-export this file so all interfaces remain stable. -/

/-! A Pascal cell saves the old entry, adds and emits the new entry, then
restores the saved entry as the carry. Every copy and clear is paid. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar
open SubexponentialSAT.Subexp.MatrixProgramSupport

abbrev cell : Cmd 8 18 :=
  .seq saveOld (.seq addCommand (.seq cacheEmit (.seq clearCarry restoreOld)))

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! One paid Pascal row pass over the framed cache. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar

abbrev row : Cmd 8 18 := .seq parse (.while 7 (.seq cell parse))

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! A fixed while loop consumes the runtime unary iteration count. -/

/-! A fixed loop builds the initial zero cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/

/-! One fixed program builds the complete unsigned binomial row from the unary
runtime parameters h and R. No coefficient or initial cache is free input. -/

/-! A fixed component routine copies the runtime width, pads or truncates one
word, and consumes that word into a reverse output buffer. -/

/-! Generic framed unsigned rows are converted to flat signed-component
arrays at a supplied runtime width. Both output arrays are physically built.
-/

/-! Finish the generic cache adapter by reversing both physically accumulated
arrays. The common width is preserved for downstream indexed reads. -/

/-! Value and shape contracts for the generic adapter and binomial row. -/

/-! Complete fixed-control binomial cache construction. The three parameters
are runtime unary stacks; the output consists of actual flat fixed-width
positive and negative arrays in increasing column order. -/

end OAI.Algorithms
end


