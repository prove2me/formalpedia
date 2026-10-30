-- Prove2me | Definitions.Def_OAIQ081S066
-- name    : OAIQ081S066
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:50:53.713525+00:00
-- url     : https://prove2.me/theorems/809222ce-07b8-4fef-b9ed-9e7381b1ec59
-- title:
--   Definitions bundle OAIQ081S066 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 96 declarations of OpenAI's Lean: 42 definitions, 1 inductive type or structure and 53 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.CeilingDivisionPrograms.Data`, `OAI.Algorithms.SubexponentialSAT.CeilingDivisionPrograms.RoundOutput`, `OAI.Algorithms.SubexponentialSAT.CeilingDivisionPrograms.incrementCmd`, `OAI.Algorithms.SubexponentialSAT.CeilingDivisionPrograms.incrementResult`, `OAI.Algorithms.SubexponentialSAT.CeilingDivisionPrograms.quotientPorts`, `OAI.Algorithms.SubexponentialSAT.CeilingDivisionPrograms.remainderPorts`, `OAI.Algorithms.SubexponentialSAT.CeilingDivisionPrograms.roundBound`, `OAI.Algorithms.SubexponentialSAT.CeilingDivisionPrograms.roundCmd`, `OAI.Algorithms.SubexponentialSAT.CounterConversions.Data`, `OAI.Algorithms.SubexponentialSAT.CounterConversions.clear`, `OAI.Algorithms.SubexponentialSAT.CounterConversions.cleared`, `OAI.Algorithms.SubexponentialSAT.CounterConversions.encodeNatCmd`, `OAI.Algorithms.SubexponentialSAT.CounterConversions.encodeNatProgram`, `OAI.Algorithms.SubexponentialSAT.CounterConversions.outputInvariant`, `OAI.Algorithms.SubexponentialSAT.CounterConversions.ports`, `OAI.Algorithms.SubexponentialSAT.CounterConversions.push`, `OAI.Algorithms.SubexponentialSAT.CounterConversions.pushed`, `OAI.Algorithms.SubexponentialSAT.CounterConversions.reset`, `OAI.Algorithms.SubexponentialSAT.CounterConversions.resetState`, `OAI.Algorithms.SubexponentialSAT.CounterConversions.state`, `OAI.Algorithms.SubexponentialSAT.CounterConversions.unaryCmd`, `OAI.Algorithms.SubexponentialSAT.CounterConversions.unaryProgram`, `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.BodySpec`, `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.FrameStable`, `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.OutsideEq`, `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.Visits`, `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.advanceCmd`, `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.advanceCost`, `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.decrementCmd`, `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.forCmd`, `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.loopCmd`, `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.program`, `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.testCmd`, `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.zeroCmd`, `OAI.Algorithms.SubexponentialSAT.CounterPredProgram.predCmd`, `OAI.Algorithms.SubexponentialSAT.CounterPredProgram.predCost`, `OAI.Algorithms.SubexponentialSAT.CounterPredProgram.predResult`, `OAI.Algorithms.SubexponentialSAT.ExecCNFSubset.subsetProgram`, `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.Data`, `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.Ports` and 3 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_CeilingDivisionPrograms`, `SubexponentialSAT_CounterConversions`, `SubexponentialSAT_CounterForPrograms`, `SubexponentialSAT_CounterPredProgram`, `SubexponentialSAT_ExecCNFMembership`, `SubexponentialSAT_ExecCNFSubset`, `SubexponentialSAT_ExecCNFTupleEnumeration`, `SubexponentialSAT_ExecClauseDedupProgram`, `SubexponentialSAT_ModularRingPrograms`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SubexpFlatAdd`, `SubexponentialSAT_SubexpScalarMachine`, `SubexponentialSAT_SubexpScanPrimitives`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S042`, `OAIQ081S045` and `OAIQ081S046` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S082`, `OAIQ081S083`, `OAIQ081S084`, `OAIQ081S085`, `OAIQ081S086`, `OAIQ081S087`, `OAIQ081S088`, `OAIQ081S089`, `OAIQ081S092`, `OAIQ081S093`, `OAIQ081S095`, `OAIQ081S096`, `OAIQ081S097`, `OAIQ081S098` and `OAIQ081S099`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S042
import Definitions.Def_OAIQ081S045
import Definitions.Def_OAIQ081S046

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_CounterForPrograms
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A finite binary-counted callback loop

The loop bound lives on a little-endian Boolean stack.  Fixed finite subroutines
perform zero testing and decrement, and an arbitrary fixed command is the loop
body.  The body may overwrite every register.  All measured evaluations below
compile to traces of a finite instruction table; proof-level state embeddings
are never used as executable instructions.
-/

namespace SubexponentialSAT.CounterForPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram SubexponentialSAT.CounterPrograms

variable {R S : ℕ}

theorem install_other_stack (p : Ports R S) (d : Data R S)
    (b present flag : Bool) (xs ys : List Bool) (i : Fin S)
    (hc : i ≠ p.counter) (hs : i ≠ p.scratch) :
    (install p d b present flag xs ys).stacks i = d.stacks i := by
  apply StructuredCalls.embedState_stack_frame
  rintro ⟨j, hj⟩
  fin_cases j
  · exact hc hj.symm
  · exact hs hj.symm

theorem install_stacks_self (p : Ports R S) (d : Data R S)
    (b present flag : Bool) (hs : d.stacks p.scratch = []) :
    (install p d b present flag (d.stacks p.counter) []).stacks = d.stacks := by
  have h := congrArg State.stacks (install_self p d)
  simpa only [install, StructuredCalls.embedState, localData, hs] using h

theorem ripple_local_trace (c b present flag : Bool) (xs : List Bool) :
    Trace (rippleProgram c) (rippleCost c xs + 1)
      ((localData b present flag xs []).withPC (some (rippleProgram c).entry))
      ((localData false false flag (ripple c xs) []).withPC none) := by
  have h : Trace (rippleProgram c) (rippleCost c xs)
      (counterCfg 0 b present flag xs [])
      (counterCfg 10 false false flag (ripple c xs) []) := by
    simpa using ripple_trace c b present flag xs []
  exact h.trans (.cons (by simp [step, counterCfg, execInstr,
    localData, State.withPC]) (.refl _))

theorem zero_local_trace (b present flag : Bool) (xs : List Bool) :
    Trace zeroProgram (8 * xs.length + 6)
      ((localData b present flag xs []).withPC (some zeroProgram.entry))
      ((localData false false (isZero xs) xs []).withPC none) := by
  have h : Trace zeroProgram (8 * xs.length + 5)
      (counterCfg 0 b present flag xs [])
      (counterCfg 9 false false (isZero xs) xs []) := by
    simpa [Nat.add_assoc] using
      SubexponentialSAT.Computation.Trace.cons (zero_step0 b present flag xs [])
        (zero_scan_trace b present true xs [])
  exact h.trans (.cons (by simp [step, counterCfg, execInstr,
    localData, State.withPC]) (.refl _))

abbrev decrementCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .call (ProgramLinking.liftProgram (rippleProgram false) p.register (stackPorts p))

abbrev zeroCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .call (ProgramLinking.liftProgram zeroProgram p.register (stackPorts p))

theorem decrement_eval (p : Ports R S) (d : Data R S) (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (decrementCmd p) (rippleCost false (d.stacks p.counter) + 1)
      d (decrementResult p d) := by
  have h := StructuredCalls.eval_call_lifted (rippleProgram false) p.register (stackPorts p) d
    p.register.injective (stackPorts p).injective
    (ripple_local_trace false (d.regs (p.register 0)) (d.regs (p.register 1))
      (d.regs (p.register 2)) (d.stacks p.counter))
  change StructuredCalls.Eval (decrementCmd p) _
    (install p d _ _ _ _ []) (decrementResult p d) at h
  rw [← hs, install_self] at h
  exact h

theorem zero_eval (p : Ports R S) (d : Data R S) (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (zeroCmd p) (8 * (d.stacks p.counter).length + 6)
      d (zeroResult p d) := by
  have h := StructuredCalls.eval_call_lifted zeroProgram p.register (stackPorts p) d
    p.register.injective (stackPorts p).injective
    (zero_local_trace (d.regs (p.register 0)) (d.regs (p.register 1))
      (d.regs (p.register 2)) (d.stacks p.counter))
  change StructuredCalls.Eval (zeroCmd p) _
    (install p d _ _ _ _ []) (zeroResult p d) at h
  rw [← hs, install_self] at h
  exact h

abbrev testCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .seq (zeroCmd p) (.base (.atom (.bnot (p.register 2) (p.register 2))))

theorem test_eval (p : Ports R S) (d : Data R S) (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (testCmd p) (8 * (d.stacks p.counter).length + 7)
      d (testResult p d) := by
  have h := StructuredCalls.Eval.seq (zero_eval p d hs)
    (StructuredCalls.Eval.base (StructuredProgram.Eval.atom
      (.bnot (p.register 2) (p.register 2)) (zeroResult p d)))
  simpa only [testCmd, testResult, Nat.add_assoc] using h

theorem testResult_stacks (p : Ports R S) (d : Data R S)
    (hs : d.stacks p.scratch = []) : (testResult p d).stacks = d.stacks := by
  change (zeroResult p d).stacks = d.stacks
  exact install_stacks_self p d _ _ _ hs

abbrev advanceCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .seq (decrementCmd p) (testCmd p)

def advanceCost (p : Ports R S) (d : Data R S) : ℕ :=
  (rippleCost false (d.stacks p.counter) + 1) +
    (8 * (ripple false (d.stacks p.counter)).length + 7)

theorem advance_eval (p : Ports R S) (d : Data R S) (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (advanceCmd p) (advanceCost p d) d (nextState p d) := by
  have h := StructuredCalls.Eval.seq (decrement_eval p d hs)
    (test_eval p (decrementResult p d) (decrementResult_scratch ..))
  simpa only [advanceCmd, advanceCost, nextState, decrementResult_counter] using h

@[simp] theorem nextState_counter (p : Ports R S) (d : Data R S) :
    (nextState p d).stacks p.counter = ripple false (d.stacks p.counter) := by
  rw [nextState, testResult_stacks p _ (decrementResult_scratch ..), decrementResult_counter]

@[simp] theorem nextState_scratch (p : Ports R S) (d : Data R S) :
    (nextState p d).stacks p.scratch = [] := by
  rw [nextState, testResult_stacks p _ (decrementResult_scratch ..), decrementResult_scratch]

@[simp] theorem nextState_flag (p : Ports R S) (d : Data R S) :
    (nextState p d).regs (p.register 2) = !(isZero ((nextState p d).stacks p.counter)) := by
  rw [nextState, testResult_flag, testResult_stacks p _ (decrementResult_scratch ..)]

/-- State invariants may ignore every register and both controller stacks. -/
def OutsideEq (p : Ports R S) (a b : Data R S) : Prop :=
  ∀ j : Fin S, j ≠ p.counter → j ≠ p.scratch → a.stacks j = b.stacks j

def FrameStable (p : Ports R S) (I : ℕ → Data R S → Prop) : Prop :=
  ∀ i a b, OutsideEq p a b → I i a → I i b

theorem testResult_outside (p : Ports R S) (d : Data R S) (hs : d.stacks p.scratch = []) :
    OutsideEq p d (testResult p d) := by
  intro j _ _
  rw [testResult_stacks p d hs]

theorem nextState_outside (p : Ports R S) (d : Data R S) :
    OutsideEq p d (nextState p d) := by
  intro j hc hs
  rw [nextState, testResult_stacks p _ (decrementResult_scratch ..)]
  exact (install_other_stack p d _ _ _ _ _ j hc hs).symm

theorem advanceCost_le (p : Ports R S) (d : Data R S)
    (hp : 0 < value (d.stacks p.counter)) :
    advanceCost p d + 1 ≤ 16 * (d.stacks p.counter).length + 16 := by
  have hr := rippleCost_le false (d.stacks p.counter)
  have hl := decrement_length hp
  simp only [advanceCost, hl]
  omega

/-- The syntax is independent of the counter word and its value. -/
abbrev loopCmd (p : Ports R S) (body : StructuredCalls.Cmd R S) : StructuredCalls.Cmd R S :=
  .while (p.register 2) (.seq body (advanceCmd p))

abbrev forCmd (p : Ports R S) (body : StructuredCalls.Cmd R S) : StructuredCalls.Cmd R S :=
  .seq (testCmd p) (loopCmd p body)

/-- Each recorded cost comes from a real execution of the fixed callback. -/
inductive Visits (p : Ports R S) (body : StructuredCalls.Cmd R S) :
    List ℕ → ℕ → Data R S → Data R S → Prop
  | done (d : Data R S) (hflag : d.regs (p.register 2) = false)
      (hzero : value (d.stacks p.counter) = 0) : Visits p body [] 1 d d
  | step {d e f : Data R S} {nb nt : ℕ} {costs : List ℕ}
      (hflag : d.regs (p.register 2) = true)
      (hpositive : 0 < value (d.stacks p.counter))
      (hbody : StructuredCalls.Eval body nb d e)
      (hcounter : e.stacks p.counter = d.stacks p.counter)
      (hscratch : e.stacks p.scratch = [])
      (tail : Visits p body costs nt (nextState p e) f) :
      Visits p body (nb :: costs) ((nb + advanceCost p e) + nt + 1) d f

theorem Visits.eval {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {costs : List ℕ} {n : ℕ} {d e : Data R S} (h : Visits p body costs n d e) :
    StructuredCalls.Eval (loopCmd p body) n d e := by
  induction h with
  | done d hf hz => exact .while_false hf
  | step hf hp hb hc hs ht ih =>
      exact .while_true hf (.seq hb (advance_eval p _ hs)) ih

/-- A bound on callback costs, indexed by the number of preceding calls. -/
abbrev BodySpec (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ) : Prop :=
  ∀ i d, I i d → d.stacks p.scratch = [] → 0 < value (d.stacks p.counter) →
    ∃ nb e, nb ≤ cost i ∧ StructuredCalls.Eval body nb d e ∧
      e.stacks p.counter = d.stacks p.counter ∧ e.stacks p.scratch = [] ∧ I (i + 1) e


/-- The recorded callback count is exactly the input value, and decrement
preserves the width of every positive counter representation. -/
theorem Visits.bounds {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {costs : List ℕ} {n : ℕ} {d e : Data R S} (h : Visits p body costs n d e) :
    costs.length = value (d.stacks p.counter) ∧
      value (e.stacks p.counter) = 0 ∧
      (e.stacks p.counter).length = (d.stacks p.counter).length ∧
      n ≤ costs.sum + costs.length * (16 * (d.stacks p.counter).length + 16) + 1 := by
  induction h with
  | done d hf hz => exact ⟨hz.symm, hz, rfl, by simp⟩
  | @step d e f nb nt costs hf hp hb hc hs ht ih =>
      rcases ih with ⟨hlen, hzero, hwidth, htime⟩
      have hep : 0 < value (e.stacks p.counter) := by simpa only [hc] using hp
      have hdec := value_decrement hep
      have hw : ((nextState p e).stacks p.counter).length =
          (d.stacks p.counter).length := by
        rw [nextState_counter, decrement_length hep, hc]
      have hv : value ((nextState p e).stacks p.counter) + 1 =
          value (d.stacks p.counter) := by
        simpa only [nextState_counter, hc] using hdec
      have hcost := advanceCost_le p e hep
      rw [hc] at hcost
      rw [hw] at htime hwidth
      refine ⟨?_, hzero, hwidth, ?_⟩
      · simpa only [List.length_cons, hlen] using hv
      · simp only [List.sum_cons, List.length_cons]
        calc
          (nb + advanceCost p e) + nt + 1 ≤
              nb + (costs.sum + costs.length * (16 * (d.stacks p.counter).length + 16) + 1) +
                (16 * (d.stacks p.counter).length + 16) := by omega
          _ = nb + costs.sum + (costs.length + 1) *
                (16 * (d.stacks p.counter).length + 16) + 1 := by ring

/-- Every total callback satisfying its invariant has a measured loop trace.
The induction is on the value of the stack data, not on the finite control. -/
theorem visits_exists (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ)
    (stable : FrameStable p I) (spec : BodySpec p body I cost) (fuel : ℕ) :
    ∀ i d, value (d.stacks p.counter) = fuel → d.stacks p.scratch = [] →
      d.regs (p.register 2) = !(isZero (d.stacks p.counter)) → I i d →
      ∃ costs n e, Visits p body costs n d e ∧ I (i + fuel) e ∧
        e.stacks p.scratch = [] ∧ costs.sum ≤ budgetSum cost i fuel := by
  induction fuel with
  | zero =>
      intro i d hv hs hf hi
      have hz : isZero (d.stacks p.counter) = true := (isZero_eq_true_iff _).2 hv
      exact ⟨[], 1, d, .done d (by simpa [hz] using hf) hv,
        by simpa using hi, hs, by simp [budgetSum]⟩
  | succ fuel ih =>
      intro i d hv hs hf hi
      have hp : 0 < value (d.stacks p.counter) := by omega
      have hz : isZero (d.stacks p.counter) = false := (isZero_eq_false_iff _).2 hp
      have hf' : d.regs (p.register 2) = true := by simpa [hz] using hf
      obtain ⟨nb, e, hnb, he, hc, hes, hei⟩ := spec i d hi hs hp
      have hep : 0 < value (e.stacks p.counter) := by simpa only [hc] using hp
      have hn : value ((nextState p e).stacks p.counter) = fuel := by
        rw [nextState_counter, hc]
        have hd := value_decrement hep
        rw [hc, hv] at hd
        omega
      have hni : I (i + 1) (nextState p e) := stable _ _ _ (nextState_outside p e) hei
      obtain ⟨costs, nt, f, ht, hfi, hfs, hbudget⟩ :=
        ih (i + 1) (nextState p e) hn (nextState_scratch ..) (nextState_flag ..) hni
      refine ⟨nb :: costs, (nb + advanceCost p e) + nt + 1, f,
        .step hf' hp he hc hes ht, ?_, hfs, ?_⟩
      · simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using hfi
      · simpa only [List.sum_cons, budgetSum] using Nat.add_le_add hnb hbudget

/-- Complete measured execution, including an explicit record of the actual
callback costs.  The overhead is linear in the count times encoded width. -/
theorem for_correct_measured (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ)
    (stable : FrameStable p I) (spec : BodySpec p body I cost)
    (d : Data R S) (hs : d.stacks p.scratch = []) (hi : I 0 d) :
    ∃ costs n e, StructuredCalls.Eval (forCmd p body) n d e ∧
      (∃ loopSteps, Visits p body costs loopSteps (testResult p d) e ∧
        n = (8 * (d.stacks p.counter).length + 7) + loopSteps) ∧
      costs.length = value (d.stacks p.counter) ∧
      I (value (d.stacks p.counter)) e ∧ value (e.stacks p.counter) = 0 ∧
      (e.stacks p.counter).length = (d.stacks p.counter).length ∧
      e.stacks p.scratch = [] ∧
      costs.sum ≤ budgetSum cost 0 (value (d.stacks p.counter)) ∧
      n ≤ costs.sum + (value (d.stacks p.counter) + 1) *
        (16 * (d.stacks p.counter).length + 16) := by
  have hst := testResult_stacks p d hs
  have hit : I 0 (testResult p d) := stable _ _ _ (testResult_outside p d hs) hi
  obtain ⟨costs, nt, e, ht, hei, hes, hbudget⟩ :=
    visits_exists p body I cost stable spec (value (d.stacks p.counter)) 0
      (testResult p d) (by rw [hst]) (by rw [hst]; exact hs)
      (by rw [testResult_flag, hst]) hit
  rcases ht.bounds with ⟨hlen, hzero, hwidth, htime⟩
  rw [hst] at hlen hwidth htime
  refine ⟨costs, (8 * (d.stacks p.counter).length + 7) + nt, e,
    .seq (test_eval p d hs) ht.eval, ⟨nt, ht, rfl⟩, hlen,
    by simpa using hei, hzero, hwidth, hes, hbudget, ?_⟩
  rw [hlen] at htime
  calc
    8 * (d.stacks p.counter).length + 7 + nt ≤
        costs.sum + value (d.stacks p.counter) *
          (16 * (d.stacks p.counter).length + 16) +
          (16 * (d.stacks p.counter).length + 16) := by omega
    _ = costs.sum + (value (d.stacks p.counter) + 1) *
          (16 * (d.stacks p.counter).length + 16) := by ring

/-- Convenient interface with the sum of user-supplied callback budgets. -/
theorem for_correct (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ)
    (stable : FrameStable p I) (spec : BodySpec p body I cost)
    (d : Data R S) (hs : d.stacks p.scratch = []) (hi : I 0 d) :
    ∃ n e, StructuredCalls.Eval (forCmd p body) n d e ∧
      I (value (d.stacks p.counter)) e ∧ value (e.stacks p.counter) = 0 ∧
      (e.stacks p.counter).length = (d.stacks p.counter).length ∧
      e.stacks p.scratch = [] ∧
      n ≤ budgetSum cost 0 (value (d.stacks p.counter)) +
        (value (d.stacks p.counter) + 1) * (16 * (d.stacks p.counter).length + 16) := by
  obtain ⟨costs, n, e, he, _, _, hei, hz, hw, hs, hb, hn⟩ :=
    for_correct_measured p body I cost stable spec d hs hi
  exact ⟨n, e, he, hei, hz, hw, hs,
    hn.trans (Nat.add_le_add_right hb _)⟩

/-- The control table grows only with the fixed callback program. -/
@[simp] theorem size_forCmd (p : Ports R S) (body : StructuredCalls.Cmd R S) :
    StructuredCalls.size (forCmd p body) = StructuredCalls.size body + 34 := by
  simp [
    StructuredCalls.size, StructuredProgram.size]
  omega

abbrev program (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (inputStack outputStack : Fin S) :
    Program R S (StructuredCalls.size (forCmd p body) + 1) :=
  StructuredCalls.compiled (forCmd p body) inputStack outputStack

end SubexponentialSAT.CounterForPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_CeilingDivisionPrograms
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Ceiling division by fixed finite bit programs

The rounding suffix tests the actual remainder word and increments the actual
quotient word precisely when that remainder is nonzero. Natural division is
used only in the semantic statement of the full routine.
-/

namespace SubexponentialSAT.CeilingDivisionPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram SubexponentialSAT.CounterPrograms

abbrev Data := StructuredProgram.State 8 8

def remainderPorts : CounterForPrograms.Ports 8 8 :=
  ⟨registers, 0, 1, by decide⟩

def quotientPorts : CounterForPrograms.Ports 8 8 :=
  ⟨registers, 7, 1, by decide⟩

abbrev incrementCmd {R S : ℕ} (p : CounterForPrograms.Ports R S) : StructuredCalls.Cmd R S :=
  .call (ProgramLinking.liftProgram (rippleProgram true) p.register
    (CounterForPrograms.stackPorts p))

noncomputable def incrementResult {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (d : StructuredProgram.State R S) : StructuredProgram.State R S :=
  CounterForPrograms.install p d false false (d.regs (p.register 2))
    (ripple true (d.stacks p.counter)) []

theorem increment_eval {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (d : StructuredProgram.State R S) (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (incrementCmd p) (rippleCost true (d.stacks p.counter) + 1)
      d (incrementResult p d) := by
  have h := StructuredCalls.eval_call_lifted (rippleProgram true) p.register
    (CounterForPrograms.stackPorts p) d p.register.injective
    (CounterForPrograms.stackPorts p).injective
    (CounterForPrograms.ripple_local_trace true (d.regs (p.register 0))
      (d.regs (p.register 1)) (d.regs (p.register 2)) (d.stacks p.counter))
  change StructuredCalls.Eval (incrementCmd p) _
    (CounterForPrograms.install p d _ _ _ _ []) (incrementResult p d) at h
  rw [← hs, CounterForPrograms.install_self] at h
  exact h

theorem increment_counter {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (d : StructuredProgram.State R S) :
    (incrementResult p d).stacks p.counter = ripple true (d.stacks p.counter) :=
  CounterForPrograms.install_counter p d _ _ _ _ _

theorem increment_other {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (d : StructuredProgram.State R S) (hs : d.stacks p.scratch = [])
    (j : Fin S) (hc : j ≠ p.counter) :
    (incrementResult p d).stacks j = d.stacks j := by
  by_cases hj : j = p.scratch
  · subst j
    exact (CounterForPrograms.install_scratch p d _ _ _ _ _).trans hs.symm
  · exact CounterForPrograms.install_other_stack p d _ _ _ _ _ j hc hj

abbrev roundCmd : StructuredCalls.Cmd 8 8 :=
  .seq (CounterForPrograms.zeroCmd remainderPorts)
    (.ite 2 (.base .skip) (incrementCmd quotientPorts))

def RoundOutput (d e : Data) : Prop :=
  e.stacks 7 = (if value (d.stacks 0) = 0 then d.stacks 7 else ripple true (d.stacks 7)) ∧
  ∀ j : Fin 8, j ≠ 7 → e.stacks j = d.stacks j

def roundBound (d : Data) : ℕ := 8 * ((d.stacks 0).length + (d.stacks 7).length) + 15

end SubexponentialSAT.CeilingDivisionPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_CounterConversions
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual binary-to-unary conversion

The finite controller consumes a little-endian binary counter on stack 0.
Each positive iteration pushes one true bit onto stack 1. Stack 2 is counter
scratch. The cleanup empties the counter and resets every Boolean register.
The numeric value controls execution through stack instructions only.
-/

namespace SubexponentialSAT.CounterConversions

open BitProgram StructuredProgram StructuredCalls CounterPrograms CounterForPrograms

abbrev Data := StructuredProgram.State 3 3

def ports : CounterForPrograms.Ports 3 3 where
  register := Function.Embedding.refl _
  counter := 0
  scratch := 2
  counter_ne_scratch := by decide

def state (regs : Fin 3 → Bool) (counter output : List Bool) : Data :=
  ⟨regs, ![counter, output, []]⟩

abbrev push (bit : Bool) : StructuredCalls.Cmd 3 3 :=
  .base (.seq (.atom (.set 0 bit)) (.atom (.push 1 0)))

def pushed (bit : Bool) (d : Data) : Data :=
  ⟨Function.update d.regs 0 bit, Function.update d.stacks 1 (bit :: d.stacks 1)⟩

theorem push_eval (bit : Bool) (d : Data) :
    StructuredCalls.Eval (push bit) 2 d (pushed bit d) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 3) bit) d).seq
    (StructuredProgram.Eval.atom (.push (1 : Fin 3) 0) _)
  exact .base (by simpa [pushed, Atom.eval, Atom.instr, State.ofCfg, State.withPC, execInstr] using h)

abbrev clear : StructuredCalls.Cmd 3 3 := .call (StackRoutines.clearProgram 0 0 1)

def cleared (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks 0 []⟩

theorem clear_eval (d : Data) :
    StructuredCalls.Eval clear (2 * (d.stacks 0).length + 3) d (cleared d) :=
  .call _ (ListRegisterProgram.clear_run 0 0 1 d.regs d.stacks)

abbrev reset : StructuredCalls.Cmd 3 3 := .base
  (.seq (.atom (.set 0 false)) (.seq (.atom (.set 1 false)) (.atom (.set 2 false))))

def resetState (d : Data) : Data := ⟨zeroRegs, d.stacks⟩

theorem reset_eval (d : Data) : StructuredCalls.Eval reset 3 d (resetState d) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 3) false) d).seq
    ((StructuredProgram.Eval.atom (.set (1 : Fin 3) false) _).seq
      (StructuredProgram.Eval.atom (.set (2 : Fin 3) false) _))
  apply StructuredCalls.Eval.base
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply CounterForPrograms.data_ext
  · funext i
    fin_cases i <;>
      simp [resetState, zeroRegs, Atom.eval, Atom.instr, State.ofCfg, execInstr]
  · rfl

def outputInvariant (tail : List Bool) (i : ℕ) (d : Data) : Prop :=
  d.stacks 1 = List.replicate i true ++ tail

theorem outputInvariant_stable (tail : List Bool) :
    FrameStable ports (outputInvariant tail) := by
  intro i a b hab hi
  exact (hab 1 (by decide) (by decide)).symm.trans hi

theorem push_spec (tail : List Bool) :
    BodySpec ports (push true) (outputInvariant tail) (fun _ => 2) := by
  intro i d hi hs _
  refine ⟨2, pushed true d, le_rfl, push_eval true d, ?_, ?_, ?_⟩
  · simp [pushed, ports]
  · simpa [pushed, ports] using hs
  · change d.stacks 1 = List.replicate i true ++ tail at hi
    simp [outputInvariant, pushed, List.replicate_succ, hi]

abbrev unaryCmd : StructuredCalls.Cmd 3 3 :=
  .seq (CounterForPrograms.forCmd ports (push true)) (.seq clear reset)

/-- The suffix is arbitrary, which permits both unary strings and terminated
natural-number fields to use the same fixed conversion loop. -/
theorem unary_correct (d : Data) (hs : d.stacks 2 = []) :
    ∃ n, StructuredCalls.Eval unaryCmd n d
      (state zeroRegs [] (List.replicate (value (d.stacks 0)) true ++ d.stacks 1)) ∧
      n ≤ coreBound (d.stacks 0) := by
  obtain ⟨n, e, he, hi, hz, hw, hes, hn⟩ := CounterForPrograms.for_correct
    ports (push true) (outputInvariant (d.stacks 1)) (fun _ => 2)
    (outputInvariant_stable _) (push_spec _) d hs (by simp [outputInvariant])
  have ho : e.stacks 1 = List.replicate (value (d.stacks 0)) true ++ d.stacks 1 := hi
  have hw' : (e.stacks 0).length = (d.stacks 0).length := hw
  have hs' : e.stacks 2 = [] := hes
  have heq : resetState (cleared e) =
      state zeroRegs [] (List.replicate (value (d.stacks 0)) true ++ d.stacks 1) := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext j
      fin_cases j <;> simp [resetState, cleared, state, ho, hs']
  refine ⟨n + ((2 * (e.stacks 0).length + 3) + 3), ?_, ?_⟩
  · rw [← heq]
    exact he.seq ((clear_eval e).seq (reset_eval (cleared e)))
  · have hn' : n ≤ value (d.stacks 0) * 2 +
        (value (d.stacks 0) + 1) * (16 * (d.stacks 0).length + 16) := by
      simpa [ports, budgetSum_const] using hn
    rw [hw']
    dsimp [coreBound]
    omega

theorem unary_eval (regs : Fin 3 → Bool) (bits tail : List Bool) :
    ∃ n, StructuredCalls.Eval unaryCmd n (state regs bits tail)
      (state zeroRegs [] (List.replicate (value bits) true ++ tail)) ∧ n ≤ coreBound bits := by
  simpa [state] using unary_correct (state regs bits tail) rfl

abbrev encodeNatCmd : StructuredCalls.Cmd 3 3 := .seq (push false) unaryCmd

def unaryProgram := StructuredCalls.compiled unaryCmd (0 : Fin 3) 1
def encodeNatProgram := StructuredCalls.compiled encodeNatCmd (0 : Fin 3) 1

theorem unary_runs (regs : Fin 3 → Bool) (bits tail : List Bool) :
    BitProgram.RunsIn unaryProgram (runtimeBound bits)
      ((state regs bits tail).withPC (some unaryProgram.entry))
      ((state zeroRegs [] (List.replicate (value bits) true ++ tail)).withPC none) := by
  obtain ⟨n, he, hn⟩ := unary_eval regs bits tail
  exact ⟨n + 1, by have := coreBound_le bits; omega,
    StructuredCalls.compiled_halt_trace he 0 1⟩

end SubexponentialSAT.CounterConversions

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_CounterPredProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Saturating predecessor by fixed Boolean-stack code

A preserving zero scan guards the verified borrow routine.  Zero words, including
arbitrarily padded zero representations, are retained; positive words are
decremented without increasing their length. The callback-free code is total.
-/

namespace SubexponentialSAT.CounterPredProgram

open BitProgram StructuredProgram CounterPrograms CounterForPrograms

variable {R S : ℕ}

abbrev predCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .seq (zeroCmd p) (.ite (p.register 2) (.base .skip) (decrementCmd p))

noncomputable def predResult (p : Ports R S) (d : Data R S) : Data R S :=
  if isZero (d.stacks p.counter) then zeroResult p d
  else decrementResult p (zeroResult p d)

def predCost (p : Ports R S) (d : Data R S) : ℕ :=
  (8 * (d.stacks p.counter).length + 6) +
    if isZero (d.stacks p.counter) then 1 else rippleCost false (d.stacks p.counter) + 2

@[simp] theorem zeroResult_counter (p : Ports R S) (d : Data R S) :
    (zeroResult p d).stacks p.counter = d.stacks p.counter := by simp [zeroResult]

@[simp] theorem zeroResult_scratch (p : Ports R S) (d : Data R S) :
    (zeroResult p d).stacks p.scratch = [] := by simp [zeroResult]

@[simp] theorem zeroResult_flag (p : Ports R S) (d : Data R S) :
    (zeroResult p d).regs (p.register 2) = isZero (d.stacks p.counter) := by
  simp [zeroResult]

theorem pred_eval (p : Ports R S) (d : Data R S) (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (predCmd p) (predCost p d) d (predResult p d) := by
  cases hz : isZero (d.stacks p.counter) with
  | true =>
      have hf : (zeroResult p d).regs (p.register 2) = true := by simp [hz]
      have hi : StructuredCalls.Eval
          (.ite (p.register 2) (.base .skip) (decrementCmd p)) 1
          (zeroResult p d) (zeroResult p d) :=
        .ite_true hf (.base (.skip _))
      simpa [predCmd, predCost, predResult, hz] using (zero_eval p d hs).seq hi
  | false =>
      have hf : (zeroResult p d).regs (p.register 2) = false := by simp [hz]
      have hd := decrement_eval p (zeroResult p d) (zeroResult_scratch p d)
      have hi : StructuredCalls.Eval
          (.ite (p.register 2) (.base .skip) (decrementCmd p))
          (rippleCost false (d.stacks p.counter) + 2)
          (zeroResult p d) (decrementResult p (zeroResult p d)) := by
        simpa [Nat.add_assoc] using StructuredCalls.Eval.ite_false hf hd
      simpa [predCmd, predCost, predResult, hz] using (zero_eval p d hs).seq hi

@[simp] theorem predResult_counter (p : Ports R S) (d : Data R S) :
    (predResult p d).stacks p.counter =
      if isZero (d.stacks p.counter) then d.stacks p.counter
      else ripple false (d.stacks p.counter) := by
  cases h : isZero (d.stacks p.counter) <;> simp [predResult, h]

@[simp] theorem predResult_scratch (p : Ports R S) (d : Data R S) :
    (predResult p d).stacks p.scratch = [] := by
  cases h : isZero (d.stacks p.counter) <;> simp [predResult, h]

theorem predResult_value (p : Ports R S) (d : Data R S) :
    value ((predResult p d).stacks p.counter) = value (d.stacks p.counter) - 1 := by
  rw [predResult_counter]
  cases hz : isZero (d.stacks p.counter) with
  | true =>
      have hv := (isZero_eq_true_iff _).1 hz
      simp [hv]
  | false =>
      have hv := value_decrement ((isZero_eq_false_iff _).1 hz)
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega

theorem predResult_toNat (p : Ports R S) (d : Data R S) :
    BinaryArithmetic.toNat ((predResult p d).stacks p.counter) =
      BinaryArithmetic.toNat (d.stacks p.counter) - 1 := by
  simpa only [value_eq_toNat] using predResult_value p d

/-- Both branches preserve the raw representation width, even at zero. -/
theorem predResult_length (p : Ports R S) (d : Data R S) :
    ((predResult p d).stacks p.counter).length = (d.stacks p.counter).length := by
  rw [predResult_counter]
  cases hz : isZero (d.stacks p.counter) with
  | true => simp
  | false => simpa using decrement_length ((isZero_eq_false_iff _).1 hz)

theorem predResult_frame (p : Ports R S) (d : Data R S)
    (j : Fin S) (hc : j ≠ p.counter) (hs : j ≠ p.scratch) :
    (predResult p d).stacks j = d.stacks j := by
  cases hz : isZero (d.stacks p.counter) with
  | true =>
      simpa [predResult, hz, zeroResult] using
        install_other_stack p d false false (isZero (d.stacks p.counter))
          (d.stacks p.counter) [] j hc hs
  | false =>
      simp only [predResult, hz, Bool.false_eq_true, ↓reduceIte, decrementResult]
      rw [install_other_stack p (zeroResult p d) _ _ _ _ _ j hc hs]
      exact install_other_stack p d _ _ _ _ _ j hc hs

/-- The bound includes the compiled program's final halt instruction. -/
theorem predCost_le (p : Ports R S) (d : Data R S) :
    predCost p d + 1 ≤ 20 * ((d.stacks p.counter).length + 1) := by
  have hr := rippleCost_le false (d.stacks p.counter)
  cases h : isZero (d.stacks p.counter) <;> simp [predCost, h] <;> omega

/-- With empty incoming scratch, the counter is the only changed stack. -/
theorem predResult_stacks (p : Ports R S) (d : Data R S) (hs : d.stacks p.scratch = []) :
    (predResult p d).stacks =
      Function.update d.stacks p.counter ((predResult p d).stacks p.counter) := by
  funext j
  by_cases hc : j = p.counter
  · subst j
    simp
  · by_cases hscratch : j = p.scratch
    · subst j
      simp [Function.update_of_ne hc, hs]
    · rw [Function.update_of_ne hc]
      exact predResult_frame p d j hc hscratch

/-- Assembly interface exposing the changed word and unconstrained registers. -/
theorem pred_correct (p : Ports R S) (d : Data R S) (hs : d.stacks p.scratch = []) :
    ∃ (n : ℕ) (regs : Fin R → Bool) (word : List Bool),
      n ≤ 20 * ((d.stacks p.counter).length + 1) ∧
      StructuredCalls.Eval (predCmd p) n d
        ⟨regs, Function.update d.stacks p.counter word⟩ ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (d.stacks p.counter) - 1 ∧
      word.length ≤ (d.stacks p.counter).length := by
  refine ⟨predCost p d, (predResult p d).regs, (predResult p d).stacks p.counter,
    ?_, ?_, predResult_toNat p d, (predResult_length p d).le⟩
  · have h := predCost_le p d
    omega
  · have heq : predResult p d =
        ⟨(predResult p d).regs,
          Function.update d.stacks p.counter ((predResult p d).stacks p.counter)⟩ :=
      CounterForPrograms.data_ext rfl (predResult_stacks p d hs)
    rw [← heq]
    exact pred_eval p d hs

@[simp] theorem size_predCmd (p : Ports R S) : StructuredCalls.size (predCmd p) = 22 := by
  simp [ StructuredCalls.size, StructuredProgram.size]

end SubexponentialSAT.CounterPredProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFMembership
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Encoded CNF membership building blocks

Fixed ports: source 0, reversed current payload 1, preserved reversed query 2,
query copy 3, and temporary stack 4. Register 4 is the answer; registers 5 and
6 are the outer-list tag and presence flag. Registers 0--3 are work bits.
-/

namespace SubexponentialSAT.ExecCNFMembership

open SubexponentialSAT.BitProgram
open SubexponentialSAT.StructuredCalls

theorem clear_eval (port : Fin 5) (d : Data) :
    Eval (clear port) (2 * (d.stacks port).length + 3) d (cleared port d) := by
  have h := StackRoutines.clearProgram_trace (r := 7) (s := 5) port 0 1 d.regs d.stacks
  have hh : step (clearProgram port)
      (StackRoutines.clearResult 2 port 0 1 d.regs d.stacks) =
      some ((cleared port d).withPC none) := by
    simp [step, StackRoutines.clearResult,
      cleared, StructuredProgram.State.withPC, execInstr]
  apply Eval.call
  change Computation.Trace (step (clearProgram port)) (2 * (d.stacks port).length + 3)
    (d.withPC (some 0)) ((cleared port d).withPC none)
  exact h.trans (.cons hh (.refl _))

end SubexponentialSAT.ExecCNFMembership

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFSubset
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual encoded clause subset testing

The fixed program uses ten Boolean registers and eight Boolean stacks. The
source clause is scanned destructively on stack 0. Stack 2 preserves the entire
encoded target clause. All comparisons use the proved encoded membership
program, after a real preserving copy of the target.
-/
namespace SubexponentialSAT.ExecCNFSubset
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- A single finite instruction table implements all runtime subset instances. -/
def subsetProgram := compiled subset 0 1

end SubexponentialSAT.ExecCNFSubset

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFTupleEnumeration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual overflow-controlled enumeration of framed binary tuples

The callback is fixed executable code. Every iteration invokes it and then
invokes the concrete framed odometer, including the final overflow increment.
The number and widths of records are never part of finite control.
-/

namespace SubexponentialSAT.ExecCNFTupleEnumeration

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram
open ExecCNFTupleOdometer

abbrev Ports := CounterForPrograms.Ports
abbrev Data := StructuredProgram.State

variable {R S : ℕ}

noncomputable def incrementResult (p : Ports R S) (d : Data R S)
    (words : List (List Bool)) : Data R S :=
  CounterForPrograms.install p d false false (bumpWords words).1
    (Encoding.encodeList id (bumpWords words).2) []

end SubexponentialSAT.ExecCNFTupleEnumeration

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseDedupProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed program for last-occurrence clause deduplication

The current clause is compared with the unread suffix using actual set
equivalence of its literal records. The suffix copy is cleared after each
query, and the final record reversal restores the prescribed clause order.
-/

namespace SubexponentialSAT.ExecClauseDedupProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)
open ExecClauseFiltersProgram (Regs Data state reset flags)

def Ready (d : Data) : Prop := ∀ i : Fin 16, i ≠ 13 → d.stacks i = []

end SubexponentialSAT.ExecClauseDedupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularRingPrograms
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.ModularRingPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ProgramLinking SubexponentialSAT.StackRoutines
open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularDivisionPrograms

/-! ## Restore a runtime-specified output width -/

open SubexponentialSAT.ModularPrograms

theorem normalize_correct (regs : Fin 8 → Bool) (input shape modulus : List Bool) :
    ∃ finalRegs,
      RunsIn normalizeProgram (7 * shape.length + 2 * input.length + 9)
        ⟨some 0, regs, normalizationState input shape [] modulus⟩
        ⟨none, finalRegs, normalizationState (padTo shape input) [] [] modulus⟩ := by
  obtain ⟨r1, h1⟩ := normalizationPrefix_correct regs input shape modulus
  let r2 := readRegs r1 1 3 none
  have tc := clearProgram_trace (0 : Fin 8) (1 : Fin 8) 3 r1
    (normalizationState (input.drop shape.length) [] (padTo shape input).reverse modulus)
  have hc := halt_after_trace normalizationClearProgram tc (2 : Fin 3) rfl rfl
  simp only [clearResult, normalization_clear] at hc
  have h2 : Trace normalizationClearProgram (2 * (input.drop shape.length).length + 3)
      ⟨some 0, r1, normalizationState (input.drop shape.length) [] (padTo shape input).reverse modulus⟩
      ⟨none, r2, normalizationState [] [] (padTo shape input).reverse modulus⟩ := by
    simpa [r2, normalizationState, Nat.add_assoc] using hc
  have tm := transferProgram_trace (2 : Fin 8) 0 (1 : Fin 8) 3
    (by decide) (by decide) r2
    (normalizationState [] [] (padTo shape input).reverse modulus)
  have hm := halt_after_trace normalizationMoveProgram tm (3 : Fin 4) rfl rfl
  simp only [transferResult, normalization_move] at hm
  have h3 : Trace normalizationMoveProgram (3 * shape.length + 3)
      ⟨some 0, r2, normalizationState [] [] (padTo shape input).reverse modulus⟩
      ⟨none, r2, normalizationState (padTo shape input) [] [] modulus⟩ := by
    simpa [r2, readRegs_reset, normalizationState, padTo_length, Nat.add_assoc] using hm
  have h12 := sequence_runs normalizationPrefixProgram normalizationClearProgram _ _ _ _ _ _
    ⟨_, le_rfl, h1⟩ ⟨_, le_rfl, h2⟩
  have ht := sequence_runs _ normalizationMoveProgram _ _ _ _ _ _ h12 ⟨_, le_rfl, h3⟩
  refine ⟨r2, ht.mono ?_⟩
  simp only [List.length_drop]
  omega

/-- Generic measured composition used below with the concrete addition and
multiplication programs. The input's shape is copied by the program itself. -/
theorem canonical_execute {l : ℕ} (p : Program 8 7 l)
    (regs finalRegs : Fin 8 → Bool) (xs ys modulus output : List Bool) (bound : ℕ)
    (hr : RunsIn p bound
      ⟨some p.entry, readRegs regs 1 3 none, scalarInput xs ys modulus⟩
      ⟨none, finalRegs, resting output modulus []⟩) :
    ∃ rf,
      RunsIn (canonicalProgram p)
        (bound + 14 * xs.length + 2 * output.length + 14)
        ⟨some (canonicalProgram p).entry, regs, extendSeven (scalarInput xs ys modulus) []⟩
        ⟨none, rf, extendSeven (resting (padTo xs output) modulus []) []⟩ := by
  have h1 := shapeCopy_correct regs xs ys modulus
  have hw := liftProgram_runsIn p id sevenPorts
    (⟨none, regs, extendSeven (resting [] modulus []) xs⟩ : Cfg 8 8 l)
    Function.injective_id sevenPorts_injective hr
  rw [embed_seven, embed_seven] at hw
  obtain ⟨r3, h3⟩ := normalize_correct finalRegs output xs modulus
  have h12 := sequence_runs shapeCopyProgram (liftProgram p id sevenPorts) _ _ _ _ _ _
    ⟨_, le_rfl, h1⟩ hw
  have ht := sequence_runs _ normalizeProgram _ _ _ _ _ _ h12 h3
  refine ⟨r3, ?_⟩
  convert ht using 1
  · omega
  · rfl

theorem wordAdd_value (regs : Fin 8 → Bool) (xs ys modulus : List Bool) (B : ℕ)
    (hx : xs.length = B) (hy : ys.length = B) (hmLength : modulus.length ≤ B + 1)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ finalRegs output,
      RunsIn wordAddProgram (6000 * (B + 1) ^ 2)
        ⟨some wordAddProgram.entry, regs, extendSeven (scalarInput xs ys modulus) []⟩
        ⟨none, finalRegs, extendSeven (resting output modulus []) []⟩ ∧
      output.length = B ∧
      BinaryArithmetic.toNat output = (BinaryArithmetic.toNat xs + BinaryArithmetic.toNat ys) % BinaryArithmetic.toNat modulus := by
  obtain ⟨r1, out, hr, hlen, hv⟩ :=
    addMod_value (readRegs regs 1 3 none) xs ys modulus hm
  obtain ⟨rf, ht⟩ := canonical_execute addModProgram regs r1 xs ys modulus out
    (600 * (modulus.length + xs.length + ys.length + 1) ^ 2) hr
  refine ⟨rf, padTo xs out, ht.mono ?_, ?_, ?_⟩
  · exact word_cost_bound _ _ _ _ _ hx hy hmLength hlen
  · simpa [hx] using padTo_length xs out
  · rw [padTo_value_of_lt, hv]
    rw [hx, hv]
    exact (Nat.mod_lt _ hm).trans_le hcapacity

end SubexponentialSAT.ModularRingPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace Selector

abbrev Code := Cmd 24 24

end Selector

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScalarMachine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Exact machine refinement of the prepared scalar callbacks

The program output agrees as a Boolean list with the callback output, not
only modulo the coefficient modulus. Fixed width and binary-value uniqueness
give the final identification. The program tables are independent of p and mu.
-/

namespace SubexponentialSAT.SubexpScalarMachine

open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.BitProgram SubexponentialSAT.ModularRingPrograms SubexponentialSAT.ModularDivisionPrograms

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

theorem wordAdd_run (regs : Fin 8 → Bool) (x y : Word (baseWidth p μ)) :
    ∃ finalRegs,
      RunsIn wordAddProgram (6000 * (baseWidth p μ + 1)^2)
        ⟨some wordAddProgram.entry, regs, extendSeven (scalarInput x.val y.val M.bits) []⟩
        ⟨none, finalRegs,
          extendSeven (resting (SubexpPreparedQuartic.wordAdd p μ M x y).1.val M.bits []) []⟩ := by
  obtain ⟨rf, output, hr, hlen, hv⟩ := wordAdd_value regs x.val y.val M.bits
    (baseWidth p μ) x.property y.property M.length_le
    (modulus_pos p μ M) (modulus_capacity p μ M)
  have hvalue : BinaryArithmetic.toNat (SubexpPreparedQuartic.wordAdd p μ M x y).1.val =
      (BinaryArithmetic.toNat x.val + BinaryArithmetic.toNat y.val) % BinaryArithmetic.toNat M.bits :=
    addBaseRun_value _ _ _ _ (modulus_pos p μ M) (modulus_capacity p μ M)
  have heq : output = (SubexpPreparedQuartic.wordAdd p μ M x y).1.val :=
    SubexpModulusConstruction.bits_eq_of_length_of_value _ _
      (hlen.trans (SubexpPreparedQuartic.wordAdd p μ M x y).1.property.symm)
      (hv.trans hvalue.symm)
  exact ⟨rf, heq ▸ hr⟩

end SubexponentialSAT.SubexpScalarMachine

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScanPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete stack operations used by the serialized coefficient scanner. -/

namespace SubexponentialSAT.SubexpScanPrimitives

open BitProgram StructuredCalls

theorem embedState_eq {r s R S : ℕ}
    (reg : Fin r → Fin R) (stack : Fin s → Fin S)
    (hreg : Function.Injective reg) (hstack : Function.Injective stack)
    (frame target : State R S) (source : State r s)
    (hr : ∀ i, target.regs (reg i) = source.regs i)
    (hs : ∀ i, target.stacks (stack i) = source.stacks i)
    (hfr : ∀ j, (¬ ∃ i, reg i = j) → target.regs j = frame.regs j)
    (hfs : ∀ j, (¬ ∃ i, stack i = j) → target.stacks j = frame.stacks j) :
    embedState reg stack frame source = target := by
  apply state_ext
  · funext j
    by_cases hj : ∃ i, reg i = j
    · obtain ⟨i, rfl⟩ := hj
      exact (embedState_register reg stack frame source hreg i).trans (hr i).symm
    · exact (embedState_register_frame reg stack frame source j hj).trans (hfr j hj).symm
  · funext j
    by_cases hj : ∃ i, stack i = j
    · obtain ⟨i, rfl⟩ := hj
      exact (embedState_stack reg stack frame source hstack i).trans (hs i).symm
    · exact (embedState_stack_frame reg stack frame source j hj).trans (hfs j hj).symm

end SubexponentialSAT.SubexpScanPrimitives

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFlatAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Streaming addition of serialized quartic coefficients

There are four calls to the actual modular-word machine. Width is supplied as
stack data. No instruction table is generated from a coefficient or its width.
-/

namespace SubexponentialSAT.SubexpFlatAdd

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

theorem addScalar_eval (regs : Fin 8 → Bool) (x y : Word (baseWidth p μ))
    (left right width packed : List Bool) (frame : Fin 6 → List Bool) :
    ∃ n ≤ 6000 * (baseWidth p μ + 1)^2, ∃ regs',
      Eval addScalar n
        (state regs x.val y.val M.bits left right width [] [] packed frame)
        (state regs' (SubexpPreparedQuartic.wordAdd p μ M x y).1.val []
          M.bits left right width [] [] packed frame) := by
  obtain ⟨regs', n, hn, ht⟩ := SubexpScalarMachine.wordAdd_run p μ M regs x y
  let a : State 8 8 := ⟨regs, ModularRingPrograms.extendSeven
    (ModularRingPrograms.scalarInput x.val y.val M.bits) []⟩
  let b : State 8 8 := ⟨regs', ModularRingPrograms.extendSeven
    (ModularDivisionPrograms.resting (SubexpPreparedQuartic.wordAdd p μ M x y).1.val
      M.bits []) []⟩
  let d := state regs x.val y.val M.bits left right width [] [] packed frame
  have ha : embedState id scalarPorts d a = d := by
    apply embedState_eq _ _ Function.injective_id scalarPorts_injective
    · intro i; rfl
    · intro i; fin_cases i <;> rfl
    · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
    · intros; rfl
  have hb : embedState id scalarPorts d b =
      state regs' (SubexpPreparedQuartic.wordAdd p μ M x y).1.val []
        M.bits left right width [] [] packed frame := by
    apply embedState_eq _ _ Function.injective_id scalarPorts_injective
    · intro i; rfl
    · intro i; fin_cases i <;> rfl
    · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
    · intro j hj
      fin_cases j <;> try rfl
      · exact False.elim (hj ⟨0,rfl⟩)
      · exact False.elim (hj ⟨1,rfl⟩)
  have hr := eval_call_lifted ModularRingPrograms.wordAddProgram id scalarPorts d
    Function.injective_id scalarPorts_injective (a := a) (b := b) ht
  exact ⟨n, hn, regs', by simpa only [ha,hb,addScalar] using hr⟩

end SubexponentialSAT.SubexpFlatAdd

end OAI.Algorithms
end


