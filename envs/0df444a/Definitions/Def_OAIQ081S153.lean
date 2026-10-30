-- Prove2me | Definitions.Def_OAIQ081S153
-- name    : OAIQ081S153
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:56:32.499969+00:00
-- url     : https://prove2.me/theorems/0596ecf5-f20d-4183-8d3c-637903c8e7d6
-- title:
--   Definitions bundle OAIQ081S153 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 48 declarations of OpenAI's Lean: 34 definitions and 14 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.finalModel`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.fullBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.fullCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.initialModel`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.middleModel`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.prefixCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.prefixEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.prefixModel`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.runtimeBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.setupEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.suffixCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.unaryModelBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues.Constants`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues.PowerBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues.PowerBounds`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues.base`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues.envelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.EarlyThreshold.code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.EarlyThreshold.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.EarlyThreshold.inputModel`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.EarlyThreshold.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.EarlyThreshold.sizeBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.preparation`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.loop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.pass`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.guardedModel`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.numberBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.producerBudget`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_CRTLocalProgramNativeInverse`, `SubexponentialSAT_SqrtLog_CodeParametersProgramBudget`, `SubexponentialSAT_SqrtLog_CodeParametersProgramUnary`, `SubexponentialSAT_SqrtLog_CostAssemblyParameterValues`, `SubexponentialSAT_SqrtLog_CostAssemblyParameterValuesBasic`, `SubexponentialSAT_SqrtLog_CostAssemblyParameterValuesLayout`, `SubexponentialSAT_SqrtLog_CostAssemblySerialization`, `SubexponentialSAT_SqrtLog_EarlyThreshold`, `SubexponentialSAT_SqrtLog_HornerProgramServices`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgram`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarMachine`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarRun`, `SubexponentialSAT_SqrtLog_LayoutBinomialProgramCell`, `SubexponentialSAT_SqrtLog_LeafParametersProgramBanked`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_RingScanService`, `SubexponentialSAT_SqrtLog_RingScanServiceLifts`, `SubexponentialSAT_SqrtLog_RingTripleBridge`, `SubexponentialSAT_UnaryForPrograms`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S138`, `OAIQ081S139` and `OAIQ081S140` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S166`, `OAIQ081S167`, `OAIQ081S168`, `OAIQ081S169`, `OAIQ081S170` and `OAIQ081S172`; the statement `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues.serialized_values_of_fourth_power`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Native.command_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues.serialized_values_of_fourth_power`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair.command_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.scan_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.scalePhase_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.step_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.middle_run`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S138
import Definitions.Def_OAIQ081S139
import Definitions.Def_OAIQ081S140

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

/-- Explicit observations of the actual callbacks, with a sum of their costs. -/
theorem for_correct_measured (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ)
    (stable : FrameStable p I) (spec : BodySpec p body I cost)
    (d : Data R S) (hi : I 0 d) :
    ∃ costs n e, Visits p body costs n d e ∧
      StructuredCalls.Eval (forCmd p body) n d e ∧
      costs.length = (d.stacks p.counter).length ∧
      I (d.stacks p.counter).length e ∧ e.stacks p.counter = [] ∧
      n = costs.sum + 2 * costs.length + 2 ∧
      costs.sum ≤ budgetSum cost 0 (d.stacks p.counter).length := by
  obtain ⟨costs, n, e, hv, hei, hb⟩ :=
    visits_exists p body I cost stable spec (d.stacks p.counter) 0 d rfl hi
  rcases hv.bounds with ⟨hlen, he, hn⟩
  exact ⟨costs, n, e, hv, hv.eval, hlen, by simpa using hei, he, hn, hb⟩

theorem for_correct (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ)
    (stable : FrameStable p I) (spec : BodySpec p body I cost)
    (d : Data R S) (hi : I 0 d) :
    ∃ n e, StructuredCalls.Eval (forCmd p body) n d e ∧
      I (d.stacks p.counter).length e ∧ e.stacks p.counter = [] ∧
      n ≤ budgetSum cost 0 (d.stacks p.counter).length +
        2 * (d.stacks p.counter).length + 2 := by
  obtain ⟨costs, n, e, _, he, hlen, hei, hempty, hn, hb⟩ :=
    for_correct_measured p body I cost stable spec d hi
  refine ⟨n, e, he, hei, hempty, ?_⟩
  rw [hn, hlen]
  omega

end SubexponentialSAT.UnaryForPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The input/output of the dynamic expander is exactly the k-major table and
triple stream used by the native ring contraction. `List.ofFn` below describes
the serialized input and theorem; the fixed program builds the repeated stream
by actual counted loops and paid source copies. -/
namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpQuarticRing

theorem triple_encoding {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B)
    (x y : RingProgram.Code (Word B) d) :
    allTripleBits (matrices table x y) = RingScan.blockBits (blocks table x y) := by
  rw [allTripleBits_eq_blocks]
  simp [matrices, blocks, List.map_ofFn, matrixTriples_coordinateRows, Function.comp_def]

/-- Native expansion on the exact finite-dimensional ring table. Degree d is
runtime data, and every occurrence of x_i/y_j is physically copied/scanned. -/
theorem expansion_eval {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B)
    (x y : RingProgram.Code (Word B) d) (degree width : List Bool)
    (regs : Fin 2 → Bool) (hd : degree.length = d) (hw : width.length = B) :
    ∃ n ≤ expandBudget B d, ∃ regs',
      Eval expand n
        (state regs {(layout (RingProgram.flat x) (RingProgram.flat y) degree width) with table := tableEncoding table})
        (state regs' {(layout (RingProgram.flat x) (RingProgram.flat y) degree width) with xs := RingScan.blockBits (blocks table x y)}) := by
  obtain ⟨n, hn, regs', ht⟩ := expand_eval B
    (layout (RingProgram.flat x) (RingProgram.flat y) degree width) (matrices table x y)
    regs (by simpa [matrices, layout] using hd) (matrices_fit table x y degree width hd) hw
  refine ⟨n, by simpa [layout, hd] using hn, regs', ?_⟩
  simpa only [table_encoding, triple_encoding, layout] using ht

theorem expansion_native {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B)
    (x y : RingProgram.Code (Word B) d) (degree width : List Bool)
    (regs : Fin 2 → Bool) (hd : degree.length = d) (hw : width.length = B) :
    ∃ regs', RunsIn program (expandBudget B d + 1)
      ((state regs {(layout (RingProgram.flat x) (RingProgram.flat y) degree width) with table := tableEncoding table}).withPC
        (some program.entry))
      ((state regs' {(layout (RingProgram.flat x) (RingProgram.flat y) degree width) with xs := RingScan.blockBits (blocks table x y)}).withPC none) := by
  obtain ⟨n, hn, regs', ht⟩ := expansion_eval table x y degree width regs hd hw
  exact ⟨regs', n + 1, Nat.add_le_add_right hn 1, compiled_halt_trace ht 2 4⟩

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanServiceLifts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem serviceExpand_eval {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B)
    (x y : RingProgram.Code (Word B) d) (regs : Fin 8 → Bool)
    (modulus result degree width zero inner outer : List Bool)
    (hd : degree.length = d) (hw : width.length = B) :
    ∃ n ≤ RingTriple.expandBudget B d + 1, ∃ rf,
      Eval serviceExpand n
        (serviceWorkState regs ⟨modulus, result, RingProgram.flat x, RingProgram.flat y,
          degree, width, zero, RingTriple.tableEncoding table, outer, inner,
          RingTriple.tableEncoding table, [], []⟩)
        (serviceWorkState rf ⟨modulus, result, RingProgram.flat x, RingProgram.flat y,
          degree, width, zero, RingTriple.tableEncoding table, outer, inner,
          [], [], blockBits (multiplicationBlocks table x y)⟩) := by
  obtain ⟨rf, n, hn, ht⟩ := RingTriple.expansion_native table x y degree width ![regs 1, regs 3] hd hw
  let s : ServiceStore := ⟨modulus, result, RingProgram.flat x, RingProgram.flat y,
    degree, width, zero, RingTriple.tableEncoding table, outer, inner,
    RingTriple.tableEncoding table, [], []⟩
  let a := RingTriple.state (![regs 1, regs 3] : Fin 2 → Bool)
    {(RingTriple.layout s.x s.y s.degree s.width) with table := s.tableWork, xs := []}
  let b := RingTriple.state rf
    {(RingTriple.layout s.x s.y s.degree s.width) with table := [], xs := blockBits (multiplicationBlocks table x y)}
  have he := eval_call_lifted RingTriple.program loadRegisters serviceExpandPorts
    (serviceWorkState regs s) loadRegisters_injective serviceExpandPorts_injective
    (a := a) (b := b) ht
  dsimp only [a, b] at he
  rw [embed_expand_service, embed_expand_service] at he
  refine ⟨n, hn, Function.update (Function.update regs 1 (rf 0)) 3 (rf 1), ?_⟩
  simpa only [s, Matrix.cons_val_zero, Matrix.cons_val_one, Function.update_eq_self] using he


end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanService
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed native service for arbitrary-degree coefficient-ring products. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- Complete native multiplication, including table copying, paid triple
expansion, both unary counters, scalar contraction, and all cleanup. The
cached table is preserved; its one-time construction is a separate service. -/
theorem serviceMul_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (x y : RingProgram.Code (Word (baseWidth p t)) d) (regs : Fin 8 → Bool)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t) :
    ∃ n ≤ serviceMulBudget (baseWidth p t) d, ∃ rf, Eval serviceMul n
      (serviceState regs M.bits [] (RingProgram.flat x) (RingProgram.flat y) degree width
        cache.zero.val (RingTriple.tableEncoding table))
      (serviceState rf M.bits
        (RingProgram.flat (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1)
        [] [] [] width cache.zero.val (RingTriple.tableEncoding table)) := by
  let initial : ServiceStore := ⟨M.bits, [], RingProgram.flat x, RingProgram.flat y,
    degree, width, cache.zero.val, RingTriple.tableEncoding table, [], [], [], [], []⟩
  let expanded : ServiceStore := {initial with stream := blockBits (multiplicationBlocks table x y)}
  let routed : ServiceStore := {initial with x := [], y := expanded.stream}
  let counted : ServiceStore := {routed with inner := repeatCount degree degree.length}
  let output : ServiceStore := ⟨M.bits,
    RingProgram.flat (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1,
    [], [], [], width, cache.zero.val, RingTriple.tableEncoding table, [], counted.inner, [], [], []⟩
  have h1 := servicePrepare_eval regs initial
  obtain ⟨n, hn, r1, h2⟩ := serviceExpand_eval table x y (readRegs regs 1 3 none)
    M.bits [] degree width cache.zero.val [] [] hd hw
  have h3 := serviceRoute_eval r1 expanded
  obtain ⟨r2, h4⟩ := serviceCount_eval (readRegs r1 1 3 none) routed
  have h5 := serviceDegree_eval r2 counted
  have hinner : counted.inner.length = d*d := by simp [counted, hd]
  obtain ⟨m, hm, r3, h6⟩ := serviceContract_eval p t M cache hz table x y
    (readRegs r2 1 3 none) width degree.reverse counted.inner (by simpa using hd) hinner hw
  have h7 := serviceFinish_eval r3 output
  have he := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7)))))
  refine ⟨_, ?_, readRegs r3 1 3 none, he⟩
  simp only [initial, expanded, routed, counted, output, hd, RingProgram.flat_length,
    repeatCount_length]
  unfold serviceMulBudget
  rw [RingTriple.tableEncoding_length, multiplicationBits_length]
  nlinarith

theorem serviceMulProgram_run (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (x y : RingProgram.Code (Word (baseWidth p t)) d) (regs : Fin 8 → Bool)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t) :
    ∃ rf, RunsIn serviceMulProgram (serviceMulBudget (baseWidth p t) d+1)
      ((serviceState regs M.bits [] (RingProgram.flat x) (RingProgram.flat y) degree width
        cache.zero.val (RingTriple.tableEncoding table)).withPC (some serviceMulProgram.entry))
      ((serviceState rf M.bits
        (RingProgram.flat (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1)
        [] [] [] width cache.zero.val (RingTriple.tableEncoding table)).withPC none) := by
  obtain ⟨n, hn, rf, ht⟩ := serviceMul_eval p t M cache hz table x y regs degree width hd hw
  exact ⟨rf, n+1, Nat.add_le_add_right hn 1, compiled_halt_trace ht 8 0⟩


end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgramServices
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fully discharged native binary services for arbitrary coefficient-vector
length. Shared by Horner, local CRT and dense polynomial services. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram.Services

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open CRTLocalProgram (ServiceSpec)

theorem multiply_native_spec (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (base : Store)
    (h : NativeReady p t M cache table base) :
    ReconstructionProgram.RingAdapter.NativeSpec base (RingProgram.flat (d := d) (B := baseWidth p t)) RingScan.serviceMulProgram
      (fun x y => (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1)
      (RingScan.serviceMulBudget (baseWidth p t) d + 1) := by
  intro regs x y
  obtain ⟨rf, hr⟩ := RingScan.serviceMulProgram_run p t M cache hz table x y regs
    (base 204) (base 202) h.degree h.width
  refine ⟨rf, ?_⟩
  simpa only [ReconstructionProgram.RingAdapter.initialNative, ReconstructionProgram.RingAdapter.finalNative, nativeStacks_eq, h.modulus, h.zero, h.table,
    RingScan.serviceState, RingScan.serviceWorkState] using hr

theorem multiply_spec (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (base : Store)
    (h : NativeReady p t M cache table base) :
    ServiceSpec base (RingProgram.flat (d := d) (B := baseWidth p t)) multiply
      (fun x y => (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1)
      (mulBudget (baseWidth p t) d) := by
  have hs := ReconstructionProgram.RingAdapter.command_spec base (RingProgram.flat (d := d) (B := baseWidth p t)) RingScan.serviceMulProgram
    (fun x y => (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1)
    (RingScan.serviceMulBudget (baseWidth p t) d + 1) (d * baseWidth p t) h.workspace
    (multiply_native_spec p t M cache hz table base h) (fun a => (RingProgram.flat_length a).le)
  convert hs using 1 <;> simp only [multiply, mulBudget, h.degree] ; omega

end SubexponentialSAT.SqrtLog.HornerProgram.Services

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramNativeInverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A standalone native inverse of a node difference. The exponent is the
residue-field cardinality minus two; the separate repair loop has length t. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram.NativeInverse
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing

theorem command_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val < 3^t)
    (s : Store)
    (hready : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache) s)
    (theta other minusOne : RingProgram.Code (RingProgram.ScalarCode 3 t) d)
    (htheta : s 213 = RingProgram.flat theta) (hother : s 218 = RingProgram.flat other)
    (hzero : s 104 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hone : s 207 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (hminus : s 211 = RingProgram.flat minusOne)
    (hq : (s 209).length = 3^d-2) (ht : (s 212).length = t)
    (hclean : ∀ i ∈ work, s i = []) :
    ExecutesIn command (budget t d) s
      (Function.update s 208 (RingProgram.flat (value t a M cache theta other minusOne))) := by
  have h := differenceInverseCommand_run s RingProgram.flat
    HornerProgram.Services.multiply HornerProgram.Services.add
    (fun x y => ((RingProgram.modelProgram t a M cache).mulRun x y).1)
    (fun x y => ((RingProgram.modelProgram t a M cache).addRun x y).1)
    (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
    (HornerProgram.Services.addBudget (baseWidth 3 t) d) (d*baseWidth 3 t)
    (HornerProgram.Services.multiply_spec 3 t M cache hz (HornerProgram.modelTable t a M cache) s hready)
    (HornerProgram.Services.add_spec 3 t M cache (HornerProgram.modelTable t a M cache) s hready)
    (fun x => (RingProgram.flat_length x).le) s theta other
    (RingProgram.modelProgram t a M cache).zeroRun.1
    (RingProgram.modelProgram t a M cache).oneRun.1 minusOne (lowFrame_refl s)
    htheta hother hzero hone hminus hready.workspace.1
    (hclean 205 (by simp [work])) (hclean 208 (by simp [work]))
    (hclean 219 (by simp [work])) (hclean 220 (by simp [work]))
    (hclean 222 (by simp [work])) (hclean 240 (by simp [work]))
    (hclean 241 (by simp [work])) (hclean 244 (by simp [work]))
    (hclean 245 (by simp [work])) (hclean 246 (by simp [work]))
  simpa only [command, budget, value, hq, ht] using h

end SubexponentialSAT.SqrtLog.CRTLocalProgram.NativeInverse

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native runtime leaf parameter production, integer guards, and paid setup.
The former composition modules are import-only compatibility shims. -/


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramBankRoots -/

/-! A fixed ten-comparison bit guard. All operands are runtime binary words.
This module states their data relation separately from parameter production. -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

@[simp] theorem scaleBound_append (B : ℕ) (xs ys : List Instr) (m : Model) :
    ScaleBound B (xs++ys) m ↔ ScaleBound B xs m ∧ ScaleBound B ys (result xs m) := by
  induction xs generalizing m with
  | nil => simp [ScaleBound,result]
  | cons i xs ih => simp [ScaleBound,result,ih,and_assoc]

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayoutCost -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

/-- Input t is at33 and qE at35. The two derived metadata words are
qE−2 at44 and B=2t at45. No other numeric table entry changes. -/
def code : List Instr := [
  .clear 44, .copy 35 44 (by decide), .pred 44, .pred 44,
  .clear 45, .add 33 33 45 (by decide) (by decide)]

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeParametersProgramUnary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Production sparse-code parameter program. Fixed arithmetic, minimum,
metadata identities and unary materialization are checked in one unit. -/

/-! Arithmetic identities used by the physical sparse-code parameter program. -/


/-! A concrete minimum operation used between two straight-line arithmetic
stages. The comparison consumes only two explicitly copied temporary words. -/


/-! Fixed finite arithmetic instructions for all sparse-code search metadata.
Ports 0 and 1 contain m and B. Outputs: q=5, D=9, t=11, tD=12,
local distance=15, r=18, rD=19, N=21. Unary conversion is a separate,
explicitly paid stage. -/
namespace SubexponentialSAT.SqrtLog.CodeParametersProgram

open BitProgram StructuredCalls BinaryArithmetic LeafParametersProgram.Bank
open LeafParametersProgram.Circuit

def prefixCode : List Instr := [
  .copy 0 2 (by decide), .logSucc 2,
  .load 3 ([false,false,false,true,false,false,true,true] : List Bool),
  .mul 1 2 4 (by decide) (by decide),
  .mul 3 4 5 (by decide) (by decide),
  .mul 5 5 6 (by decide) (by decide),
  .load 7 ([false,false,false,true] : List Bool),
  .mul 7 6 22 (by decide) (by decide),
  .mul 22 2 8 (by decide) (by decide)]

def suffixCode : List Instr := [
  .mul 7 1 10 (by decide) (by decide),
  .quot 9 10 11 (by decide) (by decide), .addConst 11 1,
  .mul 11 9 12 (by decide) (by decide),
  .load 13 ([false,false,true,false,false,true,true] : List Bool),
  .mul 13 4 14 (by decide) (by decide),
  .quot 9 14 15 (by decide) (by decide), .addConst 15 1,
  .copy 0 16 (by decide), .pred 16,
  .quot 16 9 17 (by decide) (by decide),
  .add 17 17 18 (by decide) (by decide), .addConst 18 1, .logSucc 18, .pred 18,
  .mul 18 9 19 (by decide) (by decide),
  .load 20 ([false,true] : List Bool),
  .pow 20 18 21 (by decide) (by decide)]

def initialModel (m B ml Bl : ℕ) : Model where
  val i := if i=0 then m else if i=1 then B else 0
  len i := if i=0 then ml else if i=1 then Bl else 0

def prefixModel (m B ml Bl : ℕ) : Model := result prefixCode (initialModel m B ml Bl)

def middleModel (m B ml Bl : ℕ) : Model where
  val := Function.update (prefixModel m B ml Bl).val 9 (SparseCode.degree m B)
  len := Function.update (prefixModel m B ml Bl).len 9
    ((prefixModel m B ml Bl).len 0+(prefixModel m B ml Bl).len 8)

def finalModel (m B ml Bl : ℕ) : Model := result suffixCode (middleModel m B ml Bl)

abbrev command : Cmd 8 77 :=
  .seq (LeafParametersProgram.Circuit.program prefixCode)
    (.seq minCommand (LeafParametersProgram.Circuit.program suffixCode))

def runtimeBound (m B ml Bl : ℕ) : ℕ :=
  budget prefixCode (initialModel m B ml Bl) +
  (40*((prefixModel m B ml Bl).len 0+(prefixModel m B ml Bl).len 8+1)+
   budget suffixCode (middleModel m B ml Bl))

end SubexponentialSAT.SqrtLog.CodeParametersProgram


/-! Explicit paid binary-to-unary copies for code-search metadata. -/
namespace SubexponentialSAT.SqrtLog.CodeParametersProgram

open BitProgram StructuredCalls BinaryArithmetic LeafParametersProgram.Bank

def unaryModelBudget (z : LeafParametersProgram.Circuit.Model) : ℕ :=
  (unaryPairs.map (fun p =>
    7*z.len p.1+6+(2*z.val p.1+(z.val p.1+1)*(16*z.len p.1+16)+2*z.len p.1+6))).sum

abbrev fullCommand : Cmd 8 77 := .seq command unaryCommand

def fullBudget (m B ml Bl : ℕ) : ℕ :=
  runtimeBound m B ml Bl+unaryModelBudget (finalModel m B ml Bl)

def program := compiled fullCommand 0 30

end SubexponentialSAT.SqrtLog.CodeParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeParametersProgramBudget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ordinary-polynomial cost of the actual sparse-code metadata producer.
The two exhaustive code searches have separate costs; this file accounts
for the fixed arithmetic table and all seven unary materializations. -/
namespace SubexponentialSAT.SqrtLog.CodeParametersProgram

open LeafParametersProgram.Circuit


def prefixEnvelope (m ml Bl : ℕ) : ℕ :=
  iterMajorant prefixCode.length (setupInput m ml Bl)

def setupEnvelope (m ml Bl : ℕ) : ℕ :=
  iterMajorant suffixCode.length (2*prefixEnvelope m ml Bl)

end SubexponentialSAT.SqrtLog.CodeParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramBanked
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute


open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

def guardedModel (x : Input) (l : Fin 8 → ℕ) : Model :=
  { val := fun a => if a.val < 44 then (Prepared.finalModel x l).val a else 0
    len := fun a => if a.val < 44 then (Prepared.finalModel x l).len a else 0 }

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyParameterValuesBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues

open LeafParametersProgram LeafParametersProgram.Bank LeafParametersProgram.Circuit


def Constants : Instr → Prop
  | .load _ bs => BinaryArithmetic.toNat bs ≤ 128
  | .addConst _ k => k ≤ 128
  | _ => True

def PowerBound (B : ℕ) (m : Model) : Instr → Prop
  | .pow a b _ _ _ => m.val a^m.val b ≤ B
  | _ => True

def PowerBounds (B : ℕ) : List Instr → Model → Prop
  | [],_ => True
  | i::is,m => PowerBound B m i ∧ PowerBounds B is (next m i)

end SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyParameterValuesLayout
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues

open LeafParametersProgram LeafParametersProgram.Bank LeafParametersProgram.Circuit


def base (x : Input) : ℕ := magnitude x+16*(2*magnitude x+1)^2+128

end SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyParameterValues
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues

open LeafParametersProgram LeafParametersProgram.Bank LeafParametersProgram.Circuit


/-- A fixed polynomial envelope for every actual numeric bank entry. It
includes both power outputs and the guard's reused low scratch ports. -/
def envelope (S : ℕ) : ℕ :=
  iter Serialization.code.length (iter GuardSetup.code.length
    (iter Layout.code.length (S+16*(2*S+1)^2+128)))

end SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblySerialization
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact ordinary cost of the two derived numeric metadata words. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly.RingSetup
open LeafParametersProgram


theorem serialization_budget_le (m : Circuit.Model) (S : ℕ)
    (hl : ∀ i, m.len i ≤ S) :
    Circuit.budget Serialization.code m ≤ serializationEnvelope S := by
  have he : Circuit.budget Serialization.code m =
      (2*m.len 44+3)+(7*m.len 35+5)+20*(m.len 35+1)+20*(m.len 35+1)+
      (2*m.len 45+3)+100*(m.len 33+m.len 33+1)^2 := by
    have h35 : (35 : Fin 64)≠44 := by decide
    have h45 : (45 : Fin 64)≠44 := by decide
    have h33a : (33 : Fin 64)≠45 := by decide
    have h33b : (33 : Fin 64)≠44 := by decide
    norm_num [Serialization.code,Circuit.budget,Circuit.cost,Circuit.next,
      Circuit.output,Circuit.lengthBound,Function.update,h35,h45,h33a,h33b]
    ; ring
  rw [he]
  unfold serializationEnvelope
  gcongr <;> exact hl _

end SubexponentialSAT.SqrtLog.CostAssembly.RingSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_EarlyThreshold
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A paid, fixed native producer of the early high-incidence threshold.
The source is the original ambient count in bank slot 0.  It is never replaced
by the residual count or by the later block-size parameter. -/

namespace SubexponentialSAT.SqrtLog.EarlyThreshold

open BitProgram StructuredCalls BinaryArithmetic
open LeafParametersProgram.Bank LeafParametersProgram.Circuit


/-- The only modified public words are 13 and 16.  The arithmetic operations
already include their concrete bit-level implementation and scratch cleanup. -/
def code : List Instr := [
  .clear 13, .copy 0 13 (by decide), .addConst 13 16, .logSucc 13,
  .clear 16, .sqrt 13 16 (by decide), .addConst 16 1]

abbrev command : Cmd 8 77 := LeafParametersProgram.Circuit.program code

def sizeBound (m : Model) : ℕ :=
  m.len 0 + m.len 13 + m.len 16 + Asymptotic.L (m.val 0) + 20

def program := compiled command (port 0) (port 16)

def inputModel (ambient : List Bool) : Model :=
  ⟨values (inputWords ambient), lengths (inputWords ambient)⟩

end SubexponentialSAT.SqrtLog.EarlyThreshold

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarMachine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed register language for the twelve scalar cache/temporary words.
Its interpreter is actual finite code, not a unit-cost arithmetic oracle. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing ModularRingPrograms

variable (p t : ℕ) [Fact p.Prime]

theorem halfLoop_eval (M : SubexpPreparedQuartic.Modulus p t) (v : Values p t)
    (d : Data) (h : Encoded p t M v d) :
    ∃ n e, Eval halfLoop n d e ∧
      Encoded p t M (iterateForward p t M v (d.stacks 40).length) e ∧
      e.stacks 40=[] ∧
      (∀ j, j≠40 → (∀ i, port i≠j) → e.stacks j=d.stacks j) ∧
      n ≤ (d.stacks 40).length*(3*stepBudget p t+2)+2 := by
  let I (i : ℕ) (e : Data) : Prop :=
    Encoded p t M (iterateForward p t M v i) e ∧
    ∀ j, j≠40 → (∀ a, port a≠j) → e.stacks j=d.stacks j
  have stable : UnaryForPrograms.FrameStable loopPorts I := by
    intro i a b hab ha
    constructor
    · constructor
      · constructor
        · intro j
          rw [←hab (low j) (by intro hh; have hv:=congrArg Fin.val hh; dsimp [low,loopPorts] at hv; omega)]
          exact ha.1.1.1 j
        · rw [←hab 38 (by decide)]; exact ha.1.1.2
      · intro j
        rw [←hab (port j) (port_ne40 j)]
        exact ha.1.2 j
    · intro j hj hjs; rw [←hab j hj]; exact ha.2 j hj hjs
  have spec : UnaryForPrograms.BodySpec loopPorts (sequence halfStep) I
      (fun _=>3*stepBudget p t) := by
    intro i a ha
    obtain ⟨n,e,he,hv,hf,hn⟩:=sequence_eval p t M halfStep _ a ha.1
    refine ⟨n,e,?_,he,hf 40 port_ne40,?_,?_⟩
    · simpa [halfStep] using hn
    · exact hv
    · intro j hj hjs; exact (hf j hjs).trans (ha.2 j hj hjs)
  obtain ⟨n,e,he,hi,h40,hn⟩:=UnaryForPrograms.for_correct loopPorts (sequence halfStep) I
    (fun _=>3*stepBudget p t) stable spec d ⟨h,fun _ _ _=>rfl⟩
  refine ⟨n,e,he,hi.1,h40,hi.2,?_⟩
  have bs : ∀ n i, CounterForPrograms.budgetSum (fun _=>3*stepBudget p t) i n = n*(3*stepBudget p t) := by
    intro n; induction n with
    | zero => intro i; simp [CounterForPrograms.budgetSum]
    | succ n ih => intro i; simp [CounterForPrograms.budgetSum,ih]; ring
  simp only [loopPorts,bs] at hn
  nlinarith

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing

abbrev command : Cmd 8 41 := .seq baseCommand arithmeticCommand

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed native preparation command accepts only the runtime binary
precision. It constructs its modulus, scalar cache, table, arrays and counters
with charged bit instructions, ready for the fixed Newton program. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpQuarticRing

def preparation : Cmd 8 41 := .seq boot (.seq Scalar.command finishCommand)

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

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

/-! One paid Pascal row pass over the framed cache. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar

abbrev pass : Cmd 8 18 := .seq row (.seq cacheFinishList cacheClear)

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! A fixed while loop consumes the runtime unary iteration count. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar

abbrev loop : Cmd 8 18 := .while 6 (.seq pass cacheRead)

abbrev command : Cmd 8 18 := .seq cacheRead loop
def program := compiled command 17 15

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

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

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The fixed executable preparation pipeline.  Its input is the actual
numerical bank emitted by `LeafParametersProgram`; no field polynomial,
modulus, multiplication table, nodes, or idempotent coefficients are inputs.
The stage-by-stage execution theorem is separate from this code definition.
-/


/-! Arithmetic consumers use the same bytes generated by the preceding
stages.  These are structural handoff lemmas; the complete production
trace must establish `NativeBytes` before invoking them. -/

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls StackRoutines LeafParametersProgram

def numberBudget (m : Circuit.Model) (initialWidth V W : ℕ) : ℕ :=
  (workPorts++outputPorts).length*(2*initialWidth+3)+
  (Circuit.budget Serialization.code m+1)+
  5*(7*W+6+32*(V+1)*(W+1))+(7*W+8)+32

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls LeafParametersProgram SubexpQuarticRing SubexpLiftRing

/-- Stage costs are composed with actual tape growth. All stage counts are
fixed polynomials except the explicit, independently bounded search and
Newton budgets. -/
def producerBudget (m : Circuit.Model) (initialWidth V bankWidth : ℕ) : ℕ :=
  let b0 := numberBudget m initialWidth V bankWidth
  let b1 := coreBudget (m.val 33) (m.val 34) bankWidth
  let w1 := initialWidth+b0+b1+1
  let b2 := constantsBudget w1 (baseWidth 3 (m.val 33)) (m.val 34)
  let w2 := w1+b2+1
  let b3 := nodesBudget w2 (m.val 33) (m.val 34) (m.val 21)
  let w3 := w2+b3+1
  let b4 := idempotentBudget (m.val 33) w3
  let w4 := w3+b4+1
  b0+b1+b2+b3+b4+finalDiscard.length*(2*w4+3)+32

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end


