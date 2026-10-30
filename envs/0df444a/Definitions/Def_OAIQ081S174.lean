-- Prove2me | Definitions.Def_OAIQ081S174
-- name    : OAIQ081S174
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:18:21.875905+00:00
-- url     : https://prove2.me/theorems/eacc7cc1-bd5d-414b-b341-42a5de6a3976
-- title:
--   Definitions bundle OAIQ081S174 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 34 declarations of OpenAI's Lean: 21 definitions, 1 inductive type or structure and 12 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.covered`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.inner`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.integer`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry.good`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.guarded`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.InputFields`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.ofProduced`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry.scalar`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.binomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.entry`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.guarded`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.inputMeasure`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.offsetCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.coreCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.fixedSourceRow`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.Data`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_HighQueryCount`, `SubexponentialSAT_SqrtLog_LayoutDenominatorProgramModel`, `SubexponentialSAT_SqrtLog_LayoutProgramEntryBank`, `SubexponentialSAT_SqrtLog_LayoutProgramEntryBankInner`, `SubexponentialSAT_SqrtLog_LayoutProgramIntegerEntry`, `SubexponentialSAT_SqrtLog_LayoutProgramNativePacking`, `SubexponentialSAT_SqrtLog_LayoutProgramNumerator`, `SubexponentialSAT_SqrtLog_LayoutProgramPackLabels`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCountsDefinitions`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameReady`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceConfiguration`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceParameters`, `SubexponentialSAT_SqrtLog_LayoutProgramUniversalEntry`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNative`, `SubexponentialSAT_SqrtLog_LeafParametersProgramBanked`, `SubexponentialSAT_SqrtLog_LeafParametersProgramFrontendInputBounds`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramInterpolation`, `SubexponentialSAT_SqrtLog_PerturbationAssemblySourceStored`, `SubexponentialSAT_Subexp_PackingExtractionOuter`, `SubexponentialSAT_Subexp_PackingExtractionStage`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S166`, `OAIQ081S167`, `OAIQ081S168` and `OAIQ081S169` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S180`, `OAIQ081S181`, `OAIQ081S182`, `OAIQ081S183`, `OAIQ081S184` and `OAIQ081S185`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.entryAt`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.nativeEntryContract`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.binomial_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.covered_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.covered_uncovered_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.inner_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.prepared_integer_export_cleanup`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.scalar_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Ready.metadata`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.initial_contract`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.fixedSourceRow_baseline_eq` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input.bank_ready`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.entryAt`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.nativeEntryContract`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.binomial_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.covered_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.covered_uncovered_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.inner_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.prepared_integer_export_cleanup`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.scalar_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Ready.metadata`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.initial_contract`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.fixedSourceRow_baseline_eq` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input.bank_ready`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S166
import Definitions.Def_OAIQ081S167
import Definitions.Def_OAIQ081S168
import Definitions.Def_OAIQ081S169

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

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

theorem command_eval (m : Model) (w : Words) (r : Regs) (hs : Shape m w) :
    ∃ t rf w', Eval command t (Bank.state r w) (Bank.state rf w') ∧
      Shape (result code m) w' ∧ t ≤ budget code m :=
  Circuit.program_eval code m w r hs (admissible m)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization


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

theorem guardedModel_public (x : Input) (l : Fin 8 → ℕ) (i : Fin 12) :
    (guardedModel x l).val (publicSlot i)=(Layout.model x l).val (publicSlot i) := by
  change (if (publicSlot i).val < 44 then (Prepared.finalModel x l).val (publicSlot i) else 0)=_
  rw [ite_eq_left (publicSlot_lt i)]
  exact guard_preserves_public (Layout.model x l) i

theorem guardedModel_precision (x : Input) (l : Fin 8 → ℕ) (hm : x.clauses≠0) :
    (guardedModel x l).val 33=(produce x).t :=
  (guardedModel_public x l 8).trans (Layout.model_precision x l hm)

theorem guardedModel_degree (x : Input) (l : Fin 8 → ℕ) (hq : (produce x).Q≠0) :
    (guardedModel x l).val 34=(produce x).d :=
  (guardedModel_public x l 9).trans (Layout.model_degree x l hq)

theorem guardedModel_radius (x : Input) (l : Fin 8 → ℕ) :
    (guardedModel x l).val 18=(produce x).r :=
  (guardedModel_public x l 3).trans (Layout.model_core_values x l).2.2.2.1

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutDenominatorProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete extension-ring denominator program. It first lifts the actual
scalar-half word, then runs the paid native multiplication loop. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing
open IntegerRingLiftProgram

theorem command_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (zero one minusOne : ModelCode t d)
    (s : Store) (h : CachedReady t a M cache zero one minusOne s)
    (u : RingProgram.ScalarCode 3 t) (hu : s 253 = u.val)
    (h254 : s 254 = []) (h252 : s 252 = []) :
    ExecutesIn command (budget (s 239).length t d) s
      (Function.update s 252 (RingProgram.flat (value t a M cache zero one minusOne u.val (s 239).length))) := by
  let x := cachedSignedValue t a M cache zero one minusOne u.val []
  let s1 := Function.update s 255 (RingProgram.flat x)
  have h1 : ExecutesIn modelSignedCommand (modelSignedBudget (baseWidth 3 t) t d) s s1 := by
    simpa only [hu,h254,List.length_nil,Nat.add_zero,u.property] using
      cachedSignedCommand_run t a M cache hz zero one minusOne s h
  have h2 := powerCommand_run s RingProgram.flat HornerProgram.Services.multiply
    (fun x y => ((RingProgram.modelProgram t a M cache).mulRun x y).1)
    (HornerProgram.Services.mulBudget (baseWidth 3 t) d) (d*baseWidth 3 t)
    (HornerProgram.Services.multiply_spec 3 t M cache hz (modelTable t a M cache) s h.native)
    (fun x => (RingProgram.flat_length x).le) s1 x
    one
    (CRTLocalProgram.lowFrame_update (CRTLocalProgram.lowFrame_refl s) 255 (by decide) _)
    (by simp [s1]) (by simpa [s1] using h.one)
    (by simpa [s1] using h.clean.1) (by simpa [s1] using h.clean.2.1)
    (by simpa [s1] using h.clean.2.2.1) (by simpa [s1] using h.clean.2.2.2.1)
    (by simpa [s1] using h.clean.2.2.2.2) (by simpa [s1] using h.bits)
    (by simpa [s1] using h252)
  have he : Function.update (Function.update s1 255 []) 252
      (RingProgram.flat (powerValue
        (fun x y => ((RingProgram.modelProgram t a M cache).mulRun x y).1)
        x one (s1 239).length)) =
      Function.update s 252 (RingProgram.flat (value t a M cache zero one minusOne u.val (s 239).length)) := by
    simp [s1,value,x,← h.output]
  rw [he] at h2
  simpa only [command,budget,s1,Function.update_of_ne (show (239:Fin 256)≠255 by decide)]
    using h1.seq h2

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Paid staging of the native interpolation-cache producer in the wide
leaf machine. The private 320-tape bank is disjoint from all ring and
collector masters. Native table computation is followed by paid extraction
of all five outputs; the entire staging bank is then cleared. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation
open BitProgram StructuredCalls StackRoutines SubexpLiftRing SubexpQuarticRing

abbrev coreCall : Cmd 40 768 := .call
  (ProgramLinking.liftProgram InterpolationCacheProgram.program localRegisters localPorts)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramFrontendInputBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Input-only closure of the physical parameter/cache/export costs, including
the exact binary word lengths used by the subsequent offset producer. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds
open BinaryArithmetic Bank Circuit Asymptotic
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

def inputMeasure (a : Args) := Layout.inputMeasure a.1 a.2
def guarded (a : Args) := Execute.guardedModel a.1 a.2

def offsetCost (a : Args) := 5000*(2*(guarded a).val 29+1)^2*
  ((guarded a).len 3+(guarded a).len 21+(guarded a).len 29+11)^2

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed outer loop extracts all complete blocks in block-major order. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open BitProgram StructuredCalls MatrixProgramSupport

theorem body_eval (i : ℕ) (entries : List Entry) (c : Context)
    (hblock : c.block = List.replicate i true)
    (hbuckets : c.buckets = ProgramEncoding.encodeRecords (entries.map entryWord))
    (hentries : ∀ e ∈ entries, i < e.2.length) (regs : Fin 8 → Bool) :
    ∃ n ≤ bodyBudget i entries c, ∃ rf,
      Eval body n (base regs c) (guard rf (advanced i entries c)) := by
  obtain ⟨a, ha, hsa⟩ := MatrixProgramSupport.copy_eval (15 : Fin 19) 7 9
    (by decide) (by decide) (by decide) (base regs c) rfl
  have hea : a = ready a.regs { c with keys := c.buckets, payload := [] } := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hsa]
    funext j
    fin_cases j <;> simp [base, ready, state, StackRoutines.copyStacks]
  rw [hea] at ha
  obtain ⟨nb, hnb, rb, hblockrun⟩ := blockCommand_eval i entries c hblock hentries a.regs []
  have hbr : Eval blockCommand nb
      (ready a.regs { c with keys := c.buckets, payload := [] })
      (base rb (emitEntries i entries c)) := by
    simpa only [hbuckets, List.append_nil, base] using hblockrun
  let d := emitEntries i entries c
  let pushed := { d with block := true :: d.block }
  let rp := Function.update rb (0 : Fin 8) true
  have hp : Eval (TupleProgram.pushConst 10 0 true) 2 (base rb d) (base rp pushed) := by
    have h := TupleProgram.pushConst_eval (10 : Fin 19) (0 : Fin 8) true (base rb d)
    have he : TupleProgram.pushedState 10 0 true (base rb d) = base rp pushed := by
      apply MatrixProgramSupport.data_ext <;> try rfl
      funext j
      fin_cases j <;> rfl
    rw [he] at h
    exact h
  let rf := readRegs rp 3 4 d.remaining.head?
  have hpop : Eval popRemaining 1 (base rp pushed) (base rf (advanced i entries c)) :=
    popRemaining_eval rp pushed
  have hrefresh := refresh_eval rf (advanced i entries c)
  have hbucketStack : (base regs c).stacks 15 = c.buckets := rfl
  simp only [hbucketStack] at ha
  refine ⟨(7 * c.buckets.length + 5) + (nb + (2 + (1 + 1))), ?_, rf, ?_⟩
  · dsimp [bodyBudget]
    omega
  · simpa only [body, base, ready, state, d] using ha.seq (hbr.seq (hp.seq (hpop.seq hrefresh)))

theorem loop_eval (entries : List Entry) (n i : ℕ) (c : Context)
    (hblock : c.block = List.replicate i true)
    (hremaining : c.remaining = List.replicate n true)
    (hbuckets : c.buckets = ProgramEncoding.encodeRecords (entries.map entryWord))
    (hentries : ∀ e ∈ entries, i + n ≤ e.2.length) (regs : Fin 8 → Bool) :
    ∃ steps ≤ loopBudget entries n i c, ∃ rf,
      Eval loop steps (guard regs c) (base rf (advanceMany entries n i c)) := by
  induction n generalizing i c regs with
  | zero =>
    refine ⟨1, le_rfl, (guard regs c).regs, ?_⟩
    have hg : (guard regs c).regs 4 = false := by simp [guard, base, ready, state, readRegs, hremaining]
    exact Eval.while_false hg
  | succ n ih =>
    have he : ∀ e ∈ entries, i < e.2.length := by
      intro e he
      have := hentries e he
      omega
    obtain ⟨nb, hnb, rb, hbody⟩ := body_eval i entries c hblock hbuckets he (guard regs c).regs
    have hbody' : Eval body nb (guard regs c) (guard rb (advanced i entries c)) := hbody
    obtain ⟨hb, ht, hr⟩ := advanced_static i entries c
    have hb' : (advanced i entries c).block = List.replicate (i + 1) true := by
      rw [hb, hblock]
      simp [List.replicate_succ]
    have hr' : (advanced i entries c).remaining = List.replicate n true := by
      rw [hr, hremaining]
      simp
    have ht' : (advanced i entries c).buckets =
        ProgramEncoding.encodeRecords (entries.map entryWord) := ht.trans hbuckets
    obtain ⟨nr, hnr, rf, hrest⟩ := ih (i + 1) (advanced i entries c) hb' hr' ht'
      (by intro e he; have := hentries e he; omega) rb
    have hg : (guard regs c).regs 4 = true := by
      simp [guard, base, ready, state, readRegs, hremaining, List.replicate_succ]
    refine ⟨nb + nr + 1, ?_, rf, ?_⟩
    · simp only [loopBudget]
      omega
    · exact Eval.while_true hg hbody' hrest

/-- Extract the first `n` entries of every bucket by an actual nested loop.
The storage accumulator is retained in reverse-bit form for appending leftovers. -/
theorem program_trace (entries : List Entry) (n : ℕ) (c : Context)
    (hblock : c.block = []) (hremaining : c.remaining = List.replicate n true)
    (hbuckets : c.buckets = ProgramEncoding.encodeRecords (entries.map entryWord))
    (hentries : ∀ e ∈ entries, n ≤ e.2.length) (regs : Fin 8 → Bool) :
    ∃ steps ≤ loopBudget entries n 0 c + 2, ∃ rf,
      Trace program steps ((base regs c).withPC (some program.entry))
        ((base rf (advanceMany entries n 0 c)).withPC none) := by
  obtain ⟨steps, hs, rf, he⟩ := loop_eval entries n 0 c
    (by simpa using hblock) hremaining hbuckets (by simpa using hentries) regs
  exact ⟨1 + steps + 1, by omega, rf,
    compiled_halt_trace ((refresh_eval regs c).seq he) 15 12⟩

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact relocation of complete-block extraction in the final controller. -/

namespace SubexponentialSAT.Subexp.PackingProgram

open BitProgram StructuredCalls PackingProgramSupport

theorem extraction_eval (input : Input) (entries : List PackingExtraction.Entry) (n : ℕ)
    (hentries : ∀ e ∈ entries, n ≤ e.2.length) (regs : Fin 16 → Bool) :
    ∃ steps ≤ extractionBudget entries n, ∃ rf,
      Eval extraction steps
        (bucketsOutputState input
          (ProgramEncoding.encodeRecords (entries.map PackingExtraction.entryWord))
          (List.replicate n true) regs)
        (extractionOutputState input n (extracted entries n) rf) := by
  let a := bucketsOutputState input
    (ProgramEncoding.encodeRecords (entries.map PackingExtraction.entryWord)) (List.replicate n true) regs
  have hp : project (by decide : 8 ≤ 16) (by decide : 19 ≤ 48) a =
      PackingExtraction.base (project (by decide : 8 ≤ 16) (by decide : 19 ≤ 48) a).regs
        (initialExtraction entries n) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;>
      simp [ stackPorts, a, bucketsOutputState, inputState,
 initialExtraction]
  obtain ⟨ne, hne, re, he⟩ := PackingExtraction.program_trace entries n
    (initialExtraction entries n) rfl rfl rfl hentries
    (project (by decide : 8 ≤ 16) (by decide : 19 ≤ 48) a).regs
  let b := install (by decide : 8 ≤ 16) (by decide : 19 ≤ 48) a
    (PackingExtraction.base re (extracted entries n))
  have hcall : Eval extractionCall ne a b := by
    apply lowCall_eval
    rw [hp]
    exact he
  obtain ⟨hblock, hremaining, hbuckets⟩ := PackingExtraction.advanceMany_static entries n 0
    (initialExtraction entries n) rfl rfl
  have hb : (extracted entries n).block = List.replicate n true := by
    simpa [extracted, PackingMetadata.unary] using hblock
  have hr : (extracted entries n).remaining = [] := hremaining
  have ht : (extracted entries n).buckets =
      ProgramEncoding.encodeRecords (entries.map PackingExtraction.entryWord) := hbuckets
  have hd : b.stacks = fun i =>
      if i = 10 then List.replicate n true else if i = 11 then (extracted entries n).address
      else if i = 12 then (extracted entries n).storage else if i = 13 then (extracted entries n).metadata
      else if i = 14 then (extracted entries n).addresses
      else if i = 15 then ProgramEncoding.encodeRecords (entries.map PackingExtraction.entryWord)
      else (inputState input regs).stacks i := extraction_call_stacks input entries n regs re hb hr ht
  have hv : PackingPlumbing.Valid extractionSave b := by
    simp [PackingPlumbing.Valid, PackingPlumbing.Op.Valid, extractionSave,
      PackingPlumbing.move, PackingPlumbing.Op.next, hd,
      inputState, StackRoutines.transferStacks, StackRoutines.clearStacks]
  let c := PackingPlumbing.run extractionSave b
  have hc : c = extractionOutputState input n (extracted entries n) c.regs := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;>
      simp [c, PackingPlumbing.run, extractionSave, PackingPlumbing.move, PackingPlumbing.Op.next,
        hd, inputState,
        StackRoutines.copyStacks, StackRoutines.transferStacks, StackRoutines.clearStacks]
  have hcost : PackingPlumbing.cost extractionSave b = 6 * n +
      2 * (ProgramEncoding.encodeRecords (entries.map PackingExtraction.entryWord)).length +
      7 * (extracted entries n).metadata.length + 14 := by
    simp [PackingPlumbing.cost, PackingPlumbing.Op.cost, extractionSave, PackingPlumbing.move,
      PackingPlumbing.Op.next, hd, inputState, StackRoutines.transferStacks, StackRoutines.clearStacks]
    omega
  have hrun := hcall.seq (PackingPlumbing.eval extractionSave b hv)
  refine ⟨ne + PackingPlumbing.cost extractionSave b, ?_, c.regs, ?_⟩
  · rw [hcost]
    unfold extractionBudget
    omega
  · change Eval extraction _ a c at hrun
    rw [hc] at hrun
    exact hrun

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramPackLabels
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Packing from physically produced label records. This route accepts the
incidence pair-gatherer's type labels directly, avoiding reconstruction of a
factor-to-incidence scope table. The fixed program computes blocks, uncovered
coordinates, metadata, storage order, and inverse addresses. It does not
assume any of those outputs. Label and universal-type byte production remain
explicit upstream obligations. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

variable {U : Type*} [DecidableEq U]

/-- Every packing stage after label/type production is a concrete finite program.
Only encoded input labels and the full encoded type alphabet are assumed. -/
theorem program_trace (s : Spec U) (regs : Fin 16 → Bool) :
    ∃ steps ≤ budget s, ∃ rf,
      Trace program steps
        ((PackingProgram.frontendOutputState s.params.input
          (BucketProgram.encodeRecords (records s).reverse)
          (ProgramEncoding.encodeRecords (keys s)) regs).withPC (some program.entry))
        ((s.outputState rf).withPC none) := by
  have hc : s.params.D ≤ (records s).length := by
    simp [records, BucketProgram.vertexRecords, Spec.packing]
  obtain ⟨nb, hnb, rb, hb⟩ := PackingProgram.buckets_eval s.params.input (records s) (keys s)
    s.params.D rfl hc regs
  rw [minimum_eq s, table_eq s] at hb
  obtain ⟨ne, hne, re, he⟩ := PackingProgram.extraction_eval s.params.input (entries s)
    s.packing.blockCount (PackingExtraction.typedEntries_valid s.packing s.encodeVertex s.encodeType) rb
  obtain ⟨nv, hnv, rv, hv⟩ := PackingProgram.vertices_eval s.params.input s.packing.blockCount
    s.params.D (context s) rfl re
  obtain ⟨nl, hnl, rl, hl⟩ := PackingProgram.leftovers_eval s.params.input s.packing.blockCount
    s.params.D (context s) (covered s) (context_metadata s) (context_address s) rv
  obtain ⟨hm, ha, hs, hr⟩ := leftover_outputs s
  rw [hm, ha, hs, hr] at hl
  obtain ⟨ni, hni, ri, hi⟩ := PackingProgram.inverse_eval s.params.input
    (List.replicate s.packing.blockCount true) (List.replicate s.packing.leftovers.length true)
    s.metadata s.storage (addressRecords s) s.params.D rfl rl
  rw [inverse_rows s] at hi
  have hi' : Eval PackingProgram.inverse ni
      (PackingProgram.outputState s.params.input (List.replicate s.packing.blockCount true)
        (List.replicate s.packing.leftovers.length true) s.metadata s.addresses s.storage [] rl)
      (s.outputState ri) := by
    simpa only [Spec.outputState, Spec.addresses, addressRecords,
      PackingAddressSemantics.storageAddresses, Spec.inverse] using hi
  have hpacking := hb.seq (he.seq (hv.seq (hl.seq (hi'.seq (.base (.skip _))))))
  have hall : Eval command (nb + (ne + (nv + (nl + (ni + 0)))))
      (PackingProgram.frontendOutputState s.params.input
        (BucketProgram.encodeRecords (records s).reverse)
        (ProgramEncoding.encodeRecords (keys s)) regs) (s.outputState ri) := hpacking
  refine ⟨nb + (ne + (nv + (nl + (ni + 0)))) + 1, ?_, ri,
    compiled_halt_trace hall 26 32⟩
  unfold budget
  omega

end SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramNativePacking
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! End-to-end physical packing from runtime word rows and native address
plans. Both labels and the full universal type list are generated before the
bucket/block/leftover controller runs. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.NativePacking

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem program_trace {U : Type*} [DecidableEq U] (s : Spec U) (regs : Fin 16 → Bool) :
    ∃ steps ≤ budget s, ∃ rf,
      Trace program steps
        ((NativeFrontend.plansState s.params regs).withPC (some program.entry))
        ((s.suffix.outputState rf).withPC none) := by
  obtain ⟨nf,hf,rf,htf⟩ := NativeFrontend.program_trace s.params regs s.rows_width s.plans_valid
  obtain ⟨ns,hs,rs,hts⟩ := PackLabels.program_trace s.suffix rf
  have hlabels : s.params.labelStream =
      BucketProgram.encodeRecords (PackLabels.records s.suffix).reverse := by
    rw [NativeFrontend.Params.labelStream,s.label_records]
    rfl
  have htypes : s.params.typeStream = ProgramEncoding.encodeRecords (PackLabels.keys s.suffix) := by
    rw [NativeFrontend.Params.typeStream,s.type_records]
    rfl
  rw [hlabels,htypes] at htf
  have e1 : Eval (.call NativeFrontend.program) nf
      (NativeFrontend.plansState s.params regs)
      (PackingProgram.frontendOutputState s.suffix.params.input
        (BucketProgram.encodeRecords (PackLabels.records s.suffix).reverse)
        (ProgramEncoding.encodeRecords (PackLabels.keys s.suffix)) rf) := .call NativeFrontend.program htf
  have e2 : Eval (.call PackLabels.program) ns
      (PackingProgram.frontendOutputState s.suffix.params.input
        (BucketProgram.encodeRecords (PackLabels.records s.suffix).reverse)
        (ProgramEncoding.encodeRecords (PackLabels.keys s.suffix)) rf)
      (s.suffix.outputState rs) := .call PackLabels.program hts
  refine ⟨nf+ns+1,?_,rs,compiled_halt_trace (e1.seq e2) 25 32⟩
  unfold budget
  omega

end SubexponentialSAT.SqrtLog.LayoutProgram.NativePacking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCountsDefinitions
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open LayoutTriplePreparationProgram

abbrev binomial : Cmd 9 40 := .call (ProgramLinking.liftProgram LayoutBinomialProgram.finalProgram regs8 binomialPorts)
abbrev command : Cmd 9 40 := .seq copies (.seq count (.seq binomial (.seq numerator cleanup)))
def program := compiled command 7 37


end SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramUniversalEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed control for one universal integer constraint entry. The concrete
local stages are lifted into one bank; subsequent lemmas compose their traces.
No ring inversion or field-valued matrix is used in this integer procedure. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open SubexponentialSAT.MulticolorTypes

abbrev scalar : Cmd 10 64 := .call (ProgramLinking.liftProgram
  LayoutProgramScalar.FromCounts.program scalarRegs scalarPorts)

end SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramNumerator
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete universal numerator evaluation from encoded type words and the
paid unsigned coefficient cache. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open UniversalEntry RowSelectionProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q : ℕ}

abbrev guarded : Cmd 10 64 := .seq ScanRestore.command (.ite 7 scalar clearCounts)
abbrev command : Cmd 10 64 := .seq guard (.ite 9 guarded (.base .skip))

end SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramIntegerEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Literal integer universal constraints from the actual numerator program.
The outer anchor test also suppresses the clearing diagonal outside the joint. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open UniversalEntry RowSelectionProgram MatrixExtendedEntryProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q : ℕ}

abbrev good : Cmd 10 64 := .seq Numerator.command (.seq TypeCompare.command IntegerFinish.command)
abbrev command : Cmd 10 64 := .seq guard (.ite 9 good (.base .skip))

end SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete incidence-entry program. Its read-only cache bank is200..211,
its input indices252/253, and the returned signed pair254/255. Ports212..251
belong to the caller and are outside every local subroutine map. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def integer : Code := liftCommand IntegerEntry.command 23 53 integerRegs integerPorts

def covered : Code := .ite 5
  (.seq compareBlocks (.ite 7 (.seq prepare (.seq integer exportPair)) (.base .skip)))
  (.base .skip)
def command : Code := .seq lookup (.seq (.ite 4 covered uncovered) cleanup)

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankInner
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual cached universal-entry call, including all physical staging,
export and cleanup. The caller's private fiber-loop bank is unrestricted. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open RowSelectionProgram

variable {r Q : ℕ}

def inner : Code := .seq prepare (.seq integer (.seq exportPair cleanup))

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The closed instruction table for node/head setup. The incidence entry is
the actual metadata/guard/integer program, wrapped by the paid original-owner
fiber scan and sum. There is no runtime entry-value callback in this code.
The complete semantic and quantitative refinement is proved separately. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def entry : Cmd 16 256 := LayoutFiberSumProgram.command LayoutProgram.EntryBank.command

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameReady
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete pre-state invariants for source dispatch. Metadata lookup and
whole-store comparisons preserve these low-bank arithmetic inputs. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open IntegerRingLiftProgram

def InputFields {r Q : ℕ} (a : Data) (c : Numerator.Saved) (start : Fin Q)
    (u y : UniversalType r Q 1) : Prop :=
  ∀ i : Fin 64, i≠23 → i≠24 →
    lowStore a (LayoutSourceValuesProgram.Native.numeratorPorts i)=
      (Numerator.state c (fun _=>false) start u y [] [] ([],[])).stacks i

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceConfiguration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete numerical and cache inputs to the source bank. The state predicate
contains byte representations only; it contains no program-service premise. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open IntegerRingLiftProgram RowSelectionProgram

variable {r Q d : ℕ}

structure Ready (p : Parameters r Q d) (a : Data) : Prop where
  work : WorkReady a
  input : ∀ u y : UniversalType r Q 1, InputFields a p.saved p.start u y
  ring : CachedReady p.t p.model p.modulus p.cache p.ops.zeroRun.1 p.ops.oneRun.1 p.minusOne (lowStore a)
  inverseDenominator : a.stacks 252=RingProgram.flat p.invDenom
  nodes : (a.stacks 22).length=Q
  limit : (a.stacks 47).length=p.R
  inverses : a.stacks 308=(List.ofFn (fun i=>RingProgram.flat (p.inverse i))).flatten
  negatives : a.stacks 309=(List.ofFn (fun i=>RingProgram.flat (p.negative i))).flatten
  differences : a.stacks 310=(List.ofFn (fun i=>(List.ofFn (fun j=>RingProgram.flat (p.difference i j))).flatten)).flatten
  ringWidth : a.stacks 311=p.ringWidth
  rowWidth : a.stacks 312=p.rowWidth
  zero : a.stacks 313=RingProgram.flat p.ops.zeroRun.1
  one : a.stacks 314=RingProgram.flat p.ops.oneRun.1

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblySourceStored
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The executed source predicate determines the incidence jet independently
of the particular coefficient-array witness returned by each source call. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram LeafProgram.NativeSemantics
open scoped BigOperators

noncomputable def fixedSourceRow {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (n f j : ℕ) (v : Fin n) : Polynomial (p.model.O p.t) :=
  sourceRowFamily ps n f j (totalPackedSource p P) v.val

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Pure packaging of the caches produced by native setup. No execution,
source polynomial, or interpolation table is supplied by this constructor.
The integer encoder below is a semantic witness used in the row proof; the
runtime integer lift remains the already checked native program. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open IntegerRingLiftProgram RowSelectionProgram

namespace Parameters

/-- The actual produced ring, its canonical scalar cache, and its generated
half determine every ring-valued field of `Parameters`. The inverse word is
exactly the value written by `LayoutDenominatorProgramQuery` to port728. -/
def ofProduced (s : LeafHeadSetupProgram.Native.Inputs)
    (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect s.height
      (LeafHeadSetupProgram.unary s.R) s.width words)
    (m : LeafParametersProgram.Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (u : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache u e)
    (hfield : s.Q < 3^(m.val 34)) : Parameters s.r s.Q (m.val 34) :=
  ofInputs s words hc (m.val 33) ht hd (IrreducibleSearch.data hd) M cache hp.caches.canonical
    (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero)
    (LayoutDenominatorProgramQuery.value (m.val 33) (IrreducibleSearch.data hd) M cache u s.R)
    (LeafProgram.Constants.minusOne_decode _ ht hd _ M cache)
    (LayoutDenominatorProgram.value_inverse _ ht hd _ M cache _ _ _
      (LeafProgram.Constants.zero_decode _ ht hd _ M cache)
      (LeafProgram.Constants.one_decode _ ht hd _ M cache)
      (LeafProgram.Constants.minusOne_decode _ ht hd _ M cache) u hp.caches.inverse s.R)
    hfield

end Parameters
end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The persistent physical boundary for the actual high-assignment loop.
The ring, source and parked layout words are produced once for this query and
retained across each rank. No execution or evaluator is part of this invariant. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount

open OAI BitProgram StructuredCalls SqrtLog LeafProgram
open HighQueryAdapter

abbrev Data := State 40 896

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount
end


