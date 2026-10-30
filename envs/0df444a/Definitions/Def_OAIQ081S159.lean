-- Prove2me | Definitions.Def_OAIQ081S159
-- name    : OAIQ081S159
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:02:07.599463+00:00
-- url     : https://prove2.me/theorems/a723eb06-abaf-4dce-8690-0644fed46809
-- title:
--   Definitions bundle OAIQ081S159 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 52 declarations of OpenAI's Lean: 17 definitions, 2 inductive types or structures and 33 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.CoreFrame`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.coreOutput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.cost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.finished`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.nativeStore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.prepared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.highCapacity`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.offsetCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.QueryBounds`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.inputHigh`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.makeMask`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.maskLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.prepare`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Sources`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide.project`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot.fullCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot.fullProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Clear.after`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LeafProgramSource`, `SubexponentialSAT_SqrtLog_LeafProgramSourceFrame`, `SubexponentialSAT_SqrtLog_LeafProgramSourceNative`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendCommand`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendInputBudget`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendSemantics`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramReplay`, `SubexponentialSAT_SqrtLog_LeafScopeInputBoundsQuery`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramNative`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramState`, `SubexponentialSAT_SqrtLog_NativePackingBounds`, `SubexponentialSAT_SqrtLog_NativePackingBoundsAddress`, `SubexponentialSAT_SqrtLog_NativePackingBoundsGenerated`, `SubexponentialSAT_SqrtLog_NativePackingBoundsTail`, `SubexponentialSAT_SqrtLog_PackingCallerProgramState`, `SubexponentialSAT_SqrtLog_PackingCallerProgramWide`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_RingProgramTableSetup`, `SubexponentialSAT_Subexp_PackingLeftoverStage`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S141`, `OAIQ081S142`, `OAIQ081S143`, `OAIQ081S144`, `OAIQ081S145`, `OAIQ081S146` and `OAIQ081S147` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S169`, `OAIQ081S170`, `OAIQ081S171` and `OAIQ081S172`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.finished_stacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.offset_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.query_bounds`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.finished_stacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.offset_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.query_bounds` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.scope_cost_le`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S141
import Definitions.Def_OAIQ081S142
import Definitions.Def_OAIQ081S143
import Definitions.Def_OAIQ081S144
import Definitions.Def_OAIQ081S145
import Definitions.Def_OAIQ081S146
import Definitions.Def_OAIQ081S147

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingLeftoverStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual generation of ascending vertex indices and the leftover scan in
the fixed packing controller. -/

namespace SubexponentialSAT.Subexp.PackingProgram

open BitProgram StructuredCalls PackingProgramSupport

theorem verticesBudget_le (D : ℕ) : verticesBudget D ≤ 100 * (D + 1) ^ 2 := by
  have hb := AssignmentSeedRange.budget_le D
  have hs := ProgramEncoding.encodeRecords_length_le
    ((List.range D).map AssignmentSeedRange.unary) D (by
      intro word hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      simpa only [List.length_replicate] using Nat.le_of_lt (List.mem_range.mp hi))
  change (AssignmentSeedRange.seedRecords D).length ≤ 1 + (2 * D + 2) *
    ((List.range D).map AssignmentSeedRange.unary).length at hs
  simp only [List.length_map, List.length_range] at hs
  unfold verticesBudget
  nlinarith only [hb, hs]

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The source callback used by the actual incidence-table loop. The fixed
command stages source controls, protects all four target caches, invokes the
concrete source-row instruction table, restores the target caches, and clears
source-only controls. The local source correctness theorem is joined below
through its actual execution, never through a supplied polynomial oracle. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Source
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
abbrev Data := State 16 768

def prepared (a : Data) : Data := SourceControls.prepared (SourceStaging.saved a)
noncomputable def coreOutput (a : Data) (b : State 16 340) : Data :=
  embedState id workerPort (prepared a) b
noncomputable def finished (a : Data) (b : State 16 340) : Data :=
  SourceControls.cleaned (SourceStaging.finished (coreOutput a b))
noncomputable def cost (a : Data) (b : State 16 340) (n : ℕ) : ℕ :=
  SourceStaging.beforeCost a + (SourceControls.prepareCost (SourceStaging.saved a) +
    (n+1 + (SourceStaging.afterCost (coreOutput a b) +
      clearManyCost SourceControls.extraPorts (SourceStaging.finished (coreOutput a b)))))

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact store restoration for the executed source callback. The source
kernel may change its four initialized caches and source output; the wrapper
restores all four caches and removes every staged source control. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Source
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

def CoreFrame (a : Data) (b : State 16 340) : Prop :=
  ∀ i, i ∉ coreChanged → (coreOutput a b).stacks i = (prepared a).stacks i

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed source generation in the incidence worker. The result arrays are
witnesses of the actual run; no equality of separately generated byte arrays
is inferred from equality of their polynomial meanings. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Source
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexponentialSAT.Subexp
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram

abbrev nativeStore (a : Source.Data) : LayoutSourceRowsProgram.Store :=
  (prepared a).stacks ∘ workerPort

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCommand
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native syntax from physical formula/row masters through the guarded
parameter bank. The only static input is the fixed formula-width bound k. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

def offsetCall : Code := .call (ProgramLinking.liftProgram LayoutOffsetProgram.program r8 offsetPorts)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendInputBudget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

def Query.highCapacity (q : Query) : ℕ :=
  (LeafStatisticsProgram.scopeBits q.scopeRows).length+BinaryArithmetic.toNat q.ambient+
    EarlyThreshold.threshold (BinaryArithmetic.toNat q.ambient)+q.ambient.length+
    (Asymptotic.L (BinaryArithmetic.toNat q.ambient)+1)+2

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

@[simp] theorem Query.forward_length (q : Query) :
    q.forward.length=BinaryArithmetic.toNat q.ambient := by
  simp [Query.forward,highMask]

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem initialize_eval {B d : ℕ} (hd : 0 < d)
    (c : List.Vector (Word B) d) (oneWord zeroWord minusOne : Word B)
    (s : Store) (regs : Fin 8 → Bool) (hdegree : s.degree.length = d) :
    ∃ n ≤ initializationBudget B d, ∃ rf, Eval initializeVector n
      (state regs (initialStore s c oneWord zeroWord minusOne))
      (state rf (ready {s with powers := (wordBits (initialData d oneWord zeroWord).coefficients.val).reverse, rounds := []}
        c (initialData d oneWord zeroWord) zeroWord minusOne)) := by
  let a := initialStore s c oneWord zeroWord minusOne
  let ai := {a with count := s.degree}
  have hp := copy_store_eval a ai regs 22 11 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, ai, a, initialStore])
  obtain ⟨n, hn, rf, hs⟩ := literalScan_eval d oneWord zeroWord a
    (readRegs regs 1 3 none) s.degree hdegree (by simp [a, initialStore])
  have hb : literalBits d oneWord zeroWord = wordBits (initialData d oneWord zeroWord).coefficients.val :=
    (literalWords_bits d oneWord zeroWord).symm
  have ht : literalLast d oneWord zeroWord [] = (initialData d oneWord zeroWord).last.val := by
    rw [literalLast_independent d hd oneWord zeroWord [] zeroWord.val]
    exact literalLast_word d oneWord zeroWord zeroWord
  let b := {a with left := (literalEnd d oneWord zeroWord).val, count := [], newTail := (initialData d oneWord zeroWord).last.val, output := (wordBits (initialData d oneWord zeroWord).coefficients.val).reverse}
  have hs' : Eval literalScan n (state (readRegs regs 1 3 none) ai) (state rf b) := by
    simpa only [ai, b, a, initialStore, hb, ht, List.append_nil] using hs
  have hf := finishVector_eval b rf rfl rfl
  have hendLength : (literalEnd d oneWord zeroWord).val.length = B :=
    (literalEnd d oneWord zeroWord).property
  have hlastLength : (initialData d oneWord zeroWord).last.val.length = B :=
    (initialData d oneWord zeroWord).last.property
  refine ⟨(7*(tapes a 22).length+5) +
    (n + (2*b.left.length+13*b.output.length+2*b.tail.length+9*b.newTail.length+25)),
    ?_, readRegs rf 1 3 none, ?_⟩
  · simp [a, b, initialStore, tapes, hdegree, initializationBudget,
      hendLength, hlastLength]
    nlinarith
  · simpa only [initializeVector, ready, a, ai, b, initialStore, List.reverse_reverse, List.append_nil] using
      hp.seq (hs'.seq hf)

theorem preparePowers_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ} (hd : 0 < d)
    (c : List.Vector (Word (baseWidth p t)) d) (oneWord zeroWord minusOne : Word (baseWidth p t))
    (s : Store) (regs : Fin 8 → Bool) (hmod : s.modulus = M.bits)
    (hw : s.width.length = baseWidth p t) (hdegree : s.degree.length = d) :
    ∃ n ≤ preparationBudget (baseWidth p t) d, ∃ rf, Eval preparePowers n
      (state regs (initialStore s c oneWord zeroWord minusOne))
      (state rf (ready {s with powers := allPowerBits p t M c oneWord zeroWord minusOne, rounds := []}
        c (iterData p t M zeroWord minusOne c (2*d-2) (initialData d oneWord zeroWord)) zeroWord minusOne)) := by
  let v := initialData d oneWord zeroWord
  let a := {s with powers := (wordBits v.coefficients.val).reverse, rounds := []}
  obtain ⟨ni, hni, ri, hi⟩ := initialize_eval hd c oneWord zeroWord minusOne s regs hdegree
  have hp := prepareRounds_eval (ready a c v zeroWord minusOne) ri rfl
  let rr := readRegs (readRegs (readRegs ri 1 3 none) 1 3 (s.degree ++ s.degree).head?) 1 3 (s.degree ++ s.degree).tail.head?
  obtain ⟨np, hnp, rp, hs⟩ := powerScan_eval p t M hd zeroWord minusOne c (2*d-2)
    v a rr (roundCounter s.degree) (by simp [hdegree]) hmod hw hdegree
  let b := ready {a with rounds := [], powers := (generatedBits p t M zeroWord minusOne c (2*d-2) v).reverse ++ a.powers}
    c (iterData p t M zeroWord minusOne c (2*d-2) v) zeroWord minusOne
  have hf := finishPowers_eval b rp rfl
  have hn : 2*d-2 ≤ 2*d := Nat.sub_le _ _
  have hn' : (2*d-2)+1 ≤ 2*d := by omega
  have hlength : b.powers.length ≤ 2*d*d*baseWidth p t := by
    simp only [b, ready, a, List.length_append, List.length_reverse, generatedBits_length,
      wordBits_length, List.Vector.length_val]
    calc
      (2*d-2)*d*baseWidth p t+d*baseWidth p t = ((2*d-2)+1)*(d*baseWidth p t) := by ring
      _ ≤ (2*d)*(d*baseWidth p t) := Nat.mul_le_mul_right _ hn'
      _ = 2*d*d*baseWidth p t := by ring
  have hfinish : 12*b.powers.length ≤ 24*d*d*baseWidth p t := by
    calc
      _ ≤ 12*(2*d*d*baseWidth p t) := Nat.mul_le_mul_left 12 hlength
      _ = _ := by ring
  refine ⟨ni + (14*s.degree.length+12 + (np + (12*b.powers.length+11))),
    ?_, readRegs rp 1 3 none, ?_⟩
  · have hmul := Nat.mul_le_mul_right (roundBudget (baseWidth p t) d+2) hn
    simp only [ready] at hp
    change ni + (14*s.degree.length+12 + (np + (12*b.powers.length+11))) ≤ _
    rw [hdegree]
    unfold preparationBudget
    omega
  · simpa only [preparePowers, a, b, v, rr, ready, allPowerBits, List.reverse_append,
      List.reverse_reverse] using hi.seq (hp.seq (hs.seq hf))

theorem program_run (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ} (hd : 0 < d)
    (c : List.Vector (Word (baseWidth p t)) d) (oneWord zeroWord minusOne : Word (baseWidth p t))
    (s : Store) (regs : Fin 8 → Bool) (hmod : s.modulus = M.bits)
    (hw : s.width.length = baseWidth p t) (hdegree : s.degree.length = d) :
    ∃ rf, RunsIn program (preparationBudget (baseWidth p t) d+1)
      ((state regs (initialStore s c oneWord zeroWord minusOne)).withPC (some program.entry))
      ((state rf (ready {s with powers := allPowerBits p t M c oneWord zeroWord minusOne, rounds := []}
        c (iterData p t M zeroWord minusOne c (2*d-2) (initialData d oneWord zeroWord)) zeroWord minusOne)).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := preparePowers_eval p t M hd c oneWord zeroWord minusOne s regs hmod hw hdegree
  exact ⟨rf, n+1, Nat.add_le_add_right hn 1, compiled_halt_trace he 8 0⟩

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Syntactic no-read/no-write certificate for the existing native ring
producer.  Hidden collector tapes do not affect its exact execution time. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Replay
open BitProgram StructuredCalls ProgramTapeReplay

theorem copyPlan (ps : List (Fin 640 × Fin 640))
    (hp : ∀p∈ps,¬hidden p.1 ∧ ¬hidden p.2) :
    AvoidsCmd hidden (LeafRingSetupProgram.copyPlan ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact ⟨overwrite p.1 p.2 (hp p (by simp)).1 (hp p (by simp)).2,
      ih (fun q hq => hp q (by simp [hq]))⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Replay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafScopeInputBoundsQuery
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform physical-input capacity for the produced per-query frontend data. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeInputBounds
open LeafQueryFrontend

structure QueryBounds (q : Query) (k : ℕ) : Prop where
  eight : 8 ≤ capacity q k
  ambient : BinaryArithmetic.toNat q.ambient ≤ capacity q k
  master : (Encoding.encodeList id q.clauses).length ≤ capacity q k
  rowBits : (HashScopeProgram.RawTable.inputBits q.width.length q.rows).length ≤ capacity q k
  index : q.index.length ≤ capacity q k
  modulus : q.modulus.length ≤ capacity q k
  width : q.width.length ≤ capacity q k
  ambientBits : q.ambient.length ≤ capacity q k
  widthParameter : k ≤ capacity q k
  clauseCount : q.clauses.length ≤ capacity q k
  rawRowCount : q.rows.length ≤ capacity q k
  rawRowSlots : ∀ row ∈ q.rows, row.length ≤ capacity q k
  scopeCount : q.scopeRows.length ≤ capacity q k
  scopeSlots : ∀ row ∈ q.scopeRows, row.length ≤ capacity q k
  scopeMass : LeafScopeResourceBounds.slots q.scopeRows ≤ (capacity q k)^2
  scopeBits : (LeafStatisticsProgram.scopeBits q.scopeRows).length ≤ 16*(capacity q k)^3
  forward : q.forward.length ≤ capacity q k
  free : (totals q.scopeRows q.forward).free ≤ capacity q k
  occurrence : (totals q.scopeRows q.forward).occurrence ≤ capacity q k
  incidences : (totals q.scopeRows q.forward).incidences ≤ 2*(capacity q k)^2
  uncovered : (totals q.scopeRows q.forward).uncovered ≤ capacity q k
  arity : completedArity q.scopeRows q.forward ≤ capacity q k
  factors : q.scopeRows.length+(totals q.scopeRows q.forward).uncovered ≤ 2*capacity q k

end SubexponentialSAT.SqrtLog.LeafScopeInputBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed forty-stack workspace for the two runtime readout counters. -/


/-! Actual stack construction of the sparse key (u,z,empty support), followed
by the paid query cleanup and unary-index increment. -/


/-! One concrete (u,z) coefficient fetch, addition, and index advance. -/


/-! The U loop is driven by a real unary stack. Every visit invokes the
concrete key builder and dictionary scan; no callback is left abstract. -/


/-! Seed one Z accumulator from the cached zero vector and append the
completed coefficient to the output, paying for every copy and reversal. -/


/-! Runtime Z enumeration. Completed fixed-width coefficients are prepended
in reverse and are restored once by the final output transfer. -/


/-! Build the all-false support mask from the actual ambient shape stack.
The loop length is the ambient number of variables, including unused ones. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def maskLoop : WideCode := UnaryForPrograms.forCmd maskPorts (wpush 34 false)

def makeMask : WideCode := .seq (wcopy 36 38 23) maskLoop

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! End-to-end finite readout machine. Runtime words supply both loop counts,
the ambient shape, and the already constructed coefficient zero vector. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def inputHigh (zero t J shape : List Bool) : High :=
  {zero:=zero,t:=t,J:=J,shape:=shape}

def prepare : WideCode := .seq makeMask (wcopy 29 33 23)

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NativePackingBoundsGenerated
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native address-plan frontend bounds. The source size includes the actual
input plans and the number of represented types, not a scope-generated plan. -/
namespace SubexponentialSAT.SqrtLog.NativePackingBounds
open SubexponentialSAT.Subexp LayoutProgram LayoutProgram.NativePacking
variable {U : Type*} [DecidableEq U]

theorem sourceSize_pos (s : Spec U) : 1 ≤ sourceSize s := by unfold sourceSize; omega
theorem dimension_le (s : Spec U) : s.params.D ≤ sourceSize s := by unfold sourceSize; omega
theorem width_le (s : Spec U) : s.params.width.length ≤ sourceSize s := by unfold sourceSize; omega
theorem plan_stream_input_le (s : Spec U) : s.params.planStream.length ≤ sourceSize s := by unfold sourceSize; omega
theorem plan_stream_le (s : Spec U) : s.params.planStream.length ≤ 33*sourceSize s^4 := by
  have h := PackingBudgetArithmetic.le_power (sourceSize_pos s) (by decide : 1 ≤ 4)
  have h' := plan_stream_input_le s
  omega

theorem label_cost_le (s : Spec U) :
    PackingVertexLabels.traceCost s.params.width.length s.params.planList 0 ≤
      21000 * sourceSize s ^ 7 := by
  have hp : ∀ plan ∈ s.params.planList, (PackingVertexLabels.planBytes plan).length ≤ sourceSize s := by
    intro plan hm
    have h := PackingTupleBounds.member_length_le
      (s.params.planList.map PackingVertexLabels.planPayload)
      (PackingVertexLabels.planPayload plan) (List.mem_map.mpr ⟨plan,hm,rfl⟩)
    have hframe : (PackingVertexLabels.planBytes plan).length ≤
        (PackingVertexLabels.planPayload plan).length := by
      simp only [PackingVertexLabels.planPayload,PackingVertexLabels.planBytes,Encoding.length_frame]
      omega
    exact (hframe.trans h).trans (plan_stream_input_le s)
  have hb := PackingVertexLabels.traceCost_le s.params.width.length s.params.planList 0 _ hp
  rw [NativeFrontend.Params.planList_length] at hb
  exact hb.trans (PackingBudgetArithmetic.label_trace_le _ _ _ _
    (sourceSize_pos s) (dimension_le s) (width_le s) (by have h := PackingBudgetArithmetic.le_power (sourceSize_pos s) (by decide : 1 ≤ 3); omega))

/-- The label tape starts empty, so its length is bounded by its actual
executed instruction count. No output-length certificate is assumed. -/
theorem label_stream_le (s : Spec U) : s.params.labelStream.length ≤ 21000 * sourceSize s ^ 7 := by
  have hvalid := s.plans_valid
  obtain ⟨n, rf, hn, ht⟩ := PackingVertexLabels.program_trace s.params.rows s.params.width
    s.params.planList (fun _ => false) 0 [] [] s.rows_width hvalid
  have hg := SequentialProgram.trace_stack_length_le ht (13 : Fin 15)
  have hl : s.params.labelStream.length ≤ n := by
    simpa [NativeFrontend.Params.labelStream, PackingVertexLabels.state,
      StructuredProgram.State.withPC] using hg
  exact (hl.trans hn).trans (label_cost_le s)

theorem type_stream_le (s : Spec U) : s.params.typeStream.length ≤ 5 * sourceSize s ^ 3 := by
  have h := ProgramEncoding.encodeRecords_length_le s.params.typeRows (sourceSize s ^ 2) (type_word_le s)
  rw [type_rows_count s] at h
  exact h.trans (PackingBudgetArithmetic.type_stream_le _ _ (sourceSize_pos s) (count_le s))

theorem type_cost_le (s : Spec U) :
    UniversalTypeProgram.budget s.params.alphabet s.params.Δ ≤ 10012 * sourceSize s ^ 4 := by
  have h := PackingTupleBounds.generated_powerCost_le s.params.alphabet (s.params.Δ + 1)
    (ProgramEncoding.encodeRecords s.params.alphabet).length
    (PackingTupleBounds.member_length_le s.params.alphabet)
  rw [type_power_count s] at h
  unfold UniversalTypeProgram.budget
  exact (Nat.add_le_add_right h 12).trans
    (PackingBudgetArithmetic.type_cost_le _ _ _ _ (sourceSize_pos s)
      (depth_le s) (count_le s) (alphabet_bytes_le s))

theorem frontend_bound_le (s : Spec U) :
    s.params.labelsBound+s.params.typesBound+2 ≤ 200000*sourceSize s^7 := by
  have hd : s.params.Δ ≤ sourceSize s := by have := depth_le s; omega
  have hrows : s.params.rows.flatten.length ≤ sourceSize s := by unfold sourceSize; omega
  have h := PackingBudgetArithmetic.frontend_le (sourceSize s) 0 _ _ _ _ _ _ _ _ _
    (sourceSize_pos s) (Nat.zero_le _) (dimension_le s) hd (width_le s) hrows
    (alphabet_bytes_le s) (plan_stream_le s) (label_stream_le s)
    (type_cost_le s) (type_stream_le s)
  have hl := label_cost_le s
  unfold NativeFrontend.Params.labelsBound NativeFrontend.Params.typesBound
  omega

end SubexponentialSAT.SqrtLog.NativePackingBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NativePackingBoundsTail
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Bounds for the actual packing tail

All sizes below come from the represented input and generated records.
There is no assumed runtime certificate: the cost estimates apply to the
same leftover and inverse budgets used by `PackingExecution.program_trace`.
-/

namespace SubexponentialSAT.SqrtLog.NativePackingBounds

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking LayoutProgram LayoutProgram.NativePacking

variable {U : Type*} [DecidableEq U]

theorem context_metadata_length_le (s : Spec U) :
    (PackLabels.context s.suffix).metadata.length ≤ metadataBound s.params.D s.params.typeStream.length := by
  rw [PackLabels.context_metadata s.suffix]
  exact covered_length_le s

theorem leftovers_budget_le (s : Spec U) :
    PackingProgram.leftoversBudget (PackLabels.covered s.suffix) s.params.D (PackLabels.context s.suffix) ≤
      leftoversPolynomial s.params.D s.params.typeStream.length := by
  let f := PackingProgram.leftoverResult (PackLabels.covered s.suffix) s.params.D (PackLabels.context s.suffix)
  obtain ⟨hm, ha, hs, hr⟩ := PackLabels.leftover_outputs s.suffix
  change f.metadata = s.suffix.metadata at hm
  change f.addresses = s.suffix.addresses at ha
  change f.storage.reverse ++ [false] = s.suffix.storage at hs
  change f.rank = s.suffix.packing.leftovers.length at hr
  have hmeta : f.metadata.length ≤ metadataBound s.params.D s.params.typeStream.length := by
    rw [hm]
    exact metadata_length_le s
  have haddrs : f.addresses.length ≤ addressBound s.params.D := by
    rw [ha]
    exact addresses_length_le s
  have hstorage : f.storage.length ≤ wordBound s.params.D := by
    have hlen := congrArg List.length hs
    simp only [List.length_append, List.length_reverse, List.length_singleton] at hlen
    change f.storage.length + 1 = s.suffix.storage.length at hlen
    have hb := storage_length_le s
    rw [suffix_D] at hb
    omega
  have hrank : f.rank ≤ s.params.D := by rw [hr]; exact leftovers_length_le s
  have hinit := context_address_length_le s
  have hcovered := covered_length_le s
  rw [suffix_D] at hcovered
  have hcount : (PackingLeftovers.leftovers (PackLabels.covered s.suffix) (List.range s.params.D)).length ≤
      s.params.D := by
    exact (List.length_filter_le _ _).trans (by simp)
  have hcounter := (PackingLeftovers.final_counters (PackLabels.covered s.suffix) (List.range s.params.D)
    (PackingOutputSemantics.snapshotOf (PackLabels.context s.suffix))).2
  change f.address = (PackLabels.context s.suffix).address.length +
    (PackingLeftovers.leftovers (PackLabels.covered s.suffix) (List.range s.params.D)).length at hcounter
  have haddress : f.address ≤ 2 * s.params.D := by omega
  have ht := PackingLeftovers.range_traceCost_le (PackLabels.covered s.suffix) s.params.D
    (PackingOutputSemantics.snapshotOf (PackLabels.context s.suffix))
  have ht' : PackingLeftovers.traceCost (PackLabels.covered s.suffix) (List.range s.params.D)
      (PackingOutputSemantics.snapshotOf (PackLabels.context s.suffix)) ≤
      4 + s.params.D * ((45 * s.params.D + 109) *
        metadataBound s.params.D s.params.typeStream.length + 123 * s.params.D + 155) := by
    calc
      _ ≤ 4 + s.params.D * ((45 * s.params.D + 109) *
        (SelectorProgram.rawRecords (PackLabels.covered s.suffix)).length + 62 * s.params.D +
        31 * s.params.D + 15 * ((PackLabels.context s.suffix).address.length + s.params.D) + 155) := by
          simpa only [PackingOutputSemantics.snapshotOf, Nat.zero_add] using ht
      _ ≤ 4 + s.params.D * ((45 * s.params.D + 109) *
        metadataBound s.params.D s.params.typeStream.length + 62 * s.params.D +
        31 * s.params.D + 15 * (s.params.D + s.params.D) + 155) := by gcongr
      _ = _ := by ring
  change PackingLeftovers.traceCost (PackLabels.covered s.suffix) (List.range s.params.D)
      (PackingOutputSemantics.snapshotOf (PackLabels.context s.suffix)) + 6 * f.rank + 6 * f.metadata.length +
      6 * f.addresses.length + 3 * f.storage.length +
      2 * (SelectorProgram.rawRecords (PackLabels.covered s.suffix)).length + 2 * f.address + 32 ≤ _
  unfold leftoversPolynomial
  omega

/-- Both actual tail stages have a fixed fourth-degree bound in the vertex
count and the bytes of the generated type stream. -/
theorem tail_budget_le (s : Spec U) :
    PackingProgram.leftoversBudget (PackLabels.covered s.suffix) s.params.D (PackLabels.context s.suffix) +
      PackingProgram.inverseBudget (PackLabels.addressRecords s.suffix) s.params.D ≤
      30000 * (s.params.D + s.params.typeStream.length + 1) ^ 4 := by
  let N := s.params.D + s.params.typeStream.length + 1
  have hD : s.params.D ≤ N := by dsimp [N]; omega
  have hT : s.params.typeStream.length ≤ N := by dsimp [N]; omega
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hp (k : ℕ) : N ^ k ≤ N ^ (k + 1) := by
    rw [pow_succ]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (N ^ k) hN
  have h01 : 1 ≤ N := hN
  have h12 : N ≤ N ^ 2 := by simpa using hp 1
  have h23 : N ^ 2 ≤ N ^ 3 := hp 2
  have h34 : N ^ 3 ≤ N ^ 4 := hp 3
  calc
    _ ≤ leftoversPolynomial s.params.D s.params.typeStream.length + inversePolynomial s.params.D :=
      Nat.add_le_add (leftovers_budget_le s) (inverse_budget_le s)
    _ ≤ leftoversPolynomial N N + inversePolynomial N := by
      unfold leftoversPolynomial inversePolynomial metadataBound addressBound wordBound
      gcongr
    _ = 4450 * N ^ 4 + 7450 * N ^ 3 + 8171 * N ^ 2 + 3308 * N + 1084 := by
      unfold leftoversPolynomial inversePolynomial metadataBound addressBound wordBound
      ring
    _ ≤ 30000 * N ^ 4 := by omega

end SubexponentialSAT.SqrtLog.NativePackingBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NativePackingBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial cost of the actual native address-plan suffix. -/
namespace SubexponentialSAT.SqrtLog.NativePackingBounds
open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram LayoutProgram
variable {U : Type*} [DecidableEq U]

theorem record_bytes_le (s : NativePacking.Spec U) :
    (BucketProgram.encodeRecords (PackLabels.records s.suffix)).length ≤ 21000 * sourceSize s ^ 7 := by
  have h := label_stream_le s
  rw [input_labels s, PackingBucketTable.encodeRecords_length_reverse] at h
  exact h

theorem table_payload_le (s : NativePacking.Spec U) :
    ∀ payload ∈ PackingBucketTable.table (PackLabels.records s.suffix) (PackLabels.keys s.suffix),
      payload.length ≤ 21003 * sourceSize s ^ 7 := by
  intro payload hp
  exact (PackingBucketTable.table_payload_bound (PackLabels.records s.suffix) (PackLabels.keys s.suffix) (sourceSize s ^ 2)
    (keys_word_le s) payload hp).trans
      (PackingBudgetArithmetic.bucket_payload_le _ _ (sourceSize_pos s) (record_bytes_le s))

theorem table_bytes_le (s : NativePacking.Spec U) :
    (ProgramEncoding.encodeRecords (PackingBucketTable.table (PackLabels.records s.suffix) (PackLabels.keys s.suffix))).length ≤
      43000 * sourceSize s ^ 8 := by
  have h := PackingBucketTable.table_encoded_bound (PackLabels.records s.suffix) (PackLabels.keys s.suffix) (sourceSize s ^ 2)
    (keys_word_le s)
  rw [keys_count] at h
  exact h.trans (PackingBudgetArithmetic.bucket_table_le _ _ _ (sourceSize_pos s)
    (count_le s) (record_bytes_le s))

theorem bucket_core_le (s : NativePacking.Spec U) :
    PackingBucketTable.budget (PackLabels.records s.suffix) (PackLabels.keys s.suffix) ≤ 4400000 * sourceSize s ^ 10 := by
  have h := PackingBucketTable.budget_bound (PackLabels.records s.suffix) (PackLabels.keys s.suffix) (sourceSize s ^ 2)
    (keys_word_le s)
  rw [keys_count] at h
  exact h.trans (PackingBudgetArithmetic.bucket_core_le _ _ _ (sourceSize_pos s)
    (count_le s) (record_bytes_le s))

theorem buckets_budget_le (s : NativePacking.Spec U) :
    PackingProgram.bucketsBudget (PackLabels.records s.suffix) (PackLabels.keys s.suffix) s.params.D ≤ 5000000 * sourceSize s ^ 10 := by
  unfold PackingProgram.bucketsBudget
  rw [PackingBucketTable.encodeRecords_length_reverse, ← input_types s]
  exact PackingBudgetArithmetic.bucket_stage_le _ _ _ _ _ _ _ (sourceSize_pos s)
    (record_bytes_le s) (type_stream_le s) (dimension_le s) (table_bytes_le s)
    ((PackingBucketTable.minimum_le _ _ _).trans (dimension_le s)) (bucket_core_le s)

theorem entries_word_le (s : NativePacking.Spec U) :
    ∀ entry ∈ PackLabels.entries s.suffix, (PackingExtraction.entryWord entry).length ≤ 21003 * sourceSize s ^ 7 := by
  intro entry he
  apply table_payload_le s
  rw [PackLabels.table_eq s.suffix]
  exact List.mem_map.mpr ⟨entry, he, rfl⟩

theorem entries_bytes_le (s : NativePacking.Spec U) :
    (ProgramEncoding.encodeRecords ((PackLabels.entries s.suffix).map PackingExtraction.entryWord)).length ≤
      43000 * sourceSize s ^ 8 := by
  rw [← PackLabels.table_eq s.suffix]
  exact table_bytes_le s

theorem metadata_bytes_le (s : NativePacking.Spec U) : (PackLabels.context s.suffix).metadata.length ≤ 34 * sourceSize s ^ 4 := by
  exact (context_metadata_length_le s).trans
    (PackingBudgetArithmetic.metadata_le _ _ _ (sourceSize_pos s) (dimension_le s) (type_stream_le s))

theorem extraction_loop_le (s : NativePacking.Spec U) :
    PackingExtraction.loopBudget (PackLabels.entries s.suffix) s.suffix.packing.blockCount 0
      (PackingProgram.initialExtraction (PackLabels.entries s.suffix) s.suffix.packing.blockCount) ≤
        2700000 * sourceSize s ^ 9 := by
  have hn : s.suffix.packing.blockCount ≤ sourceSize s := (block_count_le s).trans (dimension_le s)
  have hN : (PackLabels.entries s.suffix).length ≤ sourceSize s := by rw [entries_count]; exact count_le s
  have hprod : s.suffix.packing.blockCount * (PackLabels.entries s.suffix).length ≤ sourceSize s ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hn hN
  have h := PackingExtraction.loopBudget_le (PackLabels.entries s.suffix) s.suffix.packing.blockCount 0
    (PackingProgram.initialExtraction (PackLabels.entries s.suffix) s.suffix.packing.blockCount)
    (21003 * sourceSize s ^ 7) (sourceSize s) (sourceSize s ^ 2) (entries_word_le s)
    (by simpa [PackingProgram.initialExtraction] using hn)
    (by simpa [PackingProgram.initialExtraction] using hprod)
  apply h.trans
  exact PackingBudgetArithmetic.extraction_loop_le _ _ _ _ _ (sourceSize_pos s) hn hN
    (entries_bytes_le s) le_rfl

theorem extraction_budget_le (s : NativePacking.Spec U) :
    PackingProgram.extractionBudget (PackLabels.entries s.suffix) s.suffix.packing.blockCount ≤ 2800000 * sourceSize s ^ 9 := by
  exact PackingBudgetArithmetic.extraction_stage_le _ _ _ _ _ (sourceSize_pos s)
    (extraction_loop_le s) ((block_count_le s).trans (dimension_le s))
    (entries_bytes_le s) (metadata_bytes_le s)

theorem vertices_budget_le (s : NativePacking.Spec U) :
    PackingProgram.verticesBudget s.params.D ≤ 400 * sourceSize s ^ 2 := by
  have hb : s.params.D + 1 ≤ 2 * sourceSize s := by
    have := dimension_le s
    have := sourceSize_pos s
    omega
  apply (PackingProgram.verticesBudget_le s.params.D).trans
  calc
    _ ≤ 100 * (2 * sourceSize s) ^ 2 := by gcongr
    _ = _ := by ring

theorem tail_budget_scaled_le (s : NativePacking.Spec U) :
    PackingProgram.leftoversBudget (PackLabels.covered s.suffix) s.params.D (PackLabels.context s.suffix) +
      PackingProgram.inverseBudget (PackLabels.addressRecords s.suffix) s.params.D ≤ 72030000 * sourceSize s ^ 12 :=
  (tail_budget_le s).trans
    (PackingBudgetArithmetic.tail_le _ _ _ (sourceSize_pos s) (dimension_le s) (type_stream_le s))

end SubexponentialSAT.SqrtLog.NativePackingBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NativePackingBoundsAddress
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit scalar envelope for the actual two-address packing call. -/
namespace SubexponentialSAT.SqrtLog.NativePackingBounds
open SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes LayoutProgram

variable {D r Q : ℕ}

theorem address_sourceSize_le (hr : 0 < r) (hQ : 0 < Q)
    (words : List (Word r Q))
    (address : Fin D → Fin words.length × Fin words.length) :
    sourceSize (NativePacking.addressSpec hr hQ words address) ≤ addressSize D words.length r Q := by
  have hw : ∀ row∈words.map ReadPlan.encodeWord, row.length ≤ Q*r := by
    intro row hm
    obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hm
    simp [ReadPlan.encodeWord_length,ReadPlan.wordWidth]
  have hf := PairScoreBounds.volume_le (words.map ReadPlan.encodeWord) (Q*r) hw
  have hf' : (words.map ReadPlan.encodeWord).flatten.length ≤ words.length*(Q*r) := by
    simpa [List.length_flatten,PairScoreBounds.volume] using hf
  have ha := ProgramEncoding.encodeRecords_length_le (AssignmentAlphabetSemantics.wordBytes r Q)
    (Q*r) (fun row hm => (AssignmentAlphabetSemantics.wordBytes_width hr row hm).le)
  rw [AssignmentAlphabetSemantics.wordBytes_length] at ha
  have ht := PackingCanonicalSpec.types_length hr hQ 1
  simp only [blockSize,Nat.reduceAdd] at ht
  rw [Nat.mul_comm Q 2] at ht
  have hp := address_plan_stream_le words address
  unfold sourceSize addressSize
  dsimp only [NativePacking.addressSpec,NativeFrontend.Params.planStream]
  simp only [List.length_replicate,ht]
  omega

end SubexponentialSAT.SqrtLog.NativePackingBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Convert a physically scanned factor-index stream to incidence plans. -/


/-! Native per-variable incident-factor scan from the original scope stream. -/


/-! Fixed cleanup for the native scope-address scanner. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

namespace Clear
def after (j : Fin 32) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks j []⟩
theorem one_eval (j : Fin 32) (d : Data) :
    Eval (one j) (2*(d.stacks j).length+3) d (after j d) := by
  simpa [one,after,StackRoutines.clearStacks] using
    TupleProgram.clear_eval j (0 : Fin 16) 1 d
end Clear
end SubexponentialSAT.SqrtLog.PackingIncidenceInput


/-! Calls to the fixed record mapper inside the native scope scan. -/


/-! One native low-variable step, including its uncovered neutral factor. -/


/-! Runtime high-mask loop for the original-address incidence stream. -/


/-! Count the physical scope stream before constructing native incidence plans. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev fullCommand : Cmd 16 32 := .seq command Loop.command
def fullProgram := compiled fullCommand 20 25
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramWide
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The caller's private64-stack workspace lies after the live native
parameter bank340..416, which must survive until ring setup. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def project (a : Data) : Local := ⟨a.regs ∘ registers,a.stacks⟩

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput
attribute [local simp] Fin.coe_ofNat_eq_mod

structure Sources (a : Wide.Data) (p : Problem) : Prop where
  scopes : a.stacks 718=Scan.scopeBits p.scopes
  ambientUnary : a.stacks 128=Scan.unary p.n
  mask : a.stacks 719=p.mask
  ambient : SubexponentialSAT.BinaryArithmetic.toNat (a.stacks 709)=p.n
  coordinate : SubexponentialSAT.BinaryArithmetic.toNat (a.stacks 720)=p.Q
  radius : SubexponentialSAT.BinaryArithmetic.toNat (a.stacks 721)=p.r
  epsilon : SubexponentialSAT.BinaryArithmetic.toNat (a.stacks 722)=p.s
  incidence : SubexponentialSAT.BinaryArithmetic.toNat (a.stacks 723)=p.incidences

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end


