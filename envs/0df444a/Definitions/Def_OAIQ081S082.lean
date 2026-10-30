-- Prove2me | Definitions.Def_OAIQ081S082
-- name    : OAIQ081S082
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:03:23.034678+00:00
-- url     : https://prove2.me/theorems/a87a3dd5-bc42-45ef-bb4f-f0d8e0b4cc9e
-- title:
--   Definitions bundle OAIQ081S082 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 128 declarations of OpenAI's Lean: 82 definitions, 1 inductive type or structure and 45 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.DensePolynomialPrograms.addWordsTotal`, `OAI.Algorithms.SubexponentialSAT.DensePolynomialPrograms.wordStep`, `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.BodySpec`, `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.Visits`, `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.advanceCmd`, `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.advanceResult`, `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.enumerate`, `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.incrementCmd`, `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.loopCmd`, `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.program`, `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.startCmd`, `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration.startResult`, `OAI.Algorithms.SubexponentialSAT.ExecClauseDedupProgram.callback`, `OAI.Algorithms.SubexponentialSAT.ExecClauseDedupProgram.command`, `OAI.Algorithms.SubexponentialSAT.ExecClauseDedupProgram.program`, `OAI.Algorithms.SubexponentialSAT.ExecClauseDedupProgram.scan`, `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.callback`, `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.filterScan`, `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.scan`, `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.selfFilter`, `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.selfFilterProgram`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.Preserving.command`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.Preserving.program`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.Preserving.scanner`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.callback`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.command`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.program`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan.relationProgram`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationsProgram.command`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationsProgram.compare`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationsProgram.program`, `OAI.Algorithms.SubexponentialSAT.ExecClauseRelationsProgram.subsetProgram`, `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.command`, `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.eraseWithAccumulator`, `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.prepare`, `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.program`, `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.command`, `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.prepare`, `OAI.Algorithms.SubexponentialSAT.PowerCalls.Data`, `OAI.Algorithms.SubexponentialSAT.PowerCalls.Valid` and 43 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_DensePolynomialPrograms`, `SubexponentialSAT_ExecCNFMembership`, `SubexponentialSAT_ExecCNFSubset`, `SubexponentialSAT_ExecCNFTupleEnumeration`, `SubexponentialSAT_ExecClauseDedupProgram`, `SubexponentialSAT_ExecClauseFiltersProgram`, `SubexponentialSAT_ExecClauseRelationScan`, `SubexponentialSAT_ExecClauseRelationScanPreserve`, `SubexponentialSAT_ExecClauseRelationsProgram`, `SubexponentialSAT_ExecClauseSelfFilterProgram`, `SubexponentialSAT_ExecCoreChildProgram`, `SubexponentialSAT_ExecPetalChildProgram`, `SubexponentialSAT_ModularRingPrograms`, `SubexponentialSAT_PowerCalls`, `SubexponentialSAT_PowerPrograms`, `SubexponentialSAT_SqrtLog_BucketProgramPreprocessMatrix`, `SubexponentialSAT_SqrtLog_BucketProgramPreprocessRow`, `SubexponentialSAT_SqrtLog_BucketProgramPreprocessStep`, `SubexponentialSAT_SqrtLog_BucketProgramRow`, `SubexponentialSAT_SqrtLog_BucketProgramShift`, `SubexponentialSAT_SqrtLog_BucketProgramSignature`, `SubexponentialSAT_SqrtLog_RingProgramModel`, `SubexponentialSAT_SqrtLog_RingProgramQuotient`, `SubexponentialSAT_SqrtLog_RingProgramWords`, `SubexponentialSAT_SubexpFlatAdd`, `SubexponentialSAT_SubexpLiftRing`, `SubexponentialSAT_SubexpNormalizationProgram`, `SubexponentialSAT_SubexpPreparedQuartic`, `SubexponentialSAT_UnaryForPrograms`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S066`, `OAIQ081S067` and `OAIQ081S068` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S100`, `OAIQ081S101`, `OAIQ081S102`, `OAIQ081S103`, `OAIQ081S104`, `OAIQ081S107`, `OAIQ081S109`, `OAIQ081S110`, `OAIQ081S111`, `OAIQ081S113`, `OAIQ081S114` and `OAIQ081S115`; the statements `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.scan_eval`, `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preMatrixProgram_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preScan_eval`, `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.absorb_eval` and `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.removeSupersetsCall_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.scan_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preMatrixProgram_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preScan_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.rowCommand_eval` and `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixVectorProgram.matrix_trace`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S066
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S068

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLiftRing
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Uniform coefficient representations for the growing-parameter argument

Every base residue has an explicit little-endian word of width
`mu * (Nat.log 2 p + 1)`. The polynomial quotient uses one such word per
basis coefficient. These bounds keep p and mu visible. Binary modular
operations below use the existing bit/list algorithms and normalize back
to the prescribed width; their counters are source-level finite events,
not a claimed Turing-machine simulation.
-/

namespace SubexponentialSAT.SubexpLiftRing

open SubexponentialSAT.BinaryArithmetic

theorem mulBaseRun_value (B : ℕ) (modulus xs ys : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    BinaryArithmetic.toNat (mulBaseRun B modulus xs ys).1 = (BinaryArithmetic.toNat xs * BinaryArithmetic.toNat ys) % BinaryArithmetic.toNat modulus := by
  rw [mulBaseRun, normalizeBits_value]
  · exact ModularArithmetic.mulModRun_correct modulus xs ys hm
  · rw [ModularArithmetic.mulModRun_correct modulus xs ys hm]
    exact (Nat.mod_lt _ hm).trans_le hcap

end SubexponentialSAT.SubexpLiftRing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPreparedQuartic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Quartic operations with a stored modulus

The modulus is input data. None of the operations in this file computes
`p^mu`, its bit expansion, or an irreducible polynomial. Setup is separate.
-/

namespace SubexponentialSAT.SubexpPreparedQuartic

open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable (p μ : ℕ) [Fact p.Prime]

variable (M : Modulus p μ)

theorem wordMul_correct (x y : Word (baseWidth p μ)) :
    wordValue p μ (wordMul p μ M x y).1 = wordValue p μ x * wordValue p μ y := by
  unfold wordValue wordMul
  dsimp only
  rw [mulBaseRun_value]
  · simp only [M.value, ZMod.natCast_mod, Nat.cast_mul]
  · rw [M.value]; exact pow_pos (Fact.out : p.Prime).pos μ
  · rw [M.value]; exact modulus_le_width p μ

end SubexponentialSAT.SubexpPreparedQuartic

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

theorem wordMul_value (regs : Fin 8 → Bool) (xs ys modulus : List Bool) (B : ℕ)
    (hx : xs.length = B) (hy : ys.length = B) (hmLength : modulus.length ≤ B + 1)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ finalRegs output,
      RunsIn wordMulProgram (6000 * (B + 1) ^ 2)
        ⟨some wordMulProgram.entry, regs, extendSeven (scalarInput xs ys modulus) []⟩
        ⟨none, finalRegs, extendSeven (resting output modulus []) []⟩ ∧
      output.length = B ∧
      BinaryArithmetic.toNat output = (BinaryArithmetic.toNat xs * BinaryArithmetic.toNat ys) % BinaryArithmetic.toNat modulus := by
  obtain ⟨r1, out, hr, hlen, hv⟩ :=
    mulMod_value (readRegs regs 1 3 none) xs ys modulus hm
  obtain ⟨rf, ht⟩ := canonical_execute mulModProgram regs r1 xs ys modulus out
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFlatAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

theorem addOne_eval (regs : Fin 8 → Bool) (x y : Word (baseWidth p μ))
    (left right width packed : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = baseWidth p μ) :
    ∃ n ≤ wordCost (baseWidth p μ), ∃ regs',
      Eval addOne n
        (ready regs M.bits (x.val ++ left) (y.val ++ right) width packed frame)
        (ready regs' M.bits left right width
          ((SubexpPreparedQuartic.wordAdd p μ M x y).1.val.reverse ++ packed) frame) := by
  let regs₁ := readRegs regs 0 1 none
  let d₀ := ready regs M.bits (x.val ++ left) (y.val ++ right) width packed frame
  let d₁ := state regs₁ x.val [] M.bits left (y.val ++ right) width [] [] packed frame
  have h₁ : Eval (takeWord 10 11 12 8 0 0 1) (14*baseWidth p μ+11) d₀ d₁ := by
    have h := takeWord_eval d₀ 10 11 12 8 0 0 1 (by decide) (by decide)
      x.val left rfl rfl rfl (hwidth.trans x.property.symm)
    have he : afterTake d₀ 8 0 0 1 x.val left = d₁ :=
      take_left_state regs x.val M.bits left (y.val ++ right) width packed frame
    simpa only [x.property,he] using h
  let d₂ := state regs₁ x.val y.val M.bits left right width [] [] packed frame
  have h₂ : Eval (takeWord 10 11 12 9 1 0 1) (14*baseWidth p μ+11) d₁ d₂ := by
    have h := takeWord_eval d₁ 10 11 12 9 1 0 1 (by decide) (by decide)
      y.val right rfl rfl rfl (hwidth.trans y.property.symm)
    have he : afterTake d₁ 9 1 0 1 y.val right = d₂ := by
      simpa only [d₁,d₂,regs₁,StackRoutines.readRegs_reset] using
        take_right_state regs₁ x.val y.val M.bits left right width packed frame
    simpa only [y.property,he] using h
  obtain ⟨n, hn, regs₂, h₃⟩ := addScalar_eval p μ M regs₁ x y left right width packed frame
  let z := (SubexpPreparedQuartic.wordAdd p μ M x y).1
  let d₃ := state regs₂ z.val [] M.bits left right width [] [] packed frame
  have h₄ : Eval (.call (StackRoutines.transferProgram 0 13 (0 : Fin 8) 1))
      (3*baseWidth p μ+3) d₃
      (ready (readRegs regs₂ 0 1 none) M.bits left right width (z.val.reverse++packed) frame) := by
    have h := transfer_eval d₃ 0 13 0 1 (by decide) (by decide)
    have he : afterTransfer d₃ 0 13 0 1 =
        ready (readRegs regs₂ 0 1 none) M.bits left right width (z.val.reverse++packed) frame :=
      transfer_sum_state regs₂ z.val M.bits left right width packed frame
    have hl : (d₃.stacks 0).length = baseWidth p μ := z.property
    simpa only [hl,he] using h
  refine ⟨(14*baseWidth p μ+11)+(14*baseWidth p μ+11+(n+(3*baseWidth p μ+3))),
    ?_, readRegs regs₂ 0 1 none, Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ h₄))⟩
  unfold wordCost
  omega

end SubexponentialSAT.SubexpFlatAdd

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_DensePolynomialPrograms
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed streaming program for dense polynomial addition

Quartic coefficients are four consecutive fixed-width base words. The loop
uses the actual modular-word addition program and tests the input stacks.
Its instruction table is independent of the array lengths and the width.
-/

namespace SubexponentialSAT.DensePolynomialPrograms

open BitProgram StructuredCalls DensePolynomialLoop
open SubexpLiftRing SubexpQuarticRing

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

/-- The generic loop premise is discharged by the existing actual scalar trace. -/
def wordStep : DensePolynomialLoop.WordStep (baseWidth p μ) where
  cmd := SubexpFlatAdd.addOne
  modulus := M.bits
  add x y := (SubexpPreparedQuartic.wordAdd p μ M x y).1
  cost := SubexpFlatAdd.wordCost (baseWidth p μ)
  run := SubexpFlatAdd.addOne_eval p μ M

def addWordsTotal := DensePolynomialLoop.addWordsTotal (wordStep p μ M)

end SubexponentialSAT.DensePolynomialPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFMembership
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

/-- Actual call traces, not a semantic equality instruction, implement the
callback. The preserved query and source suffix make another iteration safe. -/
theorem callback_eval (d : Data) (hcopy : d.stacks 3 = []) (htmp : d.stacks 4 = []) :
    ∃ n ≤ 20 * ((d.stacks 1).length + (d.stacks 2).length + 1), ∃ e : Data,
      Eval callback n d e ∧
      e.regs 4 = decide (d.stacks 1 = d.stacks 2) ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = [] ∧ e.stacks 2 = d.stacks 2 ∧
      e.stacks 3 = [] ∧ e.stacks 4 = [] ∧
      e.regs 5 = d.regs 5 ∧ e.regs 6 = d.regs 6 := by
  obtain ⟨n, hn, e, heval, hanswer, hsource, hquery, htemp, hleft, hright, htag, hpresent⟩ :=
    SubexponentialSAT.ExecClauseCost.membershipEq_eval (copied d)
  simp only [copied_stack_zero, copied_stack_one, copied_stack_two, copied_stack_three,
    copied_stack_four, copied_reg_five, copied_reg_six, hcopy, List.append_nil]
      at hn hanswer hsource hquery htemp hleft hright htag hpresent
  let result := cleared 3 (cleared 1 e)
  let steps := (7 * (d.stacks 2).length + 5) +
    (n + ((2 * (e.stacks 1).length + 3) + (2 * (e.stacks 3).length + 3)))
  refine ⟨steps, ?_, result, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [steps]
    omega
  · apply Eval.seq (copyQuery_eval d htmp)
    apply Eval.seq heval
    apply Eval.seq (clear_eval 1 e)
    simpa [result, cleared, StackRoutines.clearStacks] using clear_eval 3 (cleared 1 e)
  · simpa [result] using hanswer
  · simpa [result, cleared, StackRoutines.clearStacks] using hsource
  · simp [result, cleared, StackRoutines.clearStacks]
  · simpa [result, cleared, StackRoutines.clearStacks] using hquery
  · simp [result]
  · simpa [result, cleared, StackRoutines.clearStacks, htmp] using htemp
  · simpa [result] using htag
  · simpa [result] using hpresent


theorem callback_contract (query : List Bool) :
    RecordPrograms.CallbackContract ports callback (fun bits => decide (bits = query))
      (perRecordCost query) (invariant query) := by
  intro bits tail base hbase
  rcases hbase with ⟨hquery, hcopy, htmp⟩
  let d := RecordPrograms.state ports base false true false tail bits.reverse
  have hd0 : d.stacks 0 = tail := by simp [d, RecordPrograms.state ]
  have hd1 : d.stacks 1 = bits.reverse := by simp [d, RecordPrograms.state ]
  have hd2 : d.stacks 2 = query.reverse := by simp [d, RecordPrograms.state, hquery]
  have hd3 : d.stacks 3 = [] := by simp [d, RecordPrograms.state, hcopy]
  have hd4 : d.stacks 4 = [] := by simp [d, RecordPrograms.state, htmp]
  have hd5 : d.regs 5 = false := by simp [d, RecordPrograms.state ]
  have hd6 : d.regs 6 = true := by simp [d, RecordPrograms.state ]
  obtain ⟨n, hn, e, he, ha, hs, hp, hq, hc, ht, hv, hpr⟩ := callback_eval d hd3 hd4
  have heq : e.regs 4 = decide (bits = query) := by simpa [hd1, hd2] using ha
  have es : e.stacks 0 = tail := hs.trans hd0
  have ev : e.regs 5 = false := hv.trans hd5
  have epr : e.regs 6 = true := hpr.trans hd6
  have eState : RecordPrograms.state ports e false true (decide (bits = query)) tail [] = e :=
    RecordPrograms.state_eq_self ports e _ _ _ _ _ ev epr heq es hp
  refine ⟨n, e, ?_, ⟨hq.trans hd2, hc, ht⟩, ?_⟩
  · simpa [perRecordCost, hd1, hd2] using hn
  · rw [eState]
    exact he

theorem membership_eval (query : List Bool) (records : List (List Bool))
    (suffix : List Bool) (base : Data) (valid : invariant query base) (v pr f : Bool) :
    ∃ (n : ℕ) (next : Data), n ≤ 4 + RecordPrograms.budget (perRecordCost query) records ∧
      invariant query next ∧
      Eval membership n
        (RecordPrograms.state ports base v pr f (Encoding.encodeList id records ++ suffix) [])
        (RecordPrograms.state ports next false true (decide (query ∈ records))
          (RecordPrograms.unread (fun bits => decide (bits = query)) records suffix)
          [decide (query ∈ records)]) := by
  obtain ⟨n, next, hn, hnext, he⟩ := RecordPrograms.iterate_run ports callback
    (fun bits => decide (bits = query)) (perRecordCost query) (invariant query)
    (callback_contract query) records suffix base valid v pr f
  rw [any_eq_membership] at he
  exact ⟨n + 1, next, by omega, hnext, Eval.seq he (emit_eval _ _ _)⟩

theorem membership_runsIn (query : List Bool) (records : List (List Bool))
    (suffix : List Bool) (base : Data) (valid : invariant query base) (v pr f : Bool) :
    ∃ next : Data, invariant query next ∧
      RunsIn membershipProgram
        ((20 * query.length + 30) * (Encoding.encodeList id records).length + 2)
        ((RecordPrograms.state ports base v pr f
          (Encoding.encodeList id records ++ suffix) []).withPC (some membershipProgram.entry))
        ((RecordPrograms.state ports next false true (decide (query ∈ records))
          (RecordPrograms.unread (fun bits => decide (bits = query)) records suffix)
          [decide (query ∈ records)]).withPC none) := by
  obtain ⟨n, next, hn, hnext, he⟩ := membership_eval query records suffix base valid v pr f
  refine ⟨next, hnext, n + 1, ?_, compiled_halt_trace he 0 1⟩
  have hbudget := budget_le query records
  omega


end SubexponentialSAT.ExecCNFMembership

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFSubset
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

/-- The real membership program lifted into the subset caller. Only its assigned
ports change; its output bit and residual sizes are explicit. -/
theorem memberCall_eval (query : List Bool) (records : List (List Bool)) (d : Data)
    (hsrc : d.stacks 3 = Encoding.encodeList id records)
    (hquery : d.stacks 1 = query.reverse) (hout : d.stacks 4 = [])
    (hcopy : d.stacks 5 = []) (htmp : d.stacks 6 = []) :
    ∃ n ≤ (20 * query.length + 30) * (Encoding.encodeList id records).length + 2,
      ∃ e : Data, Eval memberCall n d e ∧
      e.regs 4 = decide (query ∈ records) ∧
      (e.stacks 3).length ≤ (Encoding.encodeList id records).length ∧
      e.stacks 4 = [decide (query ∈ records)] ∧ e.stacks 1 = query.reverse ∧
      e.stacks 5 = [] ∧ e.stacks 6 = [] ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 2 = d.stacks 2 ∧ e.stacks 7 = d.stacks 7 ∧
      e.regs 7 = d.regs 7 ∧ e.regs 8 = d.regs 8 ∧ e.regs 9 = d.regs 9 := by
  let a : State 7 5 := ⟨d.regs ∘ memberReg, d.stacks ∘ memberStack⟩
  have hvalid : ExecCNFMembership.invariant query a := by
    exact ⟨hquery, hcopy, htmp⟩
  have hstart : RecordPrograms.state ExecCNFMembership.ports a
      (a.regs 5) (a.regs 6) (a.regs 4) (Encoding.encodeList id records ++ []) [] = a := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simpa [a, memberStack] using hsrc
    · exact hout
  obtain ⟨next, hnext, n, hn, ht⟩ := ExecCNFMembership.membership_runsIn
    query records [] a hvalid (a.regs 5) (a.regs 6) (a.regs 4)
  rw [hstart] at ht
  let b := RecordPrograms.state ExecCNFMembership.ports next false true
    (decide (query ∈ records)) (RecordPrograms.unread (fun bits => decide (bits = query)) records [])
    [decide (query ∈ records)]
  have heval := eval_call_lifted ExecCNFMembership.membershipProgram memberReg memberStack d
    memberReg_injective memberStack_injective ht
  have hea : embedState memberReg memberStack d a = d :=
    embed_restricted _ _ memberReg_injective memberStack_injective d
  rw [hea] at heval
  let e := embedState memberReg memberStack d b
  have hstack (i : Fin 5) : e.stacks (memberStack i) = b.stacks i :=
    embedState_stack _ _ _ _ memberStack_injective i
  have hreg (i : Fin 7) : e.regs (memberReg i) = b.regs i :=
    embedState_register _ _ _ _ memberReg_injective i
  refine ⟨n, hn, e, heval, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change e.regs (memberReg 4) = _
    rw [hreg]
    simp [b, RecordPrograms.state ]
  · change (e.stacks (memberStack 0)).length ≤ _
    rw [hstack]
    simpa [b, RecordPrograms.state, ExecCNFMembership.ports] using
      unread_length_le (fun bits => decide (bits = query)) records
  · change e.stacks (memberStack 1) = _
    rw [hstack]
    simp [b, RecordPrograms.state ]
  · change e.stacks (memberStack 2) = _
    rw [hstack]
    simpa [b, RecordPrograms.state, ExecCNFMembership.ports] using hnext.1
  · change e.stacks (memberStack 3) = _
    rw [hstack]
    simpa [b, RecordPrograms.state, ExecCNFMembership.ports] using hnext.2.1
  · change e.stacks (memberStack 4) = _
    rw [hstack]
    simpa [b, RecordPrograms.state, ExecCNFMembership.ports] using hnext.2.2
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)

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

variable {R S : ℕ}

abbrev incrementCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .call (ProgramLinking.liftProgram ExecCNFTupleOdometer.program p.register
    (CounterForPrograms.stackPorts p))

abbrev advanceCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .seq (incrementCmd p) (.base (.atom (.bnot (p.register 2) (p.register 2))))

noncomputable def advanceResult (p : Ports R S) (d : Data R S)
    (words : List (List Bool)) : Data R S :=
  (Atom.bnot (p.register 2) (p.register 2)).eval (incrementResult p d words)

@[simp] theorem advanceResult_flag (p : Ports R S) (d : Data R S) (words : List (List Bool)) :
    (advanceResult p d words).regs (p.register 2) = !(bumpWords words).1 := by
  simp [advanceResult, Atom.eval, State.ofCfg, Atom.instr, execInstr,
    incrementResult]

@[simp] theorem advanceResult_counter (p : Ports R S) (d : Data R S) (words : List (List Bool)) :
    (advanceResult p d words).stacks p.counter = Encoding.encodeList id (bumpWords words).2 := by
  change (incrementResult p d words).stacks p.counter = _
  simp [incrementResult]

@[simp] theorem advanceResult_scratch (p : Ports R S) (d : Data R S) (words : List (List Bool)) :
    (advanceResult p d words).stacks p.scratch = [] := by
  change (incrementResult p d words).stacks p.scratch = _
  simp [incrementResult]

abbrev startCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .base (.atom (.set (p.register 2) true))

def startResult (p : Ports R S) (d : Data R S) : Data R S :=
  (Atom.set (p.register 2) true).eval d

@[simp] theorem startResult_flag (p : Ports R S) (d : Data R S) :
    (startResult p d).regs (p.register 2) = true := by
  simp [startResult, Atom.eval, State.ofCfg, Atom.instr, execInstr ]

@[simp] theorem startResult_stacks (p : Ports R S) (d : Data R S) :
    (startResult p d).stacks = d.stacks := rfl

abbrev loopCmd (p : Ports R S) (body : StructuredCalls.Cmd R S) : StructuredCalls.Cmd R S :=
  .while (p.register 2) (.seq body (advanceCmd p))

abbrev enumerate (p : Ports R S) (body : StructuredCalls.Cmd R S) : StructuredCalls.Cmd R S :=
  .seq (startCmd p) (loopCmd p body)

/-- The log contains the payload rank at every actual callback invocation. -/
inductive Visits (p : Ports R S) (body : StructuredCalls.Cmd R S) (shape : List ℕ) :
    List ℕ → ℕ → Data R S → Data R S → Prop
  | done (d : Data R S) (hf : d.regs (p.register 2) = false) : Visits p body shape [] 1 d d
  | step {words : List (List Bool)} {d e f : Data R S} {nb na nt : ℕ} {ranks : List ℕ}
      (hf : d.regs (p.register 2) = true)
      (hw : words.map List.length = shape)
      (hc : d.stacks p.counter = Encoding.encodeList id words)
      (hb : StructuredCalls.Eval body nb d e)
      (he : e.stacks p.counter = Encoding.encodeList id words)
      (ha : StructuredCalls.Eval (advanceCmd p) na e (advanceResult p e words))
      (tail : Visits p body shape ranks nt (advanceResult p e words) f) :
      Visits p body shape (CounterPrograms.value words.flatten :: ranks) ((nb + na) + nt + 1) d f

/-- The only callback premise is a measured execution of actual fixed code,
preserving the tuple and scratch ports while maintaining its data invariant. -/
abbrev BodySpec (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (shape : List ℕ) (I : Data R S → Prop) (budget : ℕ) : Prop :=
  ∀ (words : List (List Bool)) (d : Data R S), words.map List.length = shape → I d →
    d.stacks p.counter = Encoding.encodeList id words → d.stacks p.scratch = [] →
    ∃ n e, n ≤ budget ∧ StructuredCalls.Eval body n d e ∧
      e.stacks p.counter = Encoding.encodeList id words ∧ e.stacks p.scratch = [] ∧ I e

/-- Fixed syntax size: only the chosen callback contributes variable code. -/
@[simp] theorem enumerate_size (p : Ports R S) (body : StructuredCalls.Cmd R S) :
    StructuredCalls.size (enumerate p body) = StructuredCalls.size body + 21 := by
  simp [
    StructuredCalls.size, StructuredProgram.size]
  omega

abbrev program (p : Ports R S) (body : StructuredCalls.Cmd R S) :=
  StructuredCalls.compiled (enumerate p body) p.counter p.counter

/-- Equal-width little-endian words are determined by their unsigned values. -/
theorem word_eq_of_length_value {a b : List Bool} (hl : a.length = b.length)
    (hv : CounterPrograms.value a = CounterPrograms.value b) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons x xs => simp at hl
  | cons x xs ih =>
    cases b with
    | nil => simp at hl
    | cons y ys =>
      have hl' : xs.length = ys.length := by simpa using hl
      have hxy : x = y := by
        cases x <;> cases y <;> simp [CounterPrograms.value] at hv ⊢ <;> omega
      subst y
      have hv' : CounterPrograms.value xs = CounterPrograms.value ys := by
        cases x <;> simp [CounterPrograms.value] at hv <;> omega
      exact congrArg (List.cons x) (ih hl' hv')

@[simp] theorem fixedBits_length (w n : ℕ) : (fixedBits w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [fixedBits, ih]

theorem fixedBits_value (w n : ℕ) (hn : n < 2 ^ w) :
    CounterPrograms.value (fixedBits w n) = n := by
  induction w generalizing n with
  | zero =>
    simp only [pow_zero] at hn
    have hn0 : n = 0 := by omega
    subst n
    rfl
  | succ w ih =>
    have hhalf : n / 2 < 2 ^ w := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).2
      simpa only [pow_succ] using hn
    have hbit : (decide (n % 2 = 1)).toNat = n % 2 := by
      have hmod := Nat.mod_lt n (by omega : 0 < 2)
      by_cases h : n % 2 = 1
      · simp [h]
      · simp [h]
        omega
    simp only [fixedBits, CounterPrograms.value, hbit, ih (n / 2) hhalf]
    exact Nat.mod_add_div n 2

@[simp] theorem value_replicate_false (w : ℕ) :
    CounterPrograms.value (List.replicate w false) = 0 := by
  induction w with
  | zero => rfl
  | succ w ih => simp [List.replicate_succ, ih]

/-- The separately implemented zero-tuple constructor satisfies the initial
rank condition even when either dimension is zero. -/
@[simp] theorem zero_tuple_value (r w : ℕ) :
    CounterPrograms.value (List.replicate r (List.replicate w false)).flatten = 0 := by
  simp only [List.flatten_replicate_replicate, value_replicate_false]

end SubexponentialSAT.ExecCNFTupleEnumeration

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseRelationsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving encoded clause relations

Two invocations of the concrete subset tester compute equivalence and strict
inclusion. The original encoded clauses occupy stacks 8 and 9 throughout;
stacks 0 through 7 are empty workspace at both boundaries. Registers 10 and
11 return equivalence and strict inclusion, respectively.
-/

namespace SubexponentialSAT.ExecClauseRelationsProgram

open BitProgram StructuredCalls

def subsetProgram := ProgramLinking.liftProgram ExecCNFSubset.subsetProgram regPort stackPort

abbrev compare (i j : Fin 2) : Cmd 12 10 :=
  .seq (copy (original i) 0) (.seq (copy (original j) 2)
    (.seq (.call subsetProgram) (.seq (clear 0) (.seq (clear 1) (clear 2)))))

abbrev command : Cmd 12 10 :=
  .seq (compare 0 1) (.seq save (.seq (compare 1 0) combine))

/-- One finite instruction table serves every pair of encoded clauses. -/
def program := compiled command 8 0

end SubexponentialSAT.ExecClauseRelationsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseRelationScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual clause-relation scans over encoded formulas

All modes use a fixed finite Boolean program. An outer record iterator parses
each encoded clause, then invokes the concrete preserving clause-relation
program. The query clause is preserved for callers that subsequently emit it.
-/
namespace SubexponentialSAT.ExecClauseRelationScan
open BitProgram StructuredCalls

def relationProgram := ProgramLinking.liftProgram
  ExecClauseRelationsProgram.program regPort stackPort

abbrev callback (mode : Mode) : Cmd 15 12 :=
  .seq transfer (.seq (.call relationProgram)
    (.seq (RecordPrograms.atom (.copy 14 (resultRegister mode))) clearCandidate))

abbrev command (mode : Mode) : Cmd 15 12 :=
  .seq (RecordPrograms.iterate ports (callback mode)) (RecordPrograms.atom (.push 11 14))

/-- All runtime clauses and list lengths are stored in Boolean stacks; only
the three-element mode is selected when the fixed program is built. -/
def program (mode : Mode) := compiled (command mode) 10 11

end SubexponentialSAT.ExecClauseRelationScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseRelationScanPreserve
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A preserving wrapper for repeated clause-vs-formula scans. A real copy of
the full formula is scanned, and its residual copy is explicitly cleared. -/
namespace SubexponentialSAT.ExecClauseRelationScan.Preserving
open BitProgram StructuredCalls

def scanner (mode : Mode) := ProgramLinking.liftProgram
  (ExecClauseRelationScan.program mode) id stackPort

abbrev command (mode : Mode) : Cmd 15 13 :=
  .seq copyFormula (.seq (.call (scanner mode)) clearSource)

def program (mode : Mode) := compiled (command mode) 12 11

end SubexponentialSAT.ExecClauseRelationScan.Preserving

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseFiltersProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Exact-order clause filters on encoded formulas

The relation scanner occupies stacks 0--12. The outer record pass uses stack
13 for unread records, stack 14 for the reversed output record list, and stack
15 for the reversed current payload. Two stack transfers put a clause into the
scanner and return it to the existing frame emitter.
-/


namespace SubexponentialSAT.ExecClauseFiltersProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula Mode encodeClause encodeFormula test)

abbrev scan (mode : Mode) : Cmd 15 16 :=
  .call (ProgramLinking.liftProgram (ExecClauseRelationScan.Preserving.program mode) id scanStack)

abbrev callback (mode : Mode) : Cmd 15 16 :=
  .seq (transfer 15 9) (.seq (scan mode) (.seq (clear 11)
    (.seq (transfer 9 15) (.seq (.base (.atom (.bnot 14 14))) emit))))

abbrev filterScan (mode : Mode) : Cmd 15 16 := RecordPrograms.iterate ports (callback mode)

end SubexponentialSAT.ExecClauseFiltersProgram

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

abbrev callback : Cmd 15 16 := .seq copySuffix
  (.seq (ExecClauseFiltersProgram.callback .equivalent) (ExecClauseFiltersProgram.clear 12))

abbrev scan : Cmd 15 16 := RecordPrograms.iterate ports callback

/-- Both sentinels and the final outer reversal are actual instructions. -/
abbrev command : Cmd 15 16 := .seq (pushFalse 14) (.seq scan (.seq (pushFalse 13) reverseCall))

def program := compiled command 13 13

end SubexponentialSAT.ExecClauseDedupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseSelfFilterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Complete fixed-master clause filtering

This wrapper performs the actual initial copy, record scan, cleanup, and
record-order restoration. Its input and output are on stack 13; every other
stack is empty at both boundaries.
-/

namespace SubexponentialSAT.ExecClauseFiltersProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula Mode encodeClause encodeFormula test)


abbrev selfFilter (mode : Mode) : Cmd 15 16 :=
  .seq copyMaster (.seq (pushFalse 14) (.seq (filterScan mode)
    (.seq (clear 12) (.seq (pushFalse 13) ExecClauseFilterReverse.command))))

def selfFilterProgram (mode : Mode) := compiled (selfFilter mode) 13 13

end SubexponentialSAT.ExecClauseFiltersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!+# Fixed-control encoded CNF normalization

The common boundary uses stack 13 for the formula and empty work stacks.
Literal cleanup and tautology removal are lifted into that boundary here;
clause deduplication and strict-subset deletion use the same boundary.
-/

namespace SubexponentialSAT.SubexpNormalizationProgram

open BitProgram StructuredCalls

abbrev dedupCall : Cmd 15 16 := .call ExecClauseDedupProgram.program

abbrev removeSupersetsCall : Cmd 15 16 :=
  .call (ExecClauseFiltersProgram.selfFilterProgram .strictSubset)

/-- This subroutine is also used after constructing a sparsifier child. -/
abbrev absorbCommand : Cmd 15 16 := .seq dedupCall removeSupersetsCall

end SubexponentialSAT.SubexpNormalizationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCoreChildProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual encoded construction of the core child

The caller supplies a forward encoded core clause on stack 9, an encoded
selected family on stack 12, and the parent formula on stack 13. All other
stacks are empty. The program builds the core record, removes every clause
equivalent to a selected clause, restores record order, and calls the concrete
absorber. The result is on stack 13; every other stack is empty.

The finite program does not depend on any of its three input values. The
equivalence tests, framing, reversal, and absorption are actual bit programs.
-/

namespace SubexponentialSAT.ExecCoreChildProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)
open ExecClauseFiltersProgram


/-- Finish an actual filter pass with an already encoded output accumulator.
The caller can put reversed petal records in the accumulator as well as the
singleton core used below. -/
abbrev eraseWithAccumulator : Cmd 15 16 :=
  .seq (filterScan .equivalent) (.seq (clear 12)
    (.seq (pushFalse 13) ExecClauseFilterReverse.command))

/-- Prepare the unabsorbed core child. The singleton core accumulator is
reversed together with the kept records, placing the core first. -/
abbrev prepare : Cmd 15 16 := .seq seedCore eraseWithAccumulator

abbrev command : Cmd 15 16 := .seq prepare SubexpNormalizationProgram.absorbCommand

def program := compiled command 13 13

end SubexponentialSAT.ExecCoreChildProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecPetalChildProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual construction of the petal child. The core, selected family, and
parent occupy the same three ports as the core-child program. -/
namespace SubexponentialSAT.ExecPetalChildProgram
open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)
open ExecClauseFiltersProgram

abbrev prepare : Cmd 15 16 :=
  .seq copySelected (.seq familyCall (.seq (clear 9) ExecCoreChildProgram.eraseWithAccumulator))

abbrev command : Cmd 15 16 := .seq prepare SubexpNormalizationProgram.absorbCommand

end SubexponentialSAT.ExecPetalChildProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_PowerPrograms
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Variable exponentiation with finite Boolean control

The exponent is a binary stack word.  The multiplication callback below uses
only fixed finite programs and leaves the countdown ports untouched.
-/

namespace SubexponentialSAT.PowerPrograms

open SubexponentialSAT.BitProgram
open SubexponentialSAT.StructuredProgram
open SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic

abbrev Data := StructuredProgram.State 8 9

def state (r : Regs) (base exponent acc : List Bool) : Data :=
  ⟨r, stackState base exponent acc [] [] [] [] [] []⟩

theorem embed_mul (r rf : Regs) (base exponent x y acc cp tmp rev : List Bool) :
    embedState id mulPorts (state r base exponent [])
      ⟨rf, SubexponentialSAT.BinaryPrograms.Mul.stackState x y acc cp tmp rev⟩ =
      ⟨rf, stackState base exponent y x acc cp tmp rev []⟩ := by
  simp [embedState, state, extend_mulPorts]

abbrev copyBase : StructuredCalls.Cmd 8 9 :=
  .call (SubexponentialSAT.StackRoutines.copyProgram 0 3 5 0 1)

abbrev multiply : StructuredCalls.Cmd 8 9 :=
  .call (SubexponentialSAT.ProgramLinking.liftProgram SubexponentialSAT.BinaryPrograms.Mul.program id mulPorts)

abbrev restore₁ : StructuredCalls.Cmd 8 9 :=
  .call (SubexponentialSAT.StackRoutines.transferProgram 4 3 0 1)

abbrev restore₂ : StructuredCalls.Cmd 8 9 :=
  .call (SubexponentialSAT.StackRoutines.transferProgram 3 2 0 1)

abbrev callback : StructuredCalls.Cmd 8 9 :=
  .seq copyBase (.seq multiply (.seq restore₁ restore₂))

theorem copy_eval (r : Regs) (base exponent acc : List Bool) :
    StructuredCalls.Eval copyBase (7 * base.length + 5) (state r base exponent acc)
      ⟨readRegs r 0 1 none, stackState base exponent acc base [] [] [] [] []⟩ := by
  apply StructuredCalls.Eval.call
  have h := SubexponentialSAT.StackRoutines.copyProgram_trace (0 : Fin 9) 3 5 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) r
    (stackState base exponent acc [] [] [] [] [] []) rfl
  have hh := SubexponentialSAT.StackRoutines.halt_after_trace _ h 7 rfl rfl
  convert hh using 1 <;>
    simp [state, State.withPC,
      SubexponentialSAT.StackRoutines.copyResult, SubexponentialSAT.StackRoutines.copyStacks]

theorem multiply_eval (r : Regs) (base exponent acc : List Bool) :
    ∃ rf : Regs, ∃ n ≤ 30 * (base.length + 1) * (acc.length + base.length + 1),
      StructuredCalls.Eval multiply n
        ⟨r, stackState base exponent acc base [] [] [] [] []⟩
        ⟨rf, stackState base exponent [] [] (nextAccumulator base acc) [] [] [] []⟩ := by
  obtain ⟨rf, n, hn, h⟩ := SubexponentialSAT.BinaryPrograms.Mul.run r base acc [] acc.length le_rfl (by simp)
  have ht := StructuredCalls.eval_call_lifted SubexponentialSAT.BinaryPrograms.Mul.program
    id mulPorts (state r base exponent []) Function.injective_id mulPorts_injective
    (a := ⟨r, SubexponentialSAT.BinaryPrograms.Mul.stackState base acc [] [] [] []⟩)
    (b := ⟨rf, SubexponentialSAT.BinaryPrograms.Mul.stackState [] [] (nextAccumulator base acc) [] [] []⟩) h
  refine ⟨rf, n, hn, ?_⟩
  simpa only [embed_mul] using ht

theorem restore₁_eval (r : Regs) (base exponent word : List Bool) :
    StructuredCalls.Eval restore₁ (3 * word.length + 3)
      ⟨r, stackState base exponent [] [] word [] [] [] []⟩
      ⟨readRegs r 0 1 none, stackState base exponent [] word.reverse [] [] [] [] []⟩ := by
  apply StructuredCalls.Eval.call
  have h := SubexponentialSAT.StackRoutines.transferProgram_trace (4 : Fin 9) 3 (0 : Fin 8) 1
    (by decide) (by decide) r (stackState base exponent [] [] word [] [] [] [])
  have hh := SubexponentialSAT.StackRoutines.halt_after_trace _ h 3 rfl rfl
  convert hh using 1 <;>
    simp [State.withPC,
      SubexponentialSAT.StackRoutines.transferResult, SubexponentialSAT.StackRoutines.transferStacks]

theorem restore₂_eval (r : Regs) (base exponent word : List Bool) :
    StructuredCalls.Eval restore₂ (3 * word.length + 3)
      ⟨r, stackState base exponent [] word.reverse [] [] [] [] []⟩
      (state (readRegs r 0 1 none) base exponent word) := by
  apply StructuredCalls.Eval.call
  have h := SubexponentialSAT.StackRoutines.transferProgram_trace (3 : Fin 9) 2 (0 : Fin 8) 1
    (by decide) (by decide) r (stackState base exponent [] word.reverse [] [] [] [] [])
  have hh := SubexponentialSAT.StackRoutines.halt_after_trace _ h 3 rfl rfl
  convert hh using 1 <;>
    simp [state, State.withPC,
      SubexponentialSAT.StackRoutines.transferResult, SubexponentialSAT.StackRoutines.transferStacks]

theorem callback_eval (r : Regs) (base exponent acc : List Bool) :
    ∃ rf : Regs, ∃ n ≤ 50 * (base.length + 1) * (acc.length + base.length + 1),
      StructuredCalls.Eval callback n (state r base exponent acc)
        (state rf base exponent (nextAccumulator base acc)) := by
  let r₁ := readRegs r 0 1 none
  obtain ⟨r₂, n, hn, hm⟩ := multiply_eval r₁ base exponent acc
  let r₃ := readRegs r₂ 0 1 none
  let r₄ := readRegs r₃ 0 1 none
  have ht := StructuredCalls.Eval.seq (copy_eval r base exponent acc)
    (StructuredCalls.Eval.seq hm
      (StructuredCalls.Eval.seq (restore₁_eval r₂ base exponent (nextAccumulator base acc))
        (restore₂_eval r₃ base exponent (nextAccumulator base acc))))
  refine ⟨r₄, _, ?_, ht⟩
  have hlen := nextAccumulator_length base acc
  let width := acc.length + base.length + 1
  have hscale : width ≤ (base.length + 1) * width := by
    simpa using Nat.mul_le_mul_right width (show 1 ≤ base.length + 1 by omega)
  calc
    _ ≤ n + 20 * width := by dsimp [width]; omega
    _ ≤ 30 * (base.length + 1) * width + 20 * ((base.length + 1) * width) :=
      Nat.add_le_add hn (Nat.mul_le_mul_left 20 hscale)
    _ = 50 * (base.length + 1) * (acc.length + base.length + 1) := by
      dsimp [width]
      ring

/-- The invariant ignores the countdown's two ports and all finite registers. -/
def Invariant (base : List Bool) (i : ℕ) (d : Data) : Prop :=
  d.stacks 0 = base ∧
  BinaryArithmetic.toNat (d.stacks 2) = BinaryArithmetic.toNat base ^ i ∧
  (d.stacks 2).length ≤ 1 + i * base.length ∧
  ∀ j : Fin 9, 3 ≤ j.val → j.val < 8 → d.stacks j = []

theorem invariant_initial (r : Regs) (base exponent : List Bool) :
    Invariant base 0 (state r base exponent [true]) := by
  refine ⟨rfl, by simp [state], by simp [state], ?_⟩
  intro j hj₁ hj₂
  fin_cases j <;> simp_all [state, stackState]

theorem invariant_stable (base : List Bool) (i : ℕ) {d e : Data}
    (hd : Invariant base i d)
    (hframe : ∀ j : Fin 9, j ≠ 1 → j ≠ 8 → e.stacks j = d.stacks j) :
    Invariant base i e := by
  rcases hd with ⟨hb, hv, hl, hw⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hframe 0 (by decide) (by decide)] using hb
  · simpa only [hframe 2 (by decide) (by decide)] using hv
  · simpa only [hframe 2 (by decide) (by decide)] using hl
  · intro j hj₁ hj₂
    rw [hframe j (by intro h; subst j; omega)
      (by intro h; subst j; omega)]
    exact hw j hj₁ hj₂

theorem state_of_invariant (base : List Bool) (i : ℕ) (d : Data)
    (hd : Invariant base i d) (hs : d.stacks 8 = []) :
    d = state d.regs base (d.stacks 1) (d.stacks 2) := by
  rcases hd with ⟨hb, hv, hl, hw⟩
  rcases d with ⟨r, stk⟩
  apply congrArg (State.mk r)
  funext j
  fin_cases j
  · exact hb
  · rfl
  · rfl
  · exact hw 3 (by decide) (by decide)
  · exact hw 4 (by decide) (by decide)
  · exact hw 5 (by decide) (by decide)
  · exact hw 6 (by decide) (by decide)
  · exact hw 7 (by decide) (by decide)
  · exact hs

theorem callback_invariant (base : List Bool) (i : ℕ) (d : Data)
    (hd : Invariant base i d) (hs : d.stacks 8 = []) :
    ∃ n e, n ≤ callbackBound base i ∧ StructuredCalls.Eval callback n d e ∧
      e.stacks 1 = d.stacks 1 ∧ e.stacks 8 = [] ∧ Invariant base (i + 1) e := by
  obtain ⟨rf, n, hn, he⟩ := callback_eval d.regs base (d.stacks 1) (d.stacks 2)
  refine ⟨n, state rf base (d.stacks 1) (nextAccumulator base (d.stacks 2)), ?_, ?_, rfl, rfl, ?_⟩
  · have hlen := hd.2.2.1
    dsimp [callbackBound]
    apply hn.trans
    apply Nat.mul_le_mul_left
    simp only [Nat.add_mul, one_mul]
    omega
  · rwa [← state_of_invariant base i d hd hs] at he
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · simp [state, hd.2.1, pow_succ, Nat.mul_comm]
    · have hlen := nextAccumulator_length base (d.stacks 2)
      have hold := hd.2.2.1
      change (nextAccumulator base (d.stacks 2)).length ≤ 1 + (i + 1) * base.length
      simp only [Nat.add_mul, one_mul]
      omega
    · intro j hj₁ hj₂
      fin_cases j <;> simp_all [state, stackState]

def ports : SubexponentialSAT.CounterForPrograms.Ports 8 9 where
  register := ⟨fun i => ⟨i.val, by omega⟩, by
    intro a b h
    apply Fin.ext
    exact congrArg (fun k : Fin 8 => k.val) h⟩
  counter := 1
  scratch := 8
  counter_ne_scratch := by decide

theorem invariant_frameStable (base : List Bool) :
    SubexponentialSAT.CounterForPrograms.FrameStable ports (Invariant base) := by
  intro i a b h hi
  apply invariant_stable base i hi
  intro j hj₁ hj₈
  exact (h j hj₁ hj₈).symm

theorem callback_spec (base : List Bool) :
    SubexponentialSAT.CounterForPrograms.BodySpec ports callback (Invariant base) (callbackBound base) := by
  intro i d hi hs _
  exact callback_invariant base i d hi hs

abbrev initializeAccumulator : StructuredCalls.Cmd 8 9 :=
  .base (.seq (.atom (.set 0 true)) (.atom (.push 2 0)))

theorem initialize_eval (r : Regs) (base exponent : List Bool) :
    StructuredCalls.Eval initializeAccumulator 2 (state r base exponent [])
      (state (Function.update r 0 true) base exponent [true]) := by
  apply StructuredCalls.Eval.base
  have hs := StructuredProgram.Eval.atom (.set (0 : Fin 8) true) (state r base exponent [])
  have hp := StructuredProgram.Eval.atom (.push (2 : Fin 9) 0)
    (Atom.eval (.set (0 : Fin 8) true) (state r base exponent []))
  simpa [Atom.eval, Atom.instr, State.ofCfg, State.withPC, execInstr, state] using
    StructuredProgram.Eval.seq hs hp

/-- The only loop bound is the binary word on the exponent stack. -/
abbrev command : StructuredCalls.Cmd 8 9 :=
  .seq initializeAccumulator (SubexponentialSAT.CounterForPrograms.forCmd ports callback)

/-- A fixed 85-label program, independent of base and exponent. -/
def program := StructuredCalls.compiled command (0 : Fin 9) 2

theorem command_eval (r : Regs) (base exponent : List Bool) :
    ∃ n d, StructuredCalls.Eval command n (state r base exponent []) d ∧
      Invariant base (BinaryArithmetic.toNat exponent) d ∧ BinaryArithmetic.toNat (d.stacks 1) = 0 ∧
      (d.stacks 1).length = exponent.length ∧ d.stacks 8 = [] ∧
      n ≤ workBound base exponent + 2 := by
  obtain ⟨n, d, he, hi, hz, hw, hs, hn⟩ :=
    SubexponentialSAT.CounterForPrograms.for_correct ports callback (Invariant base) (callbackBound base)
      (invariant_frameStable base) (callback_spec base)
      (state (Function.update r 0 true) base exponent [true]) rfl
      (invariant_initial _ base exponent)
  have hb := SubexponentialSAT.CounterForPrograms.budgetSum_le_mono (callbackBound base)
    (callbackBound_monotone base) (BinaryArithmetic.toNat exponent)
  have hi' : Invariant base (BinaryArithmetic.toNat exponent) d := by
    simpa [state, ports, SubexponentialSAT.CounterPrograms.value_eq_toNat] using hi
  have hz' : BinaryArithmetic.toNat (d.stacks 1) = 0 := by
    simpa [ports, SubexponentialSAT.CounterPrograms.value_eq_toNat] using hz
  have hw' : (d.stacks 1).length = exponent.length := by
    simpa [state, ports] using hw
  have hn' : n ≤ SubexponentialSAT.CounterForPrograms.budgetSum (callbackBound base) 0 (BinaryArithmetic.toNat exponent) +
      (BinaryArithmetic.toNat exponent + 1) * (16 * exponent.length + 16) := by
    simpa [state, ports, SubexponentialSAT.CounterPrograms.value_eq_toNat] using hn
  refine ⟨2 + n, d, StructuredCalls.Eval.seq (initialize_eval r base exponent) he,
    hi', hz', hw', hs, ?_⟩
  dsimp [workBound]
  omega

/-- Complete natural-power correctness, including a bound for the actual raw
output representation and a halted instruction trace. Leading zeros are allowed. -/
theorem run_value (r : Regs) (base exponent : List Bool) :
    ∃ d : Data,
      BinaryArithmetic.toNat (d.stacks 2) = BinaryArithmetic.toNat base ^ BinaryArithmetic.toNat exponent ∧
      (d.stacks 2).length ≤ 1 + BinaryArithmetic.toNat exponent * base.length ∧
      d.stacks 0 = base ∧ BinaryArithmetic.toNat (d.stacks 1) = 0 ∧
      (d.stacks 1).length = exponent.length ∧
      (∀ j : Fin 9, 3 ≤ j.val → d.stacks j = []) ∧
      BitProgram.RunsIn program (runtimeBound base exponent)
        ((state r base exponent []).withPC (some program.entry)) (d.withPC none) := by
  obtain ⟨n, d, he, hi, hz, hw, hs, hn⟩ := command_eval r base exponent
  refine ⟨d, hi.2.1, hi.2.2.1, hi.1, hz, hw, ?_, n + 1, ?_,
    StructuredCalls.compiled_halt_trace he 0 2⟩
  · intro j hj
    by_cases hlast : j.val < 8
    · exact hi.2.2.2 j hj hlast
    · have heq : j = 8 := by apply Fin.ext; omega
      simpa [heq] using hs
  · dsimp [runtimeBound]
    omega

end SubexponentialSAT.PowerPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_PowerCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source-preserving variable-power calls on fixed assigned ports. -/

namespace SubexponentialSAT.PowerCalls

open BitProgram StructuredCalls

abbrev Data (S : ℕ) := StructuredProgram.State 8 S

def Valid {S : ℕ} (p : Ports S) (d : Data S) : Prop :=
  d.stacks p.out = [] ∧ ∀ i, d.stacks (p.work i) = []

abbrev rawPower {S : ℕ} (p : Ports S) : Cmd 8 S :=
  .call (ProgramLinking.liftProgram PowerPrograms.program id (powerPorts p))

abbrev clearCounter {S : ℕ} (p : Ports S) : Cmd 8 S :=
  .call (StackRoutines.clearProgram (p.work 0) 0 1)

abbrev powerAt {S : ℕ} (p : Ports S) : Cmd 8 S :=
  .seq (ArithmeticCalls.copyAt p.exponent (p.work 0) (p.work 4))
    (.seq (rawPower p) (clearCounter p))

def rawFinish {S : ℕ} (p : Ports S) (d : Data S) (f : PowerPrograms.Data) : Data S :=
  ⟨f.regs, Function.update (Function.update d.stacks (p.work 0) (f.stacks 1))
    p.out (f.stacks 2)⟩

theorem embed_start {S : ℕ} (p : Ports S) (d : Data S) (hv : Valid p d) :
    embedState id (powerPorts p) d
      (PowerPrograms.state (ArithmeticCalls.afterCopy p.exponent (p.work 0) d).regs
        (d.stacks p.base) (d.stacks p.exponent) []) =
      ArithmeticCalls.afterCopy p.exponent (p.work 0) d := by
  apply embedState_eq_of_ports id (powerPorts p) d _ _
    Function.injective_id (powerPorts_injective p)
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;>
      simp [ArithmeticCalls.afterCopy, powerPorts, PowerPrograms.state, PowerPrograms.stackState,
        p.work.injective.eq_iff, hv.1, hv.2]
  · intro i hi
    have h0 : i ≠ p.work 0 := fun h => hi ⟨1, h.symm⟩
    simp [ArithmeticCalls.afterCopy, h0]

theorem embed_finish {S : ℕ} (p : Ports S) (d : Data S) (hv : Valid p d)
    (f : PowerPrograms.Data) (hb : f.stacks 0 = d.stacks p.base)
    (hw : ∀ i : Fin 9, 3 ≤ i.val → f.stacks i = []) :
    embedState id (powerPorts p) d f = rawFinish p d f := by
  apply embedState_eq_of_ports id (powerPorts p) d _ _
    Function.injective_id (powerPorts_injective p)
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;>
      simp [rawFinish, powerPorts, p.work.injective.eq_iff, p.work_ne_out,
        p.out_ne_base.symm, hv.2, hb, hw]
  · intro i hi
    have h0 : i ≠ p.work 0 := fun h => hi ⟨1, h.symm⟩
    have ho : i ≠ p.out := fun h => hi ⟨2, h.symm⟩
    simp [rawFinish, h0, ho]

theorem clear_finish {S : ℕ} (p : Ports S) (d : Data S) (hv : Valid p d)
    (f : PowerPrograms.Data) :
    Eval (clearCounter p) (2 * (f.stacks 1).length + 3) (rawFinish p d f)
      ⟨readRegs f.regs 0 1 none, Function.update d.stacks p.out (f.stacks 2)⟩ := by
  have h := ListRegisterProgram.clear_run (p.work 0) (0 : Fin 8) 1
    (rawFinish p d f).regs (rawFinish p d f).stacks
  have heq : StackRoutines.clearStacks (p.work 0) (rawFinish p d f).stacks =
      Function.update d.stacks p.out (f.stacks 2) := by
    funext i
    by_cases hi : i = p.work 0
    · subst i
      simp [StackRoutines.clearStacks, rawFinish, p.work_ne_out, hv.2]
    · simp [StackRoutines.clearStacks, rawFinish, Function.update_apply, hi]
  rw [heq] at h
  apply Eval.call
  simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC, rawFinish,
    p.work_ne_out] using h

/-- Both source words are retained verbatim, and every work port is restored.
The exponent is represented by data, not by a parameter in the control table. -/
theorem powerAt_spec {S : ℕ} (p : Ports S) (d : Data S) (hv : Valid p d) :
    ∃ (t : ℕ) (rf : Fin 8 → Bool) (word : List Bool),
      Eval (powerAt p) t d ⟨rf, Function.update d.stacks p.out word⟩ ∧
      BinaryArithmetic.toNat word =
        BinaryArithmetic.toNat (d.stacks p.base) ^ BinaryArithmetic.toNat (d.stacks p.exponent) ∧
      word.length ≤ 1 + BinaryArithmetic.toNat (d.stacks p.exponent) * (d.stacks p.base).length ∧
      t ≤ PowerPrograms.runtimeBound (d.stacks p.base) (d.stacks p.exponent) +
        9 * (d.stacks p.exponent).length + 8 := by
  let ready := ArithmeticCalls.afterCopy p.exponent (p.work 0) d
  have hc := ArithmeticCalls.copyAt_eval p.exponent (p.work 0) (p.work 4) d
    (p.work_ne_exponent 0).symm (p.work_ne_exponent 4).symm
    (by intro h; exact (by decide : (4 : Fin 7) ≠ 0) (p.work.injective h))
    (hv.2 0) (hv.2 4)
  obtain ⟨f, hvalue, hlen, hb, hz, hwidth, hw, n, hn, ht⟩ :=
    PowerPrograms.run_value ready.regs (d.stacks p.base) (d.stacks p.exponent)
  have hp := eval_call_lifted PowerPrograms.program id (powerPorts p) d
    Function.injective_id (powerPorts_injective p) ht
  rw [embed_start p d hv, embed_finish p d hv f hb hw] at hp
  have hall := Eval.seq hc (Eval.seq hp (clear_finish p d hv f))
  refine ⟨_, readRegs f.regs 0 1 none, f.stacks 2, hall, hvalue, hlen, ?_⟩
  rw [hwidth]
  omega

end SubexponentialSAT.PowerCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramShift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Primitive preparation of a nonnegative shifted integer coefficient.
The input signed integer is a pair P-N; W dominates N. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls

def shiftState (regs : Fin 8 → Bool) (W N P diff out : List Bool) : ShiftData :=
  ⟨regs, ![W,N,diff,[],[],[],[],[],P,out]⟩

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete decoding and shifting of one signed coefficient pair. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

def preState (regs : Fin 8 → Bool) (W : List Bool) (xs : List SignedWord)
    (out : List Bool) : PreData :=
  ⟨regs, ![W,[],[],[],[],[],[],[],[],[],signedWords xs,out,[],[]]⟩

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A measured signed row scan, followed by a physical frame-order repair. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

def preReady (regs : Fin 8 → Bool) (W : List Bool) (xs : List SignedWord)
    (out : List Bool) : PreData :=
  preState (readRegs regs 0 1 (signedWords xs).head?) W xs out

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A concrete row-major signed matrix preprocessor. All input and output
frames are scanned by fixed instructions; the original bound word is retained. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

def preMatrixState (regs : Fin 8 → Bool) (W : List Bool)
    (rows : List (List SignedWord)) (out : List Bool) : PreMatrixData :=
  ⟨regs,![W,[],[],[],[],[],[],[],[],[],[],[],[],[],words (rows.map signedWords),out,[]]⟩

def preRowCall : PreMatrixCode := .call
  (ProgramLinking.liftProgram preRowProgram id preRowPorts)

def preMatrixStep : PreMatrixCode := .seq (readWord 14 10 12 (by decide))
  (.seq preRowCall (emitFrame 11 15 12 (by decide)))

def preMatrixBody : PreMatrixCode := .seq preMatrixStep preMatrixPeek
def preMatrixLoop : PreMatrixCode := .while 1 preMatrixBody
def preMatrixScan : PreMatrixCode := .seq preMatrixPeek preMatrixLoop

def preMatrixReady (regs : Fin 8 → Bool) (W : List Bool)
    (rows : List (List SignedWord)) (acc : List Bool) : PreMatrixData :=
  preMatrixState (readRegs regs 0 1 (words (rows.map signedWords)).head?) W rows acc

def preMatrixRepair : PreMatrixCode := .seq
  (.call (ProgramLinking.liftProgram preReverseProgram id preMatrixReversePorts)) (move 16 15 12)
def preMatrixCommand : PreMatrixCode := .seq preMatrixScan preMatrixRepair
def preMatrixProgram := compiled preMatrixCommand 14 15

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The complete measured coefficient scan for one integer signature row.
Runtime EOF controls the loop; no instruction count depends on row length. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.MatrixProgramSupport

def rowReady (regs : Fin 8 → Bool) (W : List Bool) (coeffs : List (List Bool))
    (bits acc : List Bool) : DotData :=
  dotState (readRegs regs 0 1 (words coeffs).head?) W coeffs bits acc

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramSignature
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed nested row scanner.  The input matrix is a raw list of framed
rows, and each row is itself a raw list of framed coefficient words. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

def signatureState (regs : Fin 8 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (key : List Bool) : SignatureData :=
  ⟨regs, ![W,[],[],[],[],[],[],[],[],[],[],[],bits,words (rows.map words),key]⟩

def signatureReady (regs : Fin 8 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (key : List Bool) : SignatureData :=
  signatureState (readRegs regs 0 1 (words (rows.map words)).head?) W bits rows key

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramWords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-width base-ring words for arbitrary extension degree. The arithmetic
programs below are the audited fixed scalar programs; the degree does not occur
in their instruction tables. Extension-vector scanning is a separate layer. -/
namespace SubexponentialSAT.SqrtLog.RingProgram

open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.BitProgram SubexponentialSAT.ModularRingPrograms SubexponentialSAT.ModularDivisionPrograms

variable (p t : ℕ) [Fact p.Prime]

variable (M : SubexpPreparedQuartic.Modulus p t)

def scalarRing (cache : ScalarCache p t) : RepresentedRing (ScalarCode p t) (ZMod (p^t)) where
  decode := wordValue p t
  zeroRun := (cache.zero, baseWidth p t)
  oneRun := (cache.one, baseWidth p t)
  addRun := SubexpPreparedQuartic.wordAdd p t M
  mulRun := SubexpPreparedQuartic.wordMul p t M
  negRun x := SubexpPreparedQuartic.wordMul p t M x cache.minusOne
  zero_correct := cache.zero_correct
  one_correct := cache.one_correct
  add_correct := SubexpPreparedQuartic.wordAdd_correct p t M
  mul_correct := SubexpPreparedQuartic.wordMul_correct p t M
  neg_correct x := by
    rw [SubexpPreparedQuartic.wordMul_correct, cache.minusOne_correct, mul_neg_one]

@[simp] theorem scalarRing_program (cache : ScalarCache p t) :
    (scalarRing p t M cache).program = scalarProgram p t M cache := rfl

@[simp] theorem flat_length {d B : ℕ} (x : Code (Word B) d) :
    (flat x).length = d * B := by
  simp only [flat, List.length_flatten, List.map_ofFn, List.sum_ofFn]
  calc
    ∑ i : Fin d, (x i).val.length = ∑ _ : Fin d, B :=
      Finset.sum_congr rfl (fun i _ => (x i).property)
    _ = d * B := by simp

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramQuotient
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual represented arithmetic in the quotient by a supplied monic
polynomial. Irreducibility is unnecessary for ring operations. Every structure
constant is supplied by the executable companion recurrence. -/
namespace SubexponentialSAT.SqrtLog.RingProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A : Type*} [CommRing A] [Nontrivial A] [DecidableEq A]

noncomputable abbrev quotientPolynomial (ops : RepresentedRing C A) {d : ℕ} (c : Code C d) :=
  SubexponentialSAT.QuarticSearch.poly (fun i => ops.decode (c i))

def zeroVector (ops : RingProgram C) (d : ℕ) : Code C d := fun _ => ops.zeroRun.1

/-- The executable program contains no polynomial-quotient or choice operation. -/
def quotientProgram (ops : RingProgram C) {d : ℕ} (c : Code C d) : RingProgram (Code C d) :=
  program ops (structureTableRun ops c).1 (zeroVector ops d) (oneVectorRun ops d).1

/-- Explicit setup phase. Its returned program retains the materialized table,
and its cost includes all scalar callback events in constructing that table. -/
def quotientProgramRun (ops : RingProgram C) {d : ℕ} (c : Code C d) :
    RingProgram (Code C d) × ℕ :=
  let table := structureTableRun ops c
  let one := oneVectorRun ops d
  (program ops table.1 (zeroVector ops d) one.1,
    table.2 + one.2 + d * ops.zeroRun.2 + d)

@[simp] theorem quotientProgramRun_value (ops : RingProgram C) {d : ℕ} (c : Code C d) :
    (quotientProgramRun ops c).1 = quotientProgram ops c := rfl

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete ternary coefficient input and the executable represented arithmetic
for the supplied-polynomial unramified ring model. -/
namespace SubexponentialSAT.SqrtLog.RingProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.BinaryArithmetic

def liftCoefficientRun (t : ℕ) (a : ZMod 3) : ScalarCode 3 t × ℕ :=
  SubexponentialSAT.SubexpPreparedQuartic.literalWordRun 3 t (ternaryLiteral a)

theorem liftCoefficientRun_value (t : ℕ) (ht : 0 < t) (a : ZMod 3) :
    BinaryArithmetic.toNat (liftCoefficientRun t a).1.val = a.val := by
  change BinaryArithmetic.toNat (SubexponentialSAT.SubexpModulusConstruction.normalizeRun _ _).1 = _
  rw [SubexponentialSAT.SubexpModulusConstruction.normalizeRun_value, ternaryLiteral_value]
  rw [ternaryLiteral_value, ternary_baseWidth]
  have hpow : 2^2 ≤ 2^(2*t) := Nat.pow_le_pow_right (by omega) (by omega)
  have ha := a.val_lt
  norm_num at hpow
  omega

theorem liftCoefficientRun_correct (t : ℕ) (ht : 0 < t) (a : ZMod 3) :
    wordValue 3 t (liftCoefficientRun t a).1 = (a.val : ZMod (3^t)) := by
  unfold wordValue
  rw [liftCoefficientRun_value t ht]

/-- Materialized coefficient words for the lower coefficients of the monic
polynomial. The leading coefficient is implicit. -/
def liftCoefficientsRun (t : ℕ) {d : ℕ} (a : Fin d → ZMod 3) :
    Code (ScalarCode 3 t) d × ℕ := tabulateRun fun i => liftCoefficientRun t (a i)

@[simp] theorem liftCoefficientsRun_correct (t : ℕ) (ht : 0 < t) {d : ℕ}
    (a : Fin d → ZMod 3) (i : Fin d) :
    wordValue 3 t ((liftCoefficientsRun t a).1 i) = ((a i).val : ZMod (3^t)) := by
  simp only [liftCoefficientsRun, tabulateRun_eq]
  exact liftCoefficientRun_correct t ht (a i)

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

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

abbrev Data := StructuredProgram.State

end SubexponentialSAT.UnaryForPrograms

end OAI.Algorithms
end


