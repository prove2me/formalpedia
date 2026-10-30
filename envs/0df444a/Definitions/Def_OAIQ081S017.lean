-- Prove2me | Definitions.Def_OAIQ081S017
-- name    : OAIQ081S017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:24:33.964727+00:00
-- url     : https://prove2.me/theorems/675f07b9-98d3-49ab-bce2-676c10b476a6
-- title:
--   Definitions bundle OAIQ081S017 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 143 declarations of OpenAI's Lean: 110 definitions, 2 inductive types or structures, 2 instances and 29 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.Width.interpolationEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.Width.ringEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide.changed`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide.regMap`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide.stackMap`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.regMap`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.stackMap`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.coreChanged`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.workerPort`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceControls.extraPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceControls.pairs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.arithmeticPort`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.changedLocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.localBlank`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.localPort`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.physicalLive`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging.backupPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging.cachePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging.lowClearPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging.lowPort`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging.restorePairs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging.retainedLow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging.savePairs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.violationWeight`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.arity`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.arityCopies`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.bank`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.binaryPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.block`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.cleanupPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.countPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.early`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.finish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.high`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.highCopies`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.highMajorant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.lowPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.mask`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.measureMajorant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.offsetPorts` and 72 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLog_LeafProgramMarked`, `SubexponentialSAT_SqrtLog_LeafProgramQueryReadback`, `SubexponentialSAT_SqrtLog_LeafProgramQueryReadbackStore`, `SubexponentialSAT_SqrtLog_LeafProgramQueryReadbackWide`, `SubexponentialSAT_SqrtLog_LeafProgramQueryWidthArithmetic`, `SubexponentialSAT_SqrtLog_LeafProgramRecords`, `SubexponentialSAT_SqrtLog_LeafProgramSource`, `SubexponentialSAT_SqrtLog_LeafProgramSourceControls`, `SubexponentialSAT_SqrtLog_LeafProgramSourceFrame`, `SubexponentialSAT_SqrtLog_LeafProgramSourceReadyArithmetic`, `SubexponentialSAT_SqrtLog_LeafProgramSourceReadyCore`, `SubexponentialSAT_SqrtLog_LeafProgramSourceReadyInput`, `SubexponentialSAT_SqrtLog_LeafProgramSourceStaging`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendCalls`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendCommand`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendFinish`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendPorts`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendScanBounds`, `SubexponentialSAT_SqrtLog_LeafScopeResourceBounds`, `SubexponentialSAT_SqrtLog_LeafScopeResourceBoundsPolylog`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramArity`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramBoot`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramFinalize`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramLookup`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramMax`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramPrimitives`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramScope`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramVariables`, `SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsTotals`, `SubexponentialSAT_SqrtLog_LeafWeightProgram`, `SubexponentialSAT_SqrtLog_LeafWeightProgramNative`, `SubexponentialSAT_SqrtLog_LocalCodeCounting`, `SubexponentialSAT_SqrtLog_MomentsBuckets`, `SubexponentialSAT_SqrtLog_MomentsProgramNormalize`, `SubexponentialSAT_SqrtLog_MomentsProjectionProgramBase`, `SubexponentialSAT_SqrtLog_MomentsProjectionProgramNative`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramState`, `SubexponentialSAT_SqrtLog_NativePackingBoundsAddress`, `SubexponentialSAT_SqrtLog_NativePackingBoundsTail`, `SubexponentialSAT_SqrtLog_PackingCallerProgramWide`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyInputReady`, `SubexponentialSAT_SqrtLog_RingProgramTableRound`, `SubexponentialSAT_SqrtLog_RingProgramTableSemantics`, `SubexponentialSAT_SqrtLog_RingProgramTableSetup`, `SubexponentialSAT_SqrtLog_SquarefreeScaleProgram`, `SubexponentialSAT_SubexpBasePUnranking`, `SubexponentialSAT_SubexpEnumerationProgram`, `SubexponentialSAT_SubexpFactorProgram`, `SubexponentialSAT_SubexpFieldRowPreparation`, `SubexponentialSAT_SubexpFlatCount`, `SubexponentialSAT_SubexpNodeScanControl`, `SubexponentialSAT_Subexp_PackingBudgetArithmetic`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S038`, `OAIQ081S039`, `OAIQ081S040`, `OAIQ081S042` and `OAIQ081S043`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.eventually_raw_scope_guards` and `OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_sourceRows_present_model`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_forwardHighMask_guards` and `OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_sourceRows_present_model`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

namespace Guard

def widthStack : Fin 9 → Fin 11 := ![0, 1, 2, 10, 4, 5, 6, 7, 3]

end Guard

namespace Mask

abbrev Regs := Fin 8 → Bool

end Mask

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramMarked
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Weighted selector mass is the sum of ordinary marked-clause counts.
This identity justifies executing the same count pipeline once per supplied
clause; no weighted arithmetic is hidden in the local indicator evaluator. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram

open scoped BigOperators

variable {X Row E : Type*} [Fintype X] [Fintype E]

def violationWeight (bad : E → X → Bool) (x : X) : ℕ :=
  ∑ e, if bad e x then 1 else 0

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFlatCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Count decisions from the actual flat coefficient representation

Coefficients are stored constant-first, with four consecutive little-endian
words per coefficient. Width and modulus are runtime data. This adapter reads
the first word, discards the unused polynomial suffix, and executes the checked
remainder-and-positivity program. It does not serialize the array into records.
-/

namespace SubexponentialSAT.SubexpFlatCount

def store (input modulus word width : List Bool) : Fin 8 → List Bool :=
  ![input, [], [], [], [], modulus, word, width]

def decoderPorts : Fin 7 → Fin 8 := Fin.castSucc

end SubexponentialSAT.SubexpFlatCount

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryReadback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete readback/transfer adapter for the marked-query caller. The CRT
result is at261; the exact little-endian integer is delivered at323. The
unread marked-reference stream320 and mass accumulator322 are framed. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback

open SubexponentialSAT.SubexpFlatCount

def regMap (i : Fin 8) : Fin 19 := i.castAdd 11
def stackMap : Fin 8 → Fin 330 := ![261, 325, 326, 327, 328, 194, 329, 202]

end SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryReadbackWide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocation of the concrete reader into the shared marked/branch caller. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide

open SubexponentialSAT.SubexpFlatCount

def regMap (i : Fin 19) : Fin 40 := i.castAdd 21
def stackMap (i : Fin 330) : Fin 768 := i.castAdd 438

end SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryReadbackStore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact wide-store restoration for count readback.  Parser and odometer
registers are preserved even though the reusable narrow ABI includes them. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide

open SubexponentialSAT

def changed : List (Fin 768) := [261,323,324,325,326,327,328,329]

end SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEnumerationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Encoded interval enumeration by fixed finite control

A current label and a remaining count live on little-endian Boolean stacks.
The program invokes an actual body command once per label and advances using
verified finite-table increment/decrement routines.  Mathematical state
embeddings below occur only in execution proofs; no instruction evaluates an
arbitrary semantic function.
-/

namespace SubexponentialSAT.SubexpEnumerationProgram

variable {R S : ℕ}

theorem extend_restrict {A B C : Type*} (f : A → B) (g : B → C) :
    Function.extend f (g ∘ f) g = g := by
  classical
  funext b
  by_cases h : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := h
    exact (Function.FactorsThrough.extend_apply (fun _ _ h => congrArg g h) g a)
  · exact Function.extend_apply' _ _ _ h

end SubexponentialSAT.SubexpEnumerationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFactorProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete factor-row evaluation primitives

Programs in this module have fixed Boolean registers and fixed finite control.
Inputs are working copies on stacks. All costs below are actual instruction
traces; neither arithmetic comparisons nor semantic predicates are instructions.
-/

namespace SubexponentialSAT.SubexpFactorProgram

def allZero : List Bool → Bool
  | [] => true
  | b :: bs => !b && allZero bs

end SubexponentialSAT.SubexpFactorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpBasePUnranking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual base-p digit extraction

A digit is obtained by the checked binary long-division program. Its remainder
is copied to the fixed width of the modulus, while the padded high bits are
removed. Repeated extraction uses the quotient as the next rank. The modulus,
arity, and all widths are data; the instruction table is fixed.
-/

namespace SubexponentialSAT.SubexpBasePUnranking

def stepBudget (modulus rank : List Bool) : ℕ :=
  100 * (modulus.length + rank.length + 1) ^ 2 +
    11 * modulus.length + 8 * rank.length + 17

/-- Explicit cost including all divisions, digit extraction, loop tests, final
stream reversal, and halt. -/
def budget (modulus rank arity : List Bool) : ℕ :=
  arity.length * (100 * (modulus.length + rank.length + 1) ^ 2 +
    14 * modulus.length + 8 * rank.length + 19) + 6

end SubexponentialSAT.SubexpBasePUnranking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFieldRowPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving preparation of a local field-label row

Copy the enumerator's rank and the factor's unary arity into the checked
unranking routine, produce the fixed-width digit stream, and clear the padded
final quotient. The modulus, rank master, and arity master are preserved.
-/

namespace SubexponentialSAT.SubexpFieldRowPreparation

/-- The unranking workspace occupies ports 0--12. Ports 13 and 14 are masters. -/
def tapes (modulus rankMaster arityMaster rank arity output : List Bool) : Fin 15 → List Bool :=
  fun i => if i = 5 then modulus else if i = 6 then rank else if i = 8 then arity
    else if i = 12 then output else if i = 13 then rankMaster
    else if i = 14 then arityMaster else []

@[simp] theorem tapes_5 (m rm am r a o : List Bool) : tapes m rm am r a o 5 = m := rfl
@[simp] theorem tapes_6 (m rm am r a o : List Bool) : tapes m rm am r a o 6 = r := rfl
@[simp] theorem tapes_8 (m rm am r a o : List Bool) : tapes m rm am r a o 8 = a := rfl
@[simp] theorem tapes_10 (m rm am r a o : List Bool) : tapes m rm am r a o 10 = [] := rfl
@[simp] theorem tapes_12 (m rm am r a o : List Bool) : tapes m rm am r a o 12 = o := rfl
@[simp] theorem tapes_13 (m rm am r a o : List Bool) : tapes m rm am r a o 13 = rm := rfl
@[simp] theorem tapes_14 (m rm am r a o : List Bool) : tapes m rm am r a o 14 = am := rfl

@[simp] theorem tapes_update_6 (m rm am r a o word : List Bool) :
    Function.update (tapes m rm am r a o) 6 word = tapes m rm am word a o := by
  funext i; fin_cases i <;> simp [tapes]
@[simp] theorem tapes_update_8 (m rm am r a o word : List Bool) :
    Function.update (tapes m rm am r a o) 8 word = tapes m rm am r word o := by
  funext i; fin_cases i <;> simp [tapes]

def budget (modulus rank arity : List Bool) : ℕ :=
  SubexpBasePUnranking.budget modulus rank arity + 9 * rank.length + 7 * arity.length + 13

end SubexponentialSAT.SubexpFieldRowPreparation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

theorem roundBudget_covers (B d n : ℕ) (hd : 0 < d)
    (hn : n ≤ d * (18000 * (B + 1) ^ 2 + 102 * B + 90) + 2) :
    7 * (d * B) + 7 * d + 7 * B + 15 +
        (n + (2 * B + 13 * (d * B) + 2 * B + 9 * B + 25)) ≤
      d * (18000 * (B + 1) ^ 2 + 130 * B + 140) + 30 * B + 50 := by
  ring_nf at hn ⊢
  omega

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

theorem zip_ofFn {A B : Type*} {d : ℕ} (a : Fin d → A) (b : Fin d → B) :
    (List.ofFn a).zip (List.ofFn b) = List.ofFn (fun i => (a i, b i)) := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [List.ofFn_succ, List.zip_cons_cons, ih]

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableSetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

def roundCounter (degree : List Bool) : List Bool := (degree ++ degree).tail.tail

@[simp] theorem roundCounter_length (degree : List Bool) :
    (roundCounter degree).length = 2*degree.length-2 := by
  simp [roundCounter]
  omega

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryWidthArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed ordinary polynomial bounds the literal ring, interpolation and
layout-denominator setup budgets, including their staging copies. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Width
open SubexponentialSAT

def interpolationEnvelope (S : ℕ) : ℕ :=
  1000*(S+1)^2*(16*(S+1)^2+S+1)*
    (100000*(S+1)^3*(2*S+1)^2+2*S*S+1)

def ringEnvelope (C e S : ℕ) : ℕ :=
  C*(S+1)^e+1+10000*(S+(C*(S+1)^e+1)+1+interpolationEnvelope S+2)

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Width

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramRecords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Measured physical folds over sparse-hash records

This module specializes the audited framed-record iterator to an accumulator
fold which visits every record. The callback is an actual finite `Cmd`; its
local execution contract remains explicit. `foldProgram_run` concerns primitive
Boolean-register/stack transitions, not an operation counter or semantic oracle.
The same program shape handles clause-literal products, sparse weighted sums,
coefficient-array maps, and support-key dictionary scans.
-/

namespace SubexponentialSAT.SqrtLog.LeafProgram

variable {r s : ℕ} {A : Type*}

@[simp] theorem any_false (records : List (List Bool)) :
    records.any (fun _ => false) = false := by
  induction records with
  | nil => rfl
  | cons a records ih => simpa only [List.any_cons, Bool.false_or] using ih

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceStaging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Protect the target-jet caches while the source-polynomial initializer
uses the same private local ports. Source length and target jet order are
independent runtime values. These are actual copy and clear programs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging

open SubexponentialSAT

def savePairs : List (Fin 768 × Fin 768) :=
  [(532,680),(533,681),(582,682),(583,683)]
def restorePairs : List (Fin 768 × Fin 768) :=
  [(680,532),(681,533),(682,582),(683,583)]
def cachePorts : List (Fin 768) := [532,533,582,583]
def backupPorts : List (Fin 768) := [680,681,682,683]

/-- Source controls are no longer needed by inner jet preparation. Preserve
the explicitly prepared arithmetic masters and the restored target caches. -/
def retainedLow : List (Fin 205) := [5,10,104,192,193,194,201,202,203,204]
def lowPort (i : Fin 205) : Fin 768 := ⟨340+i.val,by omega⟩
def lowClearPorts : List (Fin 768) :=
  ((List.finRange 205).filter (fun i => i∉retainedLow)).map lowPort

end SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceControls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid source-control copies into the isolated 340-stack worker. All inputs
come from runtime layout/ring masters; no source polynomial is supplied. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceControls
open SubexponentialSAT

def pairs : List (Fin 768 × Fin 768) :=
  [(130,361),(131,362),(132,366),
   (710,382),(711,383),(140,384),(712,385),(138,387),(139,388),
   (135,646),(713,648),(714,649),(715,650),(717,651),(716,652),
   (280,653),(207,654),(136,677),
   (280,589),(207,590),(211,591),(728,592)]

def extraPorts : List (Fin 768) :=
  [589,590,591,592] ++ (List.finRange 84).map (fun i => (⟨596+i.val, by omega⟩ : Fin 768))

end SubexponentialSAT.SqrtLog.LeafProgram.SourceControls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSource
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
open SubexponentialSAT

def workerPort (i : Fin 340) : Fin 768 := ⟨340+i.val,by omega⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact store restoration for the executed source callback. The source
kernel may change its four initialized caches and source output; the wrapper
restores all four caches and removes every staged source control. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Source
open SubexponentialSAT

def coreChanged : List (Fin 768) := [545,532,533,582,583]

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceReadyCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Byte-level value and frame rules for source preparation. These rules
concern the actual paid copy/clear state transformer, not assumed source
execution or a supplied readiness certificate. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT
def localPort (i : Fin 340) : Fin 768 := ⟨340+i.val,by omega⟩

/-- Exactly the local stacks changed by source preparation. -/
def changedLocal : List (Fin 340) :=
  [21,22,25,26,42,43,44,45,47,48,192,193,242,243,249,250,251,252,
   306,308,309,310,311,312,313,314,337]

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNodeScanControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed traversal of flat node cells, skipping one unary-indexed node.
The included-node service is an actual command with an actual execution
contract. This file accounts for all reads, guards, index pops, and cleanup.
-/

namespace SubexponentialSAT.SubexpNodeScanControl

def ports : Fin 6 ↪ Fin 256 := ⟨![215,217,229,240,218,219], by decide⟩

end SubexponentialSAT.SubexpNodeScanControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyInputReady
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Recover the native arithmetic invariants from the actual staged cache
words and an otherwise empty low workspace. No execution premise is used. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT
attribute [local simp] Fin.coe_ofNat_eq_mod

def arithmeticCachePorts : List (Fin 256) := [5,10,104,192,193,194,201,202,203,204]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceReadyArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The arithmetic half of physical source readiness is preserved by source
control copies. The source-count initializer uses R+1, independently of J. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Native arithmetic inspects only these unchanged local stacks. -/
def arithmeticPort (i : Fin 256) : Prop :=
  (i.val < 21 ∨ i=104 ∨ (112 ≤ i.val ∧ i.val ≤ 204)) ∧ i≠192 ∧ i≠193
instance instDecidableArithmeticPort (i : Fin 256) : Decidable (arithmeticPort i) := inferInstanceAs
  (Decidable ((i.val < 21 ∨ i=104 ∨ (112 ≤ i.val ∧ i.val ≤ 204)) ∧ i≠192 ∧ i≠193))

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceReadyInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A physical caller contract. All hypotheses are bytes in retained masters,
blank work tapes, or explicit length bounds. In particular no native source
readiness or execution is assumed. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Arithmetic masters, incidence masters, and the three running literal-loop
words are allowed to be populated before source preparation. -/
def physicalLive : List (Fin 340) :=
  [5,10,104,192,193,194,201,202,203,204,206,207,208,209,210,211,212,213,
   215,216,229,233,234,235,243]

def localBlank (i : Fin 340) : Prop :=
  (i ∉ physicalLive ∧ i ∉ changedLocal) ∨ i ∈ ([192,193,242,243] : List (Fin 340))
instance instDecidableLocalBlank (i : Fin 340) : Decidable (localBlank i) := inferInstanceAs
  (Decidable ((i ∉ physicalLive ∧ i ∉ changedLocal) ∨
    i ∈ ([192,193,242,243] : List (Fin 340))))

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendPorts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed disjoint work areas for the per-query native frontend. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend

def registers (n : ℕ) (hn : n ≤ 40) (i : Fin n) : Fin 40 := ⟨i.val,by omega⟩
def block (base n : ℕ) (hn : base+n ≤ 768) (i : Fin n) : Fin 768 :=
  ⟨base+i.val,by omega⟩

def bank := block 340 77 (by decide)
def early := block 417 77 (by decide)
def scopes := block 500 80 (by decide)
def high := block 580 32 (by decide)
def stats := block 612 21 (by decide)
def arity := block 633 12 (by decide)
def mask : Fin 4 → Fin 768 := ![338,645,719,646]
def finish : Fin 3 → Fin 768 := ![613,629,642]

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramMax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native unary maximum. Consumes the new value and leaves the maximum
on the accumulator stack, using a linear number of physical bit operations. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Max
abbrev unary (n : ℕ) := List.replicate n true

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Max

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native bit lookup at a unary index. The mask source is preserved. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup
abbrev unary (n : ℕ) := List.replicate n true

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Lookup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramScope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Count precisely the unpinned identifiers in an explicit scope. The mask is
in original coordinate order and the framed natural identifiers are read at
runtime. No arity or other statistic is supplied as an input. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope
abbrev unary (n : ℕ) := List.replicate n true

def parserRegs (r : Fin 7 → Bool) (t p f : Bool) :=
  Function.update (Function.update (Function.update r 4 t) 5 p) 6 f

def lookupRegs : Fin 4 → Fin 7 := Fin.castAdd 3
def lookupStacks : Fin 5 → Fin 7 := Fin.castAdd 2

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Scope

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramArity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime outer record fold computing the maximum masked scope length and
factor count, including empty scope records. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity
abbrev unary (n : ℕ) := List.replicate n true

def parserRegs (r : Fin 10 → Bool) (t p f : Bool) :=
  Function.update (Function.update (Function.update r 7 t) 8 p) 9 f

def scopeRegs : Fin 7 → Fin 10 := Fin.castAdd 3
def scopeStacks : Fin 7 → Fin 12 := Fin.castAdd 5
def prepared (r : Fin 10 → Bool) := Function.update (Function.update (Function.update r 4 false) 5 true) 6 false

def maxRegs : Fin 3 → Fin 10 := Fin.castAdd 7
def maxStacks : Fin 3 → Fin 12 := ![4,9,10]

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-register local operations for the actual residual statistics scan. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
abbrev unary (n : ℕ) := List.replicate n true

def maxRegs : Fin 3 → Fin 10 := Fin.castAdd 7
def maxStacks : Fin 3 → Fin 21 := ![18,15,19]

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramVariables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact runtime accumulation of residual variable statistics. Each degree is
computed by scanning the serialized original scopes. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram

def countPorts : Fin 13 → Fin 21 := Fin.castAdd 8

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramBoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The variable scan is started from actual serialized scopes and a mask.
The factor count is obtained by a physical record scan, never supplied as data. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram

def factorRegs : Fin 2 → Fin 10 := Fin.castAdd 8
def factorStacks : Fin 2 → Fin 21 := ![3,1]

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramFinalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Add precisely the uncovered-variable neutral factors. Inputs are the
unary outputs of the physical scope and variable scans. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Finalize
abbrev unary (n : ℕ) := List.replicate n true

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Finalize

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The frontend calls only concrete finite machines. All state embeddings
below are specifications of actual calls, never free data transformations. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT

abbrev r2 := registers 2 (by decide)
abbrev r3 := registers 3 (by decide)
abbrev r8 := registers 8 (by decide)
abbrev r9 := registers 9 (by decide)
abbrev r10 := registers 10 (by decide)
abbrev r11 := registers 11 (by decide)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LocalCodeCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Finite counting lemmas for the local-code exhaustive search. -/

namespace SubexponentialSAT.SqrtLog.LocalCode

open scoped BigOperators

/-- Translation identifies an arbitrary fiber of a surjective homomorphism
with its zero fiber. This is the exact finite substitute for uniformity. -/
def fiberEquivZero {A B : Type*} [AddGroup A] [AddGroup B]
    (f : A →+ B) (b : B) (a : A) (ha : f a = b) :
    {x : A // f x = b} ≃ {x : A // f x = 0} where
  toFun x := ⟨x.1 - a, by rw [map_sub, x.2, ha, sub_self]⟩
  invFun x := ⟨x.1 + a, by rw [map_add, x.2, ha, zero_add]⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

end SubexponentialSAT.SqrtLog.LocalCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCommand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native syntax from physical formula/row masters through the guarded
parameter bank. The only static input is the fixed formula-width bound k. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT

def scopeCopies : List (Fin 768 × Fin 768) :=
  [(700,514),(701,546),(705,549),(706,550),(707,507),(708,501)]

def highCopies : List (Fin 768 × Fin 768) := [(718,580),(709,596),(433,597)]
def statsCopies : List (Fin 768 × Fin 768) := [(718,612),(719,632)]
def arityCopies : List (Fin 768 × Fin 768) := [(719,633),(718,640)]

def binaryPorts (src dst : Fin 768) : Fin 3 → Fin 768 := ![src,dst,647]

def countPorts : Fin 2 → Fin 768 := ![647,704]

def offsetPorts : Fin 22 → Fin 768 :=
  ![725,720,727,650,651,652,653,654,655,141,656,657,658,659,660,661,662,663,664,665,666,667]
def lowPorts : Fin 2 → Fin 768 := ![668,134]

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT
attribute [local simp] Fin.coe_ofNat_eq_mod

def cleanupPorts : List (Fin 768) := (List.finRange 262).map (block 417 262 (by decide))

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsTotals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed finite-sum and maximum specifications of the native variable scan. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open LeafStatisticsProgram

def scanSum (f : ℕ → ℕ) (v : ℕ) (mask : List Bool) : ℕ :=
  ∑ i : Fin mask.length, if mask.get i then 0 else f (v + i.val)

@[simp] theorem scanSum_nil (f : ℕ → ℕ) (v : ℕ) : scanSum f v [] = 0 := by
  simp [scanSum]

@[simp] theorem scanSum_cons (f : ℕ → ℕ) (v : ℕ) (b : Bool) (bs : List Bool) :
    scanSum f v (b :: bs) = (if b then 0 else f v) + scanSum f (v+1) bs := by
  simp [scanSum, Fin.sum_univ_succ, Nat.add_comm, Nat.add_left_comm]

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafScopeResourceBoundsPolylog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit, pointwise polylogarithmic resource envelopes. No sequence of
matrices is chosen before the ambient cutoff: all raw scope tables satisfying
the concrete slot budget share these same constants. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
open LeafStatisticsProgram

abbrev slotCoefficient (q : ℕ) := 320000*(q+2)^3 + 20000*(q+2)^2 + 1
abbrev massCoefficient (k q : ℕ) := 11 * slotCoefficient q * (k+1)
abbrev statCoefficient (k q : ℕ) := 2 * massCoefficient k q + 1
abbrev resourceExponent (q : ℕ) := 2*q+4

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafScopeResourceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Resource bounds for the exact physical scope stream, including zero
coefficients, repeated raw slots, empty hash rows, and the optional mark. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

abbrev slots {α : Type*} (rows : List (List α)) : ℕ :=
  (rows.map List.length).sum

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendScanBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT
attribute [local simp] Fin.coe_ofNat_eq_mod

def highMajorant (S : ℕ) : ℕ :=
  7*S+5+300001*(2*S+37)^3+(7*(16*S^3)+5+7*S+5+7*(S+18)+5)+
    270000*(16*S^3+4*S+40)^3+17*S+14
def measureMajorant (S : ℕ) : ℕ :=
  7*(16*S^3)+5+7*S+5+(10*(16*S^3)+7*S+12)+
    (S*(1000*(16*S^3+S+S+1)^2+50*(S+1)+50+1)+1)+2+
    7*S+5+7*(16*S^3)+5+3+(32*(S+1)+101)*(16*S^3+1)+3*S+10

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafWeightProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The Boolean part of a local squarefree head weight, executed by a fixed
parallel scan of the assignment, support mask, and head mask. -/
namespace SubexponentialSAT.SqrtLog.LeafWeightProgram

open SubexponentialSAT

/-- Missing mask cells are unselected; the intended inputs have equal length. -/
def good : List Bool → List Bool → List Bool → Bool
  | [], _, _ => true
  | a :: as, ss, hs => (!(ss.headD false && hs.headD false) || a) &&
      good as ss.tail hs.tail

abbrev tapes (a s h : List Bool) : Fin 3 → List Bool := ![a,s,h]

end SubexponentialSAT.SqrtLog.LeafWeightProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafWeightProgramNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserving physical wrapper for the Boolean head-weight scan. The actual
ring zero and one are arbitrary runtime words, so the ring degree is dynamic. -/
namespace SubexponentialSAT.SqrtLog.LeafWeightProgram.Native

open SubexponentialSAT

abbrev stackMap : Fin 3 → Fin 10 := ![5,6,7]

end SubexponentialSAT.SqrtLog.LeafWeightProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsBuckets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual attained labels and their Boolean fibers. The label codomain need
not be finite: integer signature vectors are allowed. Enumeration is the
image of each finite head assignment set, followed by its actual fibers. -/

namespace SubexponentialSAT.SqrtLog.Moments

open scoped BigOperators

section Fibers

variable {G : Type*} [Fintype G] [DecidableEq G]
variable {A L : G → Type*} [∀ g, Fintype (A g)] [∀ g, DecidableEq (L g)]

/-- The concrete finite list of attained signatures, represented as a finset. -/
def attainedLabels (label : ∀ g, A g → L g) (g : G) : Finset (L g) :=
  Finset.univ.image (label g)

abbrev LabelValue (label : ∀ g, A g → L g) (g : G) :=
  {y : L g // y ∈ attainedLabels label g}

abbrev LabelBucket (label : ∀ g, A g → L g) (g : G) (y : LabelValue label g) :=
  {a : A g // label g a = y.val}

/-- No rectangularity or equal-fiber-size premise occurs in this equivalence. -/
def actualBucketEquiv (label : ∀ g, A g → L g) :
    (∀ g, A g) ≃ Σ y : ∀ g, LabelValue label g, ∀ g, LabelBucket label g (y g) where
  toFun a := ⟨fun g => ⟨label g (a g), Finset.mem_image.mpr ⟨a g, Finset.mem_univ _, rfl⟩⟩,
    fun g => ⟨a g, rfl⟩⟩
  invFun y := fun g => (y.2 g).val
  left_inv a := rfl
  right_inv y := by
    rcases y with ⟨y, a⟩
    have hy : (fun g => (⟨label g (a g).val,
        Finset.mem_image.mpr ⟨(a g).val, Finset.mem_univ _, rfl⟩⟩ : LabelValue label g)) = y := by
      funext g
      apply Subtype.ext
      exact (a g).property
    apply Sigma.ext hy
    apply Function.hfunext rfl
    intro g g' hgg
    cases hgg
    apply Subtype.heq_iff_coe_eq _ |>.mpr
    · rfl
    · intro z
      change (label g z = label g (a g).val) ↔ (label g z = (y g).val)
      rw [(a g).property]

end Fibers

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramNormalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms



namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize

variable {K : Type*} [DecidableEq K]

def KeyBound {C : Type*} (key : K → List Bool) (W : ℕ) (l : List (K × C)) : Prop :=
  ∀ a ∈ l, (key a.1).length ≤ W

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProjectionProgramBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram

def readRegsMap : Fin 2 → Fin 5 := Fin.castAdd 3

def smallRegs : Fin 3 → Fin 5 := Fin.castAdd 2
def maskPorts : Fin 3 → Fin 10 := ![4,2,5]
def emitPorts : Fin 3 → Fin 10 := ![5,3,9]

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProjectionProgramNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms



namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram

structure Entry where
  u : ℕ
  z : ℕ
  mask : List Bool
  coeff : List Bool

def Entry.erased (e : Entry) : Entry := {e with mask:=List.replicate e.mask.length false}

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram


/-! A fixed finite program for exact-support projection of a raw sparse dictionary.
Coefficients are opaque framed payloads. No normalization or arithmetic is used. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed forty-stack workspace for the two runtime readout counters. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram

def widePorts : Fin 27 → Fin 40 := Fin.castAdd 13

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


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

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBudgetArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Numerical envelopes for the actual packing stages. Every argument below
is a size of an input or a bound established for a generated value. -/

namespace SubexponentialSAT.Subexp.PackingBudgetArithmetic

theorem le_power {S k : ℕ} (hS : 1 ≤ S) (hk : 1 ≤ k) : S ≤ S ^ k := by
  simpa only [pow_one] using Nat.pow_le_pow_right hS hk

theorem label_trace_le (S D W H : ℕ) (hS : 1 ≤ S) (hD : D ≤ S)
    (hW : W ≤ S) (hH : H ≤ 7 * S ^ 3) :
    4 + D * (12 * H + 13 + 200 * (W + H + 0 + D + 1) ^ 2) ≤ 21000 * S ^ 7 := by
  have h3 : S ≤ S ^ 3 := le_power hS (by decide)
  have h7 : S ≤ S ^ 7 := le_power hS (by decide)
  have h47 : S ^ 4 ≤ S ^ 7 := Nat.pow_le_pow_right hS (by decide)
  have hh : W + H + 0 + D + 1 ≤ 10 * S ^ 3 := by omega
  calc
    _ ≤ 4 + S * (12 * (7 * S ^ 3) + 13 + 200 * (10 * S ^ 3) ^ 2) := by gcongr
    _ ≤ 21000 * S ^ 7 := by ring_nf; omega

theorem type_stream_le (S N : ℕ) (hS : 1 ≤ S) (hN : N ≤ S) :
    1 + (2 * S ^ 2 + 2) * N ≤ 5 * S ^ 3 := by
  have h3 : S ≤ S ^ 3 := le_power hS (by decide)
  calc
    _ ≤ 1 + (2 * S ^ 2 + 2) * S := by gcongr
    _ ≤ 5 * S ^ 3 := by ring_nf; omega

theorem bucket_payload_le (S L : ℕ) (hS : 1 ≤ S) (hL : L ≤ 21000 * S ^ 7) :
    2 * S ^ 2 + 1 + L ≤ 21003 * S ^ 7 := by
  have h7 : S ≤ S ^ 7 := le_power hS (by decide)
  have h27 : S ^ 2 ≤ S ^ 7 := Nat.pow_le_pow_right hS (by decide)
  omega

theorem bucket_table_le (S N L : ℕ) (hS : 1 ≤ S) (hN : N ≤ S)
    (hL : L ≤ 21000 * S ^ 7) :
    1 + (2 * (2 * S ^ 2 + 1 + L) + 2) * N ≤ 43000 * S ^ 8 := by
  have h8 : S ≤ S ^ 8 := le_power hS (by decide)
  have hp := bucket_payload_le S L hS hL
  calc
    _ ≤ 1 + (2 * (21003 * S ^ 7) + 2) * S := by gcongr
    _ ≤ 43000 * S ^ 8 := by ring_nf; omega

theorem bucket_core_le (S N L : ℕ) (hS : 1 ≤ S) (hN : N ≤ S)
    (hL : L ≤ 21000 * S ^ 7) :
    9 + N * (6 * S ^ 2 + 100 * (L + 1) * (S ^ 2 + 1) + 7) +
      3 * (1 + (2 * (2 * S ^ 2 + 1 + L) + 2) * N) ≤ 4400000 * S ^ 10 := by
  have h7 : S ≤ S ^ 7 := le_power hS (by decide)
  have h2 : S ≤ S ^ 2 := le_power hS (by decide)
  have h10 : S ≤ S ^ 10 := le_power hS (by decide)
  have h310 : S ^ 3 ≤ S ^ 10 := Nat.pow_le_pow_right hS (by decide)
  have h810 : S ^ 8 ≤ S ^ 10 := Nat.pow_le_pow_right hS (by decide)
  have hL' : L + 1 ≤ 21001 * S ^ 7 := by omega
  have hW : S ^ 2 + 1 ≤ 2 * S ^ 2 := by omega
  have ht := bucket_table_le S N L hS hN hL
  calc
    _ ≤ 9 + S * (6 * S ^ 2 + 100 * (21001 * S ^ 7) * (2 * S ^ 2) + 7) +
        3 * (43000 * S ^ 8) := by gcongr
    _ ≤ 4400000 * S ^ 10 := by ring_nf; omega

theorem bucket_stage_le (S L T D K M C : ℕ) (hS : 1 ≤ S)
    (hL : L ≤ 21000 * S ^ 7) (hT : T ≤ 5 * S ^ 3) (hD : D ≤ S)
    (hK : K ≤ 43000 * S ^ 8) (hM : M ≤ S) (hC : C ≤ 4400000 * S ^ 10) :
    8 * L + 6 * T + 7 * D + 6 * K + 6 * M + 32 + C ≤ 5000000 * S ^ 10 := by
  have h10 : S ≤ S ^ 10 := le_power hS (by decide)
  have h310 : S ^ 3 ≤ S ^ 10 := Nat.pow_le_pow_right hS (by decide)
  have h710 : S ^ 7 ≤ S ^ 10 := Nat.pow_le_pow_right hS (by decide)
  have h810 : S ^ 8 ≤ S ^ 10 := Nat.pow_le_pow_right hS (by decide)
  omega

end SubexponentialSAT.Subexp.PackingBudgetArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NativePackingBoundsTail
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

open SubexponentialSAT.Subexp

variable {U : Type*} [DecidableEq U]

def metadataBound (D T : ℕ) : ℕ := D * (6 * D + 4 * T + 8)
def addressBound (D : ℕ) : ℕ := D * (4 * D + 2)

end SubexponentialSAT.SqrtLog.NativePackingBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NativePackingBoundsAddress
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit scalar envelope for the actual two-address packing call. -/
namespace SubexponentialSAT.SqrtLog.NativePackingBounds
open SubexponentialSAT.Subexp

/-- Both represented alphabets are charged at their actual cardinality. -/
def addressSize (D M r Q : ℕ) : ℕ :=
  D+1+r^(2*Q)+Q*r+M*(Q*r)+
    (1+(2*(Q*r)+2)*r^Q)+(1+(16*M+24)*D)+1

end SubexponentialSAT.SqrtLog.NativePackingBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Convert a physically scanned factor-index stream to incidence plans. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows
open SubexponentialSAT.Subexp

def callbackBound (h n j : ℕ) : ℕ := 200*(h+n+j+1)

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows


/-! Native per-variable incident-factor scan from the original scope stream. -/


/-! Fixed cleanup for the native scope-address scanner. -/


/-! Calls to the fixed record mapper inside the native scope scan. -/


/-! One native low-variable step, including its uncovered neutral factor. -/


/-! Runtime high-mask loop for the original-address incidence stream. -/


/-! Count the physical scope stream before constructing native incidence plans. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramWide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The caller's private64-stack workspace lies after the live native
parameter bank340..416, which must survive until ring setup. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

def registers : Fin 16 ↪ Fin 40 := ⟨Fin.castAdd 24,Fin.castAdd_injective _ _⟩
def ports : Fin 64 ↪ Fin 768 := ⟨fun i=>⟨417+i.val,by have := i.isLt; omega⟩,by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 417+i.val=417+j.val at hv
  omega⟩

@[simp] theorem ports_val (i : Fin 64) : (ports i).val = 417 + i.val := rfl

@[simp] theorem ports_eq_ports (i j : Fin 64) : ports i = ports j ↔ i = j :=
  ports.injective.eq_iff

@[simp] theorem ports_ne_low (i : Fin 64) (j : Fin 768) (hj : j.val < 417) :
    ports i ≠ j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [ports_val] at hv
  omega

@[simp] theorem low_ne_ports (j : Fin 768) (i : Fin 64) (hj : j.val < 417) :
    j ≠ ports i := ne_comm.mp (ports_ne_low i j hj)

@[simp] theorem ports_ne_high (i : Fin 64) (j : Fin 768) (hj : 481 ≤ j.val) :
    ports i ≠ j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [ports_val] at hv
  have hi := i.isLt
  omega

@[simp] theorem high_ne_ports (j : Fin 768) (i : Fin 64) (hj : 481 ≤ j.val) :
    j ≠ ports i := ne_comm.mp (ports_ne_high i j hj)

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeScaleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Base stage. -/
/-! Fixed physical ABI for scaling all coefficients in a sparse dictionary.
The low 32 stacks are the common coefficient-ring service. The eight high
stacks hold source, reversed output, scalar, key, coefficient staging, frame
staging, final output, and a preserved copy of the unary degree. -/

/-! Moves stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

structure Environment where
  modulus : List Bool
  width : List Bool
  zero : List Bool
  table : List Bool
  scalar : List Bool
  count : List Bool

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Emit stage. -/

/-! Native stage. -/

/-! Loop stage. -/

/-! Cost stage. -/

/-! Semantics stage. -/

end OAI.Algorithms
end


