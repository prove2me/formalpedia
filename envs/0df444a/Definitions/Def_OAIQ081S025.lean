-- Prove2me | Definitions.Def_OAIQ081S025
-- name    : OAIQ081S025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:26:56.521897+00:00
-- url     : https://prove2.me/theorems/a58cac2d-4323-4fd3-bf80-25cb6ba639a2
-- title:
--   Definitions bundle OAIQ081S025 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 322 declarations of OpenAI's Lean: 178 definitions and 144 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.ExecCNFMembership.Data`, `OAI.Algorithms.SubexponentialSAT.ExecCNFMembership.cleared`, `OAI.Algorithms.SubexponentialSAT.ExecCNFMembership.copied`, `OAI.Algorithms.SubexponentialSAT.ExecCNFMembership.copyQuery`, `OAI.Algorithms.SubexponentialSAT.ExecCNFMembership.copyQueryProgram`, `OAI.Algorithms.SubexponentialSAT.ExecCNFMembership.invariant`, `OAI.Algorithms.SubexponentialSAT.ExecCNFMembership.ports`, `OAI.Algorithms.SubexponentialSAT.ExecCNFRecords.captureProgram`, `OAI.Algorithms.SubexponentialSAT.ExecCNFRecords.cfg`, `OAI.Algorithms.SubexponentialSAT.ExecCNFRecords.copyCfg`, `OAI.Algorithms.SubexponentialSAT.ExecCNFRecords.copyProgram`, `OAI.Algorithms.SubexponentialSAT.ExecCNFRecords.restoreCapturedProgram`, `OAI.Algorithms.SubexponentialSAT.ExecCNFRecords.skipProgram`, `OAI.Algorithms.SubexponentialSAT.ExecCNFSubset.Data`, `OAI.Algorithms.SubexponentialSAT.ExecCNFSubset.cleared`, `OAI.Algorithms.SubexponentialSAT.ExecCNFSubset.copied`, `OAI.Algorithms.SubexponentialSAT.ExecCNFSubset.copyTarget`, `OAI.Algorithms.SubexponentialSAT.ExecCNFSubset.copyTargetProgram`, `OAI.Algorithms.SubexponentialSAT.ExecCNFSubset.finish`, `OAI.Algorithms.SubexponentialSAT.ExecCNFSubset.invariant`, `OAI.Algorithms.SubexponentialSAT.ExecCNFSubset.mark`, `OAI.Algorithms.SubexponentialSAT.ExecCNFSubset.perRecordCost`, `OAI.Algorithms.SubexponentialSAT.ExecCNFSubset.ports`, `OAI.Algorithms.SubexponentialSAT.ExecCNFTupleOdometer.program`, `OAI.Algorithms.SubexponentialSAT.ExecClauseCost.bitEqualityEnd`, `OAI.Algorithms.SubexponentialSAT.ExecClauseCost.bitEqualityProgram`, `OAI.Algorithms.SubexponentialSAT.ExecClauseCost.bitEqualityStart`, `OAI.Algorithms.SubexponentialSAT.ExecClauseCost.membershipEqProgram`, `OAI.Algorithms.SubexponentialSAT.ExecClauseCost.poppedRegs`, `OAI.Algorithms.SubexponentialSAT.ExecClauseDedupProgram.budget`, `OAI.Algorithms.SubexponentialSAT.ExecClauseDedupProgram.callbackBound`, `OAI.Algorithms.SubexponentialSAT.ExecClauseDedupProgram.copySuffix`, `OAI.Algorithms.SubexponentialSAT.ExecClauseDedupProgram.formulaCode`, `OAI.Algorithms.SubexponentialSAT.ExecClauseDedupProgram.ports`, `OAI.Algorithms.SubexponentialSAT.ExecClauseDedupProgram.pushFalse`, `OAI.Algorithms.SubexponentialSAT.ExecClauseFilterReverse.Data`, `OAI.Algorithms.SubexponentialSAT.ExecClauseFilterReverse.state`, `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.ClausePayload`, `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.callbackBound`, `OAI.Algorithms.SubexponentialSAT.ExecClauseFiltersProgram.copyMaster` and 138 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_Encoding`, `SubexponentialSAT_ExecCNFCodeTransport`, `SubexponentialSAT_ExecCNFMembership`, `SubexponentialSAT_ExecCNFRecords`, `SubexponentialSAT_ExecCNFSubset`, `SubexponentialSAT_ExecCNFTupleOdometer`, `SubexponentialSAT_ExecClauseCost`, `SubexponentialSAT_ExecClauseCost39Lift`, `SubexponentialSAT_ExecClauseDedupProgram`, `SubexponentialSAT_ExecClauseFilterReverse`, `SubexponentialSAT_ExecClauseFiltersProgram`, `SubexponentialSAT_ExecClauseRelationScan`, `SubexponentialSAT_ExecClauseRelationScanPreserve`, `SubexponentialSAT_ExecClauseRelationsProgram`, `SubexponentialSAT_ExecCleanLiteralsProgram`, `SubexponentialSAT_ExecCoreChildProgram`, `SubexponentialSAT_ExecLiteralDedupProgram`, `SubexponentialSAT_ExecPetalChildProgram`, `SubexponentialSAT_ExecPetalFamilyProgram`, `SubexponentialSAT_ExecPetalProgram`, `SubexponentialSAT_ExecQuantitativeSparsify`, `SubexponentialSAT_ExecSparsifyWorklist`, `SubexponentialSAT_ExecSunflowerCodeTransport`, `SubexponentialSAT_ExecWorklistProgram`, `SubexponentialSAT_LocalExpectation`, `SubexponentialSAT_ModularRingCore`, `SubexponentialSAT_ModularRingPrograms`, `SubexponentialSAT_ParserProgram`, `SubexponentialSAT_ProgramEncoding`, `SubexponentialSAT_ProgramStateFrames`, `SubexponentialSAT_RecordPrograms`, `SubexponentialSAT_SaturatingSubtractionProgram`, `SubexponentialSAT_SqrtLog_BinaryArgmin`, `SubexponentialSAT_StackRoutines`, `SubexponentialSAT_SubexpFrontend`, `SubexponentialSAT_SubexpModulusConstruction`, `SubexponentialSAT_SubexpNormalizationPrefixProgram`, `SubexponentialSAT_SubexpNormalizationProgram`, `SubexponentialSAT_SubexpNormalizeProgram`, `SubexponentialSAT_SubexpPostfixControl`, `SubexponentialSAT_SubexpScanPrimitives`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S000`, `OAIQ081S001` and `OAIQ081S002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S045`, `OAIQ081S046`, `OAIQ081S047`, `OAIQ081S048`, `OAIQ081S049`, `OAIQ081S050`, `OAIQ081S051`, `OAIQ081S052`, `OAIQ081S053`, `OAIQ081S054`, `OAIQ081S055`, `OAIQ081S056`, `OAIQ081S057`, `OAIQ081S058`, `OAIQ081S059`, `OAIQ081S060`, `OAIQ081S061`, `OAIQ081S062`, `OAIQ081S063`, `OAIQ081S064` and `OAIQ081S065`; the statements `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentBoundary_Ready_callback_eval`, `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback_hash_callback_eval`, `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback_marked_callback_eval`, `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSumNative_run`, `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighMarkedFrontend_accepted_command_kept_frame`, `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafContract_marked_rounds`, `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryCountReconstruction_query_run_space_with_full_frame`, `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryProducerSpace_prepared_run_space` and `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorLoad_load_run`; the proofs of `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentBoundary_Ready_callback_eval`, `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback_hash_callback_eval`, `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback_marked_callback_eval`, `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSumNative_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLeafContract_marked_rounds`, `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryCountReconstruction_query_run_space_with_full_frame`, `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryProducerSpace_prepared_run_space` and `OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorLoad_load_run`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S002

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Encoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# An explicit binary encoding of finite CNF formulas

Numeric fields are unary on the binary alphabet: `n` is `n` true bits and
one false bit. Lists use an explicit escape frame, and both levels of finite
sets are sorted before encoding. No enumeration of semantic truth values or
noncomputable choice participates in the encoding.
-/

namespace SubexponentialSAT.Encoding

theorem frame_append_injective {bits bits' rest rest' : List Bool}
    (h : frame bits ++ rest = frame bits' ++ rest') :
    bits = bits' ∧ rest = rest' := by
  have hr := congrArg readFrame h
  simpa using hr

theorem length_encodeList_lower {α : Type*} (enc : α → List Bool) (as : List α) :
    as.length + 1 ≤ (encodeList enc as).length := by
  induction as with
  | nil => simp
  | cons a as ih => rw [length_encodeList_cons]; simp only [List.length_cons]; omega

theorem length_encodeList_upper {α : Type*} (enc : α → List Bool)
    (as : List α) (K : ℕ) (hK : ∀ a ∈ as, (enc a).length ≤ K) :
    (encodeList enc as).length ≤ 1 + (2 * K + 2) * as.length := by
  induction as with
  | nil => simp
  | cons a as ih =>
      have ha := hK a (by simp)
      have ht := ih (fun b hb => hK b (by simp [hb]))
      rw [length_encodeList_cons]
      simp only [List.length_cons]
      calc
        2 * (enc a).length + 2 + (encodeList enc as).length
            ≤ 2 * K + 2 + (1 + (2 * K + 2) * as.length) := by omega
        _ = 1 + (2 * K + 2) * (as.length + 1) := by ring

theorem literalCode_injective {n : ℕ} :
    Function.Injective (literalCode (n := n)) := by
  intro a b h
  rcases a with ⟨av, ap⟩
  rcases b with ⟨bv, bp⟩
  cases ap <;> cases bp <;> simp [literalCode] at h
  · have hv : av = bv := Fin.ext (by omega)
    cases hv
    rfl
  · omega
  · omega
  · have hv : av = bv := Fin.ext (by omega)
    cases hv
    rfl

@[simp] theorem length_clauseNumbers {n : ℕ} (C : SAT.Clause (Fin n)) :
    (clauseNumbers C).length = C.card := by
  simp [clauseNumbers, Finset.card_image_of_injective _ literalCode_injective]

theorem clauseNumbers_injective {n : ℕ} :
    Function.Injective (clauseNumbers (n := n)) := by
  intro C D h
  apply Finset.image_injective literalCode_injective
  have hs := congrArg List.toFinset h
  simpa [clauseNumbers] using hs

@[simp] theorem length_cnfNumbers {n : ℕ} (F : SAT.CNF (Fin n)) :
    (cnfNumbers F).length = F.card := by
  simp [cnfNumbers, Finset.card_image_of_injective _ clauseNumbers_injective]

@[simp] theorem readNat_encodeCNF {n : ℕ} (F : SAT.CNF (Fin n)) :
    readNat (encodeCNF F) = some (n, encodeCNFBody F) := by
  simp [encodeCNF]

@[simp] theorem formulaBitLength_eq {n : ℕ} (F : SAT.CNF (Fin n)) :
    formulaBitLength F = n + 1 + (encodeCNFBody F).length := by
  simp [formulaBitLength, encodeCNF]

end SubexponentialSAT.Encoding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit costs for the executable clause loops

These routines return their result together with the number of charged events
in the displayed recursive execution. A recursive list-case inspection costs
one event; a literal equality test costs one further event. These are list-loop
and comparison units, **not** primitive bit-machine transitions. In particular,
`DecidableEq α` is an equality interface, not a unit-cost bit implementation.
No cost is attached to an arbitrary uninstrumented function.
-/

namespace SubexponentialSAT.ExecClauseCost

universe u v
variable {α : Type u} {β : Type v}

open SubexponentialSAT.BitProgram

/-- Fixed finite code comparing two bit strings destructively. Register 4 is the answer. -/
abbrev bitEqualityProgram : Program 5 2 10 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .pop 1 2 3 2
    | 2 => .bxor 4 1 3 3
    | 3 => .branch 4 8 4
    | 4 => .branch 1 5 7
    | 5 => .bxor 4 0 2 6
    | 6 => .branch 4 8 0
    | 7 => .set 4 true 9
    | 8 => .set 4 false 9
    | _ => .halt

def bitEqualityStart (r : Fin 5 → Bool) (xs ys : List Bool) : Cfg 5 2 10 :=
  ⟨some 0, r, bitStacks xs ys⟩

def poppedRegs (r : Fin 5 → Bool) (x y : Option Bool) : Fin 5 → Bool :=
  readRegs (readRegs r 0 1 x) 2 3 y

def bitEqualityEnd (r : Fin 5 → Bool) (xs ys : List Bool) (answer : Bool) : Cfg 5 2 10 :=
  ⟨none, Function.update r 4 answer, bitStacks xs ys⟩

theorem bitEquality_nil_nil (r : Fin 5 → Bool) :
    Trace bitEqualityProgram 7 (bitEqualityStart r [] [])
      (bitEqualityEnd (poppedRegs r none none) [] [] true) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, bitEqualityProgram, execInstr,
    bitEqualityStart, bitEqualityEnd, poppedRegs, readRegs, bitStacks]
  funext i
  fin_cases i <;> simp [bitStacks]

theorem bitEquality_cons_nil (r : Fin 5 → Bool) (x : Bool) (xs : List Bool) :
    Trace bitEqualityProgram 6 (bitEqualityStart r (x :: xs) [])
      (bitEqualityEnd (poppedRegs r (some x) none) xs [] false) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, bitEqualityProgram, execInstr,
    bitEqualityStart, bitEqualityEnd, poppedRegs, readRegs, bitStacks]
  funext i
  fin_cases i <;> simp [bitStacks]

theorem bitEquality_nil_cons (r : Fin 5 → Bool) (y : Bool) (ys : List Bool) :
    Trace bitEqualityProgram 6 (bitEqualityStart r [] (y :: ys))
      (bitEqualityEnd (poppedRegs r none (some y)) [] ys false) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, bitEqualityProgram, execInstr,
    bitEqualityStart, bitEqualityEnd, poppedRegs, readRegs, bitStacks]
  funext i
  fin_cases i <;> simp [bitStacks]

theorem bitEquality_cons_eq (r : Fin 5 → Bool) (x : Bool) (xs ys : List Bool) :
    Trace bitEqualityProgram 7 (bitEqualityStart r (x :: xs) (x :: ys))
      (bitEqualityStart (Function.update (poppedRegs r (some x) (some x)) 4 false) xs ys) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, bitEqualityProgram, execInstr,
    bitEqualityStart, poppedRegs, readRegs, bitStacks]
  funext i
  fin_cases i <;> simp [bitStacks]

theorem bitEquality_cons_ne (r : Fin 5 → Bool) (x y : Bool) (xs ys : List Bool)
    (h : x ≠ y) :
    Trace bitEqualityProgram 9 (bitEqualityStart r (x :: xs) (y :: ys))
      (bitEqualityEnd (poppedRegs r (some x) (some y)) xs ys false) := by
  have hxor : (x ^^ y) = true := by cases x <;> cases y <;> simp_all
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, bitEqualityProgram, execInstr,
    bitEqualityStart, bitEqualityEnd, poppedRegs, readRegs, bitStacks, hxor]
  funext i
  fin_cases i <;> simp [bitStacks]


/-- A genuine instruction trace. Comparison destroys the inspected prefixes;
it may leave residual tails on an early mismatch. -/
theorem bitEquality_runs (r : Fin 5 → Bool) (xs ys : List Bool) :
    ∃ n ≤ 9 * (xs.length + 1), ∃ c : Cfg 5 2 10,
      Trace bitEqualityProgram n (bitEqualityStart r xs ys) c ∧
      c.pc = none ∧ c.regs 4 = decide (xs = ys) := by
  induction xs generalizing r ys with
  | nil =>
    cases ys with
    | nil =>
      refine ⟨7, by simp, bitEqualityEnd (poppedRegs r none none) [] [] true,
        bitEquality_nil_nil r, rfl, ?_⟩
      simp [bitEqualityEnd]
    | cons y ys =>
      refine ⟨6, by simp, bitEqualityEnd (poppedRegs r none (some y)) [] ys false,
        bitEquality_nil_cons r y ys, rfl, ?_⟩
      simp [bitEqualityEnd]
  | cons x xs ih =>
    cases ys with
    | nil =>
      refine ⟨6, by simp; omega,
        bitEqualityEnd (poppedRegs r (some x) none) xs [] false,
        bitEquality_cons_nil r x xs, rfl, ?_⟩
      simp [bitEqualityEnd]
    | cons y ys =>
      by_cases hxy : x = y
      · subst y
        obtain ⟨n, hn, c, hc, hpc, hout⟩ :=
          ih (Function.update (poppedRegs r (some x) (some x)) 4 false) ys
        refine ⟨7 + n, ?_, c, (bitEquality_cons_eq r x xs ys).trans hc, hpc, ?_⟩
        · simp only [List.length_cons]
          omega
        · simpa using hout
      · refine ⟨9, by simp,
          bitEqualityEnd (poppedRegs r (some x) (some y)) xs ys false,
          bitEquality_cons_ne r x y xs ys hxy, rfl, ?_⟩
        simp [bitEqualityEnd, hxy]


theorem bitEquality_step_length_le {c c' : Cfg 5 2 10}
    (h : step bitEqualityProgram c = some c') (i : Fin 2) :
    (c'.stacks i).length ≤ (c.stacks i).length := by
  cases hpc : c.pc with
  | none => simp [step, hpc] at h
  | some q =>
    have he : execInstr (bitEqualityProgram.code q) c = c' := by
      simpa [step, hpc] using h
    subst c'
    fin_cases q <;> simp [ execInstr]
    all_goals
      simp only [Function.update_apply]
      split <;> simp_all [List.length_tail]

theorem bitEquality_trace_length_le {c c' : Cfg 5 2 10} {n : ℕ}
    (h : Trace bitEqualityProgram n c c') (i : Fin 2) :
    (c'.stacks i).length ≤ (c.stacks i).length := by
  induction h with
  | refl => exact le_rfl
  | cons hs ht ih => exact ih.trans (bitEquality_step_length_le hs i)


end SubexponentialSAT.ExecClauseCost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecSparsifyWorklist
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable depth-first worklist traversal for sparsification

The traversal manipulates a list of pending inputs explicitly. It never builds
the specification tree while running. A decreasing mass supplies a finite fuel
bound; the fuel loop halts as soon as the worklist is empty. The specification
tree is used only to prove the exact number of visited nodes.
-/

namespace SubexponentialSAT.ExecSparsifyWorklist

variable {α : Type*}

section ExecutableSelection

variable {n : ℕ}

abbrev Formula (n : ℕ) := ExecCNF.Formula (SAT.Literal (Fin n))

/-- A list-only pass removing repeated literals from each clause. -/
def cleanLiterals (F : Formula n) : Formula n := F.map ExecCNF.dedupLiterals

/-- Normalize once at input. The last cleanup is semantically redundant but
makes the raw-width invariant explicit at the worklist interface. -/
def normalizedInput (F : Formula n) : Formula n :=
  cleanLiterals (ExecCNF.normalize SAT.Literal.negate F)

end ExecutableSelection

end SubexponentialSAT.ExecSparsifyWorklist

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecQuantitativeSparsify
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Quantitative bounds for the executable list sparsifier

This module instantiates the actual list search and depth-first worklist at the
arithmetically selected inverse budget. The finite-set view of each output is
used only for SAT semantics. Node visits are counted by the actual worklist;
they are not presented as primitive bit-machine transitions.
-/

namespace SubexponentialSAT.ExecQuantitativeSparsify

open SAT

variable {n : ℕ}

abbrev Formula (n : ℕ) := ExecCNF.Formula (Literal (Fin n))

/-- The fixed syntactic order on the literals of a clause. -/
def literalList (C : Clause (Fin n)) : List (Literal (Fin n)) :=
  let r := fun a b : Literal (Fin n) => Encoding.literalCode a ≤ Encoding.literalCode b
  letI : IsTrans _ r := ⟨fun _ _ _ => le_trans⟩
  letI : Std.Total r := ⟨fun _ _ => le_total _ _⟩
  letI : Std.Antisymm r :=
    ⟨fun _ _ h h' => Encoding.literalCode_injective (le_antisymm h h')⟩
  C.sort r

/-- The fixed syntactic order on clauses, independent of their truth values. -/
def orderedClauses (F : CNF (Fin n)) : List (Clause (Fin n)) :=
  let r := fun C D : Clause (Fin n) => Encoding.clauseNumbers C ≤ Encoding.clauseNumbers D
  letI : IsTrans _ r := ⟨fun _ _ _ => le_trans⟩
  letI : Std.Total r := ⟨fun _ _ => le_total _ _⟩
  letI : Std.Antisymm r :=
    ⟨fun _ _ h h' => Encoding.clauseNumbers_injective (le_antisymm h h')⟩
  F.sort r

/-- A concrete list representation of the typed input formula. -/
def formulaList (F : CNF (Fin n)) : Formula n :=
  (orderedClauses F).map literalList

def encodeRawFormula (F : Formula n) : List Bool :=
  Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
    (F.map (List.map Encoding.literalCode))

@[simp] theorem literalList_set (C : Clause (Fin n)) :
    ExecCNF.clauseSet (literalList C) = C := by
  simp [ExecCNF.clauseSet, literalList]

@[simp] theorem literalList_length (C : Clause (Fin n)) :
    (literalList C).length = C.card := by simp [literalList]

@[simp] theorem mem_orderedClauses (F : CNF (Fin n)) (C : Clause (Fin n)) :
    C ∈ orderedClauses F ↔ C ∈ F := by simp [orderedClauses]

@[simp] theorem formulaList_set (F : CNF (Fin n)) :
    ExecCNF.formulaSet (formulaList F) = F := by
  ext C
  simp [ExecCNF.mem_formulaSet, formulaList]

@[simp] theorem formulaList_length (F : CNF (Fin n)) :
    (formulaList F).length = F.card := by simp [formulaList, orderedClauses]

end SubexponentialSAT.ExecQuantitativeSparsify

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Syntactic frontend for the variable-parameter SAT algorithm

The external input declares `n` Boolean coordinates. We first normalize the
finite CNF, then enumerate only its syntactically appearing coordinates in
increasing order. The resulting coordinate set is retained through all later
branching; this frontend is not reapplied at sparsification leaves.

All constructions inspect finite syntax. No satisfiability test, choice of a
satisfying assignment, or noncomputable enumeration is used by `prepare`.
-/

namespace SubexponentialSAT.SubexpFrontend

open SAT

section Rename

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

def renameLiteral (f : V → W) (l : Literal V) : Literal W :=
  ⟨f l.variable, l.positive⟩

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem eval_renameLiteral (f : V → W) (l : Literal V) (a : W → Bool) :
    (renameLiteral f l).eval a = l.eval (a ∘ f) := rfl

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem renameLiteral_negate (f : V → W) (l : Literal V) :
    renameLiteral f l.negate = (renameLiteral f l).negate := rfl

end Rename

end SubexponentialSAT.SubexpFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFCodeTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Exact list transport through literal codes

These equalities preserve clause order and the last-occurrence conventions.
They connect the encoded normalization programs to the typed executable CNF
operations, rather than identifying only their finite-set semantics.
-/

namespace SubexponentialSAT.ExecCNFCodeTransport

open ExecCNF

universe u v
variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

@[simp] theorem contains_map (f : α → β) (hf : Function.Injective f)
    (x : α) (C : Clause α) : contains (f x) (C.map f) = contains x C := by
  induction C with
  | nil => rfl
  | cons y ys ih => simp [contains, hf.eq_iff, ih]

@[simp] theorem subset_map (f : α → β) (hf : Function.Injective f)
    (C D : Clause α) : subset (C.map f) (D.map f) = subset C D := by
  induction C with
  | nil => rfl
  | cons x xs ih => simp [subset, contains_map f hf, ih]

@[simp] theorem equivalent_map (f : α → β) (hf : Function.Injective f)
    (C D : Clause α) : equivalent (C.map f) (D.map f) = equivalent C D := by
  simp [equivalent, subset_map f hf]

@[simp] theorem strictSubset_map (f : α → β) (hf : Function.Injective f)
    (C D : Clause α) : strictSubset (C.map f) (D.map f) = strictSubset C D := by
  simp [strictSubset, subset_map f hf]

@[simp] theorem dedupLiterals_map (f : α → β) (hf : Function.Injective f)
    (C : Clause α) : dedupLiterals (C.map f) = (dedupLiterals C).map f := by
  induction C with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, dedupLiterals, contains_map f hf]
      split <;> simp_all

@[simp] theorem dedupClauses_map (f : α → β) (hf : Function.Injective f)
    (F : Formula α) : dedupClauses (F.map (List.map f)) =
      (dedupClauses F).map (List.map f) := by
  induction F with
  | nil => rfl
  | cons C F ih =>
      simp only [List.map_cons, dedupClauses, List.any_map, Function.comp_def,
        equivalent_map f hf]
      split <;> simp_all

@[simp] theorem cleanLiterals_map (f : α → β) (hf : Function.Injective f)
    (F : Formula α) : cleanLiterals (F.map (List.map f)) =
      (cleanLiterals F).map (List.map f) := by
  simp [cleanLiterals, List.map_map, Function.comp_def, dedupLiterals_map f hf]

@[simp] theorem tautology_map (f : α → β) (hf : Function.Injective f)
    (negα : α → α) (negβ : β → β) (hn : ∀ x, f (negα x) = negβ (f x))
    (C : Clause α) : tautology negβ (C.map f) = tautology negα C := by
  simp only [tautology, List.any_map, Function.comp_def, ← hn, contains_map f hf]

end SubexponentialSAT.ExecCNFCodeTransport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackRoutines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-alphabet stack routines

This module records stack-state transformations and proves instruction traces
for concrete programs over Boolean stacks. The number of symbols in a stack is
runtime data; no growing alphabet is used.
-/

namespace SubexponentialSAT.StackRoutines

universe u

open BitProgram

def reverseStacks {S : Type u} [DecidableEq S] (src : S) (stk : Stacks S) : Stacks S :=
  Function.update stk src (stk src).reverse

theorem three_transfers_eq_reverse {S : Type u} [DecidableEq S]
    (src tmp₁ tmp₂ : S) (stk : Stacks S)
    (h₁ : src ≠ tmp₁) (h₂ : src ≠ tmp₂) (h₁₂ : tmp₁ ≠ tmp₂)
    (htmp₁ : stk tmp₁ = []) (htmp₂ : stk tmp₂ = []) :
    transferStacks tmp₂ src (transferStacks tmp₁ tmp₂ (transferStacks src tmp₁ stk)) =
      reverseStacks src stk := by
  funext j
  by_cases hs : j = src
  · subst j
    simp [transferStacks, reverseStacks, h₁, h₂, h₂.symm, h₁₂.symm,
      htmp₁, htmp₂]
  · by_cases ht₁ : j = tmp₁
    · subst j
      simp [transferStacks, reverseStacks, h₁, h₂, h₁₂, h₁.symm, h₂.symm, h₁₂.symm,
        htmp₁, htmp₂]
    · by_cases ht₂ : j = tmp₂
      · subst j
        simp [transferStacks, reverseStacks, h₁, h₂, h₂.symm, h₁₂.symm,
          htmp₁, htmp₂]
      · simp [transferStacks, reverseStacks, hs, ht₁, ht₂]

def reverseResult {r s l : ℕ} (exit : Fin l) (src : Fin s) (value present : Fin r)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) : Cfg r s l :=
  ⟨some exit, readRegs regs value present none, reverseStacks src stk⟩

end SubexponentialSAT.StackRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ParserProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control parsers for the canonical formula encoding

These programs operate on two Boolean stacks and two Boolean registers.
Stack 0 is input; stack 1 accumulates output. Register 0 holds the last data
bit and register 1 records whether the last pop succeeded. Thus register 1
is true on successful delimiter termination and false on malformed input.
All stated running times count actual `BitProgram.step` transitions.
-/

namespace SubexponentialSAT.ParserProgram

open SubexponentialSAT.BitProgram

def cfg {l : ℕ} (pc : Option (Fin l)) (value present : Bool)
    (input output : List Bool) : Cfg 2 2 l :=
  ⟨pc, pair value present, pair input output⟩

/-- Five fixed labels suffice to decode an arbitrary unary natural field. -/
abbrev natProgram : Program 2 2 5 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .branch 1 2 4
    | 2 => .branch 0 3 4
    | 3 => .push 1 0 0
    | _ => .halt

/-- Seven fixed labels read escaped frames of arbitrary length. The payload
is reversed on the destination stack; a stack-transfer routine restores order. -/
abbrev frameProgram : Program 2 2 7 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .branch 1 2 6
    | 2 => .branch 0 3 6
    | 3 => .pop 0 0 1 4
    | 4 => .branch 1 5 6
    | 5 => .push 1 0 0
    | _ => .halt

theorem frame_pop_tag (b v p : Bool) (input output : List Bool) :
    step frameProgram (cfg (some 0) v p (b :: input) output) =
      some (cfg (some 1) b true input output) := by
  simp [step, cfg, execInstr, readRegs]

theorem frame_present_tag (v : Bool) (input output : List Bool) :
    step frameProgram (cfg (some 1) v true input output) =
      some (cfg (some 2) v true input output) := by
  simp [step, cfg, execInstr]

theorem frame_true_tag (input output : List Bool) :
    step frameProgram (cfg (some 2) true true input output) =
      some (cfg (some 3) true true input output) := by
  simp [step, cfg, execInstr]

theorem frame_pop_data (b v p : Bool) (input output : List Bool) :
    step frameProgram (cfg (some 3) v p (b :: input) output) =
      some (cfg (some 4) b true input output) := by
  simp [step, cfg, execInstr, readRegs]

theorem frame_present_data (v : Bool) (input output : List Bool) :
    step frameProgram (cfg (some 4) v true input output) =
      some (cfg (some 5) v true input output) := by
  simp [step, cfg, execInstr]

theorem frame_push (b : Bool) (input output : List Bool) :
    step frameProgram (cfg (some 5) b true input output) =
      some (cfg (some 0) b true input (b :: output)) := by
  simp [step, cfg, execInstr]

theorem frame_false_tag (input output : List Bool) :
    step frameProgram (cfg (some 2) false true input output) =
      some (cfg (some 6) false true input output) := by
  simp [step, cfg, execInstr]

theorem frame_halt (v p : Bool) (input output : List Bool) :
    step frameProgram (cfg (some 6) v p input output) =
      some (cfg none v p input output) := by
  simp [step, cfg, execInstr]

theorem frame_cycle (b v p : Bool) (input output : List Bool) :
    Trace frameProgram 6 (cfg (some 0) v p (true :: b :: input) output)
      (cfg (some 0) b true input (b :: output)) :=
  .cons (frame_pop_tag true v p (b :: input) output)
    (.cons (frame_present_tag true (b :: input) output)
      (.cons (frame_true_tag (b :: input) output)
        (.cons (frame_pop_data b true true input output)
          (.cons (frame_present_data b input output)
            (.cons (frame_push b input output) (.refl _))))))

theorem frame_finish (v p : Bool) (input output : List Bool) :
    Trace frameProgram 4 (cfg (some 0) v p (false :: input) output)
      (cfg none false true input output) :=
  .cons (frame_pop_tag false v p input output)
    (.cons (frame_present_tag false input output)
      (.cons (frame_false_tag input output)
        (.cons (frame_halt false true input output) (.refl _))))

/-- Exact measured execution of the actual parser, preserving the unused suffix. -/
theorem frame_trace (bits rest output : List Bool) (v p : Bool) :
    Trace frameProgram (6 * bits.length + 4)
      (cfg (some 0) v p (Encoding.frame bits ++ rest) output)
      (cfg none false true rest (bits.reverse ++ output)) := by
  induction bits generalizing output v p with
  | nil => simpa [Encoding.frame_nil] using frame_finish v p rest output
  | cons b bits ih =>
      have h := (frame_cycle b v p (Encoding.frame bits ++ rest) output).trans
        (ih (b :: output) b true)
      have ht : 6 + (6 * bits.length + 4) = 6 * (b :: bits).length + 4 := by
        simp only [List.length_cons]
        omega
      simpa only [ht, Encoding.frame_cons, List.cons_append, List.reverse_cons,
        List.append_assoc, List.singleton_append, List.nil_append] using h

/-! ## In-place removal of one escape frame -/

/-! The compiler turns the preceding actual instruction traces into actual
primitive tape executions. Each overhead below belongs to one fixed program. -/

end SubexponentialSAT.ParserProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFRecords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control skipping of framed CNF records

The program below has three Boolean registers, one Boolean stack, and eleven
fixed labels. It consumes an escaped frame or one tagged list item without
materializing the payload. The payload may itself encode a list of literals,
a clause, or a more deeply nested record. Every bound is proved for actual
`BitProgram.step` traces, rather than assigned to a semantic list operation.
-/

namespace SubexponentialSAT.ExecCNFRecords

open SubexponentialSAT.BitProgram

/-- Entry 0 reads a tagged list item; entry 4 reads a raw escape frame. -/
abbrev skipProgram : Program 3 1 11 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .branch 1 2 10
    | 2 => .branch 0 3 9
    | 3 => .set 2 true 4
    | 4 => .pop 0 0 1 5
    | 5 => .branch 1 6 10
    | 6 => .branch 0 7 10
    | 7 => .pop 0 0 1 8
    | 8 => .branch 1 4 10
    | 9 => .set 2 false 10
    | _ => .halt

def cfg (pc : Option (Fin 11)) (value present found : Bool) (input : List Bool) :
    Cfg 3 1 11 := ⟨pc, regs value present found, fun _ => input⟩

theorem frame_pop_tag (b v p f : Bool) (input : List Bool) :
    step skipProgram (cfg (some 4) v p f (b :: input)) =
      some (cfg (some 5) b true f input) := by
  simp [step, cfg, execInstr, readRegs]

theorem frame_present_tag (v f : Bool) (input : List Bool) :
    step skipProgram (cfg (some 5) v true f input) =
      some (cfg (some 6) v true f input) := by
  simp [step, cfg, execInstr]

theorem frame_true_tag (f : Bool) (input : List Bool) :
    step skipProgram (cfg (some 6) true true f input) =
      some (cfg (some 7) true true f input) := by
  simp [step, cfg, execInstr]

theorem frame_pop_data (b v p f : Bool) (input : List Bool) :
    step skipProgram (cfg (some 7) v p f (b :: input)) =
      some (cfg (some 8) b true f input) := by
  simp [step, cfg, execInstr, readRegs]

theorem frame_present_data (v f : Bool) (input : List Bool) :
    step skipProgram (cfg (some 8) v true f input) =
      some (cfg (some 4) v true f input) := by
  simp [step, cfg, execInstr]

theorem frame_false_tag (f : Bool) (input : List Bool) :
    step skipProgram (cfg (some 6) false true f input) =
      some (cfg (some 10) false true f input) := by
  simp [step, cfg, execInstr]

theorem skip_halt (v p f : Bool) (input : List Bool) :
    step skipProgram (cfg (some 10) v p f input) =
      some (cfg none v p f input) := by
  simp [step, cfg, execInstr]

theorem frame_cycle (b v p f : Bool) (input : List Bool) :
    Trace skipProgram 5 (cfg (some 4) v p f (true :: b :: input))
      (cfg (some 4) b true f input) :=
  .cons (frame_pop_tag true v p f (b :: input))
    (.cons (frame_present_tag true f (b :: input))
      (.cons (frame_true_tag f (b :: input))
        (.cons (frame_pop_data b true true f input)
          (.cons (frame_present_data b f input) (.refl _)))))

theorem frame_finish (v p f : Bool) (input : List Bool) :
    Trace skipProgram 4 (cfg (some 4) v p f (false :: input))
      (cfg none false true f input) :=
  .cons (frame_pop_tag false v p f input)
    (.cons (frame_present_tag false f input)
      (.cons (frame_false_tag f input) (.cons (skip_halt false true f input) (.refl _))))

/-- Raw-frame entry consumes exactly one frame and preserves the entire suffix. -/
theorem frame_trace (bits rest : List Bool) (v p f : Bool) :
    Trace skipProgram (5 * bits.length + 4)
      (cfg (some 4) v p f (Encoding.frame bits ++ rest))
      (cfg none false true f rest) := by
  induction bits generalizing v p with
  | nil => simpa [Encoding.frame_nil] using frame_finish v p f rest
  | cons b bits ih =>
      have h := (frame_cycle b v p f (Encoding.frame bits ++ rest)).trans (ih b true)
      have ht : 5 + (5 * bits.length + 4) = 5 * (b :: bits).length + 4 := by
        simp only [List.length_cons]
        omega
      simpa only [ht, Encoding.frame_cons, List.cons_append] using h

end SubexponentialSAT.ExecCNFRecords

namespace SubexponentialSAT.ExecCNFRecords
open SubexponentialSAT.BitProgram

def copyCfg {l : ℕ} (pc : Option (Fin l)) (v p : Bool)
    (source destination scratch : List Bool) : Cfg 2 3 l :=
  ⟨pc, ParserProgram.pair v p, ports source destination scratch⟩

/-- Capture the raw bits of one frame or tagged record in reverse on scratch.
Destination port 1 is untouched. -/
abbrev captureProgram : Program 2 3 12 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .branch 1 2 11
    | 2 => .branch 0 3 11
    | 3 => .push 2 0 4
    | 4 => .pop 0 0 1 5
    | 5 => .branch 1 6 11
    | 6 => .push 2 0 7
    | 7 => .branch 0 8 11
    | 8 => .pop 0 0 1 9
    | 9 => .branch 1 10 11
    | 10 => .push 2 0 4
    | _ => .halt

theorem capture_pop_tag (b v p : Bool) (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 4) v p (b :: input) output scratch) =
      some (copyCfg (some 5) b true input output scratch) := by
  simp [step, copyCfg, execInstr, readRegs]

theorem capture_present_tag (v : Bool) (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 5) v true input output scratch) =
      some (copyCfg (some 6) v true input output scratch) := by
  simp [step, copyCfg, execInstr]

theorem capture_push_tag (v : Bool) (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 6) v true input output scratch) =
      some (copyCfg (some 7) v true input output (v :: scratch)) := by
  simp [step, copyCfg, execInstr]

theorem capture_true_tag (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 7) true true input output scratch) =
      some (copyCfg (some 8) true true input output scratch) := by
  simp [step, copyCfg, execInstr]

theorem capture_pop_data (b v p : Bool) (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 8) v p (b :: input) output scratch) =
      some (copyCfg (some 9) b true input output scratch) := by
  simp [step, copyCfg, execInstr, readRegs]

theorem capture_present_data (v : Bool) (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 9) v true input output scratch) =
      some (copyCfg (some 10) v true input output scratch) := by
  simp [step, copyCfg, execInstr]

theorem capture_push_data (b : Bool) (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 10) b true input output scratch) =
      some (copyCfg (some 4) b true input output (b :: scratch)) := by
  simp [step, copyCfg, execInstr]

theorem capture_false_tag (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 7) false true input output scratch) =
      some (copyCfg (some 11) false true input output scratch) := by
  simp [step, copyCfg, execInstr]

theorem capture_halt (v p : Bool) (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 11) v p input output scratch) =
      some (copyCfg none v p input output scratch) := by
  simp [step, copyCfg, execInstr]

theorem capture_cycle (b v p : Bool) (input output scratch : List Bool) :
    Trace captureProgram 7 (copyCfg (some 4) v p (true :: b :: input) output scratch)
      (copyCfg (some 4) b true input output (b :: true :: scratch)) :=
  .cons (capture_pop_tag true v p (b :: input) output scratch)
    (.cons (capture_present_tag true (b :: input) output scratch)
      (.cons (capture_push_tag true (b :: input) output scratch)
        (.cons (capture_true_tag (b :: input) output (true :: scratch))
          (.cons (capture_pop_data b true true input output (true :: scratch))
            (.cons (capture_present_data b input output (true :: scratch))
              (.cons (capture_push_data b input output (true :: scratch)) (.refl _)))))))

theorem capture_finish (v p : Bool) (input output scratch : List Bool) :
    Trace captureProgram 5 (copyCfg (some 4) v p (false :: input) output scratch)
      (copyCfg none false true input output (false :: scratch)) :=
  .cons (capture_pop_tag false v p input output scratch)
    (.cons (capture_present_tag false input output scratch)
      (.cons (capture_push_tag false input output scratch)
        (.cons (capture_false_tag input output (false :: scratch))
          (.cons (capture_halt false true input output (false :: scratch)) (.refl _)))))

theorem capture_frame_trace (bits rest output scratch : List Bool) (v p : Bool) :
    Trace captureProgram (7 * bits.length + 5)
      (copyCfg (some 4) v p (Encoding.frame bits ++ rest) output scratch)
      (copyCfg none false true rest output ((Encoding.frame bits).reverse ++ scratch)) := by
  induction bits generalizing v p scratch with
  | nil => simpa [Encoding.frame_nil] using capture_finish v p rest output scratch
  | cons b bits ih =>
      have h := (capture_cycle b v p (Encoding.frame bits ++ rest) output scratch).trans
        (ih (b :: true :: scratch) b true)
      have ht : 7 + (7 * bits.length + 5) = 7 * (b :: bits).length + 5 := by
        simp only [List.length_cons]
        omega
      simpa only [ht, Encoding.frame_cons, List.cons_append, List.reverse_cons,
        List.append_assoc, List.singleton_append, List.nil_append] using h

/-- Restore the captured word to forward order on the destination port. -/
abbrev restoreCapturedProgram : Program 2 3 4 := StackRoutines.transferProgram 2 1 0 1

/-- Sixteen fixed labels copy a whole raw record while consuming only that
record at the source. Its source suffix and old destination are preserved. -/
abbrev copyProgram : Program 2 3 16 := ProgramLinking.link captureProgram restoreCapturedProgram

end SubexponentialSAT.ExecCNFRecords

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseCost39Lift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms
namespace SubexponentialSAT.ExecClauseCost
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev membershipEqProgram : Program 7 5 10 :=
  SubexponentialSAT.ProgramLinking.liftProgram bitEqualityProgram membershipEqReg membershipEqStack

end SubexponentialSAT.ExecClauseCost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Shared record representation for executable programs

A scalar is stored as a Boolean payload (little-endian bits for natural
numbers; the scalar module specifies any fixed padding). A record list uses
the existing `Encoding.encodeList id`: false terminates the list; true starts
an escaped frame. Matrices and other fixed-depth schemas nest this same
representation. These are executable decoders and exact size identities,
not assertions that a machine has run them.
-/

namespace SubexponentialSAT.ProgramEncoding

abbrev encodeRecords (records : Records) : List Bool :=
  Encoding.encodeList id records

/-- Explicitly bounded recursive decoder. Every record consumes a leading
tag, so input length plus one is sufficient fuel. -/
def readRecordsAux : ℕ → List Bool → Option (Records × List Bool)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: rest => some ([], rest)
  | fuel + 1, true :: rest => do
      let (payload, afterPayload) ← Encoding.readFrame rest
      let (records, tail) ← readRecordsAux fuel afterPayload
      pure (payload :: records, tail)

def readRecords (input : List Bool) : Option (Records × List Bool) :=
  readRecordsAux (input.length + 1) input

theorem readRecordsAux_encodeList_append (records : Records) (rest : List Bool)
    (fuel : ℕ) (hfuel : records.length < fuel) :
    readRecordsAux fuel (encodeRecords records ++ rest) = some (records, rest) := by
  induction records generalizing fuel with
  | nil =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel => rfl
  | cons payload records ih =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
          have htail : records.length < fuel := by simp only [List.length_cons] at hfuel; omega
          simp only [encodeRecords, Encoding.encodeList, List.cons_append,
            List.append_assoc, readRecordsAux, Encoding.readFrame_frame_append, id_eq]
          change (readRecordsAux fuel (encodeRecords records ++ rest)).bind
            (fun result => some (payload :: result.1, result.2)) =
              some (payload :: records, rest)
          rw [ih fuel htail]
          rfl

theorem encodeRecords_length (records : Records) :
    (encodeRecords records).length =
      2 * (records.map List.length).sum + 2 * records.length + 1 := by
  induction records with
  | nil => rfl
  | cons payload records ih =>
      change (Encoding.encodeList id (payload :: records)).length = _
      rw [Encoding.length_encodeList_cons]
      change 2 * payload.length + 2 + (encodeRecords records).length = _
      rw [ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

theorem readRecords_encodeList_append (records : Records) (rest : List Bool) :
    readRecords (encodeRecords records ++ rest) = some (records, rest) := by
  apply readRecordsAux_encodeList_append
  rw [List.length_append, encodeRecords_length]
  omega

@[simp] theorem readRecords_encodeRecords (records : Records) :
    readRecords (encodeRecords records) = some (records, []) := by
  simpa using readRecords_encodeList_append records []

end SubexponentialSAT.ProgramEncoding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_RecordPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A reusable actual iterator over the project's framed-record representation.
The callback is a fixed structured program, whose executions are measured in the
same semantics as the parser and iterator. It is never an atomic semantic oracle.
-/

namespace SubexponentialSAT.RecordPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def state {r s : ℕ} (p : Ports r s) (base : State r s)
    (tagValue presentValue foundValue : Bool) (sourceWord payloadWord : List Bool) :
    State r s :=
  ⟨Function.update (Function.update (Function.update base.regs p.tag tagValue)
      p.present presentValue) p.found foundValue,
    Function.update (Function.update base.stacks p.source sourceWord) p.payload payloadWord⟩

@[simp] theorem state_tag {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f : Bool) (src out : List Bool) : (state p base v pr f src out).regs p.tag = v := by
  simp [state, p.tag_ne_present, Ne.symm p.found_ne_tag]

@[simp] theorem state_present {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f : Bool) (src out : List Bool) : (state p base v pr f src out).regs p.present = pr := by
  simp [state, Ne.symm p.found_ne_present]

@[simp] theorem state_found {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f : Bool) (src out : List Bool) : (state p base v pr f src out).regs p.found = f := by
  simp [state]

@[simp] theorem state_source {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f : Bool) (src out : List Bool) : (state p base v pr f src out).stacks p.source = src := by
  simp [state, p.source_ne_payload]

@[simp] theorem state_payload {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f : Bool) (src out : List Bool) : (state p base v pr f src out).stacks p.payload = out := by
  simp [state]

theorem state_eq_self {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f : Bool) (src out : List Bool)
    (ht : base.regs p.tag = v) (hp : base.regs p.present = pr)
    (hf : base.regs p.found = f) (hs : base.stacks p.source = src)
    (ho : base.stacks p.payload = out) : state p base v pr f src out = base := by
  cases base with
  | mk regs stk =>
      simp only at ht hp hf hs ho
      simp only [state]
      congr 1
      · funext i
        by_cases hit : i = p.tag <;> by_cases hip : i = p.present <;>
          by_cases hif : i = p.found <;> subst_vars <;>
          simp_all []
      · funext i
        by_cases his : i = p.source <;> by_cases hio : i = p.payload <;>
          subst_vars <;> simp_all []

@[simp] theorem state_state {r s : ℕ} (p : Ports r s) (base : State r s)
    (v pr f v' pr' f' : Bool) (src out src' out' : List Bool) :
    state p (state p base v pr f src out) v' pr' f' src' out' =
      state p base v' pr' f' src' out' := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases hit : i = p.tag <;> by_cases hip : i = p.present <;>
      by_cases hif : i = p.found <;> simp [state, Function.update_apply, hit, hip, hif]
  · funext i
    by_cases his : i = p.source <;> by_cases hio : i = p.payload <;>
      simp [state, Function.update_apply, his, hio]

def registerMap {r s : ℕ} (p : Ports r s) (i : Fin 2) : Fin r :=
  if i = 0 then p.tag else p.present

def stackMap {r s : ℕ} (p : Ports r s) (i : Fin 2) : Fin s :=
  if i = 0 then p.source else p.payload

theorem registerMap_injective {r s : ℕ} (p : Ports r s) : Function.Injective (registerMap p) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [registerMap, p.tag_ne_present, Ne.symm p.tag_ne_present]

theorem stackMap_injective {r s : ℕ} (p : Ports r s) : Function.Injective (stackMap p) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [stackMap, p.source_ne_payload, Ne.symm p.source_ne_payload]

abbrev reader {r s : ℕ} (p : Ports r s) : Cmd r s :=
  .call (ProgramLinking.liftProgram ParserProgram.frameProgram (registerMap p) (stackMap p))

abbrev atom {r s : ℕ} (a : StructuredProgram.Atom r s) : Cmd r s := .base (.atom a)

abbrev body {r s : ℕ} (p : Ports r s) (callback : Cmd r s) : Cmd r s :=
  .seq (reader p) (.seq callback
    (.ite p.found (atom (.set p.tag false)) (atom (.pop p.source p.tag p.present))))

abbrev loop {r s : ℕ} (p : Ports r s) (callback : Cmd r s) : Cmd r s :=
  .while p.tag (body p callback)

abbrev iterate {r s : ℕ} (p : Ports r s) (callback : Cmd r s) : Cmd r s :=
  .seq (atom (.set p.found false))
    (.seq (atom (.pop p.source p.tag p.present)) (loop p callback))

def unread (test : List Bool → Bool) : List (List Bool) → List Bool → List Bool
  | [], suffix => suffix
  | bits :: rest, suffix =>
      if test bits then Encoding.encodeList id rest ++ suffix else unread test rest suffix

def parserState (v pr : Bool) (src out : List Bool) : State 2 2 :=
  ⟨ParserProgram.pair v pr, ParserProgram.pair src out⟩

/-- State just after the outer list marker has been read. -/
def afterTag {r s : ℕ} (p : Ports r s) (base : State r s)
    (records : List (List Bool)) (suffix : List Bool) : State r s :=
  match records with
  | [] => state p base false true false suffix []
  | bits :: rest => state p base true true false
      (Encoding.frame bits ++ (Encoding.encodeList id rest ++ suffix)) []

end SubexponentialSAT.RecordPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFMembership
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

abbrev Data := State 7 5

/-- The query remains on port 2; a forward-order copy is made on port 3. -/
abbrev copyQueryProgram : Program 7 5 8 := StackRoutines.copyProgram 2 3 4 0 1

def copied (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks 2 3 d.stacks⟩

abbrev copyQuery : Cmd 7 5 := .call copyQueryProgram

def cleared (port : Fin 5) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks port d.stacks⟩

@[simp] theorem copied_stack_zero (d : Data) : (copied d).stacks 0 = d.stacks 0 := by
  simp [copied, StackRoutines.copyStacks]
@[simp] theorem copied_stack_one (d : Data) : (copied d).stacks 1 = d.stacks 1 := by
  simp [copied, StackRoutines.copyStacks]
@[simp] theorem copied_stack_two (d : Data) : (copied d).stacks 2 = d.stacks 2 := by
  simp [copied, StackRoutines.copyStacks]
@[simp] theorem copied_stack_three (d : Data) :
    (copied d).stacks 3 = d.stacks 2 ++ d.stacks 3 := by
  simp [copied, StackRoutines.copyStacks]
@[simp] theorem copied_stack_four (d : Data) : (copied d).stacks 4 = d.stacks 4 := by
  simp [copied, StackRoutines.copyStacks]
@[simp] theorem copied_reg_four (d : Data) : (copied d).regs 4 = d.regs 4 := by
  simp [copied, readRegs]
@[simp] theorem copied_reg_five (d : Data) : (copied d).regs 5 = d.regs 5 := by
  simp [copied, readRegs]
@[simp] theorem copied_reg_six (d : Data) : (copied d).regs 6 = d.regs 6 := by
  simp [copied, readRegs]

@[simp] theorem cleared_stack_self (port : Fin 5) (d : Data) :
    (cleared port d).stacks port = [] := by simp [cleared, StackRoutines.clearStacks]

@[simp] theorem cleared_reg_four (port : Fin 5) (d : Data) :
    (cleared port d).regs 4 = d.regs 4 := by simp [cleared, readRegs]
@[simp] theorem cleared_reg_five (port : Fin 5) (d : Data) :
    (cleared port d).regs 5 = d.regs 5 := by simp [cleared, readRegs]
@[simp] theorem cleared_reg_six (port : Fin 5) (d : Data) :
    (cleared port d).regs 6 = d.regs 6 := by simp [cleared, readRegs]


/-- The runtime query is on stack 2; these ports are fixed for every query. -/
abbrev ports : RecordPrograms.Ports 7 5 where
  tag := 5
  present := 6
  found := 4
  source := 0
  payload := 1
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def invariant (query : List Bool) (d : Data) : Prop :=
  d.stacks 2 = query.reverse ∧ d.stacks 3 = [] ∧ d.stacks 4 = []

/-- Coarse polynomial bound for the iterator's complete per-record budget. -/
theorem budget_le (query : List Bool) (records : List (List Bool)) :
    3 + RecordPrograms.budget (perRecordCost query) records ≤
      (20 * query.length + 30) * (Encoding.encodeList id records).length := by
  induction records with
  | nil => simp [RecordPrograms.budget, Encoding.encodeList]
  | cons bits rest ih =>
    have hstep : 6 * bits.length + perRecordCost query bits + 7 ≤
        (20 * query.length + 30) * (2 * bits.length + 2) := by
      simp only [perRecordCost, Nat.mul_add, Nat.add_mul, Nat.mul_one]
      omega
    simp only [RecordPrograms.budget, Encoding.length_encodeList_cons, id_eq]
    calc
      3 + (6 * bits.length + perRecordCost query bits + 7 +
          RecordPrograms.budget (perRecordCost query) rest)
          = (6 * bits.length + perRecordCost query bits + 7) +
              (3 + RecordPrograms.budget (perRecordCost query) rest) := by omega
      _ ≤ (20 * query.length + 30) * (2 * bits.length + 2) +
          (20 * query.length + 30) * (Encoding.encodeList id rest).length :=
        Nat.add_le_add hstep ih
      _ = (20 * query.length + 30) *
          (2 * bits.length + 2 + (Encoding.encodeList id rest).length) := by
        simp [Nat.mul_add, Nat.add_assoc]


theorem encodeList_map_encodeNat (C : List ℕ) :
    Encoding.encodeList id (C.map Encoding.encodeNat) = Encoding.encodeList Encoding.encodeNat C := by
  induction C with
  | nil => rfl
  | cons a C ih => simp [Encoding.encodeList, ih]

end SubexponentialSAT.ExecCNFMembership

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFSubset
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

abbrev Data := State 10 8

abbrev copyTargetProgram : Program 10 8 8 := StackRoutines.copyProgram 2 3 7 0 1

abbrev copied (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks 2 3 d.stacks⟩

abbrev copyTarget : Cmd 10 8 := .call copyTargetProgram

abbrev cleared (port : Fin 8) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks port d.stacks⟩

theorem unread_length_le (test : List Bool → Bool) (records : List (List Bool)) :
    (RecordPrograms.unread test records []).length ≤ (Encoding.encodeList id records).length := by
  induction records with
  | nil => simp [RecordPrograms.unread, Encoding.encodeList]
  | cons x xs ih =>
    cases h : test x <;>
      simp [RecordPrograms.unread, h, Encoding.length_encodeList_cons] ; omega

/-- Remember that the current source literal is absent from the target. -/
abbrev mark (d : Data) : Data :=
  ⟨Function.update d.regs 9 (!d.regs 4), d.stacks⟩

def invariant (records : List (List Bool)) (d : Data) : Prop :=
  d.stacks 2 = Encoding.encodeList id records ∧ d.stacks 3 = [] ∧
    d.stacks 4 = [] ∧ d.stacks 5 = [] ∧ d.stacks 6 = [] ∧ d.stacks 7 = []

def perRecordCost (records : List (List Bool)) (bits : List Bool) : ℕ :=
  50 * (bits.length + 1) * ((Encoding.encodeList id records).length + 1)

/-- The outer iterator scans the source clause, stopping at its first literal
that the concrete membership program cannot find in the preserved target. -/
def ports : RecordPrograms.Ports 10 8 where
  tag := 7
  present := 8
  found := 9
  source := 0
  payload := 1
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

/-- Invert the missing-literal flag and expose the answer as an output bit. -/
abbrev finish : Cmd 10 8 :=
  .seq (RecordPrograms.atom (.bnot 9 9)) (RecordPrograms.atom (.push 1 9))

end SubexponentialSAT.ExecCNFSubset

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFTupleOdometer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control increment of framed binary tuples

Tuple components are little-endian Boolean words carried by
`Encoding.encodeList id`. The finite table below skips framing bits and
increments only payload bits, with carry continuing into the next component.
Neither the number of components nor their widths enters the control table.
-/

namespace SubexponentialSAT.ExecCNFTupleOdometer

open SubexponentialSAT.BitProgram SubexponentialSAT.CounterPrograms

/-- Three registers hold the scanned bit, presence, and final overflow flag. -/
abbrev program : Program 3 2 18 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code q := match q.val with
    | 0 => .set 2 true 1
    | 1 => .pop 0 0 1 2
    | 2 => .branch 0 3 13
    | 3 => .push 1 0 4
    | 4 => .pop 0 0 1 5
    | 5 => .branch 0 6 12
    | 6 => .push 1 0 7
    | 7 => .pop 0 0 1 8
    | 8 => .bnot 0 0 9
    | 9 => .push 1 0 10
    | 10 => .branch 0 11 4
    | 11 => .set 2 false 14
    | 12 => .push 1 0 1
    | 13 => .push 1 0 14
    | 14 => .pop 1 0 1 15
    | 15 => .branch 1 16 17
    | 16 => .push 0 0 14
    | _ => .halt

theorem value_lt_power_length (word : List Bool) : value word < 2 ^ word.length := by
  induction word with
  | nil => simp
  | cons b bs ih =>
    cases b <;> simp [value, pow_succ] at * <;> omega

end SubexponentialSAT.ExecCNFTupleOdometer

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPostfixControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete postfix instruction dispatch and literal push

The fixed prefix tags are push `0`, add `10`, and multiply `11`.
A push tag is followed by an `Encoding.frame` coefficient payload. End of
the code stack ends the instruction stream. The base dispatcher exposes
explicit service exits. The linked program implements literal push through
the actual frame parser and a Boolean-stack encoding loop; scalar arithmetic
remains at explicit service boundaries.

Registers: 0 last bit, 1 successful-pop flag, 2 binary-operation flag.
Stacks: 0 serialized code, 1 unary operand depth, 2 framed operand data.
The operand data stack is preserved throughout dispatch. On a successful
dispatch the depth stack has already been adjusted for the pending service.
The linked literal service uses stack 3 as initially empty scratch and returns
to dispatch with that scratch empty and the framed operand list updated.
-/

namespace SubexponentialSAT.SubexpPostfixControl

open BitProgram

/-- Twenty labels, three one-bit registers, and three Boolean stacks. -/
abbrev program : Program 3 3 20 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .branch 1 2 doneExit
    | 2 => .branch 0 5 3
    | 3 => .set 0 true 4
    | 4 => .push 1 0 pushService
    | 5 => .pop 0 0 1 6
    | 6 => .branch 1 7 errorExit
    | 7 => .copy 2 0 8
    | 8 => .pop 1 0 1 9
    | 9 => .branch 1 10 errorExit
    | 10 => .pop 1 0 1 11
    | 11 => .branch 1 12 errorExit
    | 12 => .set 0 true 13
    | 13 => .push 1 0 14
    | 14 => .branch 2 mulService addService
    | _ => .halt

@[simp] theorem pushService_halt : program.code pushService = .halt := rfl
@[simp] theorem addService_halt : program.code addService = .halt := rfl
@[simp] theorem mulService_halt : program.code mulService = .halt := rfl
@[simp] theorem doneExit_halt : program.code doneExit = .halt := rfl
@[simp] theorem errorExit_halt : program.code errorExit = .halt := rfl

/-! ## Serialization of the existing postfix instruction type -/

/-! ## Literal-push service with the framed-list operand ABI -/

@[simp] theorem quadruple_zero {α : Type*} (a b c d : α) : quadruple a b c d 0 = a := rfl
@[simp] theorem quadruple_one {α : Type*} (a b c d : α) : quadruple a b c d 1 = b := rfl
@[simp] theorem quadruple_two {α : Type*} (a b c d : α) : quadruple a b c d 2 = c := rfl
@[simp] theorem quadruple_three {α : Type*} (a b c d : α) : quadruple a b c d 3 = d := rfl

/-- The first seven labels are the actual relocated frame parser. The remaining
labels rebuild the escaped payload from its reverse and add the list cons tag. -/
def literalService : Program 3 4 17 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code := Fin.addCases (motive := fun _ : Fin (7 + 10) => Instr 3 4 17)
    (fun pc : Fin 7 => ProgramLinking.relocateInstr parserRegister parserStack parserLabel
      (some 7) (ParserProgram.frameProgram.code pc))
    (fun pc : Fin 10 => match pc.val with
      | 0 => .set 0 false 8
      | 1 => .push 2 0 9
      | 2 => .pop 3 0 1 10
      | 3 => .branch 1 11 14
      | 4 => .push 2 0 12
      | 5 => .set 0 true 13
      | 6 => .push 2 0 9
      | 7 => .set 0 true 15
      | 8 => .push 2 0 16
      | _ => .halt)

@[simp] theorem literalService_code7 : literalService.code 7 = .set 0 false 8 := rfl
@[simp] theorem literalService_code8 : literalService.code 8 = .push 2 0 9 := rfl
@[simp] theorem literalService_code9 : literalService.code 9 = .pop 3 0 1 10 := rfl
@[simp] theorem literalService_code10 : literalService.code 10 = .branch 1 11 14 := rfl
@[simp] theorem literalService_code11 : literalService.code 11 = .push 2 0 12 := rfl
@[simp] theorem literalService_code12 : literalService.code 12 = .set 0 true 13 := rfl
@[simp] theorem literalService_code13 : literalService.code 13 = .push 2 0 9 := rfl
@[simp] theorem literalService_code14 : literalService.code 14 = .set 0 true 15 := rfl
@[simp] theorem literalService_code15 : literalService.code 15 = .push 2 0 16 := rfl
@[simp] theorem literalService_code16 : literalService.code 16 = .halt := rfl

/-- Concrete linkage: only push calls the literal service, whose halt is replaced
by a return to dispatch. Add/multiply remain explicit service boundaries. -/
def pushLoopProgram : Program 3 4 37 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code := Fin.addCases (motive := fun _ : Fin (20 + 17) => Instr 3 4 37)
    (fun pc : Fin 20 =>
      if pc = pushService then .goto (literalLabel 0)
      else ProgramLinking.relocateInstr id controlStack controlLabel none (program.code pc))
    (fun pc : Fin 17 =>
      ProgramLinking.relocateInstr id id literalLabel (some 0) (literalService.code pc))

@[simp] theorem pushLoop_code0 : pushLoopProgram.code 0 = .pop 0 0 1 1 := rfl
@[simp] theorem pushLoop_code1 : pushLoopProgram.code 1 = .branch 1 2 18 := rfl
@[simp] theorem pushLoop_code2 : pushLoopProgram.code 2 = .branch 0 5 3 := rfl
@[simp] theorem pushLoop_code3 : pushLoopProgram.code 3 = .set 0 true 4 := rfl
@[simp] theorem pushLoop_code4 : pushLoopProgram.code 4 = .push 1 0 15 := rfl
@[simp] theorem pushLoop_code15 : pushLoopProgram.code 15 = .goto 20 := rfl

end SubexponentialSAT.SubexpPostfixControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete syntax routines for CNF normalization

This module begins the machine implementation of normalization with the
complement-query operation used in tautology testing. `negateProgram` is one
fixed finite instruction table. It scans a unary literal code in pairs and
emits the code with its polarity flipped. Unbounded data stays on the stacks.

The theorems count actual `BitProgram.step` transitions. Full formula
deduplication, tautology filtering, and absorption are separate obligations;
this routine is not presented as the completed normalization algorithm.
-/

namespace SubexponentialSAT.SubexpNormalizeProgram

open BitProgram
open ParserProgram (cfg)

/-! ## Actual record-filter output step

The predicate's result occupies register 2. The following fixed callback
consumes the reversed record on stack 3, prepends its framed representation to
stack 2 exactly when selected, and resets the iterator's flags. Its two other
stacks are preserved. Computing the selection bit is a separate operation.
-/

/-- Enter the proved frame writer directly at its fixed encoding entry. -/
abbrev emitRecordProgram : Program 3 4 17 :=
  { SubexpPostfixControl.literalService with inputStack := 3, entry := 7 }

abbrev resetFilterFlags : StructuredProgram.Cmd 3 4 :=
  .seq (.atom (.set 0 false)) (.seq (.atom (.set 1 true)) (.atom (.set 2 false)))

/-! ## A complete record-order reversal pass

Prepending accepted records reverses their order. This second, unconditional
pass restores the order required by `List.filter` and the executable
sparsifier. It reverses the records, never the bits within a record.
-/

def filterPorts : RecordPrograms.Ports 3 4 where
  tag := 0
  present := 1
  found := 2
  source := 0
  payload := 3
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

/-! ## Exact-order contract for the full normalization filter

The selection callback in the following theorem is a fixed structured
program with measured executions. No procedure is manufactured from the
mathematical predicate. Once that callback is supplied, the theorem tracks
the output of the actual generic record iterator, including record order.
-/

end SubexponentialSAT.SubexpNormalizeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseFilterReverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Shared actual record reversal for the clause-filter storage layout. -/

namespace SubexponentialSAT.ExecClauseFilterReverse

open BitProgram StructuredCalls

abbrev Data := State 15 16

def state (regs : Regs) (source output payload : List Bool) : Data :=
  ⟨regs, ![[], [], [], [], [], [], [], [], [], [], [], [], [], source, output, payload]⟩

end SubexponentialSAT.ExecClauseFilterReverse

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseRelationsProgram
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

abbrev Data := State 12 10

def restrict (d : Data) : State 10 8 := ⟨d.regs ∘ regPort, d.stacks ∘ stackPort⟩

def clean (d : Data) : Prop := ∀ i : Fin 8, d.stacks (stackPort i) = []

def copied (src dst : Fin 10) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

abbrev copy (src dst : Fin 10) : Cmd 12 10 :=
  .call (StackRoutines.copyProgram src dst 7 0 1)

def cleared (port : Fin 10) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks port d.stacks⟩

def compareBound (source target : List (List Bool)) : ℕ :=
  80 * ((Encoding.encodeList id source).length + 1) *
    ((Encoding.encodeList id target).length + 1)

def saved (d : Data) : Data :=
  ⟨Function.update d.regs 11 (d.regs 9), d.stacks⟩

abbrev save : Cmd 12 10 := RecordPrograms.atom (.copy 11 9)

abbrev combine : Cmd 12 10 :=
  .seq (RecordPrograms.atom (.band 10 11 9))
    (.seq (RecordPrograms.atom (.bnot 9 9)) (RecordPrograms.atom (.band 11 11 9)))

def bound (source target : List (List Bool)) : ℕ :=
  160 * ((Encoding.encodeList id source).length + 1) *
    ((Encoding.encodeList id target).length + 1) + 5

end SubexponentialSAT.ExecClauseRelationsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseRelationScan
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

abbrev Data := State 15 12

def encodeClause (C : Clause) : List Bool := Encoding.encodeList id C

abbrev transferProgram : Program 15 12 4 := StackRoutines.transferProgram 11 8 0 1

abbrev transfer : Cmd 15 12 := .call transferProgram

def perClauseCost (Q : Clause) (bits : List Bool) : ℕ :=
  180 * (bits.length + 1) * ((encodeClause Q).length + 1)

def ports : RecordPrograms.Ports 15 12 where
  tag := 12
  present := 13
  found := 14
  source := 10
  payload := 11
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def encodeFormula (F : Formula) : List Bool := Encoding.encodeList encodeClause F

def bound (F : Formula) (Q : Clause) : ℕ :=
  400 * ((encodeClause Q).length + 1) * ((encodeFormula F).length + 1) + 1

end SubexponentialSAT.ExecClauseRelationScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseRelationScanPreserve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A preserving wrapper for repeated clause-vs-formula scans. A real copy of
the full formula is scanned, and its residual copy is explicitly cleared. -/
namespace SubexponentialSAT.ExecClauseRelationScan.Preserving
open BitProgram StructuredCalls

abbrev Data := State 15 13

abbrev copyFormula : Cmd 15 13 := .call (StackRoutines.copyProgram 12 10 8 0 1)

def bound (F : Formula) (Q : Clause) : ℕ :=
  512 * ((encodeClause Q).length + 1) * ((encodeFormula F).length + 1)

end SubexponentialSAT.ExecClauseRelationScan.Preserving

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseFiltersProgram
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

abbrev transfer (source target : Fin 16) : Cmd 15 16 :=
  .call (StackRoutines.transferProgram source target 0 1)

def reset (regs : Regs) : Regs := readRegs regs 0 1 none

def callbackBound (F : Formula) (Q : Clause) : ℕ :=
  ExecClauseRelationScan.Preserving.bound F Q + 11 * (encodeClause Q).length + 25

def ports : RecordPrograms.Ports 15 16 where
  tag := 0
  present := 1
  found := 14
  source := 13
  payload := 15
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def decodeClause (bits : List Bool) : Option Clause := do
  let (fields, rest) ← ProgramEncoding.readRecords bits
  if rest.isEmpty then some fields else none

@[simp] theorem decodeClause_encodeClause (Q : Clause) :
    decodeClause (encodeClause Q) = some Q := by
  change (do
    let (fields, rest) ← ProgramEncoding.readRecords (ProgramEncoding.encodeRecords Q)
    if rest.isEmpty then some fields else none) = some Q
  simp

def keep (mode : Mode) (F : Formula) (bits : List Bool) : Bool :=
  match decodeClause bits with
  | some Q => !(F.any (fun C => test mode C Q))
  | none => false

@[simp] theorem keep_encodeClause (mode : Mode) (F : Formula) (Q : Clause) :
    keep mode F (encodeClause Q) = !(F.any (fun C => test mode C Q)) := by
  simp [keep]

def ClausePayload (bits : List Bool) : Prop := ∃ Q : Clause, bits = encodeClause Q

def perClauseCost (F : Formula) (bits : List Bool) : ℕ :=
  600 * ((encodeFormula F).length + 1) * (bits.length + 1)

def formulaRecords (F : Formula) : List (List Bool) := F.map encodeClause

def filtered (mode : Mode) (master F : Formula) : Formula :=
  F.filter (fun Q => !(master.any (fun C => test mode C Q)))

abbrev copyMaster : Cmd 15 16 := .call (StackRoutines.copyProgram 13 12 9 0 1)

abbrev pushFalse (stack : Fin 16) : Cmd 15 16 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.push stack 0))

end SubexponentialSAT.ExecClauseFiltersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecLiteralDedupProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual stable literal deduplication

The fixed program tests each record against the remaining records, retains its
last occurrence, and restores record order. All membership, copy, emission,
and reversal calls are concrete finite programs with measured executions.
-/

namespace SubexponentialSAT.ExecLiteralDedupProgram

open BitProgram StructuredCalls

abbrev Data := State 10 8

abbrev ports : RecordPrograms.Ports 10 8 where
  tag := 7
  present := 8
  found := 9
  source := 0
  payload := 1
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def Clean (d : Data) : Prop :=
  d.stacks 3 = [] ∧ d.stacks 4 = [] ∧ d.stacks 5 = [] ∧
    d.stacks 6 = [] ∧ d.stacks 7 = []

abbrev copySuffixProgram : Program 10 8 8 := StackRoutines.copyProgram 0 3 7 0 1
abbrev copySuffix : Cmd 10 8 := .call copySuffixProgram
def copied (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks 0 3 d.stacks⟩

abbrev selectMissing : Cmd 10 8 := .base (.atom (.bnot 9 4))
def selectedState (d : Data) : Data := ⟨Function.update d.regs 9 (!(d.regs 4)), d.stacks⟩

def callbackBound (bits : List Bool) (rest : List (List Bool)) : ℕ :=
  (20 * bits.length + 39) * (Encoding.encodeList id rest).length + 5 * bits.length + 28

@[simp] theorem clean_state (base : Data) (v pr f : Bool) (src payload : List Bool) :
    Clean (RecordPrograms.state ports base v pr f src payload) ↔ Clean base := by
  simp [Clean, RecordPrograms.state ]

@[simp] theorem state_output (base : Data) (v pr f : Bool) (src payload : List Bool) :
    (RecordPrograms.state ports base v pr f src payload).stacks 2 = base.stacks 2 := by
  simp [RecordPrograms.state ]

/-- The suffix-dependent cost counts the actual complete callback at each
record; the parser and loop-control costs are included separately. -/
def budget : List (List Bool) → ℕ
  | [] => 0
  | bits :: rest => 6 * bits.length + callbackBound bits rest + 7 + budget rest

abbrev pushFalse (stack : Fin 8) : Cmd 10 8 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.push stack 0))

def pushed (stack : Fin 8) (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks stack (false :: d.stacks stack)⟩

def Ready (d : Data) : Prop := Clean d ∧ d.stacks 1 = [] ∧ d.stacks 2 = []

end SubexponentialSAT.ExecLiteralDedupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecClauseDedupProgram
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
open ExecClauseFiltersProgram (Regs reset flags)

abbrev copySuffix : Cmd 15 16 := .call (StackRoutines.copyProgram 13 12 9 0 1)

def callbackBound (rest : Formula) (clause : Clause) : ℕ :=
  ExecClauseFiltersProgram.callbackBound rest clause + 9 * (encodeFormula rest).length + 8

def ports : RecordPrograms.Ports 15 16 where
  tag := 0
  present := 1
  found := 14
  source := 13
  payload := 15
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def budget : Formula → ℕ
  | [] => 0
  | clause :: rest => 6 * (encodeClause clause).length + callbackBound rest clause + 7 + budget rest

abbrev pushFalse (stack : Fin 16) : Cmd 15 16 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.push stack 0))

def formulaCode (formula : List (List ℕ)) : List Bool :=
  Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) formula

end SubexponentialSAT.ExecClauseDedupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCleanLiteralsProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual clausewise literal cleanup

Each framed clause is decoded, passed to the fixed literal-deduplication
program, and framed again. An outer record reversal restores clause order.
The finite control is independent of the input formula and its clause sizes.
-/

namespace SubexponentialSAT.ExecCleanLiteralsProgram

open BitProgram StructuredCalls

abbrev Data := State 13 11
def clauseCode (clause : List ℕ) : List Bool := Encoding.encodeList Encoding.encodeNat clause
def formulaCode (formula : List (List ℕ)) : List Bool := Encoding.encodeList clauseCode formula

def Clean (d : Data) : Prop := ∀ i : Fin 8, d.stacks (bankStack i) = []

abbrev transfer (src dst : Fin 11) : Cmd 13 11 := .call (StackRoutines.transferProgram src dst 0 1)
def transferred (src dst : Fin 11) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩

abbrev select : Cmd 13 11 := RecordPrograms.atom (.set 12 true)
def selected (d : Data) : Data := ⟨Function.update d.regs 12 true, d.stacks⟩

def ports : RecordPrograms.Ports 13 11 where
  tag := 10
  present := 11
  found := 12
  source := 0
  payload := 1
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

@[simp] theorem clean_state (base : Data) (v pr f : Bool) (src payload : List Bool) :
    Clean (RecordPrograms.state ports base v pr f src payload) ↔ Clean base := by
  simp [Clean, RecordPrograms.state, ports]

@[simp] theorem state_output (base : Data) (v pr f : Bool) (src payload : List Bool) :
    (RecordPrograms.state ports base v pr f src payload).stacks 2 = base.stacks 2 := by
  simp [RecordPrograms.state, ports]

def budget : List (List ℕ) → ℕ
  | [] => 0
  | clause :: rest => 6 * (clauseCode clause).length +
      160 * ((clauseCode clause).length + 1) ^ 2 + 7 + budget rest

abbrev pushFalse (stack : Fin 11) : Cmd 13 11 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.push stack 0))

def pushed (stack : Fin 11) (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks stack (false :: d.stacks stack)⟩

def Ready (d : Data) : Prop := Clean d ∧ d.stacks 1 = [] ∧ d.stacks 2 = []

end SubexponentialSAT.ExecCleanLiteralsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizationPrefixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!+# Actual literal cleanup followed by tautology removal

This is a fixed program on the original declared variable universe. Its two
stages use the same input/output port and restore empty work stacks. The exact
list order and the length bound are retained for subsequent clause absorption.
-/

namespace SubexponentialSAT.SubexpNormalizationPrefixProgram

open BitProgram StructuredCalls

abbrev formulaCode := ExecCleanLiteralsProgram.formulaCode

end SubexponentialSAT.SubexpNormalizationPrefixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizationProgram
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

abbrev formulaCode := SubexpNormalizationPrefixProgram.formulaCode

end SubexponentialSAT.SubexpNormalizationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCoreChildProgram
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


def seedRegs (regs : Regs) : Regs :=
  flags (Function.update (Function.update (reset regs) 0 false) 14 true)
    false true false

def volume (master F : Formula) (H : Clause) : ℕ :=
  (encodeFormula master).length + (encodeFormula F).length +
    2 * (encodeClause H).length + 3

abbrev formulaCode := SubexpNormalizationProgram.formulaCode
abbrev clauseCode := ExecCleanLiteralsProgram.clauseCode

def result {α : Type*} [DecidableEq α]
    (F selected : List (List α)) (H : List α) : List (List α) :=
  ExecCNF.absorb (H :: ExecCNF.eraseClauses F selected)

def inputVolume (F selected : List (List ℕ)) (H : List ℕ) : ℕ :=
  (formulaCode selected).length + (formulaCode F).length + 2 * (clauseCode H).length + 3

end SubexponentialSAT.ExecCoreChildProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecPetalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual stable subtraction of a core from an encoded clause. Membership
tests, core copies, record emission, and order restoration use finite code. -/
namespace SubexponentialSAT.ExecPetalProgram
open BitProgram StructuredCalls

abbrev Data := State 10 9

def smallState (regs : Regs) (source query output target : List Bool) : State 10 8 :=
  ⟨regs, ![source, query, output, target, [], [], [], []]⟩

def state (regs : Regs) (source query output target core : List Bool) : Data :=
  ⟨regs, ![source, query, output, target, [], [], [], [], core]⟩

abbrev copyCore : Cmd 10 9 := .call (StackRoutines.copyProgram 8 3 7 0 1)

def callbackCost (H : List (List Bool)) (bits : List Bool) : ℕ :=
  60 * ((Encoding.encodeList id H).length + 1) * (bits.length + 1)

end SubexponentialSAT.ExecPetalProgram
namespace SubexponentialSAT.ExecPetalProgram
open BitProgram StructuredCalls

def ports : RecordPrograms.Ports 10 9 where
  tag := 7
  present := 8
  found := 9
  source := 0
  payload := 1
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def invariant (H : List (List Bool)) (d : Data) : Prop :=
  ∃ regs source output payload,
    d = state regs source payload output [] (Encoding.encodeList id H)

abbrev pushFalse (port : Fin 9) : Cmd 10 9 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.push port 0))

def pushed (port : Fin 9) (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks port (false :: d.stacks port)⟩

end SubexponentialSAT.ExecPetalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecPetalFamilyProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.ExecPetalFamilyProgram
open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)

abbrev Data := State 13 12

abbrev transfer (src dst : Fin 12) : Cmd 13 12 :=
  .call (StackRoutines.transferProgram src dst 0 1)

def cost (H : Clause) (bits : List Bool) : ℕ :=
  140 * ((encodeClause H).length + 1) * (bits.length + 1)

def ports : RecordPrograms.Ports 13 12 where
  tag := 10
  present := 11
  found := 12
  source := 0
  payload := 1
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def mapPayload (H : Clause) (bits : List Bool) : List Bool :=
  encodeClause (ExecPetalProgram.result ((ExecClauseFiltersProgram.decodeClause bits).getD []) H)

@[simp] theorem mapPayload_encodeClause (C H : Clause) :
    mapPayload H (encodeClause C) = encodeClause (ExecPetalProgram.result C H) := by
  simp [mapPayload]

def petals (F : Formula) (H : Clause) : Formula := F.map (fun C => ExecPetalProgram.result C H)

abbrev pushOutput : Cmd 13 12 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.push 2 0))

end SubexponentialSAT.ExecPetalFamilyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecPetalChildProgram
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

abbrev copySelected : Cmd 15 16 := .call (StackRoutines.copyProgram 12 0 10 0 1)

def petals {α : Type*} [DecidableEq α] (selected : List (List α)) (H : List α) : List (List α) :=
  selected.map (fun C => ExecPetalProgram.result C H)

def volume (F selected : Formula) (H : Clause) : ℕ :=
  (encodeFormula selected).length + (encodeFormula F).length + 2 * (encodeClause H).length + 3

abbrev formulaCode := SubexpNormalizationProgram.formulaCode
abbrev clauseCode := ExecCleanLiteralsProgram.clauseCode

def result {α : Type*} [DecidableEq α]
    (F selected : List (List α)) (H : List α) : List (List α) :=
  ExecCNF.absorb (petals selected H ++ ExecCNF.eraseClauses F selected)

def inputVolume (F selected : List (List ℕ)) (H : List ℕ) : ℕ :=
  (formulaCode selected).length + (formulaCode F).length + 2 * (clauseCode H).length + 3

end SubexponentialSAT.ExecPetalChildProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecSunflowerCodeTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Recovering typed sunflower witnesses from encoded candidates

The executable search manipulates literal words. Selected clauses come from
the input list, and the accepted common core lies in each selected clause.
These facts suffice to recover typed lists for proof purposes. The executable
algorithm never needs a choice of a typed inverse.
-/

namespace SubexponentialSAT.ExecSunflowerCodeTransport

open ExecCNF

universe u v
variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

@[simp] theorem clauseSet_map (f : α → β) (C : Clause α) :
    clauseSet (C.map f) = (clauseSet C).image f := by
  ext x
  simp only [mem_clauseSet, List.mem_map, Finset.mem_image]

@[simp] theorem formulaSet_map (f : α → β) (F : Formula α) :
    formulaSet (F.map (List.map f)) = (formulaSet F).image (Finset.image f) := by
  ext C
  constructor
  · intro hC
    obtain ⟨D, hD, he⟩ := mem_formulaSet.mp hC
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hD
    exact Finset.mem_image.mpr ⟨clauseSet A, mem_formulaSet.mpr ⟨A, hA, rfl⟩,
      (clauseSet_map f A).symm.trans he⟩
  · intro hC
    obtain ⟨D, hD, he⟩ := Finset.mem_image.mp hC
    obtain ⟨A, hA, rfl⟩ := mem_formulaSet.mp hD
    exact mem_formulaSet.mpr ⟨A.map f, List.mem_map.mpr ⟨A, hA, rfl⟩,
      (clauseSet_map f A).trans he⟩

/-- The actual literal payload used by the encoded CNF programs. -/
def literalWord {n : ℕ} (l : SAT.Literal (Fin n)) : List Bool :=
  Encoding.encodeNat (Encoding.literalCode l)

end SubexponentialSAT.ExecSunflowerCodeTransport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecWorklistProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Local encoded worklist updates by a fixed Boolean-stack program

The branch decision and child records are supplied as data. No formula search
or splitting callback is an instruction. Pending work, accumulated leaves, and
both child sources may have arbitrary suffixes; only the current records are
read. The five stack ports are pending, leaves, child A, child B, and scratch.
-/

namespace SubexponentialSAT.ExecWorklistProgram

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 4 5

/-- One tagged, escaped list record. The payload may encode a whole CNF. -/
def record (bits : List Bool) : List Bool := true :: Encoding.frame bits

@[simp] theorem record_length (bits : List Bool) : (record bits).length = 2 * bits.length + 2 := by
  simp [record, Encoding.length_frame]

/-- The three copy ports are fixed when this finite program is constructed. -/
abbrev copyAt (src dst : Fin 5) : Program 4 5 16 :=
  ProgramLinking.liftProgram ExecCNFRecords.copyProgram workRegs (copyPorts src dst)

def copyAfter (src dst : Fin 5) (bits rest : List Bool) (d : Data) : Data :=
  ⟨Function.update (Function.update d.regs 0 false) 1 false,
    Function.update (Function.update d.stacks src rest) dst (record bits ++ d.stacks dst)⟩

/-- Register 2 is the supplied terminal decision; register 3 is the skip flag.
Every stack may contain an arbitrary suffix except for the empty local scratch. -/
abbrev data (terminal value present found : Bool)
    (pending leaves left right : List Bool) : Data :=
  ⟨![value, present, terminal, found], ![pending, leaves, left, right, []]⟩

end SubexponentialSAT.ExecWorklistProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_LocalExpectation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Conditional expectations of local objectives

A local term is evaluated only on the still-unassigned coordinates in its
support. The resulting evaluator is proved equal to exhaustive conditional
expectation. Instrumentation counts calls to local terms, separately from
arithmetic and data-structure costs.
-/

namespace SubexponentialSAT.LocalExpectation

open SubexponentialSAT.ConditionalExpectation
open scoped BigOperators

variable {I W J : Type*} [DecidableEq I]

/-- Exhaustive conditional average on an explicit list of remaining indices. -/
def wordExpectation (alphabet : List W) (f : (I → W) → ℚ) :
    List I → (I → W) → ℚ
  | [], ω => f ω
  | i :: remaining, ω => mean alphabet
      (fun w => wordExpectation alphabet f remaining (Function.update ω i w))

theorem mean_const (alphabet : List W) (hne : alphabet ≠ []) (r : ℚ) :
    mean alphabet (fun _ => r) = r := by
  have hlen : (alphabet.length : ℚ) ≠ 0 := by
    exact_mod_cast (List.length_pos_iff.mpr hne).ne'
  simp only [mean, List.map_const', List.sum_replicate, nsmul_eq_mul]
  apply (div_eq_iff hlen).2
  ring

/-- Efficient local conditional evaluation: a separate small enumeration for
each local term, with unrelated random words omitted. -/
def localEvaluator (alphabet : List W) (terms : List J)
    (support : J → Finset I) (f : J → (I → W) → ℚ) (offset : ℚ)
    (remaining : List I) (ω : I → W) : ℚ :=
  (terms.map (fun j => wordExpectation alphabet (f j) (active (support j) remaining) ω)).sum
    - offset

section Sequential

/-- Polynomially many local evaluations per sequential candidate when term
supports are bounded. Numbered coordinates start at `fixed.length`. -/
def sequentialEvaluator (alphabet : List W) (terms : List J)
    (support : J → Finset ℕ) (f : J → (ℕ → W) → ℚ) (offset : ℚ)
    (default : W) (n : ℕ) (fixed : List W) : ℚ :=
  localEvaluator alphabet terms support f offset
    (List.range' fixed.length n) (decode default fixed)

/-- Actual sequential search using only the local evaluator. -/
def localAssign (a : W) (tail : List W) (terms : List J)
    (support : J → Finset ℕ) (f : J → (ℕ → W) → ℚ) (offset : ℚ)
    (default : W) (n : ℕ) : List W :=
  assignWithEvaluator a tail
    (sequentialEvaluator (a :: tail) terms support f offset default) n []

end Sequential

end SubexponentialSAT.LocalExpectation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularRingCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed Boolean-stack programs for arithmetic with a supplied binary modulus. -/

namespace SubexponentialSAT.ModularRingPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ProgramLinking SubexponentialSAT.StackRoutines
open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularDivisionPrograms

theorem cfg_ext {r s l : ℕ} {a b : Cfg r s l}
    (hp : a.pc = b.pc) (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  simp_all

theorem addPorts_injective : Function.Injective addPorts := by decide

theorem move_sum_first (word modulus : List Bool) :
    transferStacks (0 : Fin 7) 2 (resting word modulus []) =
      seven [] modulus [] [] word.reverse [] [] := by
  funext i; fin_cases i <;> simp [transferStacks, resting, seven]

theorem move_sum_second (word modulus : List Bool) :
    transferStacks (2 : Fin 7) 6 (seven [] modulus [] [] word.reverse [] []) =
      resting [] modulus word := by
  funext i; fin_cases i <;> simp [transferStacks, resting, seven]


end SubexponentialSAT.ModularRingPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularRingPrograms
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

theorem sevenPorts_injective : Function.Injective sevenPorts := by decide
theorem normalizePorts_injective : Function.Injective normalizePorts := by decide

theorem normalization_port_value (input shape output modulus : List Bool)
    (i : Fin 3) :
    normalizationState input shape output modulus (normalizePorts i) =
      operandStacks shape input output i := by
  fin_cases i <;> rfl

theorem normalization_port_frame (input shape output modulus : List Bool)
    (i : Fin 8) (hi : ¬ ∃ j, normalizePorts j = i) :
    normalizationState input shape output modulus i =
      normalizationState [] [] [] modulus i := by
  have h0 : i ≠ 0 := by
    intro h; subst i; exact hi ⟨1, rfl⟩
  have h2 : i ≠ 2 := by
    intro h; subst i; exact hi ⟨2, rfl⟩
  have h7 : i ≠ 7 := by
    intro h; subst i; exact hi ⟨0, rfl⟩
  simp only [normalizationState_apply, h0, h2, h7, ite_false]

theorem normalization_clear (input output modulus : List Bool) :
    clearStacks (0 : Fin 8) (normalizationState input [] output modulus) =
      normalizationState [] [] output modulus := by
  funext i; fin_cases i <;> simp [clearStacks, normalizationState]

theorem normalization_move (output modulus : List Bool) :
    transferStacks (2 : Fin 8) 0 (normalizationState [] [] output.reverse modulus) =
      normalizationState output [] [] modulus := by
  funext i; fin_cases i <;> simp [transferStacks, normalizationState]

theorem shape_copy (xs ys modulus : List Bool) :
    copyStacks (0 : Fin 8) 7 (extendSeven (scalarInput xs ys modulus) []) =
      extendSeven (scalarInput xs ys modulus) xs := by
  funext i; fin_cases i <;> simp [copyStacks, extendSeven, scalarInput, seven]

end SubexponentialSAT.ModularRingPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramStateFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Reusable data projection and framing for genuine finite subroutine calls.
The projection/embedding functions specify states; executable code uses only
the fixed instruction-port relocation already proved by ProgramLinking. -/

namespace SubexponentialSAT.StructuredCalls

open SubexponentialSAT.BitProgram

def projectState {r s R S : ℕ} (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (d : State R S) : State r s := ⟨d.regs ∘ register, d.stacks ∘ stack⟩

end SubexponentialSAT.StructuredCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SaturatingSubtractionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving saturating binary subtraction

Eight Boolean registers and eight stacks suffice. The two operands remain
on stacks 0 and 1; stack 2 receives their natural-number difference and
stacks 3 through 7 return empty. Copied concatenations supply a common
padding shape without computing a numeric width. The final borrow bit
controls a real clear loop. Every copy, pad, subtraction, and clear is
charged in the linear instruction bound.
-/

namespace SubexponentialSAT.SaturatingSubtractionProgram

open BitProgram StructuredCalls BinaryArithmetic ModularArithmetic

abbrev Code := Cmd 8 8

end SubexponentialSAT.SaturatingSubtractionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BinaryArgmin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A binary-score minimum update implemented by finite bit programs

The score is a little-endian bit word. Comparisons inspect its numeric value,
not its length. Candidate payloads may themselves be binary indices or encoded
rows. Ports 0/1 hold the incoming payload/score, 2/3 the incumbent, 4--7 are
scratch, and 8 is an untouched caller queue. Every copy and comparison below
has a measured trace of a fixed finite instruction table.
-/

namespace SubexponentialSAT.SqrtLog.BinaryArgmin

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev Data := State 8 9

end SubexponentialSAT.SqrtLog.BinaryArgmin

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpModulusConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Constructing the prime-power modulus by binary multiplication

The data routine calls the existing binary `mulRun` once per iteration and
starts with the one-bit representation of one. No natural-number exponentiation
or conversion of the encoded value occurs in the data path. A single final
traced pass trims or zero-pads the output. Cost statements count the concrete
finite-alphabet BitEvent traces, not primitive-machine execution steps.
-/

namespace SubexponentialSAT.SubexpModulusConstruction

open BinaryArithmetic

/-- Fixed-width little-endian words are determined by their numeric value. -/
theorem bits_eq_of_length_of_value (xs ys : List Bool)
    (hlen : xs.length = ys.length) (hval : BinaryArithmetic.toNat xs = BinaryArithmetic.toNat ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      have hy : ys = [] := List.length_eq_zero_iff.mp hlen.symm
      exact hy.symm
  | cons b bs ih =>
      cases ys with
      | nil => simp at hlen
      | cons c cs =>
          have hb : b = c := by
            cases b <;> cases c <;> simp_all [toNat_cons] <;> omega
          subst c
          have ht : BinaryArithmetic.toNat bs = BinaryArithmetic.toNat cs := by
            simp only [toNat_cons] at hval
            omega
          exact congrArg (List.cons b) (ih cs (Nat.succ.inj hlen) ht)

end SubexponentialSAT.SubexpModulusConstruction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScanPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete stack operations used by the serialized coefficient scanner. -/

namespace SubexponentialSAT.SubexpScanPrimitives

open BitProgram StructuredCalls

theorem state_ext {r s : ℕ} {a b : State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; cases hr; cases hs; rfl

def afterCopy {r s : ℕ} (d : State r s) (src dst : Fin s) (v p : Fin r) : State r s :=
  ⟨readRegs d.regs v p none, StackRoutines.copyStacks src dst d.stacks⟩

def afterTransfer {r s : ℕ} (d : State r s) (src dst : Fin s) (v p : Fin r) : State r s :=
  ⟨readRegs d.regs v p none, StackRoutines.transferStacks src dst d.stacks⟩

def afterTake {r s : ℕ} (d : State r s) (src dst : Fin s) (v p : Fin r)
    (bits rest : List Bool) : State r s :=
  ⟨readRegs d.regs v p none,
    Function.update (Function.update d.stacks src rest) dst (bits ++ d.stacks dst)⟩

end SubexponentialSAT.SubexpScanPrimitives

end OAI.Algorithms
end


