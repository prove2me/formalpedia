-- Prove2me | Definitions.Def_OAIQ081S154
-- name    : OAIQ081S154
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:57:57.532988+00:00
-- url     : https://prove2.me/theorems/5ded8616-228d-4076-bbc9-28cb7d227d44
-- title:
--   Definitions bundle OAIQ081S154 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 2 definitions and 14 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.generatedCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.countCopy`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLog_IdempotentPreparationProgramEncoding`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentPreparationProgramEncoding.lean), [`SubexponentialSAT_SqrtLog_IdempotentPreparationProgramPreparedTable`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentPreparationProgramPreparedTable.lean), [`SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarOutput`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentPreparationProgramScalarOutput.lean), [`SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarSemantics`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentPreparationProgramScalarSemantics.lean), [`SubexponentialSAT_SqrtLog_IdempotentPreparationProgramTable`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentPreparationProgramTable.lean), [`SubexponentialSAT_SqrtLog_IdempotentPreparationProgramTableRun`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentPreparationProgramTableRun.lean), [`SubexponentialSAT_SqrtLog_InterpolationCacheProgramCounts`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/InterpolationCacheProgramCounts.lean).
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S139`, `OAIQ081S140`, `OAIQ081S141` and `OAIQ081S142` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S166` and `OAIQ081S167`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S139
import Definitions.Def_OAIQ081S140
import Definitions.Def_OAIQ081S141
import Definitions.Def_OAIQ081S142

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open SubexpSymbolicCost SubexpQuarticRing

theorem minusOneRun_flat (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (ht : 0 < t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hm : BinaryArithmetic.toNat cache.minusOne.val < p^t) :
    RingProgram.flat (IdempotentProgram.minusOneRun (RingProgram.scalarProgram p t M cache) t).1 =
      cache.minusOne.val ++ Subexp.BlockCopyProgram.copies (3*t-1) cache.zero.val := by
  simpa only [Subexp.BlockCopyProgram.copies] using
    IdempotentProgram.minusOneRun_flat p t M cache hz hm t ht

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

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

theorem iterate_half (M : SubexpPreparedQuartic.Modulus p t) (v : Values p t)
    (h8:decode p t v 8=1) (h9:decode p t v 9 = -1) (n:ℕ) :
    decode p t (iterateForward p t M v n) 8 = IdempotentProgram.halfValue n ∧
    decode p t (iterateForward p t M v n) 9 = -1 ∧
    (∀ i:Reg, i≠6 → i≠7 → i≠8 → decode p t (iterateForward p t M v n) i=decode p t v i) := by
  induction n with
  | zero => exact ⟨h8,h9,fun _ _ _ _=>rfl⟩
  | succ n ih =>
      simp only [iterateForward,decode_run]
      have hh:=halfStep_algebra (decode p t (iterateForward p t M v n)) ih.2.1
      refine ⟨?_,hh.2.1,?_⟩
      · rw [hh.1,ih.1,IdempotentProgram.halfValue]
      · intro i hi6 hi7 hi8
        exact (hh.2.2 i hi6 hi7 hi8).trans (ih.2.2 i hi6 hi7 hi8)

local instance localInst_r5f582e_1 : Fact (Nat.Prime 3) := ⟨by decide⟩
/-- The recurrence is reduced modulo the actual runtime modulus 3^t. -/
theorem half_inverse (M : SubexpPreparedQuartic.Modulus 3 t) (v : Values 3 t)
    (h8:decode 3 t v 8=1) (h9:decode 3 t v 9 = -1) :
    2*decode 3 t (iterateForward 3 t M v t) 8=1 := by
  rw [(iterate_half 3 t M v h8 h9 t).1,IdempotentProgram.twice_halfValue]
  have hz : (3 : ZMod (3^t))^t=0 := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using ZMod.natCast_self (3^t)
  rw [hz,zero_add]

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open SubexpLiftRing SubexpQuarticRing BinaryArithmetic

variable (p t : ℕ) [Fact p.Prime]

theorem iterate_canonical (M:SubexpPreparedQuartic.Modulus p t) (v:Values p t)
    (n:ℕ) (h:Canonical p t v) : Canonical p t (iterateForward p t M v n) := by
  induction n with
  | zero=>exact h
  | succ n ih=>exact run_canonical p t M _ _ ih

attribute [local instance] OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar.instFactPrimeOfNatNat_solutions_2
theorem final_canonical (M:SubexpPreparedQuartic.Modulus 3 t) (v:Values 3 t)
    (h:Canonical 3 t v) : Canonical 3 t (finalValues t M v) :=
  run_canonical 3 t M _ _ (iterate_canonical 3 t M _ _ (run_canonical 3 t M _ _ h))

theorem final_preserves (M:SubexpPreparedQuartic.Modulus 3 t) (v:Values 3 t)
    (h8:decode 3 t v 8=1) (h9:decode 3 t v 9 = -1)
    (i:Reg) (hi6:i≠6) (hi7:i≠7) (hi8:i≠8) (hi10:i≠10) (hi11:i≠11) :
    decode 3 t (run 3 t M finalCoefficients (iterateForward 3 t M v t)) i=decode 3 t v i := by
  rw [decode_run]
  have hh:=iterate_half 3 t M v h8 h9 t
  rw [(final_algebra (decode 3 t (iterateForward 3 t M v t)) hh.2.1).2.2 i hi6 hi10 hi11]
  exact hh.2.2 i hi6 hi7 hi8

theorem final_small (M:SubexpPreparedQuartic.Modulus 3 t) (v:Values 3 t)
    (h0:decode 3 t v 0=0) (h1:decode 3 t v 1=1) (h9:decode 3 t v 9 = -1) :
    ∀i:Fin 6,decode 3 t (finalValues t M v) (i.castAdd 6)=(smallInteger i:ZMod (3^t)) := by
  have hc:=constants_algebra (decode 3 t v) h0 h1 h9
  rw [←decode_run 3 t M constants v] at hc
  intro i
  have hp:=final_preserves t M (run 3 t M constants v) hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2
    (i.castAdd 6) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide)
    (by fin_cases i <;> decide)
    (by fin_cases i <;> decide)
    (by fin_cases i <;> decide)
  change decode 3 t (finalValues t M v) (i.castAdd 6)=_ at hp
  rw [hp]
  fin_cases i
  · simpa [smallInteger] using hc.1
  · simpa [smallInteger] using hc.2.1
  · simpa [smallInteger] using hc.2.2.1
  · simpa [smallInteger] using hc.2.2.2.1
  · simpa [smallInteger] using hc.2.2.2.2.1
  · simpa [smallInteger] using hc.2.2.2.2.2.1

theorem final_half (M:SubexpPreparedQuartic.Modulus 3 t) (v:Values 3 t)
    (h0:decode 3 t v 0=0) (h1:decode 3 t v 1=1) (h9:decode 3 t v 9 = -1) :
    2*decode 3 t (finalValues t M v) 8=1 ∧
    decode 3 t (finalValues t M v) 9 = -1 := by
  have hc:=constants_algebra (decode 3 t v) h0 h1 h9
  rw [←decode_run 3 t M constants v] at hc
  have hi:=half_inverse t M (run 3 t M constants v) hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2
  have hn:decode 3 t (iterateForward 3 t M (run 3 t M constants v) t) 9 = -1 :=
    (iterate_half 3 t M _ hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2 t).2.1
  simpa [finalValues,run,finalCoefficients,Op.eval,decode] using And.intro hi hn

/-- These exact bytes are the coefficient words requested by the array builder. -/
theorem final_coefficients (M:SubexpPreparedQuartic.Modulus 3 t) (v:Values 3 t) :
    let w:=finalValues t M v
    w 10=(SubexpPreparedQuartic.wordAdd 3 t M (w 8) (w 8)).1 ∧
    w 11=(SubexpPreparedQuartic.wordMul 3 t M
      (SubexpPreparedQuartic.wordAdd 3 t M (w 10) (w 8)).1 (w 9)).1 := by
  simp [finalValues,run,finalCoefficients,Op.eval]

def generatedCache (M:SubexpPreparedQuartic.Modulus 3 t) (v:Values 3 t)
    (h0:decode 3 t v 0=0) (h1:decode 3 t v 1=1) (h9:decode 3 t v 9 = -1) :
    RingProgram.ScalarCache 3 t where
  zero := finalValues t M v 0
  one := finalValues t M v 1
  minusOne := finalValues t M v 9
  zero_correct := by simpa [decode,smallInteger] using final_small t M v h0 h1 h9 0
  one_correct := by simpa [decode,smallInteger] using final_small t M v h0 h1 h9 1
  minusOne_correct := (final_half t M v h0 h1 h9).2

theorem generated_table (M:SubexpPreparedQuartic.Modulus 3 t) (v:Values 3 t)
    (h0:decode 3 t v 0=0) (h1:decode 3 t v 1=1) (h9:decode 3 t v 9 = -1)
    (hc:Canonical 3 t v) (i:Fin 6) :
    (IdempotentProgram.integerRun (RingProgram.scalarProgram 3 t M (generatedCache t M v h0 h1 h9))
      (IdempotentTableEntryProgram.codeValue i)).1 = finalValues t M v (tableRegister i) := by
  apply IdempotentProgram.integerRun_eq_of_value 3 t M _
    (final_canonical t M v hc 0) _ _ (final_canonical t M v hc _)
  have hh:=final_small t M v h0 h1 h9
  have hh' : ∀ i : Fin 6,
      wordValue 3 t (finalValues t M v (i.castAdd 6)) =
        (smallInteger i : ZMod (3 ^ t)) := by
    intro i
    simpa only [decode] using hh i
  fin_cases i
  · simpa [tableRegister,smallInteger,IdempotentTableEntryProgram.codeValue] using hh' 0
  · simpa [tableRegister,smallInteger,IdempotentTableEntryProgram.codeValue] using hh' 1
  · simpa [tableRegister,smallInteger,IdempotentTableEntryProgram.codeValue] using hh' 3
  · simpa [tableRegister,smallInteger,IdempotentTableEntryProgram.codeValue] using hh' 2
  · simpa [tableRegister,smallInteger,IdempotentTableEntryProgram.codeValue] using hh' 4
  · simpa [tableRegister,smallInteger,IdempotentTableEntryProgram.codeValue] using hh' 5

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

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

theorem tableCommand_eval (base : Store) (entry : Cmd 8 41)
    (f : ℕ → ℕ → ℕ → List Bool) (n K : ℕ)
    (h37 : base 37 = List.replicate n true)
    (h24 : base 24 = []) (h25 : base 25 = [])
    (h26 : base 26 = []) (h38 : base 38 = [])
    (step : ∀ i, i < n → ∀ j, j < n → ∀ k, k < n → ∀ regs tail,
      ∃ cost rf, cost ≤ K ∧
        Eval entry cost (tripleState base regs i j k tail)
          (tripleState base rf i j k (f i j k ++ tail)))
    (regs : Fin 8 → Bool) (tail : List Bool) :
    ∃ cost rf, cost ≤ tableBudget n K ∧
      Eval (tableCommand entry) cost ⟨regs,Function.update base 22 tail⟩
        ⟨rf,Function.update base 22 (tableCells f n ++ tail)⟩ := by
  apply copyAndScan_eval base 37 24 22 38 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (copyAndScan 37 25 22 38 (copyAndScan 37 26 22 38 entry))
    (fun k => cells (fun i => cells (fun j => f i j k) n) n)
    (scanBudget n (scanBudget n K)) n h37 h24 h38
  intro k hk rk tk
  let bk := Function.update base 24 (List.replicate k true)
  have middle := copyAndScan_eval bk 37 25 22 38 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (copyAndScan 37 26 22 38 entry) (fun i => cells (fun j => f i j k) n)
    (scanBudget n K) n (by simp [bk,h37]) (by simp [bk,h25]) (by simp [bk,h38])
  apply middle
  intro i hi ri ti
  let bi := Function.update bk 25 (List.replicate i true)
  have inner := copyAndScan_eval bi 37 26 22 38 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) entry (fun j => f i j k) K n
    (by simp [bi,bk,h37]) (by simp [bi,bk,h26]) (by simp [bi,bk,h38])
  apply inner
  intro j hj rj tj
  exact step i hi j hj k hk rj tj

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramTableRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpScanPrimitives
open IdempotentTableEntryProgram (entryCode)

theorem nativeTable_eval (d : Data) (n B : ℕ)
    (h37 : d.stacks 37 = List.replicate n true)
    (h24 : d.stacks 24 = []) (h25 : d.stacks 25 = [])
    (h26 : d.stacks 26 = []) (h38 : d.stacks 38 = [])
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = [])
    (h2 : d.stacks 2 = []) (h3 : d.stacks 3 = []) (h4 : d.stacks 4 = [])
    (hw : ∀ c, (d.stacks (entrySource c)).length ≤ B) :
    ∃ cost rf, cost ≤ Scan.tableBudget n (200*(n+B+1)) ∧
      Eval nativeTable cost d ⟨rf,Function.update d.stacks 22
        (Scan.tableCells (cachedEntry d.stacks) n ++ d.stacks 22)⟩ := by
  suffices step : ∀ i, i < n → ∀ j, j < n → ∀ k, k < n → ∀ regs tail,
      ∃ cost rf, cost ≤ 200*(n+B+1) ∧
        Eval entryCommand cost (Scan.tripleState d.stacks regs i j k tail)
          (Scan.tripleState d.stacks rf i j k (cachedEntry d.stacks i j k ++ tail)) by
    obtain ⟨cost,rf,hcost,he⟩ := Scan.tableCommand_eval d.stacks entryCommand
      (cachedEntry d.stacks) n (200*(n+B+1)) h37 h24 h25 h26 h38 step d.regs (d.stacks 22)
    refine ⟨cost,rf,hcost,?_⟩
    simpa [nativeTable] using he
  intro i hi j hj k hk regs tail
  let a := Scan.tripleState d.stacks regs i j k tail
  obtain ⟨cost,rf,hcost,he⟩ := entryCommand_eval a i j k
    (by simp [a,Scan.tripleState]) (by simp [a,Scan.tripleState])
    (by simp [a,Scan.tripleState]) (by simp [a,Scan.tripleState,h0])
    (by simp [a,Scan.tripleState,h1]) (by simp [a,Scan.tripleState,h2])
    (by simp [a,Scan.tripleState,h3]) (by simp [a,Scan.tripleState,h4])
  have hsource : a.stacks (entrySource (entryCode i j k)) =
      cachedEntry d.stacks i j k := by
    change a.stacks (entrySource (entryCode i j k)) = d.stacks (entrySource (entryCode i j k))
    generalize entryCode i j k = code
    fin_cases code <;> simp [a,Scan.tripleState,entrySource]
  refine ⟨cost,rf,?_,?_⟩
  · rw [hsource] at hcost
    have hw' := hw (entryCode i j k)
    dsimp [cachedEntry] at hcost
    omega
  · have ha22 : a.stacks 22=tail := by simp [a,Scan.tripleState]
    rw [hsource,ha22] at he
    simpa [a,Scan.tripleState,Function.update_idem] using he

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

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

theorem prepared_nativeTable_eval (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t)
    (d : Data) (hp : Scalar.Prepared t M cache u d)
    (h37 : d.stacks 37=List.replicate (3*t) true)
    (h26 : d.stacks 26=[]) (h22 : d.stacks 22=[]) :
    ∃ cost rf, cost ≤ Scan.tableBudget (3*t) (200*(3*t+SubexpLiftRing.baseWidth 3 t+1)) ∧
      Eval nativeTable cost d ⟨rf,Function.update d.stacks 22
        (IdempotentProgram.tableTape (IdempotentProgram.tableCode (t := t) (RingProgram.scalarProgram 3 t M cache)))⟩ := by
  have h0 : d.stacks 0=[] := hp.rest.1 0
  have h1 : d.stacks 1=[] := hp.rest.1 1
  have h2 : d.stacks 2=[] := hp.rest.1 2
  have h3 : d.stacks 3=[] := hp.rest.1 3
  have h4 : d.stacks 4=[] := hp.rest.1 4
  obtain ⟨cost,rf,hcost,he⟩ := nativeTable_eval d (3*t) (SubexpLiftRing.baseWidth 3 t)
    h37 hp.temporary24 hp.temporary25 h26 hp.rest.2 h0 h1 h2 h3 h4
    (fun c => (prepared_source_width t M cache u d hp c).le)
  refine ⟨cost,rf,hcost,?_⟩
  simpa only [prepared_tableCells t M cache u d hp,h22,List.append_nil] using he

theorem prepared_pool_length (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t)
    (d : Data) (hp : Scalar.Prepared t M cache u d) (i : Scalar.Reg) :
    (d.stacks (Scalar.port i)).length ≤ SubexpLiftRing.baseWidth 3 t := by
  fin_cases i
  · exact (prepared_source_width t M cache u d hp 0).le
  · exact (prepared_source_width t M cache u d hp 1).le
  · exact (prepared_source_width t M cache u d hp 3).le
  · exact (prepared_source_width t M cache u d hp 2).le
  · exact (prepared_source_width t M cache u d hp 4).le
  · exact (prepared_source_width t M cache u d hp 5).le
  · simp [Scalar.port,hp.temporary24]
  · simp [Scalar.port,hp.temporary25]
  · simp [Scalar.port,hp.half,u.property]
  · simp [Scalar.port,hp.minusOne,cache.minusOne.property]
  · change (d.stacks 30).length ≤ _
    rw [hp.twice]
    exact (SubexpPreparedQuartic.wordAdd 3 t M u u).1.property.le
  · change (d.stacks 31).length ≤ _
    rw [hp.minusThree]
    exact (SubexpPreparedQuartic.wordMul 3 t M
      (SubexpPreparedQuartic.wordAdd 3 t M (SubexpPreparedQuartic.wordAdd 3 t M u u).1 u).1
      cache.minusOne).1.property.le

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramCounts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid materialization of canonical unary word and table lengths. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def countCopy (src dst : Fin 320) : Code := .seq (copy src 272) (consumeCount 272 dst)

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end


