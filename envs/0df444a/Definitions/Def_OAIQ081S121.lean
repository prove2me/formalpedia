-- Prove2me | Definitions.Def_OAIQ081S121
-- name    : OAIQ081S121
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:32:42.082141+00:00
-- url     : https://prove2.me/theorems/532d0609-125c-444c-aa1d-fcbd6307eb18
-- title:
--   Definitions bundle OAIQ081S121 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 22 declarations of OpenAI's Lean: 9 definitions and 13 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.binaryLiftWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.Coeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.negativeBytes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.negativeValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl.input`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.WideCode`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_IdempotentProgramComplete`, `SubexponentialSAT_SqrtLog_IdempotentProgramFinal`, `SubexponentialSAT_SqrtLog_IdempotentProgramRegisters`, `SubexponentialSAT_SqrtLog_IdempotentProgramSerialization`, `SubexponentialSAT_SqrtLog_IdempotentProgramService`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramModel`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramTables`, `SubexponentialSAT_SqrtLog_IrreducibleSearch`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrap`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapPreparation`, `SubexponentialSAT_SqrtLog_IrreducibleSearchModel`, `SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan`, `SubexponentialSAT_SqrtLog_IrreducibleSearchSelection`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramState`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S100`, `OAIQ081S101`, `OAIQ081S103`, `OAIQ081S104` and `OAIQ081S105` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S141`, `OAIQ081S142`, `OAIQ081S145` and `OAIQ081S146`; the statement `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.binaryLiftWords_indicator`; the proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.binaryLiftWords_indicator`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S100
import Definitions.Def_OAIQ081S101
import Definitions.Def_OAIQ081S103
import Definitions.Def_OAIQ081S104
import Definitions.Def_OAIQ081S105

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramRegisters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source-preserving storage for the fixed Newton register machine. Every
copy, replacement, and clearing operation is an actual finite bit program. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open BitProgram StructuredCalls StackRoutines

theorem prepareOperands_eval (d : RegisterData) (left right : Fin 41)
    (hl : 32 ≤ left.val) (hr : 32 ≤ right.val)
    (hl38 : left ≠ 38) (hr38 : right ≠ 38)
    (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = [])
    (h11 : d.stacks 11 = []) (h38 : d.stacks 38 = []) :
    Eval (prepareOperands left right)
      (7*(d.stacks left).length + 7*(d.stacks right).length +
        7*(d.stacks 37).length + 15) d (preparedOperands d left right) := by
  have hl8 : left ≠ 8 := by intro h; have hv : left.val = 8 := congrArg Fin.val h; omega
  have hr8 : right ≠ 8 := by intro h; have hv : right.val = 8 := congrArg Fin.val h; omega
  have hr9 : right ≠ 9 := by intro h; have hv : right.val = 9 := congrArg Fin.val h; omega
  have h1 := ArithmeticCalls.copyAt_eval left (8 : Fin 41) 38 d
    hl8 hl38 (by decide) h8 h38
  have h2 := ArithmeticCalls.copyAt_eval right (9 : Fin 41) 38
    (ArithmeticCalls.afterCopy left 8 d) hr9 hr38 (by decide)
    (by simp [ArithmeticCalls.afterCopy, h9])
    (by simp [ArithmeticCalls.afterCopy, h38])
  have h3 := ArithmeticCalls.copyAt_eval (37 : Fin 41) 11 38
    (ArithmeticCalls.afterCopy right 9 (ArithmeticCalls.afterCopy left 8 d))
    (by decide) (by decide) (by decide)
    (by simp [ArithmeticCalls.afterCopy, h11])
    (by simp [ArithmeticCalls.afterCopy, h38])
  convert h1.seq (h2.seq h3) using 1 <;>
    simp [ preparedOperands, ArithmeticCalls.afterCopy,
      hr8] ; omega

/-- All argument copies and the replacement are paid. The only hypothesis
about the arithmetic itself is an actual evaluation of its fixed command. -/
theorem registerBinary_eval (raw : Cmd 8 41) (d e : RegisterData)
    (target left right : Fin 41) (result : List Bool) (n : ℕ)
    (ht : 32 ≤ target.val) (hl : 32 ≤ left.val) (hr : 32 ≤ right.val)
    (ht38 : target ≠ 38) (hl38 : left ≠ 38) (hr38 : right ≠ 38)
    (h0 : d.stacks 0 = []) (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = [])
    (h11 : d.stacks 11 = []) (h38 : d.stacks 38 = [])
    (run : Eval raw n (preparedOperands d left right) e)
    (output : e.stacks = Function.update d.stacks 0 result) :
    ∃ f, Eval (registerBinary raw target left right)
      (n + 7*(d.stacks left).length + 7*(d.stacks right).length +
        7*(d.stacks 37).length + 2*(d.stacks target).length + 9*result.length + 26) d f ∧
      f.stacks = Function.update d.stacks target result := by
  have ht0 : target ≠ 0 := by intro h; have hv : target.val = 0 := congrArg Fin.val h; omega
  have prepare := prepareOperands_eval d left right hl hr hl38 hr38 h8 h9 h11 h38
  have store := storeResult_eval e target ht0 ht38 (by rw [output]; simpa using h38)
  refine ⟨storedResult e target, ?_, ?_⟩
  · convert prepare.seq (run.seq store) using 1 ;
      simp [ output, ht0] ; omega
  · rw [storedResult_stacks e target ht0, output]
    funext j
    by_cases hjt : j = target
    · subst j; simp [ht0]
    · by_cases hj0 : j = 0
      · subst j; simp [hjt, h0]
      · simp [hjt, hj0]

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramSerialization
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpQuarticRing

theorem tableTape_eq_encoding {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B) :
    tableTape table = RingTriple.tableEncoding table := by
  simp [tableTape, tableWords, RingTriple.tableEncoding, List.map_flatten, List.flatten_flatten,
    List.map_ofFn, Function.comp_def]


end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramService
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Lift the common 32-stack arithmetic ABI into the Newton machine and prove
that the source-preserving register wrapper has the exact specified effect. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open BitProgram StructuredCalls

/-- Any proved native add/multiply service can be wrapped without assuming
free copies or unbounded register access. The exact result overwrites target. -/
theorem registerService_eval (command : Cmd 8 32) (d : RegisterData)
    (modulus width zero table degree leftWord rightWord result : List Bool)
    (target left right : Fin 41) (n : ℕ) (rf : Fin 8 → Bool)
    (context : ServiceContext d modulus width zero table)
    (hd : d.stacks 37 = degree) (hlword : d.stacks left = leftWord)
    (hrword : d.stacks right = rightWord) (hs : d.stacks 38 = [])
    (ht : 32 ≤ target.val) (hl : 32 ≤ left.val) (hr : 32 ≤ right.val)
    (ht38 : target ≠ 38) (hl38 : left ≠ 38) (hr38 : right ≠ 38)
    (run : Eval command n
      (RingScan.serviceState (preparedOperands d left right).regs
        modulus [] leftWord rightWord degree width zero table)
      (RingScan.serviceState rf modulus result [] [] [] width zero table)) :
    ∃ f, Eval (registerBinary (callService command) target left right)
      (n+1 + 7*leftWord.length + 7*rightWord.length + 7*degree.length +
        2*(d.stacks target).length + 9*result.length + 26) d f ∧
      f.stacks = Function.update d.stacks target result := by
  have hcontext : ∀ i : Fin 32, d.stacks (servicePorts i) =
      (RingScan.serviceState d.regs modulus [] [] [] [] width zero table).stacks i := context
  have h0 : d.stacks 0 = [] := hcontext 0
  have h8 : d.stacks 8 = [] := hcontext 8
  have h9 : d.stacks 9 = [] := hcontext 9
  have h11 : d.stacks 11 = [] := hcontext 11
  obtain ⟨e, he, hout⟩ := callService_eval command _ _ (preparedOperands d left right)
    (Function.update d.stacks 0 result) n rfl (by
      intro i
      rw [preparedOperands_stacks d left right hr]
      have hi := hcontext i
      fin_cases i <;>
        simp [servicePorts, hd, hlword, hrword,
          RingScan.serviceState, RingScan.serviceWorkState, RingScan.serviceTapes] at hi ⊢ <;>
        exact hi) (by
      intro i
      have hi := hcontext i
      fin_cases i <;>
        simp [servicePorts, RingScan.serviceState,
          RingScan.serviceWorkState, RingScan.serviceTapes] at hi ⊢ <;> exact hi) (by
      intro j hj
      have hlow : 32 ≤ j.val := by
        apply Nat.le_of_not_gt
        intro hjlt
        exact hj ⟨(⟨j.val, hjlt⟩ : Fin 32), Fin.ext rfl⟩
      have hj0 : j ≠ 0 := by intro h; have hv : j.val = 0 := congrArg Fin.val h; omega
      have hj8 : j ≠ 8 := by intro h; have hv : j.val = 8 := congrArg Fin.val h; omega
      have hj9 : j ≠ 9 := by intro h; have hv : j.val = 9 := congrArg Fin.val h; omega
      have hj11 : j ≠ 11 := by intro h; have hv : j.val = 11 := congrArg Fin.val h; omega
      rw [preparedOperands_stacks d left right hr]
      simp [hj0, hj8, hj9, hj11]) run
  obtain ⟨f, hf, hfs⟩ := registerBinary_eval (callService command) d e target left right result
    (n+1) ht hl hr ht38 hl38 hr38 h0 h8 h9 h11 hs he hout
  exact ⟨f, by simpa only [hlword, hrword, hd] using hf, hfs⟩

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramFinal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete native Newton lift and the exact degree-three coefficient output.
The input-state contract includes prepared scalar constants and the cached
H-adic table; native preparation is a separate remaining construction. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open BitProgram StructuredCalls SubexpSymbolicCost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def binaryLiftWords (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t) :
    RingProgram.Code (RingProgram.ScalarCode 3 t) (3*t) :=
  (liftRun (binaryArrayProgram (RingProgram.scalarProgram 3 t M cache) t)
    (initialRun (RingProgram.scalarProgram 3 t M cache) t u).1 t).1

end SubexponentialSAT.SqrtLog.IdempotentProgram


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramComplete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed finite bit program constructs the ternary H-adic lift from its
binary precision alone. Preparation, array arithmetic, iteration and output
serialization are all covered by actual bit-instruction traces. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open BitProgram StructuredCalls SubexpQuarticRing

theorem completeProgram_output_length (t : ℕ)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (u : RingProgram.ScalarCode 3 t) :
    (RingProgram.flat (binaryLiftWords t M cache u)).length=6*t^2 := by
  rw [RingProgram.flat_length,RingProgram.ternary_baseWidth]
  ring

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Values computed by the physical interpolation-cache producer. Every
entry is a typed output of an executable ring program. The uniform inverse
routine has an explicit zero-diagonal interpretation. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram

open SubexponentialSAT
open scoped BigOperators

abbrev Coeff (t d : ℕ) := RingProgram.Code (RingProgram.ScalarCode 3 t) d

def negativeValue (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne x : Coeff t d) : Coeff t d :=
  ((RingProgram.modelProgram t a M cache).mulRun x minusOne).1

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramTables
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete ordered native tables; all working streams are empty again. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexpLiftRing

def negativeBytes (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (xs : List (Coeff t d)) :=
  xs.flatMap fun x => RingProgram.flat (negativeValue t a M cache minusOne x)

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable arbitrary-degree irreducible search over F₃

Search all monic degree-`d` coefficient vectors and reject each candidate
which is the product of two nonconstant arrays of degree at most `d`.
The test uses explicit convolution. Mathematical finite-field existence
proves that the executable search succeeds for every positive `d`.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open Polynomial

theorem coefficients_irreducible {d : ℕ} (hd : 0 < d) :
    Irreducible (QuarticSearch.poly (coefficients d)) := by
  cases hs : (search d).1 with
  | none => exact False.elim (search_ne_none hd hs)
  | some c =>
      have hf : (candidates d).find? (fun c => (evaluate c).1) = some c := by
        simpa only [search, QuarticSearch.scan_value] using hs
      have hp := List.find?_some hf
      have hi := (passes_iff hd c).mp (by simpa using hp)
      simpa [coefficients, hs] using hi

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! A fixed framed call generates an ordered table from a runtime unary depth.
Only its output and depth ports change; the generator's sentinel is paid for
and cleared before returning. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open BitProgram StructuredCalls
open Subexp.TupleProgram SubexpOrderedTupleData
open SubexpEnumerationPayload SubexpTupleRefinement

theorem generateAt_eval (candidate : Bool) (a : Data) (ha : GeneratorReady candidate a) :
    ∃ t rf, Eval (generateAt candidate) t a
      ⟨rf, Function.update
        (Function.update a.stacks (generatorOut candidate) (tableWord (a.stacks 6).length))
        6 []⟩ ∧
      t ≤ IrreducibleSearchEnumeration.cost (a.stacks 6).length + 5 := by
  classical
  let small : State 10 9 :=
    ⟨fun i => a.regs (generatorRegs i), fun i => a.stacks (generatorMap candidate i)⟩
  have ha10 := ha.1
  have ha0 := ha.2.1 0 (by decide)
  have ha1 := ha.2.1 1 (by decide)
  have ha2 := ha.2.1 2 (by decide)
  have ha3 := ha.2.1 3 (by decide)
  have ha4 := ha.2.1 4 (by decide)
  have ha5 := ha.2.1 5 (by decide)
  have hl : outerInvariant IrreducibleSearchEnumeration.alphabet
      (a.stacks 6) (small.regs 9) small := by
    simp [outerInvariant, small, generatorMap, ha.1, alphabetWord, ha1, ha2, ha4, ha5]
  obtain ⟨next, hn, t, ht, he⟩ := IrreducibleSearchEnumeration.program_runsIn
    IrreducibleSearchEnumeration.alphabet (a.stacks 6) (small.regs 9) small hl
    (by simpa [small, generatorMap] using ha.2.2)
    (by simpa [small, generatorMap] using ha0)
    (by simpa [small, generatorMap] using ha3)
  have hstart : embedState generatorRegs (generatorMap candidate) a small = a := by
    apply embedState_eq_of_ports generatorRegs (generatorMap candidate) a a small
      generatorRegs_injective (generatorMap_injective candidate)
    all_goals intros; rfl
  rcases hn with ⟨⟨h1,h3,h4,h6,h7,h8,h9⟩,h0,h2,h5⟩
  have hout : next.stacks 0 = tableWord (a.stacks 6).length := by
    simpa only [tableWord, IrreducibleSearchEnumeration.alphabet,
      orderedRows_encoded, IrreducibleSearch.candidates] using h0
  let mid : Data := ⟨Function.extend generatorRegs next.regs a.regs,
    Function.update (Function.update
      (Function.update a.stacks (generatorOut candidate) (tableWord (a.stacks 6).length))
      6 []) 3 [false]⟩
  have hend : embedState generatorRegs (generatorMap candidate) a next = mid := by
    apply embedState_eq_of_ports generatorRegs (generatorMap candidate) a mid next
      generatorRegs_injective (generatorMap_injective candidate)
    · intro i
      exact generatorRegs_injective.extend_apply _ _ _
    · intro i hi
      exact Function.extend_apply' _ _ _ hi
    · intro i
      fin_cases i <;> cases candidate <;>
        simp_all [mid, generatorMap, generatorOut, alphabetWord]
    · intro i hi
      have ho : i ≠ generatorOut candidate := fun h => hi ⟨0, h.symm⟩
      have h6' : i ≠ 6 := fun h => hi ⟨8, h.symm⟩
      have h3' : i ≠ 3 := fun h => hi ⟨5, h.symm⟩
      simp [mid, ho, h6', h3']
  have hcall := eval_call_lifted IrreducibleSearchEnumeration.program
    generatorRegs (generatorMap candidate) a generatorRegs_injective
    (generatorMap_injective candidate) he
  rw [hstart, hend] at hcall
  have hc := clearCmd_eval 3 mid
  have hfinal : Function.update mid.stacks 3 [] =
      Function.update
        (Function.update a.stacks (generatorOut candidate) (tableWord (a.stacks 6).length))
        6 [] := by
    funext i
    by_cases hi : i = 3
    · subst i
      cases candidate <;> simp [mid, generatorOut, ha3]
    · simp [mid, hi]
  refine ⟨t + 5, readRegs mid.regs 0 1 none, ?_, ?_⟩
  · simpa only [generateAt, show (mid.stacks 3).length = 1 by simp [mid],
      show 2 * 1 + 3 = 5 from rfl, hfinal] using hcall.seq hc
  · simpa only [IrreducibleSearchEnumeration.cost] using Nat.add_le_add_right ht 5

end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap


/-! Paid construction of both search tables from a single unary depth word. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchSelection
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact first-success selection, including the existing chosen polynomial. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open SubexpEnumerationPayload SubexpTupleRefinement

theorem find_candidates_eq_coefficients {d : ℕ} (hd : 0 < d) :
    (candidates d).find? passes = some (coefficients d) := by
  have hv : (search d).1 = (candidates d).find? passes := by
    simp only [search, QuarticSearch.scan_value, evaluate_value]
  cases hs : (search d).1 with
  | none => exact False.elim (search_ne_none hd hs)
  | some c =>
      rw [← hv, hs]
      simp only [coefficients, hs, Option.getD_some]

theorem find_encoded_eq_coefficients {d : ℕ} (hd : 0 < d)
    (check : List Bool → Bool)
    (hcheck : ∀ c : Fin d → F, check (encodeTuple (scalarCode 3) c) = passes c) :
    ((candidates d).map (encodeTuple (scalarCode 3))).find? check =
      some (encodeTuple (scalarCode 3) (coefficients d)) := by
  rw [List.find?_map]
  have he : check ∘ encodeTuple (scalarCode 3) = (passes : (Fin d → F) → Bool) := by
    funext c
    exact hcheck c
  rw [he, find_candidates_eq_coefficients hd]
  rfl

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native irreducible-polynomial search: concrete factor callbacks,
saved universal scans, exact ordered candidate selection, and measured cost. -/

/-! A fixed factor-pair callback and universal scan. All checker arithmetic,
record extraction, array splitting, and cleanup use explicit bit programs. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

open BitProgram StructuredCalls IrreducibleSearchProgram
open Subexp.BlockSearchPreparation (restrictState lifted_call)
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

theorem embed_wide (before after : State 16 18) (tag present found : Bool)
    (source payload saved count extra : List Bool) :
    embedState lowRegs lowStacks (wide before tag present found source payload saved count extra)
      after = wide after tag present found source payload saved count extra := by
  apply SubexpScanPrimitives.embedState_eq lowRegs lowStacks lowRegs_injective lowStacks_injective
  · intro i; simp [wide, lowRegs]
  · intro i; simp [wide, lowStacks]
  · intro j hj
    revert hj
    refine Fin.addCases (m := 16) (n := 3) (fun i => ?_) (fun i => ?_) j
    · intro hi; exact (hi ⟨i,rfl⟩).elim
    · intro _; simp [wide]
  · intro j hj
    revert hj
    refine Fin.addCases (m := 18) (n := 6) (fun i => ?_) (fun i => ?_) j
    · intro hi; exact (hi ⟨i,rfl⟩).elim
    · intro _; simp [wide]

def Ready {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (depth count saved extra : List Bool) (base : Data) : Prop :=
  ∃ regs tag present found source payload,
    base = wide (pairState [] [] (List.ofFn c) depth [] [] [] regs)
      tag present found source payload saved count extra

end SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

/-! Fixed first-success scan using the concrete saved factor checker. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

open BitProgram StructuredCalls IrreducibleSearchProgram
open Subexp.BlockSearchPreparation (restrictState lifted_call)
open SubexpEnumerationPayload SubexpTupleRefinement
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

def Ready (d : ℕ) (depth count extra : List Bool) (base : Data) : Prop :=
  ∃ old : List IrreducibleSearch.F, old.length ≤ d ∧
    ∃ regs it ip iff ot op ofd source payload,
      base = wide (readyLow old depth count d regs it ip iff) ot op ofd source payload extra

theorem Ready.record_state {d : ℕ} {depth count extra : List Bool} {base : Data}
    (h : Ready d depth count extra base) (v pr f : Bool) (source payload : List Bool) :
    Ready d depth count extra (RecordPrograms.state ports base v pr f source payload) := by
  obtain ⟨old, hold, regs, it, ip, found, ot, op, ofd, src, out, rfl⟩ := h
  rw [record_state_wide]
  exact ⟨old, hold, regs, it, ip, found, v, pr, f, source, payload, rfl⟩

def input (d : ℕ) (depth count extra : List Bool) : Data :=
  wide (readyLow [] depth count d (fun _ => false) false false false)
    false false false (ProgramEncoding.encodeRecords (candidateRecords d)) [] extra

end SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrap
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open BitProgram StructuredCalls
open SubexpEnumerationPayload SubexpTupleRefinement IrreducibleSearchProgram
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

theorem input_eq (depth : List Bool) : input depth =
    state depth [] [] [] [] [] (fun _ => false) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> simp [ layout]


end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The supplied ring model uses the polynomial actually found by search
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

/-- Execution coefficients with their proved irreducibility certificate. -/
def data {d : ℕ} (hd : 0 < d) : RingModel.Data d where
  coefficients := coefficients d
  irreducible := coefficients_irreducible hd

@[simp] theorem data_coefficients {d : ℕ} (hd : 0 < d) :
    (data hd).coefficients = coefficients d := rfl

end SubexponentialSAT.SqrtLog.IrreducibleSearch

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
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev WideCode := Cmd 8 40

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


