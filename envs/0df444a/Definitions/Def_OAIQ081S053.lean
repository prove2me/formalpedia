-- Prove2me | Definitions.Def_OAIQ081S053
-- name    : OAIQ081S053
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:42:00.990791+00:00
-- url     : https://prove2.me/theorems/94016365-35fb-4c7e-86ed-65c42f8f8fcd
-- title:
--   Definitions bundle OAIQ081S053 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 73 declarations of OpenAI's Lean: 43 definitions, 1 inductive type or structure and 29 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.finishedStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.codeRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.instructionRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.Clean`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.modelScaledBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.modelSignedBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.polynomialBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.scanState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.negativeBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.negativeTableBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap.clearCmd`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap.input`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl.clearCandidate`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl.savedPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl.split`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchPairAdapter.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchPairAdapter.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.candidateCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.pairTailCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.clearIndex`, `OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPreparation.restrictState`, `OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchProgram.SavedPorts`, `OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchProgram.allCommand`, `OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchProgram.anyCommand`, `OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchProgram.negateResult`, `OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchProgram.savedAllCommand`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectorMapProgram.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram.Ready`, `OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram.appendEncoded`, `OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram.extendOutput`, `OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram.innerInvariant`, `OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram.innerPorts`, `OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram.outerInvariant`, `OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram.outerPorts`, `OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram.readDepthState`, `OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram.tuplePorts` and 4 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramFinish`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramPreparedTable`, `SubexponentialSAT_SqrtLog_IdempotentProgramTrace`, `SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramLookup`, `SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramValue`, `SubexponentialSAT_SqrtLog_IntegerRingLiftProgram`, `SubexponentialSAT_SqrtLog_IntegerRingLiftProgramModel`, `SubexponentialSAT_SqrtLog_IntegerRingLiftProgramPrimitive`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramNative`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramTables`, `SubexponentialSAT_SqrtLog_IrreducibleSearch`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBasic`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrap`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapPrimitives`, `SubexponentialSAT_SqrtLog_IrreducibleSearchCompanionList`, `SubexponentialSAT_SqrtLog_IrreducibleSearchFactorEnumeration`, `SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan`, `SubexponentialSAT_SqrtLog_IrreducibleSearchPairAdapter`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgram`, `SubexponentialSAT_SqrtLog_LayoutProgramScalar`, `SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram`, `SubexponentialSAT_SqrtLog_RingModel`, `SubexponentialSAT_SubexpNormalizeProgram`, `SubexponentialSAT_SubexpOrderedTupleData`, `SubexponentialSAT_SubexpPostfixControl`, `SubexponentialSAT_SubexpScanPrimitives`, `SubexponentialSAT_SubexpSetupStorage`, `SubexponentialSAT_Subexp_BlockSearchPreparation`, `SubexponentialSAT_Subexp_BlockSearchProgram`, `SubexponentialSAT_Subexp_SelectorMapProgram`, `SubexponentialSAT_Subexp_TupleProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S023`, `OAIQ081S024`, `OAIQ081S025`, `OAIQ081S027`, `OAIQ081S028`, `OAIQ081S029`, `OAIQ081S030`, `OAIQ081S031`, `OAIQ081S032`, `OAIQ081S033` and `OAIQ081S035` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S069`, `OAIQ081S070`, `OAIQ081S071`, `OAIQ081S072`, `OAIQ081S073`, `OAIQ081S074`, `OAIQ081S075`, `OAIQ081S078`, `OAIQ081S079` and `OAIQ081S080`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S024
import Definitions.Def_OAIQ081S025
import Definitions.Def_OAIQ081S027
import Definitions.Def_OAIQ081S028
import Definitions.Def_OAIQ081S029
import Definitions.Def_OAIQ081S030
import Definitions.Def_OAIQ081S031
import Definitions.Def_OAIQ081S032
import Definitions.Def_OAIQ081S033
import Definitions.Def_OAIQ081S035

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

def afterReverse {r s : ℕ} (d : State r s) (src : Fin s) (v p : Fin r) : State r s :=
  ⟨readRegs d.regs v p none, StackRoutines.reverseStacks src d.stacks⟩

end SubexponentialSAT.SubexpScanPrimitives

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramTrace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed four-register Newton instruction stream and its exact execution
relation. Registers contain coefficient arrays at the intended instantiation.
This is an arithmetic-register trace, not yet a native Boolean-stack trace. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost

variable {C R : Type*} [CommRing R]

def instructionRun (ops : RingProgram C) (i : ArithmeticInstruction)
    (state : Registers C) : Registers C × ℕ :=
  match i with
  | .add dst left right =>
      let out := ops.addRun (state left) (state right)
      (Function.update state dst out.1, out.2+1)
  | .mul dst left right =>
      let out := ops.mulRun (state left) (state right)
      (Function.update state dst out.1, out.2+1)
  | .neg dst src =>
      let out := ops.negRun (state src)
      (Function.update state dst out.1, out.2+1)

def codeRun (ops : RingProgram C) : List ArithmeticInstruction → Registers C → Registers C × ℕ
  | [], state => (state, 0)
  | i::is, state =>
      let next := instructionRun ops i state
      let rest := codeRun ops is next.1
      (rest.1, next.2+rest.2)

theorem codeRun_append (ops : RingProgram C) (xs ys : List ArithmeticInstruction)
    (state : Registers C) :
    codeRun ops (xs++ys) state =
      ((codeRun ops ys (codeRun ops xs state).1).1,
        (codeRun ops xs state).2+(codeRun ops ys (codeRun ops xs state).1).2) := by
  induction xs generalizing state with
  | nil => simp [codeRun]
  | cons i xs ih =>
      simp only [List.cons_append, codeRun, ih]
      simp only [Nat.add_assoc]

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

open BitProgram StructuredCalls

theorem popLookup (r : Fin 8 → Bool) (xs ys zs bs : List Bool) :
    Eval (.base (.atom (.pop 2 0 1))) 1 (data r xs ys zs bs)
      (data (readRegs r 0 1 zs.head?) xs ys zs.tail bs) := by
  convert Eval.base (StructuredProgram.Eval.atom (.pop 2 0 1)
    (data r xs ys zs bs)) using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [data,
      StructuredProgram.Atom.instr,execInstr]

end SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramValue
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

open IdempotentProgram

theorem entryCode_correct {t : ℕ} (i j k : Fin (3*t)) :
    codeValue (entryCode i.val j.val k.val) = hadicTable i j k := by
  have ha : i.val%3+j.val%3 ≤ 4 := by omega
  by_cases hk : k.val < 3*(i.val/3+j.val/3)
  · have h0 : k.val ≠ 3*(i.val/3+j.val/3)+(i.val%3+j.val%3) := by omega
    have h1 : k.val ≠ 3*(i.val/3+j.val/3)+1 := by omega
    have h2 : k.val ≠ 3*(i.val/3+j.val/3)+2 := by omega
    have h3 : k.val ≠ 3*(i.val/3+j.val/3+1) := by omega
    have h4 : k.val ≠ 3*(i.val/3+j.val/3+1)+1 := by omega
    simp [entryCode,hk,codeValue,hadicTable,atomInteger,h0,h1,h2,h3,h4]
  · rw [entryCode,ite_eq_right hk,coefficientsAt_value _ ha]
    have h0 : k.val-3*(i.val/3+j.val/3) = i.val%3+j.val%3 ↔
        k.val = 3*(i.val/3+j.val/3)+(i.val%3+j.val%3) := by omega
    have h1 : k.val-3*(i.val/3+j.val/3) = 1 ↔
        k.val = 3*(i.val/3+j.val/3)+1 := by omega
    have h2 : k.val-3*(i.val/3+j.val/3) = 2 ↔
        k.val = 3*(i.val/3+j.val/3)+2 := by omega
    have h3 : k.val-3*(i.val/3+j.val/3) = 3 ↔
        k.val = 3*(i.val/3+j.val/3+1) := by omega
    have h4 : k.val-3*(i.val/3+j.val/3) = 4 ↔
        k.val = 3*(i.val/3+j.val/3+1)+1 := by omega
    simp only [h0,h1,h2,h3,h4,hadicTable,atomInteger]

end SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

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

theorem entrySource_eq_scalar (c : Fin 6) :
    entrySource c = Scalar.port (Scalar.tableRegister c) := by
  fin_cases c <;> rfl

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpQuarticRing

def finishedStacks (s : Fin 41 → List Bool) (t : ℕ) (table : List Bool) : Fin 41 → List Bool :=
  fun i => if i ∈ preparationDiscard then [] else (arrayStacks (Function.update s 22 table) t) i

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

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
open CRTLocalProgram (LowFrame lowFrame_update lowFrame_refl
  CachePort)

def scanState {C : Type*} (base : Store) (encode : C → List Bool)
    (bs : List Bool) (a p : C) : Store :=
  Function.update (Function.update (Function.update base 246 bs) 247 (encode a)) 248 (encode p)

def Clean (s : Store) : Prop :=
  s 120 = [] ∧ s 240 = [] ∧ s 241 = [] ∧ s 244 = [] ∧ s 245 = []

theorem clean_scanState {C : Type*} (base : Store) (encode : C → List Bool)
    (bs : List Bool) (a p : C) (h : Clean base) : Clean (scanState base encode bs a p) := by
  simpa [Clean, scanState] using h

theorem frame_scanState {C : Type*} (base : Store) (encode : C → List Bool)
    (bs : List Bool) (a p : C) : LowFrame base (scanState base encode bs a p) :=
  lowFrame_update (lowFrame_update (lowFrame_update (lowFrame_refl base)
    246 (by decide) _) 247 (by decide) _) 248 (by decide) _

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Unramified ring attached to a supplied irreducible ternary polynomial

`Data.coefficients` is execution data. An irreducible-search correctness proof
can supply `Data.irreducible`; no separate choice of a minimum polynomial is
made in this model. All polynomial lifts use coefficient representatives.
-/

noncomputable section
namespace SubexponentialSAT.SqrtLog.RingModel

open Polynomial

namespace Data

variable {d : ℕ} (a : Data d) (t : ℕ)

theorem residuePolynomial_irreducible : Irreducible a.residuePolynomial := a.irreducible

end Data

end SubexponentialSAT.SqrtLog.RingModel

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite coefficient tests for arbitrary-degree irreducible search

Only vectors, finite lists, and scalar arithmetic are executed. `ofFn` and
the polynomial interpretation occur solely in the correctness proofs.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open Polynomial
open scoped BigOperators

theorem convolution_eq_coeff {R : Type*} [CommSemiring R] [DecidableEq R] {n : ℕ}
    (a b : Fin n → R) (j : ℕ) :
    convolution a b j = (Polynomial.ofFn n a * Polynomial.ofFn n b).coeff j := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y => (Polynomial.ofFn n a).coeff x * (Polynomial.ofFn n b).coeff y) j]
  simp only [ofFn_coeff_entry, convolution]

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IntegerRingLiftProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete, fixed native programs lifting a pair of arbitrary little-endian
binary words to the actual RingModel. There is no integer-lifting callback.
The only runtime constants are explicit represented ring caches. -/
namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open CRTLocalProgram (lowFrame_refl)

def modelSignedBudget (bits t d : ℕ) : ℕ :=
  signedBudget bits (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
    (HornerProgram.Services.addBudget (baseWidth 3 t) d) (d * baseWidth 3 t)
def modelScaledBudget (bits t d : ℕ) : ℕ :=
  scaledBudget bits (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
    (HornerProgram.Services.addBudget (baseWidth 3 t) d) (d * baseWidth 3 t)

theorem modelSignedBudget_le_scaled (bits t d : ℕ) :
    modelSignedBudget bits t d ≤ modelScaledBudget bits t d := by
  unfold modelSignedBudget modelScaledBudget scaledBudget
  omega

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IntegerRingLiftProgramPrimitive
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Primitive bit-machine refinement. All instruction tables are fixed,
including their simulation overhead; input integer magnitudes are never loop
bounds. The sole nonconstant scan count is the total input word length. -/
namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def polynomialBudget (bits t d : ℕ) : ℕ :=
  bits * (100000*(d+1)^3*(baseWidth 3 t+1)^2 + 80*d*baseWidth 3 t + 110) +
    200000*(d+1)^3*(baseWidth 3 t+1)^2 + 203*d*baseWidth 3 t + 251

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual finite arithmetic subprograms used in the cache scans. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing

def negativeBudget (t d : ℕ) :=
  HornerProgram.Services.mulBudget (baseWidth 3 t) d + 40*(d*baseWidth 3 t)+51

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

def negativeTableBudget (t d Q : ℕ) :=
  nodeScanBudget (negativeBudget t d) (d*baseWidth 3 t) Q+9*(Q*(d*baseWidth 3 t))+7

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

theorem mem_candidates (d : ℕ) (c : Fin d → F) : c ∈ candidates d :=
  QuarticSearch.mem_vectors _ (QuarticSearch.mem_elements 3) d c

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control Cartesian tuple generation

Alphabet words, tuple payloads, and iteration depths are stack data.  The
instruction tables below do not depend on any of their lengths.
-/

namespace SubexponentialSAT.Subexp.TupleProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem frame_eq_escaped (bits : List Bool) :
    Encoding.frame bits = escaped bits ++ [false] := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [Encoding.frame_cons, ih]

theorem escapeProgram_trace (bits out : List Bool) (v pr : Bool) :
    Trace escapeProgram (5 * bits.length + 3)
      (ParserProgram.cfg (some 0) v pr bits out)
      (ParserProgram.cfg none false false [] (escaped bits.reverse ++ out)) := by
  induction bits generalizing out v pr with
  | nil =>
      refine .cons (b := ParserProgram.cfg (some 1) false false [] out) ?_ ?_
      · simp [step, ParserProgram.cfg, execInstr, readRegs]
      refine .cons (b := ParserProgram.cfg (some 5) false false [] out) ?_ ?_
      · simp [step, ParserProgram.cfg, execInstr]
      refine .cons ?_ (.refl _)
      simp [step, ParserProgram.cfg, execInstr]
  | cons b bits ih =>
      have t := ih (true :: b :: out) true true
      have cycle : Trace escapeProgram 5
          (ParserProgram.cfg (some 0) v pr (b :: bits) out)
          (ParserProgram.cfg (some 0) true true bits (true :: b :: out)) := by
        refine .cons (b := ParserProgram.cfg (some 1) b true bits out) ?_ ?_
        · simp [step, ParserProgram.cfg, execInstr, readRegs]
        refine .cons (b := ParserProgram.cfg (some 2) b true bits out) ?_ ?_
        · simp [step, ParserProgram.cfg, execInstr]
        refine .cons (b := ParserProgram.cfg (some 3) b true bits (b :: out)) ?_ ?_
        · simp [step, ParserProgram.cfg, execInstr]
        refine .cons (b := ParserProgram.cfg (some 4) true true bits (b :: out)) ?_ ?_
        · simp [step, ParserProgram.cfg, execInstr]
        refine .cons ?_ (.refl _)
        simp [step, ParserProgram.cfg, execInstr]
      convert cycle.trans t using 1 <;>
        simp [List.reverse_cons, List.append_assoc] ; omega

theorem copy_eval {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (a : State r s) (ht : a.stacks tmp = []) :
    Eval (.call (StackRoutines.copyProgram src dst tmp value present))
      (7 * (a.stacks src).length + 5) a
      ⟨readRegs a.regs value present none, StackRoutines.copyStacks src dst a.stacks⟩ := by
  apply Eval.call
  have h := StackRoutines.halt_after_trace _
    (StackRoutines.copyProgram_trace src dst tmp value present hsd hst htd hvp
      a.regs a.stacks ht) 7 rfl rfl
  simpa [StructuredProgram.State.withPC, StackRoutines.copyResult,
    StackRoutines.copyProgram, Nat.add_assoc] using h

/-! The fixed ABI uses ten Boolean registers and nine Boolean stacks:
0 prior tuples, 1 saved alphabet, 2 current reversed tuple, 3 alphabet cursor,
4 reversed word, 5 output, 6 copied tuple, 7 copy scratch, 8 unary depth.
Registers 0--2 and 3--5 belong to the two framed iterators, 6--7 are scratch,
and 8--9 belong to the eventual depth loop. -/

def outerPorts : RecordPrograms.Ports 10 9 :=
  ⟨0, 1, 2, 0, 2, by decide, by decide, by decide, by decide⟩

def innerPorts : RecordPrograms.Ports 10 9 :=
  ⟨3, 4, 5, 3, 4, by decide, by decide, by decide, by decide⟩

def wordPorts : RecordPrograms.Ports 10 9 :=
  ⟨6, 7, 8, 4, 5, by decide, by decide, by decide, by decide⟩

def tuplePorts : RecordPrograms.Ports 10 9 :=
  ⟨6, 7, 8, 6, 5, by decide, by decide, by decide, by decide⟩

def innerInvariant (alphabet : List Bool) (tuple tail depth : List Bool) (guard : Bool)
    (a : State 10 9) : Prop :=
  a.stacks 1 = alphabet ∧ a.stacks 2 = tuple.reverse ∧ a.stacks 0 = tail ∧
  a.stacks 6 = [] ∧ a.stacks 7 = [] ∧ a.stacks 8 = depth ∧
  a.regs 0 = false ∧ a.regs 1 = true ∧ a.regs 2 = false ∧ a.regs 9 = guard

theorem unread_false (records : Records) (suffix : List Bool) :
    RecordPrograms.unread (fun _ => false) records suffix = suffix := by
  induction records <;> simp_all [RecordPrograms.unread]

def outerInvariant (alphabet : Records) (depth : List Bool) (guard : Bool)
    (a : State 10 9) : Prop :=
  a.stacks 1 = ProgramEncoding.encodeRecords alphabet ∧
  a.stacks 3 = [] ∧ a.stacks 4 = [] ∧ a.stacks 6 = [] ∧ a.stacks 7 = [] ∧
  a.stacks 8 = depth ∧ a.regs 9 = guard

def extendOutput (alphabet : Records) (tuple out : List Bool) : List Bool :=
  alphabet.foldl (fun out word => prependRecord (tuple ++ word) out) out

def appendEncoded (records : Records) (out : List Bool) : List Bool :=
  records.foldr prependRecord out

theorem appendEncoded_encodeRecords (xs ys : Records) :
    appendEncoded xs (ProgramEncoding.encodeRecords ys) =
      ProgramEncoding.encodeRecords (xs ++ ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [appendEncoded, prependRecord, ProgramEncoding.encodeRecords,
      Encoding.encodeList] at ih ⊢; exact ih

theorem fold_prependRecord (xs : Records) (out : List Bool) :
    xs.foldl (fun out bits => prependRecord bits out) out = appendEncoded xs.reverse out := by
  simp [appendEncoded, List.foldr_reverse ]

theorem fold_extendOutput (tuples alphabet : Records) (out : List Bool) :
    tuples.foldl (fun out tuple => extendOutput alphabet tuple out) out =
      appendEncoded (cartesianOutput tuples alphabet) out := by
  rw [cartesianOutput, ← fold_prependRecord]
  induction tuples generalizing out with
  | nil => rfl
  | cons tuple tuples ih =>
      simp only [List.foldl_cons, List.flatMap_cons, List.foldl_append]
      simpa only [List.foldl_map, extendOutput] using ih (extendOutput alphabet tuple out)

def Ready (alphabet rows : Records) (depth : List Bool) (guard : Bool)
    (a : State 10 9) : Prop :=
  outerInvariant alphabet depth guard a ∧
  a.stacks 0 = ProgramEncoding.encodeRecords rows ∧ a.stacks 2 = [] ∧ a.stacks 5 = [false]

abbrev readDepthState (a : State 10 9) : State 10 9 :=
  ⟨readRegs a.regs 8 9 (a.stacks 8).head?, Function.update a.stacks 8 (a.stacks 8).tail⟩

end SubexponentialSAT.Subexp.TupleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BlockSearchPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed preparation of candidate tables, split dimensions, and coefficient
tuples for the universal block search. All three dimensions are runtime data. -/

namespace SubexponentialSAT.Subexp.BlockSearchPreparation

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def restrictState {r s R S : ℕ} (ρ : Fin r → Fin R) (σ : Fin s → Fin S)
    (a : State R S) : State r s := ⟨a.regs ∘ ρ, a.stacks ∘ σ⟩

end SubexponentialSAT.Subexp.BlockSearchPreparation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPostfixControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

/-! ## Serialization of the existing postfix instruction type -/

/-! ## Literal-push service with the framed-list operand ABI -/

theorem escapeBits_append (a b : List Bool) :
    escapeBits (a ++ b) = escapeBits a ++ escapeBits b := by
  induction a with
  | nil => rfl
  | cons a as ih => simp [escapeBits, ih]

theorem frame_eq_escape (bits : List Bool) :
    Encoding.frame bits = escapeBits bits ++ [false] := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [Encoding.frame_cons, escapeBits, ih]

end SubexponentialSAT.SubexpPostfixControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

/-! ## A complete record-order reversal pass

Prepending accepted records reverses their order. This second, unconditional
pass restores the order required by `List.filter` and the executable
sparsifier. It reverses the records, never the bits within a record.
-/

def PrependEffect (bits : List Bool)
    (before after : StructuredProgram.State 3 4) : Prop :=
  after.stacks 1 = before.stacks 1 ∧
    after.stacks 2 = true :: (Encoding.frame bits ++ before.stacks 2)

@[simp] theorem unread_false (records : List (List Bool)) (suffix : List Bool) :
    RecordPrograms.unread (fun _ => false) records suffix = suffix := by
  induction records with
  | nil => rfl
  | cons bits records ih => simpa [RecordPrograms.unread] using ih

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpOrderedTupleData
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! # Exact lexicographic tuple order for the selected quartic search -/

namespace SubexponentialSAT.SubexpOrderedTupleData

open SubexpTupleRefinement

def orderedRows (alphabet : List (List Bool)) : ℕ → List (List Bool) → List (List Bool)
  | 0, rows => rows
  | n + 1, rows => orderedRows alphabet n (orderedCartesian rows alphabet)

theorem orderedRows_eq (alphabet rows : List (List Bool)) (n : ℕ) :
    orderedRows alphabet n rows =
      rows.flatMap fun pre => (QuarticSearch.vectors alphabet n).map
        (fun v => pre ++ tuplePayload v) := by
  induction n generalizing rows with
  | zero => simp [orderedRows, QuarticSearch.vectors, tuplePayload]
  | succ n ih =>
      rw [orderedRows, ih]
      simp only [orderedCartesian, QuarticSearch.vectors, List.flatMap_assoc,
        List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def,
        tuplePayload_cons, List.append_assoc]

theorem orderedRows_empty (alphabet : List (List Bool)) (n : ℕ) :
    orderedRows alphabet n [[]] = (QuarticSearch.vectors alphabet n).map tuplePayload := by
  simpa using orderedRows_eq alphabet [[]] n

theorem orderedRows_encoded {A : Type*} (code : StackEncoding.BlockCode A)
    (alphabet : List A) (n : ℕ) :
    orderedRows (alphabet.map code.block) n [[]] =
      (QuarticSearch.vectors alphabet n).map (encodeTuple code) := by
  rw [orderedRows_empty, vectors_map]
  simp only [List.map_map, Function.comp_def, tuplePayload_map]

@[simp] theorem orderedRows_empty_length (alphabet : List (List Bool)) (n : ℕ) :
    (orderedRows alphabet n [[]]).length = alphabet.length ^ n := by
  rw [orderedRows_empty, List.length_map, QuarticSearch.length_vectors]

end SubexponentialSAT.SubexpOrderedTupleData

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed word loading and framed stack routines for the search bootstrap. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open BitProgram StructuredCalls

abbrev Data := State 22 28

theorem copyCmd_eval (src dst : Fin 28) (a : Data)
    (hsd : src ≠ dst) (hs7 : src ≠ 7) (h7d : (7 : Fin 28) ≠ dst)
    (h7 : a.stacks 7 = []) :
    Eval (copyCmd src dst) (7 * (a.stacks src).length + 5) a
      ⟨readRegs a.regs 0 1 none,
        Function.update a.stacks dst (a.stacks src ++ a.stacks dst)⟩ := by
  exact Subexp.TupleProgram.copy_eval src dst 7 0 1 hsd hs7 h7d (by decide) a h7

abbrev clearCmd (src : Fin 28) : Cmd 22 28 :=
  .call (StackRoutines.clearProgram src 0 1)

end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BlockSearchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed control for the universal-block finite search

The commands in this file scan runtime framed lists. Their finite control
depends on the supplied finite predicate program and fixed ports, never on
the block dimension, field size, or list lengths. Predicate specifications
are measured `StructuredCalls.Eval` contracts for actual finite code.
-/

namespace SubexponentialSAT.Subexp.BlockSearchProgram

open BitProgram StructuredCalls

/-- Negate the predicate-result register using two actual instructions. -/
abbrev negateResult {r s : ℕ} (p : RecordPrograms.Ports r s) : Cmd r s :=
  .ite p.found (RecordPrograms.atom (.set p.found false))
    (RecordPrograms.atom (.set p.found true))

abbrev anyCommand {r s : ℕ} (p : RecordPrograms.Ports r s) (predicate : Cmd r s) : Cmd r s :=
  RecordPrograms.iterate p predicate

abbrev allCommand {r s : ℕ} (p : RecordPrograms.Ports r s) (predicate : Cmd r s) : Cmd r s :=
  .seq (RecordPrograms.iterate p (.seq predicate (negateResult p))) (negateResult p)

/-- The saved enumeration is copied for each quantifier invocation. -/
structure SavedPorts (r s : ℕ) extends RecordPrograms.Ports r s where
  saved : Fin s
  temporary : Fin s
  saved_ne_source : saved ≠ source
  saved_ne_payload : saved ≠ payload
  temporary_ne_source : temporary ≠ source
  temporary_ne_payload : temporary ≠ payload
  saved_ne_temporary : saved ≠ temporary

abbrev savedAllCommand {r s : ℕ} (p : SavedPorts r s) (predicate : Cmd r s) : Cmd r s :=
  .seq (.call (StackRoutines.copyProgram p.saved p.source p.temporary p.tag p.present))
    (.seq (allCommand p.toPorts predicate)
      (.seq (.call (StackRoutines.clearProgram p.source p.tag p.present))
        (RecordPrograms.atom (.set p.present true))))

/-! A full-dimensional candidate needs only universal scalar tests. -/

open scoped BigOperators
open SubexponentialSAT.QuarticSearch

end SubexponentialSAT.Subexp.BlockSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchFactorEnumeration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed tuple-generation call produces all concatenated factor pairs. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open SubexpOrderedTupleData SubexpTupleRefinement SubexpEnumerationPayload

theorem orderedRows_add (alphabet : List (List Bool)) (n m : ℕ)
    (rows : List (List Bool)) :
    orderedRows alphabet (n + m) rows =
      orderedRows alphabet m (orderedRows alphabet n rows) := by
  induction n generalizing rows with
  | zero => simp [orderedRows]
  | succ n ih =>
      simpa only [Nat.succ_add, orderedRows] using ih (orderedCartesian rows alphabet)

theorem orderedRows_from_rows (alphabet : List (List Bool)) (n : ℕ)
    (rows : List (List Bool)) :
    orderedRows alphabet n rows =
      rows.flatMap (fun pre => (orderedRows alphabet n [[]]).map (pre ++ ·)) := by
  rw [orderedRows_eq, orderedRows_empty]
  simp only [List.map_map, Function.comp_def]

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical storage operations for the closed parameter setup

All copies, clears, and register resets are fixed instruction sequences or
calls to proved bit programs. Their state transformations below are assertion
notation only. The setup program uses them to isolate dirty arithmetic
subroutines from the persistent parameter words.
-/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem copy_eval {S : ℕ} (src dst tmp : Fin S) (a : Data S)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (ht : a.stacks tmp = []) :
    Eval (copyCmd src dst tmp) (7 * (a.stacks src).length + 5) a (copyState src dst a) := by
  apply Eval.call
  exact ListRegisterProgram.copy_run src dst tmp (0 : Fin 16) 1
    hsd hst htd (by decide) a.regs a.stacks ht

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchPairAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed physical split of a concatenated pair of coefficient arrays. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchPairAdapter

open BitProgram StructuredCalls SubexpSetupStorage IrreducibleSearchProgram

abbrev command : Cmd 16 6 :=
  .seq (copyCmd 1 2 5) (.seq (prefixCall registers firstPorts)
    (.seq (copyCmd 1 2 5) (prefixCall registers secondPorts)))
def program := compiled command 0 4

end SubexponentialSAT.SqrtLog.IrreducibleSearchPairAdapter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed fixed-bit F₃ factor checker. The complete command is independent
of the degree. All coefficient addresses and loop bounds are runtime unary
words; source vectors are preserved and scratch stacks are discharged. -/


/-! Coefficient -/

/-! A fixed coefficient kernel: two preserved source arrays, a preserved
unary coefficient address plus one, and an output stack. Every copy, padded
prefix, coefficient reversal, multiply-add and cleanup is an actual call. -/


/-! CoefficientRun -/

/-! The closed, fixed-program boundary for one arbitrary convolution
coefficient. Its sources and runtime unary address are preserved and all
work stacks are empty again. -/


/-! ProductLift -/

/-! A framed invocation of the source-preserving coefficient kernel. The
extra stack stores the remaining runtime product length. -/


/-! Product -/

/-! A fixed outer loop runs the coefficient kernel at successively longer
unary addresses. Source arrays are preserved; all output coefficients are
physically written in decreasing degree order. -/


/-! ProductRun -/


/-! Monic -/

/-! Appending the implicit monic coefficient uses two physical transfers.
No input-dependent instruction table or uncharged array append is used. -/


/-! MonicAlgebra -/


/-! CheckLift -/

/-! Framed calls to the physical Boolean predicates. -/


/-! PairProduct -/


/-! Candidate -/

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open SubexponentialSAT.StructuredProgram (Atom)

abbrev candidateCommand : Cmd 16 18 :=
  .seq (copyCmd 13 15 17) <| .seq (appendOneCommand 15 3) <|
  .seq (copyCmd 14 5 17) <| .seq (copyCmd 14 5 17) <|
  .seq (.base (atomsCommand candidateCountAtoms)) (prefixCall sixRegisters candidatePorts)

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram


/-! ProductCheck -/


/-! Pair -/

/-! Closed primitive pair test. All three source vectors and the runtime
unary degree are preserved. The return bit is exactly the scalar pairPass. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open SubexponentialSAT.StructuredProgram (Atom)

abbrev pairTailCommand : Cmd 16 18 :=
  .seq (.base (.atom (.push 12 3))) <| .seq (copyCmd 0 3 17) <|
  .seq (nonconstantCall 3) <| .seq (.base (.atom (.push 12 3))) <|
  .seq (copyCmd 1 3 17) <| .seq (nonconstantCall 3) (.base (atomsCommand pairFlagsAtoms))

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

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
open Subexp.BlockSearchPreparation (restrictState )
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

def ports : RecordPrograms.Ports 19 24 :=
  ⟨16,17,18,18,19,by decide,by decide,by decide,by decide⟩

abbrev split : Cmd 19 24 := .call (ProgramLinking.liftProgram
  IrreducibleSearchPairAdapter.program lowRegs splitStacks)

def savedPorts : Subexp.BlockSearchProgram.SavedPorts 19 24 where
  toPorts := ports
  saved := 20
  temporary := 21
  saved_ne_source := by decide
  saved_ne_payload := by decide
  temporary_ne_source := by decide
  temporary_ne_payload := by decide
  saved_ne_temporary := by decide

end SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

/-! Fixed first-success scan using the concrete saved factor checker. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

open BitProgram StructuredCalls IrreducibleSearchProgram
open Subexp.BlockSearchPreparation (restrictState )
open SubexpEnumerationPayload SubexpTupleRefinement
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

def ports : RecordPrograms.Ports 22 28 :=
  ⟨19,20,21,24,25,by decide,by decide,by decide,by decide⟩

abbrev clearCandidate : Cmd 22 28 := .call (StackRoutines.clearProgram 13 19 20)

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

/-- The actual machine input has only its unary depth stack populated. -/
def input (depth : List Bool) : Data := StructuredProgram.ioState 14 depth


end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchCompanionList
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A sequential list implementation of one companion-matrix step. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

variable {R : Type*} [Ring R]

theorem companionScan_eq_mulX {d : ℕ} (c a : Fin d → R) :
    companionScan (entry a (d - 1)) 0 (List.ofFn (fun i => (c i, a i))) =
      List.ofFn (mulX c a) := by
  rw [companionScan_ofFn]
  apply congrArg List.ofFn
  funext i
  unfold mulX
  by_cases hi : i.val = 0
  · simp [hi]
  · simp [hi, entry, show i.val - 1 < d by omega]

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete arithmetic adapters for the cached layout scalar loop.
The working signed pair occupies 0/1, the next operand 2/3, the record queue
15, and the saved sum 16/17. All arithmetic is an actual compiled bit program.
-/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

abbrev Data := State 8 18

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


-- LayoutTriplePreparationProgramLookup.lean

/-! List-level cache representation for the preserving physical array scan. -/

/-! One real triple-production iteration: two scans, three serializers and
paid cleanup. Only a parity bit is kept outside the subroutine registers. -/

/-! A fixed, paid iteration producing the three real scalar operands. -/

/-! The native unary loop produces all triples in increasing binomial index. -/

/-! Initial unary copy/parity and final stream reversal are native paid calls. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

def clearIndex : Code := .call (StackRoutines.clearProgram 9 0 1)

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgram.lean

/-! Complete cache-to-triple primitive program with all scans and copies paid. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorMapProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed loop applying the selected-index map to query records

The selector uses ports 0--5.  Port 6 is the framed query cursor, port 7
preserves the raw key/payload table, and port 8 accumulates framed answers.
Answers are prepended, so the returned record list reverses query order.
-/

namespace SubexponentialSAT.Subexp.SelectorMapProgram

open BitProgram StructuredCalls

abbrev Data := State 8 9

end SubexponentialSAT.Subexp.SelectorMapProgram

end OAI.Algorithms
end


