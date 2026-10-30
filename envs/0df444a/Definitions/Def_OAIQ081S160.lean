-- Prove2me | Definitions.Def_OAIQ081S160
-- name    : OAIQ081S160
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:03:52.371984+00:00
-- url     : https://prove2.me/theorems/d3d8beea-1daa-44b8-977f-b0e8643ce7e7
-- title:
--   Definitions bundle OAIQ081S160 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 33 declarations of OpenAI's Lean: 21 definitions and 12 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide.parameterStore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.clearLowBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.coreBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.dataMass`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.selectionBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.selectionSize`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.suffix`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.suffixBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift.work`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.coreBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingPrefixProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingPrefixProgram.multiply`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingPrefixProgram.prepare`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingPrefixProgram.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.headSetup`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.heads`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.preparePrefix`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.literalPorts`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputProgram.outputState`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_FactorTableProgram`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsLoader`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsSelection`, `SubexponentialSAT_SqrtLog_PackingCallerProgramCleanup`, `SubexponentialSAT_SqrtLog_PackingCallerProgramCore`, `SubexponentialSAT_SqrtLog_PackingCallerProgramExportFacts`, `SubexponentialSAT_SqrtLog_PackingCallerProgramSelect`, `SubexponentialSAT_SqrtLog_PackingCallerProgramStage`, `SubexponentialSAT_SqrtLog_PackingCallerProgramSuffix`, `SubexponentialSAT_SqrtLog_PackingCallerProgramWide`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_PackingLoaderProgram`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramBounds`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramCore`, `SubexponentialSAT_SqrtLog_PackingPrefixProgram`, `SubexponentialSAT_SqrtLog_PackingPrefixProgramLift`, `SubexponentialSAT_SqrtLog_PackingPrefixProgramRun`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeadSetup`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeads`, `SubexponentialSAT_Subexp_AssignmentInputProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S143`, `OAIQ081S144`, `OAIQ081S145` and `OAIQ081S147` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S170`, `OAIQ081S171` and `OAIQ081S172`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S143
import Definitions.Def_OAIQ081S144
import Definitions.Def_OAIQ081S145
import Definitions.Def_OAIQ081S147

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual selected-factor table runs over ambient variable IDs. Each low
payload is specialized immediately before its framed table entry is retained.
The source scratch embedding excludes persistent layout masters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

def literalPorts : UnaryForPrograms.Ports 16 896 := ⟨573,0,1⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
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


/-! Calls to the fixed record mapper inside the native scope scan. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def work (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out source payload : List Bool) : Data :=
  ⟨r, fun j => if j=2 then (Encoding.encodeNat v).reverse
    else if j=5 then Scan.unary scopes.length
    else if j=7 then source else if j=9 then Scan.unary (Scan.indices scopes v).length
    else if j=12 then payload else (Scan.data r scopes n v z mask out).stacks j⟩

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Lift


/-! One native low-variable step, including its uncovered neutral factor. -/


/-! Runtime high-mask loop for the original-address incidence stream. -/


/-! Count the physical scope stream before constructing native incidence plans. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInputProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical input construction for sequential type assignment

All parameters are unary stack data. The fixed program constructs the one-hot
word alphabet, reads its actual first word, derives its packed view, and builds
the exact seed range and dimensions expected by `AssignmentInitProgram`.
-/

namespace SubexponentialSAT.Subexp.AssignmentInputProgram

open BitProgram StructuredCalls SubexpSetupStorage AssignmentInputCall

def outputState (r Q delta D E : ℕ) (pairs : List Bool) : Data :=
  AssignmentInitProgram.inputState (context r Q delta D E pairs) (fun _ => false)

end SubexponentialSAT.Subexp.AssignmentInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native alphabet/seed construction followed by actual assignment copying.
The old producer is used at delta=0 so the seed count is exactly ambient+factors;
the new scorer's four-word depth is installed separately. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def coreBudget (r Q n f : ℕ) (pairs : List Bool) : ℕ :=
  AssignmentInputProgram.budget r Q 0 n f pairs+1+
    AssignmentInitProgram.sourceCost (context r Q n f pairs)

theorem coreBudget_polynomial (r Q n f : ℕ) (pairs : List Bool) (hr : 0 < r) :
    coreBudget r Q n f pairs ≤ 21000*(extent r Q n f pairs+1)^4 := by
  have ha := AssignmentInputProgram.budget_le r Q 0 n f pairs hr
  have hb := AssignmentInitProgram.sourceCost_le (context r Q n f pairs)
    (extent r Q n f pairs)
    (by dsimp [extent,context,AssignmentInputProgram.extent,AssignmentInputProgram.context]; omega)
    (by dsimp [extent,context,AssignmentInputProgram.extent,AssignmentInputProgram.context]; omega)
    (by dsimp [extent,context,AssignmentInputProgram.extent,AssignmentInputProgram.context]; omega)
  change _ ≤ 20000*(extent r Q n f pairs+1)^4 at ha
  unfold coreBudget
  have hp : 1 ≤ extent r Q n f pairs+1 := by omega
  have hs : (extent r Q n f pairs+1)^2 ≤ (extent r Q n f pairs+1)^4 :=
    Nat.pow_le_pow_right hp (by decide)
  have hf : 1 ≤ (extent r Q n f pairs+1)^4 := one_le_pow₀ hp
  omega

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed native loader from the incidence installer's actual tapes and
binary metadata to the sequential packing selector's initialized tapes. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def budget (outside : Store) (scopes : List Bool) (n k f : ℕ) (pairs : List Bool) :=
  captureBudget scopes.length n k f + parameterBudget outside +
    coreBudget (SubexponentialSAT.BinaryArithmetic.toNat (outside 59))
      (SubexponentialSAT.BinaryArithmetic.toNat (outside 55)) n f pairs + finishBudget outside + 1

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The loader's complete native cost, including emitted alphabet size. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem budget_polynomial (outside : Store) (scopes : List Bool) (n k f : ℕ)
    (pairs : List Bool) (hr : 0 < SubexponentialSAT.BinaryArithmetic.toNat (outside 59)) :
    budget outside scopes n k f pairs ≤ 22000*(sizeBound outside scopes n k f pairs)^4 := by
  let B := sizeBound outside scopes n k f pairs
  have hB : 1 ≤ B := by dsimp [B,sizeBound]; omega
  have hE : extent (SubexponentialSAT.BinaryArithmetic.toNat (outside 59))
      (SubexponentialSAT.BinaryArithmetic.toNat (outside 55)) n f pairs+1 ≤ B := by
    dsimp [B,sizeBound]; omega
  have hcore := (coreBudget_polynomial (SubexponentialSAT.BinaryArithmetic.toNat (outside 59))
    (SubexponentialSAT.BinaryArithmetic.toNat (outside 55)) n f pairs hr).trans
      (Nat.mul_le_mul_left 21000 (Nat.pow_le_pow_left hE 4))
  have hR := unary_bound (outside 59) B
    (by dsimp [B,sizeBound]; omega) (by dsimp [B,sizeBound]; omega) hB
  have hQ := unary_bound (outside 55) B
    (by dsimp [B,sizeBound]; omega) (by dsimp [B,sizeBound]; omega) hB
  have hcapture : captureBudget scopes.length n k f ≤ 56*B := by
    dsimp [captureBudget,B,sizeBound]; omega
  have hfinish : finishBudget outside ≤ 60*B := by
    dsimp [finishBudget,B,sizeBound]; omega
  have hsq : B ≤ B^2 := by nlinarith
  have hpow : B^2 ≤ B^4 := Nat.pow_le_pow_right hB (by decide)
  have hone : 1 ≤ B^4 := hB.trans (hsq.trans hpow)
  change _ ≤ 22000*B^4
  unfold budget parameterBudget
  omega

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramCleanup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open PackingLoaderProgram

def clearLowBudget (d : Small) :=
  ((List.finRange 48).map (fun i=>2*(d.stacks i).length+3)).sum

theorem clearLowBudget_le (d : Small) (B : ℕ)
    (h : ∀ i,(d.stacks i).length ≤ B) : clearLowBudget d ≤ 48*(2*B+3) := by
  unfold clearLowBudget
  calc
    _ ≤ ((List.finRange 48).map (fun _=>2*B+3)).sum := by
      apply List.sum_le_sum
      intro i hi
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (h i)) 3
    _ = _ := by
      have hsum (xs : List (Fin 48)) :
          (xs.map (fun _ => 2*B+3)).sum = xs.length*(2*B+3) := by
        induction xs with
        | nil => simp
        | cons x xs ih =>
            simp only [List.map_cons,List.sum_cons,List.length_cons,ih]
            rw [Nat.add_mul,one_mul]
            exact Nat.add_comm _ _
      rw [hsum,List.length_finRange]

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingPrefixProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid prefix preparation. Raw unary inputs may contain arbitrary bits;
only their lengths matter. The persistent table and both counters survive. -/

namespace SubexponentialSAT.SqrtLog.PackingPrefixProgram

open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.Subexp

abbrev multiply : Cmd 3 11 :=
  liftCommand BasisTransposePlanProgram.multiply 0 4 id mulStack

end SubexponentialSAT.SqrtLog.PackingPrefixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingPrefixProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingPrefixProgram

open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.Subexp

/-- All control is fixed. Counter values, table width and prefix length are
runtime data. Only the first h*W table bits are read. -/
abbrev command : Cmd 3 11 :=
  .seq (copy 1 5) (.seq (normalize 4)
    (.seq (copy 2 5) (.seq (normalize 8)
      (.seq (copy 4 5) (.seq multiply
        (.seq (clear 8) (.seq readPrefix (clear 6))))))))

def program := compiled command 0 3

end SubexponentialSAT.SqrtLog.PackingPrefixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingPrefixProgramLift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingPrefixProgram

open SubexponentialSAT BitProgram StructuredCalls

abbrev prepare {r s : ℕ} (p : Ports r s) : Cmd r s :=
  .call (ProgramLinking.liftProgram program p.register p.stack)

end SubexponentialSAT.SqrtLog.PackingPrefixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeadSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native head-stage gate and paid extraction of its prior-word prefix. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

abbrev preparePrefix : Cmd 16 48 := PackingPrefixProgram.prepare prefixABI

abbrev headSetup : Cmd 16 48 := .seq gate preparePrefix

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeads
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual head-score production from the controller table and alphabet. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

abbrev heads : Cmd 16 48 := .seq headSetup (.seq copyAlphabet
  (.seq resetHead (.seq headCandidates headCleanup)))

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramSelect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Run the concrete weighted selector while retaining the literal width and
alphabet for the native packing-layout suffix. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram

def dataMass (d : Small) := ∑ i : Fin 48,(d.stacks i).length

def selectionSize (d : Small) (rows : List (List Bool)) :=
  dataMass d+rows.flatten.length+rows.length+1

def selectionBudget (d : Small) (rows : List (List Bool)) (controllerCost : ℕ) :=
  7*(d.stacks 10).length+5+(7*(d.stacks 39).length+5)+controllerCost+
    (7*rows.flatten.length+5)+48*(2*selectionSize d rows+3)

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramSuffix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Full native layout suffix followed by a paid metadata save and cleanup. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open PackingLoaderProgram

def suffix : Code := .seq prepareSuffix
  (.seq (.call (ProgramLinking.liftProgram LayoutProgram.NativePacking.program id lowPorts))
    (.seq (saveHigh 32 63) clearLow))

def suffixBudget {U : Type*} [DecidableEq U] (outside : Store)
    (s : LayoutProgram.NativePacking.Spec U) :=
  prepareBudget outside + LayoutProgram.NativePacking.budget s +
    (7*s.suffix.metadata.length+5) + clearLowBudget (s.suffix.outputState (fun _=>false))

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! All local computation is now composed: native plans and pairs, actual
word selection, and the native layout metadata suffix. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

def ready (outside : Store) (p : Problem) (regs : Fin 16 → Bool) : Small :=
  readyLocal regs p.r p.Q p.n p.factors (PairScoreProgram.pairRecords p.raw)
    (outside 56) (outside 57) (outside 58) (outside 59)

noncomputable def coreBudget (outside : Store) (p : Problem)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :=
  produceBudget p.scopes p.n p.mask +
  PackingLoaderProgram.budget (planStore outside p) (Scan.scopeBits p.scopes) p.n p.mask.length
    p.factors (PairScoreProgram.pairRecords p.raw) +
  selectionBudget (ready outside p (fun _=>false)) ((p.words a tail).map ReadPlan.encodeWord)
    (PackingProgram.Assembly.Scope.cost p.scopes p.n p.mask a tail p.s
      (outside 56) (outside 57) (outside 58) (outside 59)) +
  suffixBudget (selectedStore outside p a tail) (p.spec a tail)

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsLoader
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem loader_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S)
    (hp : Parameters outside p) :
    PackingLoaderProgram.budget (planStore outside p) (Scan.scopeBits p.scopes) p.n p.mask.length
      p.factors (PairScoreProgram.pairRecords p.raw) ≤ loaderEnvelope S := by
  have he := extent_le h
  have hb := PackingLoaderProgram.budget_polynomial (planStore outside p)
    (Scan.scopeBits p.scopes) p.n p.mask.length p.factors (PairScoreProgram.pairRecords p.raw)
    (by simpa [planStore,hp.radius] using p.hr)
  apply hb.trans
  unfold loaderEnvelope
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  simp [PackingLoaderProgram.sizeBound,planStore,hp.radius,hp.coordinate]
  rcases h with ⟨hpos,hn,hf,hm,hr,hq,hs,ha,ht,hsc,hmask,h55,h56,h57,h58,h59⟩
  omega

theorem outputState_le (ctx : AssignmentInitProgram.Context) (B N : ℕ)
    (hn : ctx.seedCount ≤ N) (hw : ctx.defaultWord.length ≤ B)
    (hp : ctx.packedAlphabet.length ≤ B) (ha : ctx.alphabetRecords.length ≤ B)
    (hwi : ctx.width.length ≤ B) (hd : ctx.depth.length ≤ B)
    (hr : ctx.rawPairs.length ≤ B) (hs : ctx.seedRecords.length ≤ B) (i : Fin 48) :
    ((AssignmentInitProgram.outputState ctx).stacks i).length ≤ N*B+B+N := by
  have hm := Nat.mul_le_mul hn hw
  fin_cases i <;> simp [AssignmentInitProgram.outputState,AssignmentInitProgram.state,
    AssignmentInitProgram.unary,BlockCopyProgram.copies_length] <;> omega


theorem ready_word_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S)
    (regs : Fin 16 → Bool) (i : Fin 48) :
    ((ready outside p regs).stacks i).length ≤ readyEnvelope S := by
  let ctx := PackingLoaderProgram.context p.r p.Q p.n p.factors (PairScoreProgram.pairRecords p.raw)
  have he := extent_le h
  have hn : ctx.seedCount ≤ 2*S := by
    dsimp [ctx,PackingLoaderProgram.context,AssignmentInputProgram.context,AssignmentInputProgram.seedCount]
    have := h.n; have := h.factors
    omega
  have hd : ctx.defaultWord.length ≤ extentEnvelope S := by
    dsimp [ctx,PackingLoaderProgram.context,AssignmentInputProgram.context]
    dsimp [extent,AssignmentInputProgram.extent] at he
    omega
  have hpa : ctx.packedAlphabet.length ≤ extentEnvelope S := by
    dsimp [ctx,PackingLoaderProgram.context,AssignmentInputProgram.context]
    dsimp [extent,AssignmentInputProgram.extent] at he
    omega
  have har : ctx.alphabetRecords.length ≤ extentEnvelope S := by
    dsimp [ctx,PackingLoaderProgram.context,AssignmentInputProgram.context]
    dsimp [extent,AssignmentInputProgram.extent] at he
    omega
  have hwi : ctx.width.length ≤ extentEnvelope S := by
    dsimp [ctx,PackingLoaderProgram.context,AssignmentInputProgram.context,AssignmentInputProgram.unary]
    simp only [List.length_replicate]
    dsimp [extent,AssignmentInputProgram.extent] at he
    omega
  have hpr : ctx.rawPairs.length ≤ extentEnvelope S := by
    dsimp [ctx,PackingLoaderProgram.context,AssignmentInputProgram.context]
    dsimp [extent,AssignmentInputProgram.extent] at he
    omega
  have hsr : ctx.seedRecords.length ≤ extentEnvelope S := by
    dsimp [ctx,PackingLoaderProgram.context,AssignmentInputProgram.context]
    dsimp [extent,AssignmentInputProgram.extent] at he
    omega
  have hdepth : ctx.depth.length ≤ extentEnvelope S := by
    dsimp [ctx,PackingLoaderProgram.context,AssignmentInputProgram.context,AssignmentInputProgram.unary]
    unfold extentEnvelope
    omega
  have hout := outputState_le ctx (extentEnvelope S) (2*S) hn hd hpa har hwi hdepth hpr hsr i
  have h56 := h.l56
  have h57 := h.l57
  have h58 := h.l58
  have h59 := h.l59
  change (if i=20 then outside 56 else if i=21 then outside 57 else if i=22 then outside 58
    else if i=23 then outside 59 else if i=34 then List.replicate 4 true
    else (AssignmentInitProgram.outputState ctx).stacks i).length ≤ _
  split_ifs <;> (try simp only [List.length_replicate]) <;> unfold readyEnvelope <;> omega

theorem ready_mass_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S)
    (regs : Fin 16 → Bool) : dataMass (ready outside p regs) ≤ 48*readyEnvelope S := by
  unfold dataMass
  calc
    _ ≤ ∑ _i : Fin 48, readyEnvelope S := Finset.sum_le_sum (fun i _=>ready_word_le h regs i)
    _ = _ := by simp

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsSelection
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

theorem selection_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (hrows : (a::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes p.r p.Q) :
    selectionBudget (ready outside p (fun _=>false)) ((p.words a tail).map ReadPlan.encodeWord)
      (PackingProgram.Assembly.Scope.cost p.scopes p.n p.mask a tail p.s
        (outside 56) (outside 57) (outside 58) (outside 59)) ≤ selectionEnvelope S := by
  have hc := controller_le h a tail hrows
  have h10 := ready_word_le h (fun _=>false) 10
  have h39 := ready_word_le h (fun _=>false) 39
  have hm := ready_mass_le h (fun _=>false)
  have hn : p.n+p.factors ≤ 2*S := by have := h.n; have := h.factors; omega
  have hw := width_le h
  unfold selectionBudget selectionSize selectionEnvelope
  rw [words_bits,List.length_map,p.words_length]
  gcongr

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

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

theorem bank_frame (a : Data) (b : State 16 64) (i : Fin 768)
    (hi : i.val < 417 ∨ 481 ≤ i.val) :
    (embedState registers ports a b).stacks i=a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change 417+j.val=i.val at hv
  have := j.isLt
  omega

theorem bank_register_frame (a : Data) (b : State 16 64) (i : Fin 40)
    (hi : 16 ≤ i.val) :
    (embedState registers ports a b).regs i=a.regs i := by
  apply embedState_register_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val=i.val at hv
  have := j.isLt
  omega

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramExportFacts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem copyMany_congr {S : ℕ} (ps : List (Fin S × Fin S)) (a b : State 16 S)
    (h : a.stacks=b.stacks) :
    (copyManyState ps a).stacks=(copyManyState ps b).stacks ∧
    copyManyCost ps a=copyManyCost ps b := by
  induction ps generalizing a b with
  | nil => exact ⟨h,rfl⟩
  | cons p ps ih =>
    have hs : (copyState p.1 p.2 a).stacks=(copyState p.1 p.2 b).stacks := by simp only [copyState_stack,h]
    obtain ⟨h1,h2⟩ := ih _ _ hs
    exact ⟨h1,by simp only [copyManyCost,h,h2]⟩

theorem clearMany_congr {S : ℕ} (ps : List (Fin S)) (a b : State 16 S)
    (h : a.stacks=b.stacks) :
    (clearManyState ps a).stacks=(clearManyState ps b).stacks ∧
    clearManyCost ps a=clearManyCost ps b := by
  induction ps generalizing a b with
  | nil => exact ⟨h,rfl⟩
  | cons p ps ih =>
    have hs : (clearState p a).stacks=(clearState p b).stacks := by simp only [clearState,h]
    obtain ⟨h1,h2⟩ := ih _ _ hs
    exact ⟨h1,by simp only [clearManyCost,h,h2]⟩

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid copies from the actual query frontend's persistent master bank. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open PackingLoaderProgram PackingIncidenceInput
attribute [local simp] Fin.coe_ofNat_eq_mod

def parameterStore (a : Local) : Fin 64 → List Bool := fun i=>
  if i=55 then a.stacks 720 else if i=56 then a.stacks 709
  else if i=57 then a.stacks 722 else if i=58 then a.stacks 723
  else if i=59 then a.stacks 721 else []

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end


