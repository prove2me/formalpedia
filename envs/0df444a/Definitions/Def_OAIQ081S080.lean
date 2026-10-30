-- Prove2me | Definitions.Def_OAIQ081S080
-- name    : OAIQ081S080
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:05:28.520983+00:00
-- url     : https://prove2.me/theorems/c031bc05-1343-480b-9448-cd3ab0ef9915
-- title:
--   Definitions bundle OAIQ081S080 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 79 declarations of OpenAI's Lean: 35 definitions, 2 instances and 42 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.head`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.incidence`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.shifted`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.constantsState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.coordinateLoaded`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.finishedTarget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.rawWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.rowsReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.targetBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.targetState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.nativeBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.runBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.selectedBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.stepBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.increment`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram.keyCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationMaskProgram.advance`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationMaskProgram.pushBit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgram.Key.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgram.Key.pushFalse`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgram.decodeRecords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRank.rationalUnits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.decodeCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.localInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.streamData`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidates.matrixWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Floor.trimCfg`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.inputVolume`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative.stageFinal`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.ofPolynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.polynomial`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInitProgram.inputState`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentRecordViews.afterTag`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentRecordViews.data`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_CodeCandidates`, `SubexponentialSAT_SqrtLogSpace_CommandStackTransport`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_BinaryClogProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLogSpace_HashTrialStage`, `SubexponentialSAT_SqrtLogSpace_TruncatedRing`, `SubexponentialSAT_SqrtLog_PackingWeightProgramBasic`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyConstants`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyCoordinate`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyScan`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyStoredCore`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyTarget`, `SubexponentialSAT_SqrtLog_PerturbationBetaProgramBounds`, `SubexponentialSAT_SqrtLog_PerturbationBetaProgramRun`, `SubexponentialSAT_SqrtLog_PerturbationBetaProgramSelected`, `SubexponentialSAT_SqrtLog_PerturbationBetaProgramStep`, `SubexponentialSAT_SqrtLog_PerturbationEmitProgram`, `SubexponentialSAT_SqrtLog_PerturbationMaskProgram`, `SubexponentialSAT_SqrtLog_PerturbationProgramKey`, `SubexponentialSAT_SqrtLog_PerturbationProgramStored`, `SubexponentialSAT_SqrtLog_ProducedQueryRankProvenance`, `SubexponentialSAT_SqrtLog_RingModel`, `SubexponentialSAT_SqrtLog_RowSelectionProgramParser`, `SubexponentialSAT_SqrtLog_RowSelectionProgramReuse`, `SubexponentialSAT_SqrtLog_RowSelectionProgramStream`, `SubexponentialSAT_SubexpInputFrames`, `SubexponentialSAT_SubexpSetupStorage`, `SubexponentialSAT_Subexp_AssignmentInitProgram`, `SubexponentialSAT_Subexp_AssignmentInputCall`, `SubexponentialSAT_Subexp_AssignmentRecordViews`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S045`, `OAIQ081S046`, `OAIQ081S047`, `OAIQ081S048`, `OAIQ081S051`, `OAIQ081S052`, `OAIQ081S053`, `OAIQ081S054`, `OAIQ081S058`, `OAIQ081S059`, `OAIQ081S060`, `OAIQ081S061`, `OAIQ081S062` and `OAIQ081S063` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S098` and `OAIQ081S099`; the statement `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.multiplyReuseCommand_eval_total`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.readback_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.addEntry_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.accumulate_eval_total`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.multiply_eval_total`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.scalarProgram_runsIn_total`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.stageCost_linear` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.multiplyReuseCommand_eval_total`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S045
import Definitions.Def_OAIQ081S046
import Definitions.Def_OAIQ081S047
import Definitions.Def_OAIQ081S048
import Definitions.Def_OAIQ081S051
import Definitions.Def_OAIQ081S052
import Definitions.Def_OAIQ081S053
import Definitions.Def_OAIQ081S054
import Definitions.Def_OAIQ081S058
import Definitions.Def_OAIQ081S059
import Definitions.Def_OAIQ081S060
import Definitions.Def_OAIQ081S061
import Definitions.Def_OAIQ081S062
import Definitions.Def_OAIQ081S063

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeCandidates
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The retained domain of the code search is one word of two-bit scalars.
The tuple counter visits all four digits; the physical converter rejects the
unused digits and produces the original scalar-frame arithmetic format. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidates

open SubexpEnumerationPayload

@[simp] theorem fieldWords_length {p d : ℕ} [Fact p.Prime] (v : Fin d → ZMod p) :
    (fieldWords v).length = d := by simp [fieldWords]

@[simp] theorem fieldWords_flatten_length {p d : ℕ} [Fact p.Prime]
    (v : Fin d → ZMod p) : (fieldWords v).flatten.length = d * scalarWidth p := by
  simp [List.length_flatten, fieldWords_shape]

/-- Row-major matrix indexing is the supplied `finProdFinEquiv` convention. -/
def matrixWords {p rows cols : ℕ} [Fact p.Prime]
    (matrix : Fin rows → Fin cols → ZMod p) : List (List Bool) :=
  fieldWords fun i : Fin (rows * cols) =>
    matrix (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

@[simp] theorem matrixWords_shape {p rows cols : ℕ} [Fact p.Prime]
    (matrix : Fin rows → Fin cols → ZMod p) :
    (matrixWords matrix).map List.length = List.replicate (rows * cols) (scalarWidth p) :=
  fieldWords_shape _

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidates
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CommandStackTransport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! All-prefix resource transport for the existing exact-time tape replay.
The imported avoidance certificate excludes reads as well as writes, including
`peek`. Erasing hidden caller data is a proof construction only: the actual
instruction table and its measured number of steps remain unchanged. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandStackTransport

open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay

variable {r s l : ℕ}

/-- An arbitrary prefix of the rebased execution is the rebase of the exact
same-length prefix of the original execution. -/
theorem trace_prefix_rebase (H : Fin s → Prop) [DecidablePred H]
    {p : Program r s l} (hp : AvoidsProgram H p)
    (frame : Fin s → List Bool) {steps prefixSteps : ℕ} {a b : Cfg r s l}
    (ht : Trace p steps a b) {intermediate : Cfg r s l}
    (hle : prefixSteps ≤ steps)
    (hprefix : Trace p prefixSteps (rebaseCfg H frame a) intermediate) :
    ∃ source, Trace p prefixSteps a source ∧
      intermediate = rebaseCfg H frame source := by
  obtain ⟨source, hs⟩ := trace_prefix_exists ht hle
  exact ⟨source, hs, trace_same_length_unique hprefix (trace_rebase H hp hs frame)⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandStackTransport
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_BinaryClogProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual floor and ceiling logarithm bit programs, without packing or schedule imports. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Floor

open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.CounterPrograms

def trimCfg (pc : Option (Fin 6)) (b present : Bool) (xs : List Bool) : Cfg 3 3 6 :=
  ⟨pc, counterRegs b present false, lengthStacks [] xs []⟩

/-! ## Concrete input reversal -/

/-! ## Reindex and call the checked binary word-length counter -/

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Floor
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace Selector

def inputVolume (F : Formula) (base : List Bool) : ℕ :=
  (Filter.formulaCode F).length + base.length + 1

end Selector

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashTrialStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact finite staging extracted from `SqrtLog.LeafOuterNativeStage` for the
space-aware hash pipeline. Semantic query provenance remains in the original
module, while these declarations live in the stronger development's namespace. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
open OAI BitProgram StructuredCalls SqrtLog.LeafOuterProgram
open Subexp

def stageFinal : Cmd 40 896 := routes masterRoutes

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TruncatedRing
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Dense lifting and Taylor coefficients

`Truncated R n` stores exactly `n` coefficients. Its multiplication is the
existing total-order convolution, and its ring laws follow from the surjective
coefficient projection from `R[X]`. Nesting the construction stores the shared
lifting marker outside the Taylor variable. The final marker readout is additive.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog.TotalOrder

namespace Truncated

variable {R : Type*} {n : ℕ}

section Semiring

variable [CommSemiring R]

noncomputable section

/-- The coefficient projection. This is a semantic map, not the native evaluator. -/
def ofPolynomial (n : ℕ) (P : Polynomial R) : Truncated R n := ⟨toArray n P⟩

/-- The canonical polynomial represented by the stored array. -/
def polynomial (a : Truncated R n) : Polynomial R := asPolynomial a.coeff

@[simp] theorem coeff_ofPolynomial (P : Polynomial R) (j : Fin n) :
    (ofPolynomial n P).coeff j = P.coeff j.val := rfl

@[simp] theorem ofPolynomial_polynomial (a : Truncated R n) :
    ofPolynomial n a.polynomial = a := by
  ext j
  simp [ofPolynomial, polynomial]

theorem ofPolynomial_surjective : Function.Surjective (ofPolynomial (R := R) n) :=
  fun a => ⟨a.polynomial, ofPolynomial_polynomial a⟩

@[simp] theorem ofPolynomial_zero : ofPolynomial n (0 : Polynomial R) = 0 := by
  ext j
  simp

@[simp] theorem ofPolynomial_one : ofPolynomial n (1 : Polynomial R) = 1 := by
  ext j
  simp [Polynomial.coeff_one]

@[simp] theorem ofPolynomial_add (P Q : Polynomial R) :
    ofPolynomial n (P + Q) = ofPolynomial n P + ofPolynomial n Q := by
  ext j
  simp

@[simp] theorem ofPolynomial_mul (P Q : Polynomial R) :
    ofPolynomial n (P * Q) = ofPolynomial n P * ofPolynomial n Q := by
  ext j
  rw [coeff_ofPolynomial, coeff_mul, Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro uv huv
  have huv' := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
  have hu : uv.1 < n := by omega
  have hv : uv.2 < n := by omega
  simp [arrayCoeff, hu, hv]

end
end Semiring

end Truncated

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWeightProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed binary computation of the reciprocal-error packing coefficients.
Sources 0..3 hold n,s,M,r. Outputs 4,5 hold n²s² and 8M²r².
Ports 6,7 and 8..12 are temporary products and arithmetic scratch. -/
namespace SubexponentialSAT.SqrtLog.PackingWeightProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls

def shifted (d : Data) : Data :=
  ⟨Function.update d.regs 0 false,
    Function.update d.stacks 5 (false :: false :: false :: d.stacks 5)⟩

def incidence (d : Data) : ℕ :=
  SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 0)^2 * SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 1)^2
def head (d : Data) : ℕ :=
  8 * SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 2)^2 * SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 3)^2

end SubexponentialSAT.SqrtLog.PackingWeightProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

instance fieldFinite : Finite a.E := LiftRing.extension_finite_type a.residuePolynomial_monic
instance fieldFintype : Fintype a.E := Fintype.ofFinite _

def decodeCount (ht : 0 < t) (x : a.O t) : ℕ := (a.readBase t ht x).val

end Data

end SubexponentialSAT.SqrtLog.RingModel

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyConstants
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid construction of the polynomial Horner point and seed. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpPolynomialConstructor
open DensePolynomialProgram.Constructor

def constantsState (s : Store) (J W : ℕ) : Store :=
  Function.update (Function.update (Function.update s
    239 (Counter.paddedBits W (s 207) (s 207) J))
    247 (Counter.paddedBits W (s 209) (s 208) J)) 254 (s 207)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationProgramKey
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native construction of a positive-Z singleton key from its runtime unary
exponent and support mask. The reversed result feeds the sparse record emitter. -/
namespace SubexponentialSAT.SqrtLog.PerturbationProgram.Key
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl

def pushFalse : Code := Subexp.TupleProgram.pushConst 222 0 false

def command : Code := .seq (copy 220 222) (.seq pushFalse
  (.seq (copy 221 222) (.seq pushFalse
    (.call (StackRoutines.reverseProgram 222 223 224 (0 : Fin 16) 1)))))

end SubexponentialSAT.SqrtLog.PerturbationProgram.Key

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationEmitProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native emission of the positive part of a shifted coefficient array.
The dimensions and the singleton support mask are runtime data. The constant
cell is consumed without emission; all later cells are framed, including zero
coefficients. No normalization or arithmetic oracle is used. -/
namespace SubexponentialSAT.SqrtLog.PerturbationEmitProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl

def keyCommand : Code := liftCommand PerturbationProgram.Key.command 0 0 id keyMap

def increment : Code := Subexp.TupleProgram.pushConst 221 0 true

end SubexponentialSAT.SqrtLog.PerturbationEmitProgram


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationMaskProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed native constructor for original-coordinate singleton masks.
Masters212/218 are retained; output214 and scratch120/221/222/223 are the
only touched stacks. No table of masks or semantic mask oracle is supplied. -/
namespace SubexponentialSAT.SqrtLog.PerturbationMaskProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

abbrev pushBit (b : Bool) : Code := Subexp.TupleProgram.pushConst 214 0 b

/-- One native step advances the caller's original-coordinate unary index. -/
abbrev advance : Code := Subexp.TupleProgram.pushConst 218 0 true

end SubexponentialSAT.SqrtLog.PerturbationMaskProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyCoordinate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Per-coordinate physical composition. Original ambient variable IDs remain
unchanged throughout row loading, singleton support construction and emission. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpPolynomialConstructor

def coordinateLoaded (s : Store) (bits rest mask : List Bool) : Store :=
  Function.update (Function.update (Function.update s 230 rest) 219 bits) 214 mask

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native traversal of the actual runtime-framed row list. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

def rowsReady {C : Type*} (base : Store) (encode : C → List Bool)
    (j : ℕ) (cs : List C) (acc count : List Bool) : Store :=
  Function.update (Function.update (Function.update (Function.update base
    230 (Encoding.encodeList encode cs)) 231 count) 218 (List.replicate j true)) 217 acc


end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationProgramStored
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpDensePolynomial
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree Squarefree.Sparse

variable {C R V : Type*} [CommRing R] [DecidableEq V]

def decodeRecords (ops : RepresentedRing C R) (l : List (Index V × C)) :
    Sparse.Data (Index V) R := l.map (fun a => (a.1,ops.decode a.2))

end SubexponentialSAT.SqrtLog.PerturbationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyStoredCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Validity and exact denotation of the reversed, unnormalized coefficient
stream emitted by the new perturbation assembly. Zero coefficients remain. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT.SubexpSymbolicCost
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree Squarefree.Sparse PerturbationProgram
open scoped BigOperators

variable {C R : Type*} [CommRing R]

def rawWords {n : ℕ} (beta : C) (tails : Fin n → List C) :
    List (Index (Fin n) × C) :=
  ((Index.origin,beta) ::
    (List.ofFn fun v => coefficientRecords v 1 (tails v)).flatten).reverse

theorem coefficient_mem {n : ℕ} (v : Fin n) (j : ℕ) (p : List C)
    (a : Index (Fin n) × C) (ha : a ∈ coefficientRecords v j p) :
    a.1.u = 0 ∧ j ≤ a.1.z ∧ a.1.z < j+p.length ∧ a.1.vars = {v} := by
  induction p generalizing j with
  | nil => simp [coefficientRecords] at ha
  | cons c cs ih =>
      rcases List.mem_cons.mp ha with h | h
      · subst a
        exact ⟨rfl,le_rfl,by simp,rfl⟩
      · obtain ⟨hu,hlo,hhi,hv⟩ := ih (j+1) h
        exact ⟨hu,by omega,by simp only [List.length_cons]; omega,hv⟩

theorem coefficient_pairwise {n : ℕ} (v : Fin n) (j : ℕ) (p : List C) :
    (coefficientRecords v j p).Pairwise (fun a b => a.1 ≠ b.1) := by
  induction p generalizing j with
  | nil => simp [coefficientRecords]
  | cons c cs ih =>
      apply List.pairwise_cons.mpr
      constructor
      · intro a ha he
        have hz := (coefficient_mem v (j+1) cs a ha).2.1
        have hez := congrArg Index.z he
        simp only at hez
        omega
      · exact ih (j+1)

theorem rows_pairwise {n : ℕ} (tails : Fin n → List C)
    (vs : List (Fin n)) (hv : vs.Nodup) :
    (vs.flatMap fun v => coefficientRecords v 1 (tails v)).Pairwise
      (fun a b => a.1 ≠ b.1) := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
      obtain ⟨hn,ht⟩ := List.nodup_cons.mp hv
      apply List.pairwise_append.mpr
      refine ⟨coefficient_pairwise v 1 (tails v),ih ht,?_⟩
      intro a ha b hb he
      obtain ⟨w,hw,hb⟩ := List.mem_flatMap.mp hb
      have hav := (coefficient_mem v 1 (tails v) a ha).2.2.2
      have hbw := (coefficient_mem w 1 (tails w) b hb).2.2.2
      have hevars := congrArg Index.vars he
      rw [hav,hbw] at hevars
      have hvw : v=w := by simpa using hevars
      exact hn (hvw.symm ▸ hw)

theorem rawWords_nodup {n : ℕ} (beta : C) (tails : Fin n → List C) :
    ((rawWords beta tails).map Prod.fst).Nodup := by
  rw [rawWords,List.map_reverse]
  apply List.nodup_reverse.mpr
  apply List.pairwise_map.mpr
  apply List.pairwise_cons.mpr
  constructor
  · intro a ha he
    obtain ⟨l,hl,ha⟩ := List.mem_flatten.mp ha
    obtain ⟨v,hv⟩ := List.mem_ofFn.mp hl
    subst l
    have hz := (coefficient_mem v 1 (tails v) a ha).2.1
    have hez := congrArg Index.z he
    simp [Index.origin] at hez
    omega
  · have hrows := rows_pairwise tails (List.finRange n) (List.nodup_finRange n)
    simpa [List.finRange,List.flatMap_def,List.map_ofFn,Function.comp_def] using hrows

theorem rawWords_valid (ops : RepresentedRing C R) {n : ℕ}
    (t J : ℕ) (ht : 0 < t) (hJ : 0 < J)
    (beta : C) (tails : Fin n → List C) (hlen : ∀ v, (tails v).length < J) :
    Sparse.ValidData Finset.univ t J (decodeRecords ops (rawWords beta tails)) := by
  intro a ha
  simp only [Sparse.keys,decodeRecords,List.map_map,Function.comp_def,
    rawWords,List.map_reverse,List.mem_reverse] at ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  rcases List.mem_cons.mp hb with he | hb
  · subst b
    simp [Index.Kept,Index.Valid,Index.origin,ht,hJ]
  · obtain ⟨l,hl,hb⟩ := List.mem_flatten.mp hb
    obtain ⟨v,hv⟩ := List.mem_ofFn.mp hl
    subst l
    obtain ⟨hu,hlo,hhi,hvars⟩ := coefficient_mem v 1 (tails v) b hb
    have hj : b.1.z < J := by have := hlen v; omega
    refine ⟨⟨by simpa [hu] using ht,hj⟩,?_,Finset.subset_univ _⟩
    simpa [Index.Valid,hvars] using hlo

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyTarget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Dynamic target-jet cache installation. Full source-degree metadata at210
is untouched while the arithmetic count is temporarily changed to213. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram.Constructor

def targetState (s : Store) (J W : ℕ) : Store :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update s
      193 (s 213)) 243 (s 213))
      192 (Counter.paddedBits W (s 207) (s 207) J))
      247 (Counter.paddedBits W (s 209) (s 208) J)) 254 (s 207))
      236 (s 192)) 237 (s 193)) 238 (s 243)

def targetBudget (s : Store) (J W : ℕ) : ℕ :=
  9*((s 192).length+(s 193).length+(s 243).length)+14*J+9*(J*W)+7*W+
    440*(J+1)*(W+1)+47


def finishedTarget (s : Store) : Store :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update s
      236 []) 192 (s 236)) 237 []) 193 (s 237)) 238 []) 243 (s 238)) 247 []) 254 []

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgramSelected
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One selected coefficient row is evaluated by the actual Horner command
and accumulated by the actual extension-ring addition service. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing
open CRTLocalProgram (LowFrame lowFrame_update lowFrame_refl)

def selectedBudget (n t d : ℕ) : ℕ :=
  HornerProgram.modelBudget n t d + HornerProgram.Services.addBudget (baseWidth 3 t) d +
    32*(d*baseWidth 3 t)+7*n+36

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgramStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing
open CRTLocalProgram (LowFrame lowFrame_update lowFrame_refl)

def stepBudget (L t d : ℕ) : ℕ :=
  11*(L*(d*baseWidth 3 t))+selectedBudget L t d+13

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed native beta scan from preserved row/choice masters. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing
open CRTLocalProgram (LowFrame lowFrame_update lowFrame_refl)

def runBudget (s : Store) (n L t d : ℕ) : ℕ :=
  initBudget s+n*(stepBudget L t d+2)+2+(4*(d*baseWidth 3 t)+14)

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial native cost, including framing, all skipped rows, and cleanup.
The parser dependency has a fixed16/256 ABI owned by this helper. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing

def nativeBudget (n L t d : ℕ) : ℕ :=
  7*(n*(2*(L*(d*baseWidth 3 t))+2)+1)+7*n+21*(d*baseWidth 3 t)+25+
    n*(stepBudget L t d+2)+2+(4*(d*baseWidth 3 t)+14)

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramReuse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed cleanup adapter makes signed arithmetic reusable inside loops. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def pairState (regs : Fin 8 → Bool) (positive negative : List Bool) : Data :=
  ⟨regs, fun j => if j = 0 then positive else if j = 1 then negative else []⟩

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramParser
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit framed input parsing for streams of signed binary word pairs. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def streamData (regs : Fin 8 → Bool) (acc next : WordPair) (queue : List Bool) : StreamData :=
  ⟨regs, fun j => if j=0 then acc.1 else if j=1 then acc.2 else
    if j=2 then next.1 else if j=3 then next.2 else if j=15 then queue else []⟩

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramStream
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Arithmetic callbacks on a fixed stream ABI. The remaining record stream is
preserved byte-for-byte across each real signed-arithmetic call. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def localInput (regs : Fin 8 → Bool) (acc next : WordPair) : Data :=
  ⟨regs, fun j => if j=0 then acc.1 else if j=1 then acc.2 else
    if j=2 then next.1 else if j=3 then next.2 else []⟩

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

theorem resetMany_eval {S : ℕ} (rs : List (Fin 16)) (a : Data S) :
    Eval (resetMany rs) rs.length a (resetManyState rs a) := by
  induction rs generalizing a with
  | nil => exact .base (.skip a)
  | cons r rs ih =>
    have h := Eval.seq (Eval.base (StructuredProgram.Eval.atom (.set r false) a))
      (ih ((StructuredProgram.Atom.set r false).eval a))
    simpa only [resetMany, resetManyState, List.length_cons, Nat.add_comm] using h

theorem resetMany_stacks {S : ℕ} (rs : List (Fin 16)) (a : Data S) :
    (resetManyState rs a).stacks = a.stacks := by
  induction rs generalizing a with
  | nil => rfl
  | cons r rs ih => exact ih ((StructuredProgram.Atom.set r false).eval a)

theorem resetMany_regs {S : ℕ} (rs : List (Fin 16)) (a : Data S) (i : Fin 16) :
    (resetManyState rs a).regs i = if i ∈ rs then false else a.regs i := by
  induction rs generalizing a with
  | nil => simp [resetManyState]
  | cons r rs ih =>
    rw [resetManyState, ih]
    by_cases hr : i = r <;> by_cases hs : i ∈ rs <;>
      simp [hr, hs, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]

theorem resetWork_eval {S : ℕ} (a : Data S) :
    Eval resetWork 9 a (resetManyState workRegisters a) := by
  simpa only [resetWork, workRegisters, List.length_ofFn] using resetMany_eval workRegisters a

theorem resetWork_reg {S : ℕ} (a : Data S) (i : Fin 9) :
    (resetManyState workRegisters a).regs (i.castLE (by decide)) = false := by
  rw [resetMany_regs]
  apply ite_eq_left
  rw [workRegisters, List.mem_ofFn]
  exact ⟨i, rfl⟩

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInitProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical initialization of the sequential assignment memory

The input contains the already generated alphabet and incidence records.
This fixed routine duplicates the runtime tables, creates the initial packed
assignment by actual repeated copying, and clears all temporary ports. The
production of the input records is a separate frontend stage.
-/

namespace SubexponentialSAT.Subexp.AssignmentInitProgram

open BitProgram StructuredCalls StackRoutines

def inputState (ctx : Context) (regs : Fin 16 → Bool) : Data :=
  state ctx regs ctx.defaultWord [] [] [] []

theorem copyRemaining_eval (ctx : Context) :
    Eval copyRemaining (7 * ctx.seedCount + 5)
      (state ctx (fun _ => false) ctx.defaultWord [] [] [] [])
      (state ctx (fun _ => false) ctx.defaultWord [] (unary ctx.seedCount) [] []) := by
  have h := TupleProgram.copy_eval (47 : Fin 48) 11 1 (0 : Fin 16) 1
    (by decide) (by decide) (by decide) (by decide)
    (state ctx (fun _ => false) ctx.defaultWord [] [] [] []) (by simp [state])
  convert h using 1
  · simp [state, unary]
  · apply congrArg₂ StructuredProgram.State.mk
    · funext j; fin_cases j <;> simp [state, readRegs]
    · funext j; fin_cases j <;> simp [state, copyStacks]

theorem copyCounter_eval (ctx : Context) :
    Eval copyCounter (7 * ctx.seedCount + 5)
      (state ctx (fun _ => false) ctx.defaultWord [] (unary ctx.seedCount) [] [])
      (state ctx (fun _ => false) ctx.defaultWord [] (unary ctx.seedCount)
        (unary ctx.seedCount) []) := by
  have h := TupleProgram.copy_eval (47 : Fin 48) 2 1 (0 : Fin 16) 1
    (by decide) (by decide) (by decide) (by decide)
    (state ctx (fun _ => false) ctx.defaultWord [] (unary ctx.seedCount) [] [])
    (by simp [state])
  convert h using 1
  · simp [state, unary]
  · apply congrArg₂ StructuredProgram.State.mk
    · funext j; fin_cases j <;> simp [state, readRegs]
    · funext j; fin_cases j <;> simp [state, copyStacks]

theorem copyAlphabet_eval (ctx : Context) :
    Eval copyAlphabet (7 * ctx.alphabetRecords.length + 5)
      (state ctx (fun _ => false) ctx.defaultWord
        (BlockCopyProgram.copies ctx.seedCount ctx.defaultWord) (unary ctx.seedCount) [] [])
      (state ctx (fun _ => false) ctx.defaultWord
        (BlockCopyProgram.copies ctx.seedCount ctx.defaultWord) (unary ctx.seedCount) []
        ctx.alphabetRecords) := by
  have h := TupleProgram.copy_eval (30 : Fin 48) 39 1 (0 : Fin 16) 1
    (by decide) (by decide) (by decide) (by decide)
    (state ctx (fun _ => false) ctx.defaultWord
      (BlockCopyProgram.copies ctx.seedCount ctx.defaultWord) (unary ctx.seedCount) [] [])
    (by simp [state])
  convert h using 1
  · simp [state]
  · apply congrArg₂ StructuredProgram.State.mk
    · funext j; fin_cases j <;> simp [state, readRegs]
    · funext j; fin_cases j <;> simp [state, copyStacks]

theorem output_memory {A : Type*} (encode : A → List Bool) (a : A) (tail : List A)
    (ctx : Context) (hword : ctx.defaultWord = encode a)
    (halphabet : ctx.packedAlphabet = ((a :: tail).map encode).flatten)
    (hwidth : ctx.width.length = (encode a).length) :
    SequentialProgram.Memory encode a tail ctx.seedCount [] (outputState ctx).stacks := by
  constructor
  · simp [outputState, state, BlockCopyProgram.copies, hword]
  · simp [outputState, state, halphabet]
  · simpa [outputState, state] using hwidth
  · simp [outputState, state]
  · intro j hj
    have hn : j ≠ 8 ∧ j ≠ 9 ∧ j ≠ 10 ∧ j ≠ 11 ∧ j.val < 20 :=
      (show ∀ j : Fin 48, j ∈ SequentialProgram.scratchPorts →
        j ≠ 8 ∧ j ≠ 9 ∧ j ≠ 10 ∧ j ≠ 11 ∧ j.val < 20 by decide) j hj
    have h30 : j ≠ 30 := by intro h; subst j; omega
    have h34 : j ≠ 34 := by intro h; subst j; omega
    have h39 : j ≠ 39 := by intro h; subst j; omega
    have h45 : j ≠ 45 := by intro h; subst j; omega
    have h46 : j ≠ 46 := by intro h; subst j; omega
    have h47 : j ≠ 47 := by intro h; subst j; omega
    simp [outputState, state, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1,
      h30, h34, h39, h45, h46, h47]

end SubexponentialSAT.Subexp.AssignmentInitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInputCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One-output physical calls in the assignment-input workspace. -/

namespace SubexponentialSAT.Subexp.AssignmentInputCall

open BitProgram StructuredCalls SubexpSetupStorage

theorem prepare_regs (inputs : List (Fin 48 × Fin 48)) (a : Data) (j : Fin 16)
    (hj : j.val < 9) : (prepareState 31 work inputs a).regs j = false := by
  have hbefore : ∀ i : Fin 16, i.val < 9 → (beforeCopies 31 work a).regs i = false := by
    intro i hi
    exact resetWork_reg _ ⟨i.val, hi⟩
  suffices ∀ (b : Data), (∀ i : Fin 16, i.val < 9 → b.regs i = false) →
      (copyManyState inputs b).regs j = false from this _ hbefore
  induction inputs with
  | nil => intro b hb; exact hb j hj
  | cons p ps ih =>
      intro b hb
      apply ih (copyState p.1 p.2 b)
      intro i hi
      by_cases h0 : i = 0
      · subst i; simp [copyState, readRegs]
      · by_cases h1 : i = 1
        · subst i; simp [copyState, readRegs]
        · simpa [copyState, readRegs, h0, h1] using hb i hi

theorem within_mono {r s : ℕ} {a : State r s} {B C : ℕ}
    (h : Within a B) (hBC : B ≤ C) : Within a C := fun j => (h j).trans hBC

theorem within_clear (port : Fin 48) (a : Data) (B : ℕ) (h : Within a B) :
    Within (clearState port a) B := by
  intro j
  by_cases hj : j = port
  · subst j; simp [clearState]
  · simpa [clearState, hj] using h j

theorem within_copy (src dst : Fin 48) (a : Data) (B : ℕ) (h : Within a B) :
    Within (copyState src dst a) (2 * B) := by
  intro j
  by_cases hj : j = dst
  · subst j
    simp only [copyState_stack, Function.update_self, List.length_append]
    have hs := h src
    have hd := h dst
    omega
  · rw [copyState_frame src dst j a hj]
    exact (h j).trans (by omega)

theorem copyMany_bound (inputs : List (Fin 48 × Fin 48)) (a : Data) (B : ℕ)
    (h : Within a B) :
    Within (copyManyState inputs a) (2 ^ inputs.length * B) ∧
      copyManyCost inputs a ≤ inputs.length * (7 * 2 ^ inputs.length * B + 5) := by
  induction inputs generalizing a B with
  | nil => simpa [copyManyState, copyManyCost] using h
  | cons p ps ih =>
      obtain ⟨hs, ht⟩ := ih (copyState p.1 p.2 a) (2 * B) (within_copy p.1 p.2 a B h)
      constructor
      · simpa only [copyManyState, List.length_cons, pow_succ, Nat.mul_assoc,
          Nat.mul_left_comm, Nat.mul_comm] using hs
      · have hp := h p.1
        have hpow : 1 ≤ 2 ^ ps.length := one_le_pow₀ (by decide)
        have hpowB := Nat.mul_le_mul_right B hpow
        simp only [copyManyCost, List.length_cons, pow_succ]
        nlinarith

theorem within_reset (rs : List (Fin 16)) (a : Data) (B : ℕ) (h : Within a B) :
    Within (resetManyState rs a) B := by
  simpa only [Within, resetMany_stacks] using h

theorem within_embed {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 10)
    (a : Data) (out : State r s) (B : ℕ) (ha : Within a B) (ho : Within out B) :
    Within (embedState (register hr) (stack hs) a out) B := by
  classical
  intro j
  by_cases hj : ∃ i, stack hs i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [embedState_stack _ _ _ _ (stack_injective hs)]
    exact ho i
  · rw [embedState_stack_frame _ _ _ _ j hj]
    exact ha j

end SubexponentialSAT.Subexp.AssignmentInputCall

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentRecordViews
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed parser-based views of an actual framed word alphabet. -/

namespace SubexponentialSAT.Subexp.AssignmentRecordViews

open BitProgram StructuredCalls TupleProgram

abbrev data (v p f : Bool) (src acc out : List Bool) : Data :=
  ⟨![v, p, f], ![src, acc, out]⟩

theorem parse_eval (v p f : Bool) (bits rest acc out : List Bool) :
    Eval parse (6 * bits.length + 4)
      (data v p f (Encoding.frame bits ++ rest) acc out)
      (data false true f rest (bits.reverse ++ acc) out) := by
  let a := data v p f (Encoding.frame bits ++ rest) acc out
  let b := data false true f rest (bits.reverse ++ acc) out
  have ha : embedState firstTwo firstTwo a
      (⟨ParserProgram.pair v p, ParserProgram.pair (Encoding.frame bits ++ rest) acc⟩ : State 2 2) = a := by
    apply embedState_eq_of_ports _ _ _ _ _ firstTwo_injective firstTwo_injective
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hb : embedState firstTwo firstTwo a
      (⟨ParserProgram.pair false true, ParserProgram.pair rest (bits.reverse ++ acc)⟩ : State 2 2) = b := by
    apply embedState_eq_of_ports _ _ _ _ _ firstTwo_injective firstTwo_injective
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> first | rfl | exact (hi ⟨0, rfl⟩).elim | exact (hi ⟨1, rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> first | rfl | exact (hi ⟨0, rfl⟩).elim | exact (hi ⟨1, rfl⟩).elim
  have h := eval_call_lifted ParserProgram.frameProgram firstTwo firstTwo a
    firstTwo_injective firstTwo_injective
    (a := (⟨ParserProgram.pair v p,
      ParserProgram.pair (Encoding.frame bits ++ rest) acc⟩ : State 2 2))
    (b := (⟨ParserProgram.pair false true,
      ParserProgram.pair rest (bits.reverse ++ acc)⟩ : State 2 2))
    (ParserProgram.frame_trace bits rest acc v p)
  simpa only [parse, ha, hb] using h

theorem pop_eval (v p f b : Bool) (src acc out : List Bool) :
    Eval pop 1 (data v p f (b :: src) acc out) (data v true b src acc out) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.pop (0 : Fin 3) 2 1)
    (data v p f (b :: src) acc out))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [
      StructuredProgram.Atom.instr, execInstr, readRegs]
  · funext i; fin_cases i <;> simp [
      StructuredProgram.Atom.instr, execInstr, readRegs]

abbrev afterTag (rows : List (List Bool)) (rest acc out : List Bool) : Data :=
  match rows with
  | [] => data false true false rest acc out
  | bits :: rows => data false true true
      (Encoding.frame bits ++ (ProgramEncoding.encodeRecords rows ++ rest)) acc out

theorem pop_records_eval (p f : Bool) (rows : List (List Bool)) (rest acc out : List Bool) :
    Eval pop 1 (data false p f (ProgramEncoding.encodeRecords rows ++ rest) acc out)
      (afterTag rows rest acc out) := by
  cases rows with
  | nil => simpa [afterTag, ProgramEncoding.encodeRecords, Encoding.encodeList] using
      pop_eval false p f false rest acc out
  | cons bits rows =>
      simpa [afterTag, ProgramEncoding.encodeRecords, Encoding.encodeList, List.append_assoc] using
        pop_eval false p f true
          (Encoding.frame bits ++ (ProgramEncoding.encodeRecords rows ++ rest)) acc out

theorem loop_eval (rows : List (List Bool)) (rest acc out : List Bool) :
    Eval loop (6 * (rows.map List.length).sum + 6 * rows.length + 1)
      (afterTag rows rest acc out)
      (data false true false rest (rows.flatten.reverse ++ acc) out) := by
  induction rows generalizing acc with
  | nil => simpa [afterTag] using
      (Eval.while_false (body := .seq parse pop) (test := (2 : Fin 3))
        (a := data false true false rest acc out) rfl)
  | cons bits rows ih =>
      have hp := parse_eval false true true bits (ProgramEncoding.encodeRecords rows ++ rest) acc out
      have ht := pop_records_eval true true rows rest (bits.reverse ++ acc) out
      have h := Eval.while_true (test := (2 : Fin 3))
        (a := afterTag (bits :: rows) rest acc out) rfl
        (hp.seq ht) (ih (bits.reverse ++ acc))
      convert h using 1 <;>
        simp [ List.reverse_append, List.append_assoc, Nat.mul_add] ; omega

theorem transfer_eval (v p f : Bool) (src acc out : List Bool) :
    Eval transfer (3 * acc.length + 3) (data v p f src acc out)
      (data false false f src [] (acc.reverse ++ out)) := by
  have h := TupleProgram.transfer_eval (1 : Fin 3) 2 (0 : Fin 3) 1
    (by decide) (by decide) (data v p f src acc out)
  convert h using 1
  · simp []
  · apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [ readRegs]
    · funext i; fin_cases i <;> simp [ StackRoutines.transferStacks]

theorem setFirst_eval (v p f : Bool) (src acc out : List Bool) :
    Eval setFirst 1 (data v p f src acc out) (data false p f src acc out) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 3) false)
    (data v p f src acc out))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  · rfl

theorem flatten_eval (v p f : Bool) (rows : List (List Bool)) (rest out : List Bool) :
    Eval flatten (9 * (rows.map List.length).sum + 6 * rows.length + 6)
      (data v p f (ProgramEncoding.encodeRecords rows ++ rest) [] out)
      (data false false false rest [] (rows.flatten ++ out)) := by
  have h1 := setFirst_eval v p f (ProgramEncoding.encodeRecords rows ++ rest) [] out
  have h2 := pop_records_eval p f rows rest [] out
  have h3 := loop_eval rows rest [] out
  simp only [List.append_nil] at h3
  have h4 := transfer_eval false true false rest rows.flatten.reverse out
  simp only [List.reverse_reverse] at h4
  have h := h1.seq (h2.seq (h3.seq h4))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp [List.length_flatten]
  omega

theorem flatten_trace (v p f : Bool) (rows : List (List Bool)) (rest out : List Bool) :
    Trace flattenProgram (9 * (rows.map List.length).sum + 6 * rows.length + 7)
      ((data v p f (ProgramEncoding.encodeRecords rows ++ rest) [] out).withPC
        (some flattenProgram.entry))
      ((data false false false rest [] (rows.flatten ++ out)).withPC none) := by
  convert compiled_halt_trace (flatten_eval v p f rows rest out) 0 2 using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl

theorem setFlag_eval (v p f : Bool) (src acc out : List Bool) :
    Eval setFlag 1 (data v p f src acc out) (data v p false src acc out) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.set (2 : Fin 3) false)
    (data v p f src acc out))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  · rfl

end SubexponentialSAT.Subexp.AssignmentRecordViews

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpInputFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual frame and tag readers for the row/input-pair stream. -/

namespace SubexponentialSAT.SubexpInputFrames

open BitProgram StructuredCalls

theorem readField_execute {S : ℕ} (source target : Fin S) (h : source ≠ target)
    (d : State 8 S) (bits tail : List Bool)
    (hsource : d.stacks source = Encoding.frame bits ++ tail)
    (hempty : d.stacks target = []) :
    ∃ e : State 8 S, Eval (readField source target h) (6 * bits.length + 4) d e ∧
      e.stacks = Function.update (Function.update d.stacks source tail) target bits.reverse := by
  let p := ports source target h
  let e := RecordPrograms.state p d false true (d.regs 2) tail bits.reverse
  have hstart : RecordPrograms.state p d (d.regs 0) (d.regs 1) (d.regs 2)
      (Encoding.frame bits ++ tail) [] = d :=
    RecordPrograms.state_eq_self p d _ _ _ _ _ rfl rfl rfl hsource hempty
  have ht := RecordPrograms.reader_eval p d bits tail [] (d.regs 0) (d.regs 1) (d.regs 2)
  rw [hstart] at ht
  refine ⟨e, ?_, rfl⟩
  simpa only [List.append_nil] using ht

end SubexponentialSAT.SubexpInputFrames

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryRankProvenance
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The rank certificate refers to the packing and word table actually
produced by the native packing caller, with its original incidence order. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open PackingCallerProgram

def rationalUnits (Q : ℕ) : SubexponentialSAT.SubexpRowInterpolation.NodeUnits (rationalNode Q) :=
  SubexponentialSAT.SubexpRowInterpolation.NodeUnits.ofField _
    (by intro i j h; apply Fin.ext; exact_mod_cast (by simpa [rationalNode] using h : (i.val:ℚ)=(j.val:ℚ)))
    (by
      intro i
      have hi : (0:ℚ) ≤ (i.val:ℚ) := by positivity
      dsimp [rationalNode]
      linarith)

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms
end


