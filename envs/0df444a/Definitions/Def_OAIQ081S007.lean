-- Prove2me | Definitions.Def_OAIQ081S007
-- name    : OAIQ081S007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:22:49.274324+00:00
-- url     : https://prove2.me/theorems/6c4fbcbd-8b55-43d4-b09b-9b09e27ecde5
-- title:
--   Definitions bundle OAIQ081S007 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 99 declarations of OpenAI's Lean: 70 definitions, 5 inductive types or structures, 1 instance and 23 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.RingSetup.idempotentEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.RingSetup.serializationEnvelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.enumerationWork`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.exponentConstant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.forwardHighMask`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.maxTotalRank`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.measuredArity`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.sparseWork`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor.Counter.paddedBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.Hash.Ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashAlphabet.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashParameters.Ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant.emitRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant.emitStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant.key`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant.padStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashParametersProgram.ABI.inputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashParametersProgram.ABI.outputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashParametersProgram.ABI.registers`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashParametersProgram.ABI.selectorStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashParametersProgram.ABI.stackMap`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashParametersProgram.ABI.work`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashParametersProgram.logRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashParametersProgram.logStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgram.controllerBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgram.loadBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgram.roundBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgram.roundsBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgram.selectBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.degree`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.highPrefix`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan.scanBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan.tableBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.finishBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.polynomialBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.F`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.nonconstant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.precision`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Constants.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.arithmeticCleanPorts` and 35 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLog_CostAssembly`, `SubexponentialSAT_SqrtLog_CostAssemblyEnumeration`, `SubexponentialSAT_SqrtLog_CostAssemblyFinal`, `SubexponentialSAT_SqrtLog_CostAssemblyHighMask`, `SubexponentialSAT_SqrtLog_CostAssemblyProducedGuards`, `SubexponentialSAT_SqrtLog_CostAssemblyRankBudget`, `SubexponentialSAT_SqrtLog_CostAssemblyRingBounds`, `SubexponentialSAT_SqrtLog_CostAssemblySerialization`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramConstructor`, `SubexponentialSAT_SqrtLog_ExecutionHash`, `SubexponentialSAT_SqrtLog_ExecutionHashAlphabet`, `SubexponentialSAT_SqrtLog_ExecutionHashParameters`, `SubexponentialSAT_SqrtLog_HashCircuitProgramConstant`, `SubexponentialSAT_SqrtLog_HashParametersProgramFinal`, `SubexponentialSAT_SqrtLog_HashParametersProgramLog`, `SubexponentialSAT_SqrtLog_HashSelectProgram`, `SubexponentialSAT_SqrtLog_HashSelectProgramLoop`, `SubexponentialSAT_SqrtLog_HashSelectProgramRound`, `SubexponentialSAT_SqrtLog_HashSelectProgramScan`, `SubexponentialSAT_SqrtLog_HashSelectProgramSelect`, `SubexponentialSAT_SqrtLog_HighIncidenceProgram`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramScan`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramFinish`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScan`, `SubexponentialSAT_SqrtLog_IdempotentProgramCompleteCost`, `SubexponentialSAT_SqrtLog_IrreducibleSearch`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBasic`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapCost`, `SubexponentialSAT_SqrtLog_IrreducibleSearchCost`, `SubexponentialSAT_SqrtLog_LeafParametersProgram`, `SubexponentialSAT_SqrtLog_LeafProgramConstants`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramConstantBridge`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramPorts`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramPositivity`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramSpec`, `SubexponentialSAT_SqrtLog_LeafStatisticsSemantics`, `SubexponentialSAT_SqrtLog_ReconstructionProgramReady`, `SubexponentialSAT_SqrtLog_RingNodeProgram`, `SubexponentialSAT_SqrtLog_SquarefreeBasic`, `SubexponentialSAT_SqrtLog_SquarefreeProgramPrepend`, `SubexponentialSAT_SqrtLog_SquarefreeProgramScan`, `SubexponentialSAT_SqrtLog_SquarefreeSparseProduct`, `SubexponentialSAT_SqrtLog_SupportProgramCount`, `SubexponentialSAT_SubexpNodeCost`, `SubexponentialSAT_SubexpOrderedTupleData`, `SubexponentialSAT_SubexpSetupStorage`, `SubexponentialSAT_Subexp_IncidencePlanSpec`, `SubexponentialSAT_Subexp_PairScoreBounds`, `SubexponentialSAT_Subexp_TupleProgram`, `SubexponentialSAT_Truncation`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S029`, `OAIQ081S030`, `OAIQ081S031`, `OAIQ081S032`, `OAIQ081S033`, `OAIQ081S035`, `OAIQ081S036`, `OAIQ081S037`, `OAIQ081S038`, `OAIQ081S039`, `OAIQ081S040`, `OAIQ081S042` and `OAIQ081S043`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_residual_enumeration_ambient_bound` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.arity_pos_of_free_pos`; the proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_residual_enumeration_ambient_bound`.
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

namespace Filter

def emitStack : Fin 4 → Fin 14 := ![11, 9, 12, 13]


end Filter

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Sparse squarefree polynomials. The index monoid multiplies by support union,
so the coefficient algebra imposes X_v^2 = X_v without enumerating all supports. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

variable {V R : Type*}

/-- A type tag prevents the support-union multiplication leaking to all finsets. -/
structure Support (V : Type*) where
  vars : Finset V
  deriving DecidableEq

@[ext] theorem Support.ext {a b : Support V} (h : a.vars = b.vars) : a = b := by
  cases a; cases b; cases h; rfl

noncomputable section

variable [DecidableEq V] [CommSemiring R]

def weight (x : V → R) (s : Finset V) : R := ∏ v ∈ s, x v

end
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Truncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Canonical truncation before substitution

Polynomials are represented with U outermost, Z in the middle, and the X variables
innermost.  Truncation is an operation on canonical polynomial representatives;
we never assert that U = 1 defines a map out of the truncated quotient.
-/

namespace SubexponentialSAT.Truncation

noncomputable section

open scoped BigOperators

variable {R ι : Type*} [CommSemiring R]

/-- Delete all coefficients of degree at least n. -/
def trunc {A : Type*} [Semiring A] (n : ℕ) (P : Polynomial A) : Polynomial A :=
  Polynomial.ofFinsupp (.ofCoeff (P.toFinsupp.coeff.filter fun j => j < n))

end

end SubexponentialSAT.Truncation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparseProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

structure Index (V : Type*) where
  u : ℕ
  z : ℕ
  vars : Finset V
  deriving DecidableEq

namespace Index

variable {V : Type*} [DecidableEq V]

def join (a b : Index V) : Index V := ⟨a.u + b.u, a.z + b.z, a.vars ∪ b.vars⟩

end Index

end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SupportProgramCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SupportProgram

open scoped BigOperators

def count (n J : ℕ) : ℕ := ∑ j ∈ Finset.range J, n.choose j

@[simp] theorem count_zero (n : ℕ) : count n 0 = 0 := by simp [count]

@[simp] theorem count_succ (n J : ℕ) :
    count n (J + 1) = count n J + n.choose J := by
  simp [count, Finset.sum_range_succ]

@[simp] theorem count_empty_variables (J : ℕ) : count 0 (J + 1) = 1 := by
  induction J with
  | zero => simp [count]
  | succ J ih => rw [count_succ, ih]; simp

end SubexponentialSAT.SqrtLog.SupportProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Numerical assembly of the sparse-query costs.  `sparseWork` is an explicit
natural-valued upper cost, not a running-time oracle. Connecting an executable
program to these counters and charging coefficient arithmetic are separate
machine-refinement obligations. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology

/-- All resource counters remain visible. `ordinary` contains the fixed
polynomial work outside support enumeration; `bits` charges primitive
arithmetic. `calls` includes unsuccessful hash candidates and marked counts. -/
def sparseWork (n J setup calls branches labels bits ordinary : ℕ) : ℕ :=
  setup + calls * branches * labels * bits * (ordinary + 1)^8 *
    (SupportProgram.count n J + 1)^4

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The integer-signature and head-bucket enumeration costs, with the actual
joint-signature count rather than rank used as the exponential resource. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology

/-- Uniform head size and joint-label estimates give this concrete enumeration
counter.  The number of heads is a polynomial factor, not an exponent n. -/
def enumerationWork (labelBase rows heads headSize : ℕ) : ℕ :=
  labelBase^rows * heads * 2^headSize

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact runtime parameter semantics. Every definition below uses natural
arithmetic; the executable refinements are separate from these specifications.
The original ambient dimension is retained through high-incidence branching. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram

def precision (ambient clauses : ℕ) : ℕ := ambient + Nat.size clauses + 1

end SubexponentialSAT.SqrtLog.LeafParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyFinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One closed cost expression with actual jet order, hash candidate count,
high-incidence branch count, and joint-signature/head enumeration. The two
remaining algorithmic interfaces are setup work and ordinary primitive work. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology

/-- All fixed-k numerical losses are displayed in this coefficient. -/
noncomputable def exponentConstant (k q : ℕ) : ℝ :=
  707+4*(384*(((k*30*(256*(28*q+312)):ℕ):ℝ)+1)+1)

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_IncidencePlanSpec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Ordered incidence plans from finite scope lists

The numeric producer records incident factors in their input order. The
typed refinement uses the rank in that same list as the local slot.
-/

namespace SubexponentialSAT.Subexp.IncidencePlanSpec

/-- Record incident factor positions while advancing through the scope list. -/
def incidenceFrom (v start : ℕ) : List (List ℕ) → List ℕ
  | [] => []
  | C :: Cs =>
      if v ∈ C then start :: incidenceFrom v (start + 1) Cs
      else incidenceFrom v (start + 1) Cs

def incidentIndices (scopes : List (List ℕ)) (v : ℕ) : List ℕ :=
  incidenceFrom v 0 scopes

def degree (scopes : List (List ℕ)) (v : ℕ) : ℕ :=
  (incidentIndices scopes v).length

end SubexponentialSAT.Subexp.IncidencePlanSpec

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramSpec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Pure specifications for the native residual statistics scans. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
abbrev degree := Subexp.IncidencePlanSpec.degree

structure Totals where
  free : ℕ
  occurrence : ℕ
  incidences : ℕ
  uncovered : ℕ
  deriving DecidableEq, Repr

def Totals.add (t : Totals) (d : ℕ) : Totals :=
  ⟨t.free+1,max (max 1 d) t.occurrence,t.incidences+max 1 d,
    t.uncovered+(if d=0 then 1 else 0)⟩

def variableTotals (scopes : List (List ℕ)) : ℕ → List Bool → Totals → Totals
  | _,[],t => t
  | v,b::bs,t => variableTotals scopes (v+1) bs (if b then t else t.add (degree scopes v))

namespace Scope
def low (mask : List Bool) (v : ℕ) : Bool := !(mask[v]?.getD true)
end Scope

namespace Arity
def arity (mask : List Bool) (scopes : List (List ℕ)) (a : ℕ) :=
  scopes.foldl (fun t scope => max (scope.filter (Scope.low mask)).length t) a

end Arity
end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The runtime scan equals the statistics of the actual residual scope family,
with precisely one neutral singleton for each unused free coordinate. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open LeafStatisticsProgram

/-- This literal zero record is definitionally the native boot record. -/
def zero : Totals := ⟨0, 0, 0, 0⟩

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Elementary nondegeneracy conditions for the measured native statistics. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
open scoped BigOperators
open LeafStatisticsSemantics

def measured (scopes : List (List ℕ)) (mask : List Bool) : Totals :=
  variableTotals scopes 0 mask LeafStatisticsSemantics.zero

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyProducedGuards
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Instantiate the uniform guard theorem with the actual measured scope
statistics.  Only the retained-half and scope-size estimates remain as
upstream obligations; positivity and neutral coverage are derived here. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open LeafStatisticsProgram LeafParametersProgram

def measuredArity (scopes : List (List ℕ)) (mask : List Bool) : ℕ :=
  max (Arity.arity mask scopes 0)
    (if (measured scopes mask).uncovered = 0 then 0 else 1)

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical high-incidence selection from supplied explicit scopes

The input is a framed list of scopes with original natural-number identifiers.
Every query invokes the audited source-preserving record/membership scan. The
cutoff is a supplied unary integer in this module; no arithmetic or translation
from clauses to scopes is silently performed. The fixed program appends the
strict comparison bit and advances the original-coordinate counter.
-/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram

abbrev degree := Subexp.IncidencePlanSpec.degree

end SubexponentialSAT.SqrtLog.HighIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Full original-coordinate scan using a runtime unary loop counter. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram
attribute [local irreducible] Subexp.IncidencePlanSpec.degree

/-- Reverse order is the physical stack order; reversing gives coordinates
`0, ..., n-1`. Unused coordinates have degree zero and are retained in the mask. -/
def highPrefix (scopes : List (List ℕ)) (cut : ℕ) : ℕ → List Bool
  | 0 => []
  | n + 1 => decide (cut < degree scopes n) :: highPrefix scopes cut n

@[simp] theorem highPrefix_length (scopes : List (List ℕ)) (cut n : ℕ) :
    (highPrefix scopes cut n).length = n := by
  induction n <;> simp [highPrefix, *]

end SubexponentialSAT.SqrtLog.HighIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyHighMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Guard success for the actual forward mask computed from all supplied raw
scopes.  The high cutoff counts raw entries, including harmless overcounts. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open LeafStatisticsProgram LeafStatisticsSemantics HighIncidenceProgram

def forwardHighMask (scopes : List (List ℕ)) (n τ : ℕ) : List Bool :=
  (highPrefix scopes (((scopes.map List.length).sum * τ) ⌈/⌉ n) n).reverse

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyRankBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A single proof-only rank parameter for finitely many nodes or queries.
The maximum is used only in the analysis of attained signatures; it does not
require a runtime row-basis computation or bound the number of stored rows. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open scoped BigOperators

def maxTotalRank {X G : Type*} [Fintype G]
    (nodes : Finset X) (rank : X → G → ℕ) : ℕ :=
  nodes.sup (fun x => ∑ g, rank x g)

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblySerialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact ordinary cost of the two derived numeric metadata words. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly.RingSetup
open LeafParametersProgram


def serializationEnvelope (S : ℕ) : ℕ :=
  (2*S+3)+(7*S+5)+20*(S+1)+20*(S+1)+(2*S+3)+100*(S+S+1)^2

end SubexponentialSAT.SqrtLog.CostAssembly.RingSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native descending-index traversal. The remaining unary counter is the
runtime index passed to the callback. Prefixing each generated word therefore
materializes the final array in increasing index order, without a precomputed
array or a value-dependent control table. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan

def scanBudget (n K : ℕ) : ℕ := n*(K+9)+7

/-- The exact runtime budget for three source-preserving unary loops. -/
def tableBudget (n K : ℕ) : ℕ := scanBudget n (scanBudget n (scanBudget n K))

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

def finishBudget (t B W : ℕ) : ℕ :=
  Scan.tableBudget (3*t) (200*(3*t+B+1)) +500*(3*t+1)*(B+1)+30*(2*W+3)

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramCompleteCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! An explicit polynomial primitive-time envelope for native preparation
and all Newton iterations, as a function of precision and input length. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

def polynomialBudget (t inputWidth : ℕ) : ℕ :=
  100000000*(t+inputWidth+2)^4 +
  7*t*(41000*(3*t+1)^3*(2*t+1)^2) +
  (t+1)*(16*(inputWidth+1)+16)+2

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBasic
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

abbrev F := ZMod 3

/-- Test that a stored factor has a nonzero positive-degree coefficient. -/
def nonconstant {n : ℕ} (a : Fin n → F) : Bool :=
  (List.finRange n).any fun i => decide (0 < i.val ∧ a i ≠ 0)

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearch
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

instance primeThree : Fact (Nat.Prime 3) := ⟨by decide⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

/-- Frame payload without its final delimiter. -/
def escaped (bits : List Bool) : List Bool := bits.flatMap fun b => [true, b]

@[simp] theorem escaped_nil : escaped [] = [] := rfl
@[simp] theorem escaped_cons (b : Bool) (bits : List Bool) :
    escaped (b :: bits) = true :: b :: escaped bits := rfl

/-! The fixed ABI uses ten Boolean registers and nine Boolean stacks:
0 prior tuples, 1 saved alphabet, 2 current reversed tuple, 3 alphabet cursor,
4 reversed word, 5 output, 6 copied tuple, 7 copy scratch, 8 unary depth.
Registers 0--2 and 3--5 belong to the two framed iterators, 6--7 are scratch,
and 8--9 belong to the eventual depth loop. -/

end SubexponentialSAT.Subexp.TupleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNodeCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! # A polynomial instruction bound for the fixed four-coordinate node program -/

namespace SubexponentialSAT.SubexpNodeCost

open Subexp.TupleProgram

def payloadSize (xs : List (List Bool)) : ℕ := (xs.map List.length).sum

@[simp] theorem payloadSize_nil : payloadSize [] = 0 := rfl
@[simp] theorem payloadSize_cons (x : List Bool) (xs : List (List Bool)) :
    payloadSize (x :: xs) = x.length + payloadSize xs := rfl
@[simp] theorem payloadSize_append (xs ys : List (List Bool)) :
    payloadSize (xs ++ ys) = payloadSize xs + payloadSize ys := by
  simp [payloadSize]
@[simp] theorem payloadSize_reverse (xs : List (List Bool)) :
    payloadSize xs.reverse = payloadSize xs := by simp [payloadSize]

theorem payloadSize_prefix (word : List Bool) (alphabet : List (List Bool)) :
    payloadSize (alphabet.map (word ++ ·)) =
      alphabet.length * word.length + payloadSize alphabet := by
  induction alphabet with
  | nil => simp
  | cons a as ih => simp [ih, Nat.add_mul]; omega

end SubexponentialSAT.SubexpNodeCost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpOrderedTupleData
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! # Exact lexicographic tuple order for the selected quartic search -/

namespace SubexponentialSAT.SubexpOrderedTupleData

def orderedCartesian (rows alphabet : List (List Bool)) : List (List Bool) :=
  rows.flatMap fun row => alphabet.map (row ++ ·)

end SubexponentialSAT.SubexpOrderedTupleData

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairScoreBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Closed bounds for the actual tuple generator and pair scorer

All costs below are the explicit bounds attached to proved executions of the
fixed programs.  The tuple recurrence is bounded from its actual list sizes;
no scalar-operation or callback-cost oracle is assumed.
-/

namespace SubexponentialSAT.Subexp.PairScoreBounds

def volume (rows : List (List Bool)) : ℕ := (rows.map List.length).sum

@[simp] theorem volume_nil : volume [] = 0 := rfl
@[simp] theorem volume_cons (row : List Bool) (rows : List (List Bool)) :
    volume (row :: rows) = row.length + volume rows := rfl

@[simp] theorem volume_append (xs ys : List (List Bool)) :
    volume (xs ++ ys) = volume xs + volume ys := by simp [volume]

@[simp] theorem volume_reverse (xs : List (List Bool)) :
    volume xs.reverse = volume xs := by simp [volume]

theorem volume_le (rows : List (List Bool)) (L : ℕ)
    (h : ∀ row ∈ rows, row.length ≤ L) : volume rows ≤ rows.length * L := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    have hr := h row (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [volume_cons, List.length_cons]
    nlinarith

end SubexponentialSAT.Subexp.PairScoreBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Counted scalar implementation of the irreducible-polynomial search

The traces below execute the finite arithmetic and Boolean tests and count
their scalar operations. This is a scalar trace, not a claim that arbitrary
natural-number indexing or list construction costs one primitive bit step.
All stored scalar coefficients are in the fixed field F₃.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open scoped BigOperators

theorem succ_le_three_pow (d : ℕ) : d + 1 ≤ 3 ^ d := by
  induction d with
  | zero => simp
  | succ d ih => rw [pow_succ]; omega

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

def workRegisters : List (Fin 16) := List.ofFn (fun i : Fin 9 => i.castLE (by decide))

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

theorem first_term_bound (d N W : ℕ) (hN : 1 ≤ N) (hdN : d + 1 ≤ N) :
    800 * (d + 1) * N * ((d + 1) * W + 1) ≤ (800 * (W + 1)) * N^4 := by
  have hN34 : N^3 ≤ N^4 := pow_le_pow_right₀ hN (by decide)
  calc
    _ ≤ 800 * N * N * (N * W + N) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right N (Nat.mul_le_mul_left 800 hdN))
        (Nat.add_le_add (Nat.mul_le_mul_right W hdN) hN)
    _ = (800 * (W + 1)) * N^3 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hN34

theorem second_term_bound (d N W : ℕ) (hN : 1 ≤ N) (hdN : d + 1 ≤ N) :
    800 * ((d + 1) + (d + 1) + 1) * (9 * N^2) *
      (((d + 1) + (d + 1) + 1) * W + 1) ≤ (21600 * (3 * W + 1)) * N^4 := by
  have hfN : (d + 1) + (d + 1) + 1 ≤ 3 * N := by omega
  calc
    _ ≤ 800 * (3 * N) * (9 * N^2) * ((3 * N) * W + N) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 800 hfN))
        (Nat.add_le_add (Nat.mul_le_mul_right W hfN) hN)
    _ = _ := by ring

theorem rest_bound (d N K : ℕ) (hN : 1 ≤ N) (hdN : d + 1 ≤ N) :
    28 * d + 4 * K + 89 ≤ (28 + 4 * K + 89) * N^4 := by
  have hN4 : N ≤ N^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hN (show 1 ≤ 4 by decide)
  have hd4 : d ≤ N^4 := (Nat.le_succ d).trans (hdN.trans hN4)
  have h14 : 1 ≤ N^4 := hN.trans hN4
  calc
    _ = 28 * d + (4 * K + 89) * 1 := by omega
    _ ≤ 28 * N^4 + (4 * K + 89) * N^4 :=
      Nat.add_le_add (Nat.mul_le_mul_left 28 hd4) (Nat.mul_le_mul_left _ h14)
    _ = _ := by simp only [add_mul, Nat.add_assoc]

theorem terms_bound (d N W K : ℕ) (hN : 1 ≤ N) (hdN : d + 1 ≤ N) :
    800 * (d + 1) * N * ((d + 1) * W + 1) +
      800 * ((d + 1) + (d + 1) + 1) * (9 * N^2) *
        (((d + 1) + (d + 1) + 1) * W + 1) + 28 * d + 4 * K + 89 ≤
      (800 * (W + 1) + 21600 * (3 * W + 1) + 28 + 4 * K + 89) * N^4 := by
  have h := Nat.add_le_add (Nat.add_le_add (first_term_bound d N W hN hdN)
    (second_term_bound d N W hN hdN)) (rest_bound d N K hN hdN)
  simpa only [add_mul, Nat.add_assoc] using h

theorem factor_power (d : ℕ) :
    3 ^ ((d + 1) + (d + 1)) = 9 * (3 ^ d)^2 := by
  rw [show (d + 1) + (d + 1) = d * 2 + 2 by omega, pow_add, pow_mul]
  norm_num [Nat.mul_comm]

end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramConstants
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical dynamic-dimension constants. The same fixed loop emits a scalar
seed in coordinate zero followed by scalar zero in every other coordinate. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Constants

def budget (B d : ℕ) : ℕ := d * (22 * B + 25) + 4 * B + 16

end SubexponentialSAT.SqrtLog.LeafProgram.Constants

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramPorts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed physical layout for native ring preparation.

The local setup has 32 registers and 640 stacks.  It can be lifted into the
40-register/768-stack leaf caller.  The collector's stacks 320--339 are never
used.  Arithmetic metadata is written directly to its native consumer port;
temporary search, scalar, table, and node data have disjoint workspaces.
-/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

/-- Dynamic-d constant vectors have separate scratch from table generation.
Only their output location varies among full one, minus one, and zero. -/
def constant (out : Fin 640) : Fin 27 → Fin 640 := fun i =>
  if i = 0 then 538 else if i = 15 then out else if i = 22 then 204 else
  if i = 24 then 203 else ⟨584 + i.val, by omega⟩

/-- The closed idempotent program is run in a private workspace after the
ordinary ring setup. Its local cleanup therefore cannot clear native t or
other metadata. Repeating its scalar preparation has polynomial cost. -/
def idempotent (i : Fin 41) : Fin 640 := ⟨480+i.val, by omega⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramReady
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Static readiness obtained from the physically prepared input tapes.
No arithmetic, program trace, or canonicality hypothesis is hidden here. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.InputReady

open SubexponentialSAT

/-- Exactly the empty physical ports used by the two native arithmetic banks
and the dense base-word adder. Ports5/10 are populated by the paid entry code. -/
def emptyPorts : List (Fin 320) :=
  [0,1,2,3,4,6,7,8,9,11,12,13,112,113,114,115,116,117,118,119,120,
   128,129,130,131,132,134,135,136,137,138,139,141,142,143,144,
   146,147,148,149,151,152,153,154,155,156,157,158,159,198,199,200]

end SubexponentialSAT.SqrtLog.ReconstructionProgram.InputReady

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingNodeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed physical program generating all nonzero radix nodes up to a runtime
bound. The bound counts down, so prepending each row gives ascending order. -/
namespace SubexponentialSAT.SqrtLog.RingNodeProgram

open SubexponentialSAT
/-- One node extraction including binary decrement and the next loop test. -/
def stepBudget (B L d : ℕ) : ℕ :=
  d * (100 * (B + L + 1)^2 + 14*B + 8*L + 19) + 25*L + 7*d + 35

/-- Explicit bit-program instruction budget, before the fixed primitive overhead. -/
def budget (B L d Q : ℕ) : ℕ := 8*L + 8 + Q * (stepBudget B L d + 1)

end SubexponentialSAT.SqrtLog.RingNodeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramConstantBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

def constantScratch : List (Fin 27) :=
  [1,2,3,4,6,7,8,11,13,14,15,19,20,23]

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The fixed executable preparation pipeline.  Its input is the actual
numerical bank emitted by `LeafParametersProgram`; no field polynomial,
modulus, multiplication table, nodes, or idempotent coefficients are inputs.
The stage-by-stage execution theorem is separate from this code definition.
-/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

def idempotentPorts : List (Fin 640) :=
  (List.finRange 41).map idempotent

def arithmeticCleanPorts : List (Fin 640) :=
  (ReconstructionProgram.InputReady.emptyPorts ++ [5,10,104]).map
    (fun i : Fin 320 => i.castLE (by decide))


end SubexponentialSAT.SqrtLog.LeafRingSetupProgram


/-! Arithmetic consumers use the same bytes generated by the preceding
stages.  These are structural handoff lemmas; the complete production
trace must establish `NativeBytes` before invoking them. -/

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

/-- Explicit clearing makes the constant constructor independent of the
search/table producers' discarded work tapes. -/
def constantStartPorts : List (Fin 640) :=
  [538,639] ++ ([207,211,280] : List (Fin 640)).flatMap
    (fun out => constantScratch.map (constant out))

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

def idempotentStartPorts : List (Fin 640) := 281::639::idempotentPorts

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyRingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed polynomial bound for the actual ring producer's numerical cost.
The size cap includes the unary numeric bank bound V, so large stored values
are not silently replaced by their binary lengths. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly.RingSetup

open LeafRingSetupProgram LeafParametersProgram

def idempotentEnvelope (t W : ℕ) : ℕ :=
  idempotentStartPorts.length*(2*W+3)+(7*W+8)+32+
  IdempotentProgram.polynomialBudget t W+(7*(6*t^2)+8)

end SubexponentialSAT.SqrtLog.CostAssembly.RingSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramConstructor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Width-generic padded constant and linear polynomial constructors. The
physical instruction table is unchanged; its zero-cell width and polynomial
length are runtime tapes. All output construction and cleanup is charged. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor
namespace Counter
def paddedBits (W : ℕ) (low high : List Bool) : ℕ → List Bool
  | 0 => []
  | 1 => low
  | n + 2 => low ++ high ++ List.replicate (n * W) false

end Counter

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ExecutionHashAlphabet
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A paid, runtime-sized alphabet for the sparse-hash selector.  The existing
binary countdown emits all words below the supplied count; this wrapper also
clears its padded counter.  No instruction table depends on the count or word
width.  Only the six explicitly mapped stacks can change. -/

namespace SubexponentialSAT.SqrtLog.Execution.HashAlphabet

def budget (count width : ℕ) : ℕ :=
  (count + 1) * (60 * width + 60) + 2 * width + 3

end SubexponentialSAT.SqrtLog.Execution.HashAlphabet

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed unary-counter controller for K greedy rounds. The round command
must supply a paid actual execution; the counter is runtime stack data. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

def roundsBudget (cost count : ℕ) : ℕ := count * (cost + 2) + 2

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Measured enumeration and binary argmin over unevaluated payloads. The mass
callback is fixed executable syntax and must provide a trace for each payload.
The loop therefore charges every losing candidate as well as the winner. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

variable {r s : ℕ}

def loadBudget (C cost : ℕ) : ℕ := 6 * C + cost + 10

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectProgramSelect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Unseeded binary argmin. The first mass evaluation, first score copy and
all remaining candidate evaluations are paid by the same finite program. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

variable {r s : ℕ}

def selectBudget (B C cost count : ℕ) : ℕ :=
  (count + 1) * (loadBudget C cost + 100 * (B + C + 1) + 4)

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectProgramRound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One concrete greedy round copies the saved family, evaluates every row,
selects a binary minimum, and prepends the winner to the current matrix. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.Subexp

variable {r s : ℕ}

def roundBudget (B C cost familyBits count : ℕ) : ℕ :=
  7 * familyBits + 5 + selectBudget B C cost count + 5 * C + 2 * B + 10

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed deterministic hash selector. Its input carries a unary round
counter and a saved candidate queue. Every round copies that queue, pays
for every mass evaluation, takes a binary argmin, and appends the winner.
The only computational premise is the explicit trace specification of the
mass subprogram; no semantic SAT or mass instruction occurs in the code. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.Subexp

variable {r s : ℕ}

def controllerBudget (B C cost familyBits count rounds : ℕ) : ℕ :=
  roundsBudget (roundBudget B C cost familyBits count) rounds

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ExecutionHash
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete native sparse-hash controller, including alphabet expansion,
unary control construction and candidate generation.  The remaining service
contract is an actual bit-machine evaluation of each candidate's mass; it is
not an arithmetic oracle or a unit-cost semantic callback. -/

namespace SubexponentialSAT.SqrtLog.Execution.Hash

open HashSelectProgram

structure Ports (R S : ℕ) where
  register : Fin 10 → Fin R
  stack : Fin 14 → Fin S
  register_injective : Function.Injective register
  stack_injective : Function.Injective stack

end SubexponentialSAT.SqrtLog.Execution.Hash

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashParametersProgramLog
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native logarithmic component of the hash-parameter setup. -/
namespace SubexponentialSAT.SqrtLog.HashParametersProgram

def logRegisters : Fin 3 → Fin 8 := Fin.castAdd 5
def logStacks : Fin 3 → Fin 22 := ![3,15,16]

end SubexponentialSAT.SqrtLog.HashParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashParametersProgramFinal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Production hash-parameter program. The arithmetic, ABI, and cost proofs
are checked together; the former split module paths remain compatibility
imports of this file. -/

/-! Fixed native arithmetic for alphabet size, sparse-code distance parameter,
and selector round cap. Every operation is a proved finite Boolean program. -/


/-! Exact metadata loading and selector-port installation. Metadata is outside
all fourteen selector ports. The fixed scratch bank is physically cleared. -/
namespace SubexponentialSAT.SqrtLog.HashParametersProgram.ABI

open SubexpSetupStorage

def registers : Fin 8 → Fin 16 := Fin.castAdd 8
def stackMap (i : Fin 22) : Fin 44 := ⟨17+i.val,by omega⟩
def work : List (Fin 44) := List.ofFn stackMap
def inputs : List (Fin 44 × Fin 44) := [(14,17),(15,18),(16,19)]
def outputs : List (Fin 44 × Fin 44) := [(31,0),(26,5),(30,6)]

end SubexponentialSAT.SqrtLog.HashParametersProgram.ABI


/-! Polynomial step budget for the complete physical parameter setup. -/


/-! Exported fixed program and the selector's actual fourteen-port interface. -/
namespace SubexponentialSAT.SqrtLog.HashParametersProgram.ABI

open SubexpSetupStorage

def selectorStacks : Fin 14 → Fin 44 := Fin.castAdd 30

end SubexponentialSAT.SqrtLog.HashParametersProgram.ABI

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ExecutionHashParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocation of the actual metadata arithmetic into a caller which also
holds the formula and ring context. Only binary n, m and B are supplied;
3m, the tuple depth and the number of hash rounds are computed by the fixed
parameter program. The empty-formula branch is handled by the leaf caller. -/

namespace SubexponentialSAT.SqrtLog.Execution.HashParameters

structure Ports (R S : ℕ) where
  register : Fin 16 → Fin R
  stack : Fin 44 → Fin S
  register_injective : Function.Injective register
  stack_injective : Function.Injective stack

end SubexponentialSAT.SqrtLog.Execution.HashParameters

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramPrepend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed primitive emission of a key/coefficient record. Both source words
are reversed; all bits, framing tags and source cleanup are executed. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program

def payloadPorts : Fin 2 → Fin 3 := ![1,2]
def keyPorts : Fin 2 → Fin 3 := ![0,2]

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramConstant
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Construct a cached sparse constant from a shape word and a forward flat
coefficient. Zero support bits, key delimiters, reversal, record framing and
cleanup all execute on the native bit machine. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant

def key (n : ℕ) : List Bool := List.replicate (n+2) false

def padStacks : Fin 3 → Fin 6 := Fin.castAdd 3

def emitRegisters : Fin 3 → Fin 8 := Fin.castAdd 5
def emitStacks : Fin 3 → Fin 6 := ![2,4,5]
end SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-sized dictionary deletion. One fixed loop visits every encoded
record and retains every nonmatching record, reversing record order. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program

abbrev ByteRecord := List Bool × List Bool

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end


