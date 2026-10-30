-- Prove2me | Definitions.Def_OAIQ081S016
-- name    : OAIQ081S016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:24:12.152879+00:00
-- url     : https://prove2.me/theorems/edc1deb5-7ab7-4398-8702-d0237b60c1e4
-- title:
--   Definitions bundle OAIQ081S016 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 147 declarations of OpenAI's Lean: 85 definitions, 6 inductive types or structures and 56 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Node.cleanupPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.boolInt`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.planIndex`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.digitAt`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.shift`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.Protected`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.conversionCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.numericCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.inputIndex`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.inputPlan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.localPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.localRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.outputPlan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.privatePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.coreWritePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.nodeFramePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.nodeInputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.nodes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.numericPlan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.parameters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.registers`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.ringCachePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.scalar`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.search`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.table`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.unaryPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.unaryRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.wideRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.Tape`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.Tape`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.clean`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.tapes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.D`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.High`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.innerHigh`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.unary`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.wideTapes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan.unary`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.Store`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.lowPorts` and 51 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLog_LeafProgramNode`, `SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteBaseline`, `SubexponentialSAT_SqrtLog_LeafProgramNodeConcretePlan`, `SubexponentialSAT_SqrtLog_LeafProgramNodeFrames`, `SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsShift`, `SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsTarget`, `SubexponentialSAT_SqrtLog_LeafProgramQueryCleanup`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendConvert`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendNumericBound`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramBase`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramInterpolation`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramPorts`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramTableBridge`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramWords`, `SubexponentialSAT_SqrtLog_MomentsProgramDictionaryState`, `SubexponentialSAT_SqrtLog_MomentsProjectionProgramBase`, `SubexponentialSAT_SqrtLog_MomentsProjectionProgramNative`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramState`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramFrame`, `SubexponentialSAT_SqrtLog_ResidualEmbeddingBranch`, `SubexponentialSAT_SqrtLog_ResidualEmbeddingIncidence`, `SubexponentialSAT_SqrtLog_RingCoefficientLiftProgram`, `SubexponentialSAT_SqrtLog_RingProgramTableBasic`, `SubexponentialSAT_SqrtLog_RingProgramTableMachine`, `SubexponentialSAT_SqrtLog_RingProgramTableRound`, `SubexponentialSAT_SqrtLog_RingProgramTableSemantics`, `SubexponentialSAT_SqrtLog_RingProgramTableSetup`, `SubexponentialSAT_SqrtLog_RingProgramTableStep`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgram`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramBasic`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramBlock`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramMatrix`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramOuter`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramRowStep`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramRows`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramSemantics`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramStep`, `SubexponentialSAT_SqrtLog_TotalOrderBasic`, `SubexponentialSAT_SubexpArgumentProgram`, `SubexponentialSAT_SubexpBasePUnranking`, `SubexponentialSAT_SubexpExponentProgram`, `SubexponentialSAT_SubexpFieldRowPreparation`, `SubexponentialSAT_SubexpKeyPadProgram`, `SubexponentialSAT_SubexpTaylorFrames`, `SubexponentialSAT_Subexp_AssignmentInitProgram`, `SubexponentialSAT_Subexp_AssignmentInputProgram`, `SubexponentialSAT_Subexp_AssignmentInputState`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S038`, `OAIQ081S039`, `OAIQ081S040`, `OAIQ081S043` and `OAIQ081S058`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`.
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

def subsetReg : Fin 12 → Fin 13 := Fin.castAdd 1
def subsetStack : Fin 10 → Fin 11 := Fin.castAdd 1

end Guard

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpArgumentProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite-control serialization of marked-incidence arguments

The raw-list ABI is `Encoding.encodeList id` of record bodies
`frame key ++ frame coefficient`. Coefficient payloads are opaque bit strings.
The term writer consumes one coefficient frame and a reversed key, restoring
its scratch stacks. All loops below execute fixed Boolean/stack instructions.
-/

namespace SubexponentialSAT.SubexpArgumentProgram

def writerRegs (i : Fin 3) : Fin 5 := ⟨i.val, by omega⟩

def destination (outer : Bool) : Fin 6 := if outer then 3 else 5

theorem writerRegs_injective : Function.Injective writerRegs := by
  intro i j h
  exact Fin.ext (congrArg (fun v : Fin 5 => v.val) h)

abbrev finishedRegs (regs : Fin 5 → Bool) : Fin 5 → Bool :=
  Function.update (Function.update regs 0 true) 1 false

end SubexponentialSAT.SubexpArgumentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

/-- The finite tape layout of additive sparse insertion. All fields are runtime
bit strings; this record is used only to state the physical program invariant. -/
structure Tape where
  modulus : List Bool := []
  width : List Bool := []
  count : List Bool := []
  dict : List Bool := []
  query : List Bool := []
  coeff : List Bool := []
  remain : List Bool := []
  found : List Bool := []
  left : List Bool := []
  right : List Bool := []
  out : List Bool := []
  steps : List Bool := []
  result : List Bool := []
  combined : List Bool := []

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

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


/-- Division workspace 0--7; arity counter8; copied width9; transfer scratch10;
reversed digit stream11; final forward digit stream12. -/
def tapes (rem modulus rank quotient arity width scratch rev output : List Bool) :
    Fin 13 → List Bool :=
  fun i => if i = 0 then rem else if i = 5 then modulus else if i = 6 then rank
    else if i = 7 then quotient else if i = 8 then arity else if i = 9 then width
    else if i = 10 then scratch else if i = 11 then rev else if i = 12 then output else []

@[simp] theorem tapes_0 (rem modulus rank quotient arity width scratch rev output : List Bool) :
    tapes rem modulus rank quotient arity width scratch rev output 0 = rem := rfl
@[simp] theorem tapes_5 (rem modulus rank quotient arity width scratch rev output : List Bool) :
    tapes rem modulus rank quotient arity width scratch rev output 5 = modulus := rfl
@[simp] theorem tapes_6 (rem modulus rank quotient arity width scratch rev output : List Bool) :
    tapes rem modulus rank quotient arity width scratch rev output 6 = rank := rfl
@[simp] theorem tapes_7 (rem modulus rank quotient arity width scratch rev output : List Bool) :
    tapes rem modulus rank quotient arity width scratch rev output 7 = quotient := rfl
@[simp] theorem tapes_8 (rem modulus rank quotient arity width scratch rev output : List Bool) :
    tapes rem modulus rank quotient arity width scratch rev output 8 = arity := rfl
@[simp] theorem tapes_9 (rem modulus rank quotient arity width scratch rev output : List Bool) :
    tapes rem modulus rank quotient arity width scratch rev output 9 = width := rfl
@[simp] theorem tapes_10 (rem modulus rank quotient arity width scratch rev output : List Bool) :
    tapes rem modulus rank quotient arity width scratch rev output 10 = scratch := rfl
@[simp] theorem tapes_11 (rem modulus rank quotient arity width scratch rev output : List Bool) :
    tapes rem modulus rank quotient arity width scratch rev output 11 = rev := rfl
@[simp] theorem tapes_12 (rem modulus rank quotient arity width scratch rev output : List Bool) :
    tapes rem modulus rank quotient arity width scratch rev output 12 = output := rfl


def divisionPorts : Fin 8 ↪ Fin 13 where
  toFun i := i.castLE (by decide)
  inj' := by
    intro i j h
    apply Fin.ext
    simpa using congrArg (fun x : Fin 13 => x.val) h

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

def stackPort (i : Fin 13) : Fin 15 := i.castLE (by decide)

end SubexponentialSAT.SubexpFieldRowPreparation

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

structure Tape where
  input : List Bool := []
  target : List Bool := []
  key : List Bool := []
  coeff : List Bool := []
  work : List Bool := []
  newkey : List Bool := []
  tmp : List Bool := []
  tmp2 : List Bool := []
  output : List Bool := []
  framed : List Bool := []

def tapes (a : Tape) : Fin 10 → List Bool :=
  ![a.input,a.target,a.key,a.coeff,a.work,a.newkey,a.tmp,a.tmp2,a.output,a.framed]

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

/-- All scratch tapes are empty at a record boundary. -/
def clean (source query output : List Bool) : Tape :=
  { input:=source,target:=query.reverse,output:=output }

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
abbrev D := MomentsProgram.Dictionary.Tape

structure High where
  zero : List Bool := []
  t : List Bool := []
  J : List Bool := []
  u : List Bool := []
  z : List Bool := []
  remU : List Bool := []
  remZ : List Bool := []
  mask : List Bool := []
  output : List Bool := []
  shape : List Bool := []
  tmp1 : List Bool := []
  tmp2 : List Bool := []
  tmp3 : List Bool := []

def wideTapes (a : D) (h : High) : Fin 40 → List Bool :=
  ![a.out,[],[],[],[],a.modulus,[],[],a.left,a.right,[],a.steps,a.width,[],[],
    a.dict,a.query,a.coeff,a.remain,[],[],[],a.found,[],a.count,a.result,a.combined,
    h.zero,h.t,h.J,h.u,h.z,h.remU,h.remZ,h.mask,h.output,h.shape,h.tmp1,h.tmp2,h.tmp3]

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! Actual stack construction of the sparse key (u,z,empty support), followed
by the paid query cleanup and unary-index increment. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram

def unary (u : ℕ) : List Bool := List.replicate u true

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! One concrete (u,z) coefficient fetch, addition, and index advance. -/


/-! The U loop is driven by a real unary stack. Every visit invokes the
concrete key builder and dictionary scan; no callback is left abstract. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram

def innerHigh (h : High) (u : ℕ) (rem : List Bool) : High :=
  {h with u:=unary u,remU:=rem}

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! Seed one Z accumulator from the cached zero vector and append the
completed coefficient to the output, paying for every copy and reversal. -/


/-! Runtime Z enumeration. Completed fixed-width coefficients are prepended
in reverse and are restored once by the final output transfer. -/


/-! Build the all-false support mask from the actual ambient shape stack.
The loop length is the ambient number of variables, including unused ones. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The closed node worker: generate the actual head/bucket tables, stage the
ring caches, enumerate bounded supports, execute all assignment factors, and
read the resulting dense jet. Its final clear reclaims the node workspace.
The instruction table has no supplied node evaluator or precomputed jet. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.Node
open SubexponentialSAT

/-- The actual masters are outside this bank. The node input78 is consumed;
the dense output102 is the sole retained new value. Port104 remains empty,
which is an allowed shape in the indexed node collector. -/
def cleanupPorts : List (Fin 768) :=
  (List.finRange 768).filter fun i =>
    decide ((i.val < 142 ∧ i.val ≠ 102) ∨
      (143 ≤ i.val ∧ i.val < 192) ∨
      (340 ≤ i.val ∧ i.val < 700) ∨ (710 ≤ i.val ∧ i.val < 713))

end SubexponentialSAT.SqrtLog.LeafProgram.Node

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ResidualEmbeddingBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed high-coordinate branches and original ambient coordinate labels.
Only free assignments are summed inside one branch. -/
namespace SubexponentialSAT.SqrtLog.ResidualEmbedding

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Free (H : Finset V) := {v : V // v ∉ H}

def inclusion (H : Finset V) : Free H ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

omit [Fintype V] [DecidableEq V] in
@[simp] theorem inclusion_apply (H : Finset V) (v : Free H) : inclusion H v = v.val := rfl

end SubexponentialSAT.SqrtLog.ResidualEmbedding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_TotalOrderBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Shared total-order truncation of nilpotent expansions

The outer variable is a formal marker U. `output` evaluates the canonical
representative after truncation at U = 1. This is an additive operation on
polynomials, not a homomorphism out of the quotient by U^t.
-/
namespace SubexponentialSAT.SqrtLog.TotalOrder

noncomputable section

open scoped BigOperators

variable {R S α : Type*} [CommSemiring R] [CommSemiring S]

/-- A finite expansion whose s-th coefficient carries s powers of h. -/
def row (t : ℕ) (e : ℕ → R) (h : R) : Polynomial R :=
  ∑ j ∈ Finset.range t, Polynomial.monomial j (e j * h ^ j)

@[simp] theorem coeff_row (t j : ℕ) (e : ℕ → R) (h : R) :
    (row t e h).coeff j = if j < t then e j * h ^ j else 0 := by
  classical
  simp [row, Polynomial.coeff_monomial]

/-- The full product is a semantic object; the executable version uses arrays. -/
def fullProduct (s : Finset α) (t : ℕ) (e : α → ℕ → R) (h : α → R) :
    Polynomial R := ∏ i ∈ s, row t (e i) (h i)

@[simp] theorem map_row (f : R →+* S) (t : ℕ) (e : ℕ → R) (h : R) :
    (row t e h).map f = row t (fun j => f (e j)) (f h) := by
  classical
  simp [row, Polynomial.map_sum]

@[simp] theorem map_fullProduct (f : R →+* S) (s : Finset α) (t : ℕ)
    (e : α → ℕ → R) (h : α → R) :
    (fullProduct s t e h).map f =
      fullProduct s t (fun i j => f (e i j)) (fun i => f (h i)) := by
  classical
  simp [fullProduct, Polynomial.map_prod]

end

end SubexponentialSAT.SqrtLog.TotalOrder

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The reconstruction target retains one shared total U-order. Its source
rows retain original variable identifiers, and its outer sum is over free
Boolean assignments in one fixed-high branch. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

open scoped BigOperators
open Polynomial
noncomputable section

variable {R : Type*} [CommRing R] {V : Type*} [Fintype V] [DecidableEq V]

/-- The digit family may be the actual computed coefficient array; there is
no assumption that its untruncated product has the required small degree. -/
def digitAt {t : ℕ} (digits : Fin t → R[X]) (L : R[X]) (j : ℕ) : R[X] :=
  if hj : j < t then (digits ⟨j,hj⟩).comp L else 0

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcretePlan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The original-address source lookup is exactly the owner pullback used by
integer-bucket locality, including repeated owner incidences. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators

variable {r Q d n : ℕ}

def planIndex (ps : List (ℕ × ℕ)) (n f j : ℕ) (h : (j,n+f)∈ps) : Fin ps.length :=
  ⟨ps.idxOf (j,n+f),by
    simpa only [List.idxOf,beq_eq_decide] using List.idxOf_lt_length_iff.mpr h⟩

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ResidualEmbeddingIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Residual incidence rows may be stored at original ambient indices by
padding high coordinates with zero. Their jet and evaluation are unchanged. -/
namespace SubexponentialSAT.SqrtLog.ResidualEmbedding

open scoped BigOperators
noncomputable section

variable {V A R : Type*} [Fintype V] [DecidableEq V]

def padZero [Zero A] (H : Finset V) (f : Free H → A) (v : V) : A :=
  if hv : v ∉ H then f ⟨v, hv⟩ else 0

omit [Fintype V] in
@[simp] theorem padZero_low [Zero A] (H : Finset V) (f : Free H → A) (v : Free H) :
    padZero H f v.val = f v := by simp [padZero, v.property]

omit [Fintype V] in
@[simp] theorem padZero_high [Zero A] (H : Finset V) (f : Free H → A) (v : V)
    (hv : v ∈ H) : padZero H f v = 0 := by simp [padZero, hv]

end
end SubexponentialSAT.SqrtLog.ResidualEmbedding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The local variable Z is a shift of the common global path T. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
noncomputable section

variable {R : Type*} [CommRing R] {V : Type*}

def shift (theta : R) : R[X] →+* R[X] :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.X+Polynomial.C theta)

@[simp] theorem shift_apply (theta : R) (P : R[X]) :
    shift theta P=P.comp (Polynomial.X+Polynomial.C theta) := rfl

@[simp] theorem shift_C (theta c : R) : shift theta (Polynomial.C c)=Polynomial.C c := by
  simp [shift_apply]

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteBaseline
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact integer bucket signatures restore the baseline used in a native
factor jet to the value of the shared fixed-high source path. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators

variable {r Q d n : ℕ}

def boolInt (b : Bool) : ℤ := if b then 1 else 0

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpExponentProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite Boolean programs for exponent keys

The key adder below has one fixed sixteen-instruction table.  Its two input
words contain unary-delimited exponents; a third input is a unary output-width
counter.  Each round consumes one counter bit and emits one result bit.  Once
the source adder has ended, further rounds emit zero padding.  It therefore
implements truncation and padding without interpreting a dimension as control
code, and without converting an exponent to an unbounded machine register.
-/

namespace SubexponentialSAT.SubexpExponentProgram

/-- Prefix of a word, padded by false bits to exactly the requested width. -/
def padTake (width : ℕ) (bits : List Bool) : List Bool :=
  bits.take width ++ List.replicate (width - bits.length) false

@[simp] theorem padTake_zero (bits : List Bool) : padTake 0 bits = [] := by
  simp [padTake]

@[simp] theorem padTake_nil (width : ℕ) :
    padTake width [] = List.replicate width false := by simp [padTake]

@[simp] theorem padTake_cons (width : ℕ) (b : Bool) (bits : List Bool) :
    padTake (width + 1) (b :: bits) = b :: padTake width bits := by
  simp [padTake]

theorem padTake_length (width : ℕ) (bits : List Bool) :
    (padTake width bits).length = width := by
  simp only [padTake, List.length_append, List.length_take, List.length_replicate]
  omega

end SubexponentialSAT.SubexpExponentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpKeyPadProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed five-instruction routine copies a forward key for exactly the
number of bits in a unary width counter. Empty input reads as false, so the
same routine truncates long keys and zero-pads short keys. -/

namespace SubexponentialSAT.SubexpKeyPadProgram

open SubexpExponentProgram

def storage (input counter output : List Bool) : Fin 3 → List Bool :=
  ![input, counter, output]

theorem padTake_step (n : ℕ) (input : List Bool) :
    padTake (n + 1) input = input.head?.getD false :: padTake n input.tail := by
  cases input <;> simp [List.replicate_succ]

end SubexponentialSAT.SubexpKeyPadProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTaylorFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-control conversion of a flat coefficient stream into an ordered
list of framed coefficients. Runtime counters determine the coefficient
width and requested count. Missing high coefficients are actually read as
zero by the existing padded-reader program. -/

namespace SubexponentialSAT.SubexpTaylorFrames

open SubexpExponentProgram

structure Words where
  input : List Bool
  width : List Bool
  todo : List Bool
  counter : List Bool := []
  payload : List Bool := []
  record : List Bool := []
  packed : List Bool := []
  scratch : List Bool := []
  output : List Bool := []

def store (w : Words) : Fin 9 → List Bool :=
  ![w.input, w.width, w.counter, w.todo, w.payload, w.record,
    w.packed, w.scratch, w.output]

def padStacks : Fin 3 → Fin 9 := ![0, 2, 4]
def writerStacks : Fin 6 → Fin 9 := ![0, 4, 1, 5, 2, 7]

theorem padStacks_injective : Function.Injective padStacks := by decide
theorem writerStacks_injective : Function.Injective writerStacks := by decide

def chunks (B : ℕ) : ℕ → List Bool → List (List Bool)
  | 0, _ => []
  | n + 1, input => padTake B input :: chunks B n (input.drop B)

@[simp] theorem chunks_length (B n : ℕ) (input : List Bool) : (chunks B n input).length = n := by
  induction n generalizing input with
  | zero => rfl
  | succ n ih => simp [chunks, ih]

def data (width : List Bool) (n : ℕ) (input packed : List Bool) : Words :=
  {input := input, width := width, todo := List.replicate n true, packed := packed}

end SubexponentialSAT.SubexpTaylorFrames

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid conversion of flat fixed-width node words to framed node records.
Both the width and the number of nodes are read from runtime unary tapes. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeFrames

open SubexponentialSAT.SubexpTaylorFrames
open SubexponentialSAT.SubexpExponentProgram

theorem chunks_flatten (B : ℕ) (words : List (List Bool))
    (hw : ∀ word ∈ words, word.length = B) :
    chunks B words.length words.flatten = words := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    have hword := hw word (by simp)
    have hrest : ∀ w ∈ words, w.length = B := fun w h => hw w (by simp [h])
    simp only [List.length_cons, List.flatten_cons, chunks]
    rw [show padTake B (word ++ words.flatten) = word by
      rw [← hword]
      simp [padTake ]]
    rw [show (word ++ words.flatten).drop B = words.flatten by
      rw [← hword]; simp]
    rw [ih hrest]

theorem flatten_length (B : ℕ) (words : List (List Bool))
    (hw : ∀ word ∈ words, word.length = B) : words.flatten.length = words.length * B := by
  induction words with
  | nil => simp
  | cons word words ih =>
    have hword := hw word (by simp)
    have hrest : ∀ w ∈ words, w.length = B := fun w h => hw w (by simp [h])
    simp [hword, ih hrest, Nat.add_mul, Nat.add_comm]

end SubexponentialSAT.SqrtLog.LeafProgram.NodeFrames

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryCleanup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid reclamation after one marked or accepted query. The port list is part
of the fixed program syntax. Only the collector, immutable formula/row inputs,
and the outer caller's high ports survive. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT

def Protected (i : Fin 768) : Prop :=
  i=320 ∨ i=322 ∨ i=323 ∨ i=700 ∨ i=701 ∨ i=707 ∨ i=708 ∨ i=709 ∨ 744 ≤ i.val

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendConvert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT

def conversionCost (v : ℕ) := v*(8*v+10)+5

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendNumericBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT
attribute [local simp] Fin.coe_ofNat_eq_mod

def numericCost (ambient clauses : List Bool) (k free occ arity factors mass : ℕ) : ℕ :=
  7*ambient.length+5+7*clauses.length+5+2*k.bits.length+1+
    conversionCost free+conversionCost occ+conversionCost arity+conversionCost factors+conversionCost mass

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native primitives used by the companion-table preparation machine. -/
namespace SubexponentialSAT.SqrtLog.RingProgramTable

def loadRegisters : Fin 2 → Fin 8 := ![1, 3]

def loadPorts (src dst : Fin 27) : Fin 5 → Fin 27 := ![src, dst, 12, 13, 14]

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

def triplePorts : Fin 15 → Fin 27 := Fin.castAdd 12

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramPorts
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

def registers (n : ℕ) (h : n ≤ 32) : Fin n → Fin 32 :=
  fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

theorem registers_injective (n : ℕ) (h : n ≤ 32) :
    Function.Injective (registers n h) := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun x : Fin 32 => x.val) hij

/-- The runtime numerical bank is kept until every unary serialization and
node-count copy has finished. -/
def parameters (i : Fin 77) : Fin 640 := ⟨340 + i.val, by omega⟩

/-- Search depth is the final native ring dimension.  The encoded F3
coefficient list on 195 is temporary; padding consumes it. -/
def search : Fin 28 → Fin 640 := fun i =>
  if i = 13 then 195 else if i = 14 then 204 else ⟨420 + i.val, by omega⟩

/-- Boot, scalar-cache construction, and (when needed) Newton preparation
share this local workspace.  The binary-t input remains a private copy. -/
def scalar : Fin 41 → Fin 640 := fun i =>
  if i = 5 then 194 else if i = 12 then 202 else
  if i = 17 then 203 else if i = 29 then 212 else ⟨480 + i.val, by omega⟩

/-- Padded coefficients remain at search port21 =441.  Scalar one is copied
to the consumed seed538; its canonical master at498 is preserved. -/
def table : Fin 42 → Fin 640 := fun i =>
  if i = 0 then 538 else if i = 5 then 194 else if i = 12 then 202 else
  if i = 17 then 508 else if i = 21 then 441 else if i = 22 then 204 else
  if i = 24 then 203 else if i = 27 then 201 else ⟨540 + i.val, by omega⟩

def nodes : Fin 15 → Fin 640 := fun i =>
  if i = 12 then 256 else if i = 14 then 204 else ⟨612 + i.val, by omega⟩

theorem search_injective : Function.Injective search := by decide
theorem scalar_injective : Function.Injective scalar := by decide
theorem table_injective : Function.Injective table := by decide

/-- Leave the parser/branch registers16--23 untouched when this setup is
called inside the agreed 40-register leaf ambient. -/
def wideRegisters (i : Fin 32) : Fin 40 :=
  if h : i.val < 16 then ⟨i.val, by omega⟩ else ⟨i.val+8, by omega⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid word movement and binary-to-unary conversion used by ring setup.
The helpers update actual tapes; a state equality is never used as a free
copy, clear, or counter conversion. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

def unaryRegisters : Fin 3 → Fin 32 := ![29,30,31]

def unaryPorts (src dst : Fin 640) (i : Fin 14) : Fin 640 :=
  if i = 0 then src else if i = 1 then dst else ⟨625+i.val, by omega⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingCoefficientLiftProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! A fixed scanner widens consecutive two-bit coefficients using a runtime
width tape. The original width is preserved, and all bit movement is paid. -/
namespace SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram

def tapes (input width shape word output temp final : List Bool) : Fin 7 → List Bool :=
  ![input,width,shape,word,output,temp,final]

def paddingPorts : Fin 3 → Fin 7 := ![2,3,4]
theorem paddingPorts_injective : Function.Injective paddingPorts := by decide

end SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram


/-! Exact byte bridge from canonical F3 coefficients to the supplied-polynomial
ring model. The program itself has no degree or width parameter. -/


/-! Search-to-table ABI. The search has 22 registers and 28 stacks. In particular,
stack24 may contain unread candidates and is outside this adapter's ports. -/
namespace SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram

def searchRegisters : Fin 8 → Fin 22 := Fin.castAdd 14
def searchPorts : Fin 7 → Fin 28 := ![13,12,23,15,25,26,21]
theorem searchRegisters_injective : Function.Injective searchRegisters := Fin.castAdd_injective _ _
theorem searchPorts_injective : Function.Injective searchPorts := by decide

end SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram

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

def roundBudget (B d : ℕ) : ℕ := d*(18000*(B+1)^2+130*B+140)+30*B+50

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

@[simp] theorem listOfFn_get {A : Type*} {d : ℕ} (v : List.Vector A d) :
    List.ofFn v.get = v.val := by
  have h := congrArg List.Vector.toList (List.Vector.ofFn_get v)
  change List.ofFn v.get = v.toList
  simpa only [List.Vector.toList_ofFn] using h

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

def initializationBudget (B d : ℕ) : ℕ := d*(40*B+30)+20*B+40


def preparationBudget (B d : ℕ) : ℕ :=
  initializationBudget B d + 14*d+12 + 2*d*(roundBudget B d+2)+2 + 24*d*d*B+11

theorem preparationBudget_polynomial (B d : ℕ) :
    preparationBudget B d ≤ 50000*(d+1)^2*(B+1)^2 := by
  unfold preparationBudget initializationBudget roundBudget
  nlinarith [Nat.zero_le (d^2*B^2), Nat.zero_le (d^2*B), Nat.zero_le (d*B^2),
    Nat.zero_le (d*B), Nat.zero_le (d^2), Nat.zero_le (B^2)]

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-control primitives for laying out a stored power table.  All indices,
dimensions, and scalar widths are data on unary tapes. -/
namespace SubexponentialSAT.SqrtLog.RingTableLayout

structure Store where
  powers : List Bool
  degree : List Bool
  width : List Bool
  out : List Bool := []
  word : List Bool := []
  index : List Bool := []
  kc : List Bool := []
  ic : List Bool := []
  jc : List Bool := []
  ki : List Bool := []
  ii : List Bool := []
  ji : List Bool := []
  rev : List Bool := []

def tapes (s : Store) : Fin 18 → List Bool :=
  ![s.powers, s.degree, s.width, s.out, s.word, s.index,
    [], [], [], [], [], s.kc, s.ic, s.jc, s.ki, s.ii, s.ji, s.rev]

def readPorts : Fin 8 → Fin 18 := ![0, 4, 5, 2, 6, 7, 8, 9]
theorem readPorts_injective : Function.Injective readPorts := by decide

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

def wordAt (rows : List (List Bool)) (i : ℕ) : List Bool := rows[i]!

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

def rowBits (rows : List (List Bool)) (d start : ℕ) : ℕ → List Bool
  | 0 => []
  | n+1 => wordAt rows start ++ rowBits rows d (start+d) n

def emitBudget (B d C : ℕ) : ℕ := C * (14*B+17) + 18*B + 7*d + 29

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramRowStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

def rowBudget (B d C : ℕ) : ℕ := d * (emitBudget B d C + 2) + 9*C + 14*d + 20

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

abbrev matrixBits (rows : List (List Bool)) (d start : ℕ) : ℕ → List Bool
  | 0 => []
  | n+1 => rowBits rows d start d ++ matrixBits rows d (start+d) n

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

def blockBudget (B d C : ℕ) : ℕ := d*(rowBudget B d C+2) + 9*C + 7*d + 16

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramOuter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

abbrev layoutBits (rows : List (List Bool)) (d start : ℕ) : ℕ → List Bool
  | 0 => []
  | n+1 => matrixBits rows d start d ++ layoutBits rows d (start+1) n

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

theorem rowBits_eq_ofFn (rows : List (List Bool)) (d n start : ℕ) :
    rowBits rows d start n =
      (List.ofFn fun j : Fin n => wordAt rows (start+j.val*d)).flatten := by
  induction n generalizing start with
  | zero => simp [rowBits]
  | succ n ih =>
      simp [rowBits, List.ofFn_succ, ih, Nat.add_mul,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem table_index_lt (d k i j : ℕ) (hk : k < d) (hi : i < d) (hj : j < d) :
    k+i*d+j*d < d*(2*d-1) := by
  have hs : i+j+1 ≤ 2*d-1 := by omega
  have hm := Nat.mul_le_mul_right d hs
  nlinarith

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A uniform finite program transforming power-major scalar records into the
k-major multiplication table. No dimension changes its finite control. -/
namespace SubexponentialSAT.SqrtLog.RingTableLayout

abbrev initial (powers degree width : List Bool) : Store where
  powers := powers
  degree := degree
  width := width

def budget (d B : ℕ) : ℕ :=
  d*(blockBudget B d (2*d*d+d)+2) + 9*d + 3*d^3*B + 13

/-- A coarse polynomial bound independent of the stored scalar values. -/
theorem budget_polynomial (d B : ℕ) : budget d B + 1 ≤ 1000*(d+1)^5*(B+1) := by
  simp only [budget, blockBudget, rowBudget, emitBudget]
  ring_nf
  omega

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable.Machine

def prepPorts : Fin 27 → Fin 42 := Fin.castAdd 15
def layoutPorts : Fin 18 → Fin 42 :=
  ![25, 22, 12, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41]
def layoutRegisters : Fin 2 → Fin 8 := ![1, 3]

theorem prepPorts_injective : Function.Injective prepPorts := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 42 => x.val) h)
theorem layoutPorts_injective : Function.Injective layoutPorts := by decide
theorem layoutRegisters_injective : Function.Injective layoutRegisters := by decide

def combineRegs (regs : Fin 8 → Bool) (localRegs : Fin 2 → Bool) : Fin 8 → Bool :=
  Function.update (Function.update regs 1 (localRegs 0)) 3 (localRegs 1)

@[simp] theorem combineRegs_self (regs : Fin 8 → Bool) :
    combineRegs regs ![regs 1, regs 3] = regs := by simp [combineRegs]

theorem nativeBudget_polynomial (B d : ℕ) :
    preparationBudget B d + RingTableLayout.budget d B + 3 ≤
      52000*(d+1)^5*(B+1)^2 := by
  have hp := preparationBudget_polynomial B d
  have hl := RingTableLayout.budget_polynomial d B
  have hd : (d+1)^2 ≤ (d+1)^5 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hb : B+1 ≤ (B+1)^2 := by nlinarith
  have hbig : 1 ≤ (d+1)^5*(B+1)^2 := Nat.succ_le_of_lt (by positivity)
  have hpp : 50000*(d+1)^2*(B+1)^2 ≤ 50000*(d+1)^5*(B+1)^2 := by gcongr
  have hlp : 1000*(d+1)^5*(B+1) ≤ 1000*(d+1)^5*(B+1)^2 := by gcongr
  nlinarith


end SubexponentialSAT.SqrtLog.RingProgramTable.Machine

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/- Component: LeafRingSetupProgramScalar.lean -/

/-! The first concrete stage of ring setup.  Only the runtime binary
precision is supplied.  The generated scalar cache remains exposed while
the extension-ring table and constants are built.  The idempotent producer
later uses a separately framed preparation, with its own charged cost. -/

/-! Actual irreducible search followed by coefficient padding.  The model
below is the one selected by the finite search, not a supplied polynomial. -/

/-! Table generation for the cache produced by the native scalar stage.
The cache is not replaced by a separately chosen mathematical cache. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

open RingProgramTable

local instance instFactPrimeOfNatNat_solutions_1 : Fact (Nat.Prime 3) := ⟨by decide⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

/- Component: LeafRingSetupProgramNodes.lean -/

/-! Physical node generation and record framing at the ring-setup ports. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

def nodeFramePorts : Fin 9 → Fin 640 := ![256,280,295,296,297,298,299,306,300]

theorem nodeFramePorts_injective : Function.Injective nodeFramePorts := by decide

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

/- Component: LeafRingSetupProgramConstants.lean -/

/-! Actual constant-vector and idempotent calls in the setup workspace. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramTableBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical table-input projection and the exact native table-call bridge. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open RingProgramTable

local instance instFactPrimeOfNatNat_solutions_3 : Fact (Nat.Prime 3) := ⟨by decide⟩


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


/-! Arithmetic consumers use the same bytes generated by the preceding
stages.  These are structural handoff lemmas; the complete production
trace must establish `NativeBytes` before invoking them. -/

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

def numericPlan : List (Fin 640 × Fin 640) :=
  [(374,204),(384,209),(382,243),(340,191),(361,296)]

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram



namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

def coreWritePorts : List (Fin 640) :=
  [253,538] ++ (List.finRange 41).map scalar ++
    (List.finRange 28).map search ++ (List.finRange 42).map LeafRingSetupProgram.table

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

def nodeInputs : List (Fin 640 × Fin 640) := [(203,617),(361,625)]

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

def ringCachePorts : List (Fin 640) :=
  [194,202,204,203,201,212,253,280,207,211,190,249,250,251]

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Paid staging of the native interpolation-cache producer in the wide
leaf machine. The private 320-tape bank is disjoint from all ring and
collector masters. Native table computation is followed by paid extraction
of all five outputs; the entire staging bank is then cleared. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation



def localRegisters (i : Fin 16) : Fin 40 := i.castLE (by decide)
def localPorts (i : Fin 320) : Fin 768 := ⟨340+i.val,by omega⟩
theorem localRegisters_injective : Function.Injective localRegisters := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 40 => x.val) h
theorem localPorts_injective : Function.Injective localPorts := by
  intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp [localPorts] at this; omega

def privatePorts : List (Fin 768) := (List.finRange 320).map localPorts

theorem privatePorts_mem (i : Fin 320) : localPorts i ∈ privatePorts := by
  exact List.mem_map_of_mem (List.mem_finRange i)

theorem privatePorts_not_low (i : Fin 768) (hi : i.val < 340) : i∉privatePorts := by
  intro hm
  obtain ⟨j,_,hj⟩ := List.mem_map.mp hm
  have hh := congrArg Fin.val hj
  dsimp [localPorts] at hh
  omega

theorem privatePorts_not_high (i : Fin 768) (hi : 660 ≤ i.val) : i∉privatePorts := by
  intro hm
  obtain ⟨j,_,hj⟩ := List.mem_map.mp hm
  have hh := congrArg Fin.val hj
  dsimp [localPorts] at hh
  omega

def inputPlan : List (Fin 768 × Fin 768) :=
  [(280,444),(194,534),(201,541),(202,542),(203,543),(204,544),
   (207,547),(209,549),(211,551),(212,552),(256,596)]

def outputPlan : List (Fin 768 × Fin 768) :=
  [(599,713),(600,714),(601,715),(602,716),(603,717)]

theorem inputPlan_ports : ∀p∈inputPlan,p.1≠p.2 ∧ p.1≠699 ∧ p.2≠699 := by
  intro p hp
  simp only [inputPlan,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem outputPlan_ports : ∀p∈outputPlan,p.1≠p.2 ∧ p.1≠699 ∧ p.2≠699 := by
  intro p hp
  simp only [outputPlan,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl <;> decide

def inputIndex : Fin 320 → Option (Fin 768) := fun i =>
  if i=104 then some 280 else if i=194 then some 194 else
  if i=201 then some 201 else if i=202 then some 202 else
  if i=203 then some 203 else if i=204 then some 204 else
  if i=207 then some 207 else if i=209 then some 209 else
  if i=211 then some 211 else if i=212 then some 212 else
  if i=256 then some 256 else none

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation

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


/-! Native per-variable incident-factor scan from the original scope stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan
abbrev unary (n : ℕ) := List.replicate n true
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan


/-! Fixed cleanup for the native scope-address scanner. -/


/-! Calls to the fixed record mapper inside the native scope scan. -/


/-! One native low-variable step, including its uncovered neutral factor. -/


/-! Runtime high-mask loop for the original-address incidence stream. -/


/-! Count the physical scope stream before constructing native incidence plans. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framing and paid parameter serialization for the packing loader. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
abbrev Store := Fin 64 → List Bool

def lowPorts : Fin 48 ↪ Fin 64 := ⟨Fin.castAdd 16, Fin.castAdd_injective _ _⟩

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInitProgram
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

structure Context where
  defaultWord : List Bool
  packedAlphabet : List Bool
  alphabetRecords : List Bool
  width : List Bool
  depth : List Bool
  rawPairs : List Bool
  seedRecords : List Bool
  seedCount : ℕ

def unary (n : ℕ) : List Bool := List.replicate n true

end SubexponentialSAT.Subexp.AssignmentInitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInputState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical input boundary for assignment-alphabet construction. -/

namespace SubexponentialSAT.Subexp.AssignmentInputProgram

abbrev unary (n : ℕ) := List.replicate n true

end SubexponentialSAT.Subexp.AssignmentInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInputProgram
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

def seedCount (delta D E : ℕ) : ℕ := E + (delta + 1) * D

end SubexponentialSAT.Subexp.AssignmentInputProgram

end OAI.Algorithms
end


