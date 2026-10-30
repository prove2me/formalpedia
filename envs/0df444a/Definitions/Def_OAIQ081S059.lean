-- Prove2me | Definitions.Def_OAIQ081S059
-- name    : OAIQ081S059
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:44:29.113648+00:00
-- url     : https://prove2.me/theorems/f0d63cab-b246-4602-9de2-71c52c8cbbfa
-- title:
--   Definitions bundle OAIQ081S059 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 94 declarations of OpenAI's Lean: 62 definitions and 32 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Cleanup.resetState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Count.Prepare.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.clear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.move`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds.hashServiceBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Mass.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.branchPath`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.violates`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.afterMove`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.clauseValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.foldEffect`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.literalValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.scalarJet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.scopeBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.outputCoefficients`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.MaskData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.maskData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows.readerPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgram.coefficientRecords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.NativeState.cleanPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.NativeState.workingClean`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram.loop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram.pad`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram.scan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram.searchCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram.step`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.Machine.layout`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.afterLoad`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.afterTransfer`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.prepareRound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.prepareRounds`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayout.blockStep`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayout.clear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayout.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayout.emit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayout.finish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayout.finishBlock`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayout.finishRow` and 22 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LeafProgramCleanup`, `SubexponentialSAT_SqrtLog_LeafProgramCountPrepare`, `SubexponentialSAT_SqrtLog_LeafProgramFactorBase`, `SubexponentialSAT_SqrtLog_LeafProgramFactorBoundsServices`, `SubexponentialSAT_SqrtLog_LeafProgramHash`, `SubexponentialSAT_SqrtLog_LeafProgramMass`, `SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteBaseline`, `SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsCount`, `SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsSource`, `SubexponentialSAT_SqrtLog_LeafProgramQueryReadback`, `SubexponentialSAT_SqrtLog_LeafProgramRecords`, `SubexponentialSAT_SqrtLog_LeafProgramScalarRow`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramSpec`, `SubexponentialSAT_SqrtLog_MomentsOutput`, `SubexponentialSAT_SqrtLog_MomentsProjectionProgramMask`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_PerturbationProgramStored`, `SubexponentialSAT_SqrtLog_ReconstructionProgramState`, `SubexponentialSAT_SqrtLog_RingCoefficientLiftProgram`, `SubexponentialSAT_SqrtLog_RingProgramTableBasic`, `SubexponentialSAT_SqrtLog_RingProgramTableLoop`, `SubexponentialSAT_SqrtLog_RingProgramTableMachine`, `SubexponentialSAT_SqrtLog_RingProgramTablePowers`, `SubexponentialSAT_SqrtLog_RingProgramTableRound`, `SubexponentialSAT_SqrtLog_RingProgramTableSetup`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgram`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramBasic`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramBlock`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramMatrix`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramOuter`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramRowStep`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramRows`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramStep`, `SubexponentialSAT_SqrtLog_SquarefreeSparseOps`, `SubexponentialSAT_SqrtLog_SquarefreeSparseProduct`, `SubexponentialSAT_SqrtLog_TotalOrderBasic`, `SubexponentialSAT_SubexpArgumentProgram`, `SubexponentialSAT_SubexpBasePUnranking`, `SubexponentialSAT_SubexpTaylorFrames`, `SubexponentialSAT_Subexp_AssignmentInitProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S023`, `OAIQ081S024`, `OAIQ081S025`, `OAIQ081S026`, `OAIQ081S027`, `OAIQ081S028`, `OAIQ081S029`, `OAIQ081S030`, `OAIQ081S031`, `OAIQ081S032`, `OAIQ081S037` and `OAIQ081S038` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S076`, `OAIQ081S077`, `OAIQ081S080` and `OAIQ081S081`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S024
import Definitions.Def_OAIQ081S025
import Definitions.Def_OAIQ081S026
import Definitions.Def_OAIQ081S027
import Definitions.Def_OAIQ081S028
import Definitions.Def_OAIQ081S029
import Definitions.Def_OAIQ081S030
import Definitions.Def_OAIQ081S031
import Definitions.Def_OAIQ081S032
import Definitions.Def_OAIQ081S037
import Definitions.Def_OAIQ081S038

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramCleanup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid restoration of the isolated count-query worker. The selector's mass
contract requires literal frame preservation, so all 340 worker stacks and all
22 registers are restored by actual instructions after exporting the score. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Cleanup

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def resetState {r s : ℕ} : List (Fin r) → State r s → State r s
  | [], a => a
  | i::is, a => resetState is ((StructuredProgram.Atom.set i false).eval a)

end SubexponentialSAT.SqrtLog.LeafProgram.Cleanup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryReadback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete readback/transfer adapter for the marked-query caller. The CRT
result is at261; the exact little-endian integer is delivered at323. The
unread marked-reference stream320 and mass accumulator322 are framed. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpFlatCount

def afterMove (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,
    StackRoutines.transferStacks 324 323 (StackRoutines.transferStacks 261 324 a.stacks)⟩

@[simp] theorem afterMove_output (a : Data) (hs : a.stacks 323 = []) (ht : a.stacks 324 = []) :
    (afterMove a).stacks 323 = a.stacks 261 := by
  simp [afterMove, StackRoutines.transferStacks, hs, ht]

@[simp] theorem afterMove_scratch (a : Data) : (afterMove a).stacks 324 = [] := by
  simp [afterMove, StackRoutines.transferStacks]

end SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete caller frame seen at every loaded Hermite node. -/

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.NativeState

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram

def workingClean : List (Fin 320) := Middle.cleanPorts ++
  CRTLocalProgram.localWork.map localPorts ++
  (List.ofFn fun i => localPorts (SubexpConvolutionControl.bufferPorts i))

def cleanPorts : List (Fin 320) := initialCleanPorts ++ workingClean ++ [5,10]

end SubexponentialSAT.SqrtLog.ReconstructionProgram.NativeState

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramCountPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual reclamation of node-work scratch before Hermite reconstruction.
The static port set includes both the native CRT work ports and the scalar/
polynomial arithmetic readiness ports, together with the reader temporaries. Runtime data are cleared by real
stack loops; persistent node and jet inputs remain outside this set. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Count.Prepare

open SubexponentialSAT BitProgram StructuredCalls

def ports : List (Fin 768) :=
  (((ReconstructionProgram.NativeState.cleanPorts ++ ReconstructionProgram.InputReady.emptyPorts).map crtStacks) ++
    [323,324,325,326,327,328,329]).dedup

end SubexponentialSAT.SqrtLog.LeafProgram.Count.Prepare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramRecords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.RecordPrograms

variable {r s : ℕ} {A : Type*}

def foldEffect (read : State r s → A) (step : List Bool → A → A)
    (bits : List Bool) (before after : State r s) : Prop :=
  read after = step bits (read before)

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparseProduct
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

namespace Sparse

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

theorem canonical_atom (t J : ℕ) (a : Index V) (c : R) :
    canonical t J (atom a c) = if a.Kept t J then atom a c else 0 := by
  by_cases ht : a.u < t <;> by_cases hj : a.z < J
  all_goals simp only [Index.Kept, ht, hj, and_self, and_false, false_and, ite_true, if_true, ite_false]
  all_goals ext u z
  all_goals by_cases hu : u = a.u <;> by_cases hz : z = a.z <;>
    subst_vars <;> simp_all [atom, coeff_canonical, Polynomial.coeff_monomial, eq_comm]
  all_goals split_ifs <;> first | rfl | omega

end Sparse
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparseOps
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

namespace Sparse

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

def constant (t J : ℕ) (c : R) : Data (Index V) R :=
  if 0 < t ∧ 0 < J then [(Index.origin, c)] else []

def one (t J : ℕ) : Data (Index V) R := constant t J 1

theorem denote_constant (t J : ℕ) (c : R) :
    denote (constant (V := V) t J c) = canonical t J (atom Index.origin c) := by
  rw [canonical_atom]
  by_cases h : 0 < t ∧ 0 < J <;> simp [constant, Index.Kept, Index.origin, h, denote, decode]

theorem denote_one (t J : ℕ) :
    denote (one (V := V) (R := R) t J) = canonical t J 1 := by
  rw [one, denote_constant, atom_origin_one]

end Sparse

end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Wide native factor arithmetic and paid tape movement. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls

def clear (src : Fin 768) : Code :=
  .call (StackRoutines.clearProgram src 0 1)
def move (src dst : Fin 768) : Code := .seq (copy src dst) (clear src)


end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramHash
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Sparse clause-circuit evaluation for one hash row

The input is a list of supplied nonzero coefficients and width-k clause lists.
The evaluator visits those lists directly; it never builds a truth table on the
union of the clause scopes. Counters include measured variable lookup and ring
callbacks. Their primitive realization is a separate obligation, not inferred
from these counters. `Algebra` also admits canonical truncated operations, whose
decoder need not be a homomorphism into the untruncated polynomial ring.
-/

namespace SubexponentialSAT.SqrtLog.LeafProgram

open SubexponentialSAT.SubexpSymbolicCost

variable {V C A : Type*}

def literalValue (alg : Algebra A) (value : V → A) (l : SAT.Literal V) : A :=
  if l.positive then alg.add alg.one (alg.neg (value l.variable))
  else value l.variable

def clauseValue (alg : Algebra A) (value : V → A) : List (SAT.Literal V) → A
  | [] => alg.one
  | l :: ls => alg.mul (literalValue alg value l) (clauseValue alg value ls)

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramScalarRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Flat ring coefficients may scale sparse dictionaries directly. They need
not first be serialized as a singleton sparse dictionary. This interface is
used by the native weighted-clause interpreter. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

variable {V R : Type*} [DecidableEq V] [CommRing R]
variable {vars : Finset V} {t J : ℕ}

noncomputable def scalarJet (c : R) : Jet V R := Sparse.atom Index.origin c

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpArgumentProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

open BitProgram StructuredCalls
open SubexpRecordScan

abbrev Data := StructuredProgram.State 5 6

theorem embedState_eq {r s R S : ℕ}
    (reg : Fin r → Fin R) (stack : Fin s → Fin S)
    (hreg : Function.Injective reg) (hstack : Function.Injective stack)
    (frame target : State R S) (source : State r s)
    (hr : ∀ i, target.regs (reg i) = source.regs i)
    (hs : ∀ i, target.stacks (stack i) = source.stacks i)
    (hfr : ∀ j, (¬ ∃ i, reg i = j) → target.regs j = frame.regs j)
    (hfs : ∀ j, (¬ ∃ i, stack i = j) → target.stacks j = frame.stacks j) :
    embedState reg stack frame source = target :=
  embedState_eq_of_ports reg stack frame target source hreg hstack hr hfr hs hfs

abbrev afterWriter (outer : Bool) (d : Data) (bits : List Bool) : Data :=
  ⟨finishedRegs d.regs,
    Function.update (Function.update d.stacks 1 []) (destination outer)
      (true :: (Encoding.frame bits ++ d.stacks (destination outer)))⟩

end SubexponentialSAT.SubexpArgumentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpBasePUnranking
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

open BitProgram StructuredCalls StackRoutines
open BinaryArithmetic ModularQuotientArithmetic

/-- Fixed-width little-endian digit returned by one division. -/
def digit (modulus rank : List Bool) : List Bool :=
  (divide modulus rank).2.take modulus.length

def nextRank (modulus rank : List Bool) : List Bool := (divide modulus rank).1

@[simp] theorem digit_length (modulus rank : List Bool) :
    (digit modulus rank).length = modulus.length := by
  simp only [digit, List.length_take, divide_remainder_length]
  omega

@[simp] theorem nextRank_length (modulus rank : List Bool) :
    (nextRank modulus rank).length = rank.length := by simp [nextRank]

/-- Least-significant base-p digit first; each digit itself is little-endian. -/
def digitWords (modulus : List Bool) : ℕ → List Bool → List (List Bool)
  | 0, _ => []
  | k + 1, rank => digit modulus rank :: digitWords modulus k (nextRank modulus rank)

@[simp] theorem digitWords_length (modulus rank : List Bool) (k : ℕ) :
    (digitWords modulus k rank).length = k := by
  induction k generalizing rank with
  | zero => rfl
  | succ k ih => simp [digitWords, ih]

@[simp] theorem digitWords_flatten_length (modulus rank : List Bool) (k : ℕ) :
    (digitWords modulus k rank).flatten.length = k * modulus.length := by
  induction k generalizing rank with
  | zero => simp [digitWords]
  | succ k ih => simp [digitWords, ih, Nat.succ_mul, Nat.add_comm]

/-- Fixed-width digit extraction and quotient preparation after long division.
The digit is prepended in reverse to a stream that is reversed once at the end. -/
abbrev collectDigit : Cmd 8 13 :=
  .seq (.call (copyProgram 5 9 10 1 3))
    (.seq (.call (ArrayPrograms.countedTransferProgram 9 0 11 1 3))
      (.seq (.call (clearProgram 0 1 3))
        (.seq (.call (transferProgram 7 10 1 3)) (.call (transferProgram 10 6 1 3)))))

end SubexponentialSAT.SubexpBasePUnranking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorBoundsServices
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Bounds for the measured native factor services and their paid cleanup.
The retained-key capacity remains an explicit argument of every envelope. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native MomentsProgram
open IdempotentApplyProgram.Steps

def hashServiceBound (B d n u J N k m L : ℕ) : ℕ :=
  Cost.programBound B d n u J N k m+
    IdempotentApplyProgram.Bounds.totalEnvelope B d n u J N L+
    58*Cost.bytesBound B d n u J N+2*tableBound B d n u J N+
    Cost.productBound B d n u J N+64

end SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramMass
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The primitive integer accumulator used after each marked-clause count.
Both operands have runtime lengths. The fixed instruction table adds them
exactly and restores little-endian orientation; no arithmetic instruction or
precomputed mass is admitted into the machine model. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Mass

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

variable {r s : ℕ}

noncomputable def state (p : Ports r s) (frame : State r s)
    (regs : Fin 8 → Bool) (acc next : List Bool) : State r s :=
  embedState p.register p.stack frame (data regs acc next)

end SubexponentialSAT.SqrtLog.LeafProgram.Mass

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

/-- Coefficient emission scans the explicit list once. No monomial universe is
constructed; j is a unary exponent field of polynomially bounded value. -/
def coefficientRecords (v : V) : ℕ → List C → List (Index V × C)
  | _, [] => []
  | j, c :: cs => (⟨0,j,{v}⟩,c) :: coefficientRecords v (j+1) cs

omit [DecidableEq V] in
@[simp] theorem coefficientRecords_length (v : V) (j : ℕ) (p : List C) :
    (coefficientRecords v j p).length = p.length := by
  induction p generalizing j with
  | nil => rfl
  | cons c cs ih => simp [coefficientRecords, ih]

end SubexponentialSAT.SqrtLog.PerturbationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_TotalOrderBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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
open SubexponentialSAT.Truncation SubexponentialSAT.NilpotentDefect

variable {R S α : Type*} [CommSemiring R] [CommSemiring S]

/-- The unique chosen representative has U-degree strictly below t. -/
def retainedProduct (s : Finset α) (t : ℕ) (e : α → ℕ → R) (h : α → R) :
    Polynomial R := trunc t (fullProduct s t e h)

/-- Evaluation applies to the chosen polynomial representative only. -/
def output (s : Finset α) (t : ℕ) (e : α → ℕ → R) (h : α → R) : R :=
  (retainedProduct s t e h).eval 1

end

end SubexponentialSAT.SqrtLog.TotalOrder

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A concrete dense Z-output list for CRT reconstruction. Its entries are
obtained only by sparse coefficient scans and a finite sum over retained U. -/

namespace SubexponentialSAT.SqrtLog.Moments

open scoped BigOperators
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

variable {R V : Type*} [CommSemiring R] [DecidableEq V]

def outputCoefficients (t J : ℕ) (l : Sparse.Data (Index V) R) : List R :=
  tabulate J (fun z => ∑ u ∈ Finset.range t, Sparse.fetch ⟨u, z, ∅⟩ l)

@[simp] theorem outputCoefficients_length (t J : ℕ) (l : Sparse.Data (Index V) R) :
    (outputCoefficients t J l).length = J := tabulate_length _ _

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact fixed-high query count for the code-derived shared-order target. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
noncomputable section
attribute [local instance] Classical.propDecidable

variable {R K : Type*} [CommRing R] [CommRing K] [DecidableEq K]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Empty clauses have violation one, as in the actual clause interpreter. -/
def violates (clause : List (SAT.Literal V)) (x : V → Bool) : Bool :=
  clause.all (fun l => !(l.eval x))

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Original IDs and fixed-high constants are retained in the source path.
All summation variables are free coordinates. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
noncomputable section

variable {R V : Type*} [CommRing R] [Fintype V] [DecidableEq V]

/-- The row bank is indexed by factor and original variable ID. -/
def branchPath (H : Finset V) (high : H → Bool)
    (rows : ℕ → V → ResidualEmbedding.Free H → R[X])
    (x : ResidualEmbedding.Free H → Bool) (i : ℕ) (v : V) : R[X] :=
  if hv : v ∈ H then Polynomial.C (HashInput.boolValue (high ⟨v,hv⟩))
  else ∑ w, rows i v w * Polynomial.C (HashInput.boolValue (x w))

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteBaseline
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open DensePolynomialProgram SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open LayoutProgram PerturbationAssembly

variable {r Q d n : ℕ}

@[simp] theorem boolInt_cast {R : Type*} [CommRing R] (b : Bool) :
    (boolInt b : R)=HashInput.boolValue b := by cases b <;> simp [boolInt,HashInput.boolValue]

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native primitives used by the companion-table preparation machine. -/
namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def afterTransfer (d : Data) (src dst : Fin 27) : Data :=
  ⟨readRegs d.regs 1 3 none, transferStacks src dst d.stacks⟩

theorem copy_eval (d : Data) (src dst : Fin 27)
    (hsd : src ≠ dst) (hs : src ≠ 23) (hd : (23 : Fin 27) ≠ dst)
    (htmp : d.stacks 23 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (afterCopy d src dst) :=
  .call _ (ListRegisterProgram.copy_run src dst 23 1 3 hsd hs hd
    (by decide) d.regs d.stacks htmp)

def afterLoad (d : Data) (src dst : Fin 27) (word tail : List Bool) : Data :=
  ⟨readRegs d.regs 1 3 none,
    Function.update (Function.update d.stacks src tail) dst (word ++ d.stacks dst)⟩


theorem copy_store_eval (s t : Store) (regs : Fin 8 → Bool) (src dst : Fin 27)
    (hsd : src ≠ dst) (hs : src ≠ 23) (hd : (23 : Fin 27) ≠ dst)
    (heq : copyStacks src dst (tapes s) = tapes t) :
    Eval (copy src dst) (7 * (tapes s src).length + 5) (state regs s)
      (state (readRegs regs 1 3 none) t) := by
  have h := copy_eval (state regs s) src dst hsd hs hd (by rfl)
  simpa only [afterCopy, state, heq] using h

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem popCount_eval (s : Store) (regs : Fin 8 → Bool) :
    Eval popCount 1 (state regs s)
      (state (readRegs regs 1 3 s.count.head?) {s with count := s.count.tail}) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (r := 8) (s := 27) 11 1 3)
    (state regs s) using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr, tapes]

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTaylorFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpExponentProgram

/-- The reader tests counter presence, so either bit value is a valid tick. -/
theorem pad_round (bit : Bool) (regs : Fin 2 → Bool) (input counter output : List Bool) :
    Trace SubexpKeyPadProgram.program 4
      (SubexpKeyPadProgram.cfg (some 0) regs input (bit :: counter) output)
      (SubexpKeyPadProgram.cfg (some 0) (readRegs regs 0 1 input.head?)
        input.tail counter (input.head?.getD false :: output)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, SubexpKeyPadProgram.program,
    execInstr, SubexpKeyPadProgram.cfg, SubexpKeyPadProgram.storage,
    readRegs, Function.update_apply]
  all_goals first | (constructor <;> funext i <;> fin_cases i <;> simp) | (funext i <;> fin_cases i <;> simp)

theorem pad_counter_trace (counter : List Bool) (regs : Fin 2 → Bool)
    (input output : List Bool) :
    ∃ finalRegs, Trace SubexpKeyPadProgram.program (4 * counter.length + 3)
      (SubexpKeyPadProgram.cfg (some 0) regs input counter output)
      (SubexpKeyPadProgram.cfg none finalRegs (input.drop counter.length) []
        ((padTake counter.length input).reverse ++ output)) := by
  induction counter generalizing regs input output with
  | nil => exact ⟨readRegs regs 0 1 none, by
      simpa using (SubexpKeyPadProgram.exit_trace regs input output)⟩
  | cons bit counter ih =>
      have h1 := pad_round bit regs input counter output
      obtain ⟨rr, h2⟩ := ih (readRegs regs 0 1 input.head?) input.tail
        (input.head?.getD false :: output)
      refine ⟨rr, ?_⟩
      have ht := h1.trans h2
      rw [List.drop_tail] at ht
      simp only [List.length_cons, SubexpKeyPadProgram.padTake_step,
        List.reverse_cons, List.append_assoc]
      convert ht using 1
      · omega
      · simp only [List.singleton_append]

end SubexponentialSAT.SubexpTaylorFrames

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
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ModularPrograms
open SubexponentialSAT.Subexp.MatrixProgramSupport

def pad : Code := .call (ProgramLinking.liftProgram paddingProgram id paddingPorts)

def step : Code := .seq takeTwo (.seq (copy 1 2 5) pad)

end SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram


namespace SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

def loop : Code := .while 7 (.seq step peek)
def scan : Code := .seq peek loop

def command : Code := .seq scan (transfer 4 6)

end SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram


/-! Exact byte bridge from canonical F3 coefficients to the supplied-polynomial
ring model. The program itself has no degree or width parameter. -/


/-! Search-to-table ABI. The search has 22 registers and 28 stacks. In particular,
stack24 may contain unread candidates and is outside this adapter's ports. -/
namespace SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev searchCommand : Cmd 22 28 := liftCommand command 0 6 searchRegisters searchPorts

end SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableRound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev prepareRound : Cmd 8 27 :=
  .seq (copy 21 16) (.seq (copy 22 11) (copy 24 0))

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTablePowers
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem popRound_eval (s : Store) (regs : Fin 8 → Bool) :
    Eval popRound 1 (state regs s)
      (state (readRegs regs 1 3 s.rounds.head?) {s with rounds := s.rounds.tail}) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (r := 8) (s := 27) 26 1 3)
    (state regs s) using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr, tapes]

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev prepareRounds : Cmd 8 27 :=
  .seq (copy 22 26) (.seq (copy 22 26) (.seq popRound popRound))

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-control primitives for laying out a stored power table.  All indices,
dimensions, and scalar widths are data on unary tapes. -/
namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev clear (dst : Fin 18) : Cmd 2 18 := .call (clearProgram dst 0 1)

theorem copy_eval (d : Data) (src dst : Fin 18)
    (hsd : src ≠ dst) (hs : src ≠ 10) (hd : (10 : Fin 18) ≠ dst)
    (htmp : d.stacks 10 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (afterCopy d src dst) :=
  .call _ (ListRegisterProgram.copy_run src dst 10 0 1 hsd hs hd
    (by decide) d.regs d.stacks htmp)

abbrev read : Cmd 2 18 := .call
  (ProgramLinking.liftProgram (ArrayUpdatePrograms.readProgram (0 : Fin 2) 1) id readPorts)

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

/-- Read one scalar at the current flat-record offset, prepend its reversed
bits to the output accumulator, and advance the offset by one vector. -/
abbrev emit : Cmd 2 18 :=
  .seq (copy 16 5) (.seq read (.seq (transfer 4 17) (copy 1 16)))

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem pop_eval (d : Data) (port : Fin 18) : Eval (pop port) 1 d (afterPop d port) :=
  .base (.atom _ _)

theorem jPop_eval (s : Store) (regs : Fin 2 → Bool) :
    Eval (pop 13) 1 (state regs s)
      (state (readRegs regs 0 1 s.jc.head?) {s with jc := s.jc.tail}) := by
  have h := pop_eval (state regs s) 13
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [ state, tapes]

abbrev jLoop : Cmd 2 18 := .while 1 (.seq emit (pop 13))
abbrev jScan : Cmd 2 18 := .seq (pop 13) jLoop

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramRowStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev finishRow : Cmd 2 18 := .seq (clear 16) (copy 1 15)
abbrev rowStep : Cmd 2 18 := .seq startRow (.seq jScan finishRow)

theorem startRow_eval (s : Store) (regs : Fin 2 → Bool)
    (hj : s.ji = []) (hc : s.jc = []) :
    ∃ rf, Eval startRow (7*s.ii.length + 7*s.degree.length + 10)
      (state regs s) (state rf {s with ji := s.ii, jc := s.degree}) := by
  let d := state regs s
  let a := afterCopy d 15 16
  have h1 := copy_eval d 15 16 (by decide) (by decide) (by decide) (by rfl)
  have h2 := copy_eval a 1 13 (by decide) (by decide) (by decide) (by rfl)
  have hf : afterCopy a 1 13 =
      state (afterCopy a 1 13).regs {s with ji := s.ii, jc := s.degree} := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [a, d, afterCopy, copyStacks, state, tapes, hj, hc]
  refine ⟨(afterCopy a 1 13).regs, ?_⟩
  rw [← hf]
  convert h1.seq h2 using 1
  all_goals try with_reducible_and_instances rfl
  simp [a, d, afterCopy, copyStacks, state, tapes]
  omega

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem iPop_eval (s : Store) (regs : Fin 2 → Bool) :
    Eval (pop 12) 1 (state regs s)
      (state (readRegs regs 0 1 s.ic.head?) {s with ic := s.ic.tail}) := by
  have h := pop_eval (state regs s) 12
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [ state, tapes]

abbrev iLoop : Cmd 2 18 := .while 1 (.seq rowStep (pop 12))
abbrev iScan : Cmd 2 18 := .seq (pop 12) iLoop

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramBlock
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev finishBlock : Cmd 2 18 := .seq (clear 15) (.base (.atom (.push 14 0)))
abbrev blockStep : Cmd 2 18 := .seq startBlock (.seq iScan finishBlock)

theorem startBlock_eval (s : Store) (regs : Fin 2 → Bool)
    (hi : s.ii = []) (hc : s.ic = []) :
    ∃ rf, Eval startBlock (7*s.ki.length + 7*s.degree.length + 10)
      (state regs s) (state rf {s with ii := s.ki, ic := s.degree}) := by
  let d := state regs s
  let a := afterCopy d 14 15
  have h1 := copy_eval d 14 15 (by decide) (by decide) (by decide) (by rfl)
  have h2 := copy_eval a 1 12 (by decide) (by decide) (by decide) (by rfl)
  have hf : afterCopy a 1 12 =
      state (afterCopy a 1 12).regs {s with ii := s.ki, ic := s.degree} := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [a, d, afterCopy, copyStacks, state, tapes, hi, hc]
  refine ⟨(afterCopy a 1 12).regs, ?_⟩
  rw [← hf]
  convert h1.seq h2 using 1
  all_goals try with_reducible_and_instances rfl
  simp [a, d, afterCopy, copyStacks, state, tapes]
  omega

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem kPop_eval (s : Store) (regs : Fin 2 → Bool) :
    Eval (pop 11) 1 (state regs s)
      (state (readRegs regs 0 1 s.kc.head?) {s with kc := s.kc.tail}) := by
  have h := pop_eval (state regs s) 11
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [ state, tapes]

abbrev kLoop : Cmd 2 18 := .while 1 (.seq blockStep (pop 11))
abbrev kScan : Cmd 2 18 := .seq (pop 11) kLoop

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A uniform finite program transforming power-major scalar records into the
k-major multiplication table. No dimension changes its finite control. -/
namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev finish : Cmd 2 18 := .seq (clear 14) (transfer 17 3)
abbrev command : Cmd 2 18 := .seq (copy 1 11) (.seq kScan finish)
abbrev program : Program 2 18 (size command + 1) := compiled command 0 3

theorem initialize_eval (powers degree width : List Bool) (regs : Fin 2 → Bool) :
    ∃ rf, Eval (copy 1 11) (7*degree.length+5)
      (state regs (initial powers degree width))
      (state rf {(initial powers degree width) with kc := degree}) := by
  let d := state regs (initial powers degree width)
  have h := copy_eval d 1 11 (by decide) (by decide) (by decide) (by rfl)
  refine ⟨(afterCopy d 1 11).regs, ?_⟩
  convert h using 1
  · rfl
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [d, state, tapes, copyStacks]

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableMachine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable.Machine

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem embed_prep (regs oldRegs : Fin 8 → Bool) (s old : Store) (table : List Bool) :
    embedState id prepPorts (state oldRegs old table) (RingProgramTable.state regs s) =
      state regs s table := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id prepPorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; simp [state, prepPorts]
  · intro i hi
    have hg : ¬i.val < 27 := by
      intro h
      exact hi ⟨⟨i.val,h⟩, Fin.ext rfl⟩
    simp [state, hg]

theorem embed_layout (regs : Fin 8 → Bool) (lr : Fin 2 → Bool)
    (s : Store) (old table : List Bool) :
    embedState layoutRegisters layoutPorts (state regs s old)
      (RingTableLayout.state lr {(RingTableLayout.initial s.powers s.degree s.width) with out := table}) =
      state (combineRegs regs lr) s table := by
  apply embedState_eq_of_ports _ _ _ _ _ layoutRegisters_injective layoutPorts_injective
  · intro i; fin_cases i <;> simp [state, combineRegs, RingTableLayout.state, layoutRegisters]
  · intro i hi
    have h1 : i ≠ 1 := fun h => hi ⟨0,h.symm⟩
    have h3 : i ≠ 3 := fun h => hi ⟨1,h.symm⟩
    simp [state, combineRegs, h1, h3]
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    have hn : i.val ≠ 27 := by
      intro h
      exact hi ⟨3, Fin.ext h.symm⟩
    simp [state, hn]

abbrev layout : Cmd 8 42 := .call (ProgramLinking.liftProgram RingTableLayout.program layoutRegisters layoutPorts)

end SubexponentialSAT.SqrtLog.RingProgramTable.Machine

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
open BitProgram StructuredCalls LeafParametersProgram SubexpQuarticRing SubexpLiftRing

/-- All collector tapes lie outside every setup write set. -/
theorem collector_not_touched (i : Fin 640) (hlo : 320 ≤ i.val) (hhi : i.val < 340) :
    i∉finalDiscard ∧ i∉idempotentStartPorts ∧ i∉296::nodesStartPorts ∧
    i∉constantStartPorts ∧ i∉([190,249,250,251] : List (Fin 640)) ∧ i∉coreWritePorts := by
  have hall (j : Fin 20) :
      let x : Fin 640 := ⟨320+j.val,by omega⟩
      x∉finalDiscard ∧ x∉idempotentStartPorts ∧ x∉296::nodesStartPorts ∧
      x∉constantStartPorts ∧ x∉([190,249,250,251] : List (Fin 640)) ∧ x∉coreWritePorts := by
    fin_cases j <;> exact of_decide_eq_true rfl
  let j : Fin 20 := ⟨i.val-320,by omega⟩
  have hi : (⟨320+j.val,by omega⟩ : Fin 640)=i := by
    apply Fin.ext
    dsimp [j]
    omega
  simpa only [hi] using hall j

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramSpec
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Pure specifications for the native residual statistics scans. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
abbrev scopeBits := SubexpIncidenceSlotProgram.scopeBits

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProjectionProgramMask
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native scan used by exact-support projection: consume a mask while
copying its bits and an equally long zero mask to reversed accumulators. -/
namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

abbrev MaskData := State 3 3

def maskData (regs : Fin 3 → Bool) (source copy zeros : List Bool) : MaskData :=
  ⟨regs, ![source,copy,zeros]⟩

def ready (regs : Fin 3 → Bool) (source copy zeros : List Bool) : MaskData :=
  maskData (readRegs regs 0 1 source.head?) source copy zeros

@[simp] theorem ready_guard (regs : Fin 3 → Bool) (source copy zeros : List Bool) :
    (ready regs source copy zeros).regs 1 = !source.isEmpty := by
  cases source <;> simp [ready,maskData,readRegs]

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram

end OAI.Algorithms
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
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def readerPorts : RecordPrograms.Ports 6 9 :=
  ⟨3,4,5,8,2,by decide,by decide,by decide,by decide⟩
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

abbrev Data := State 16 48

def state (ctx : Context) (regs : Fin 16 → Bool)
    (word assignment remaining counter duplicate : List Bool) : Data :=
  ⟨regs, fun j =>
    if j = 0 then word
    else if j = 2 then counter
    else if j = 8 then assignment
    else if j = 9 then ctx.packedAlphabet
    else if j = 10 then ctx.width
    else if j = 11 then remaining
    else if j = 30 then ctx.alphabetRecords
    else if j = 34 then ctx.depth
    else if j = 39 then duplicate
    else if j = 45 then ctx.rawPairs
    else if j = 46 then ctx.seedRecords
    else if j = 47 then unary ctx.seedCount else []⟩

def outputState (ctx : Context) : Data :=
  state ctx (fun _ => false) []
    (BlockCopyProgram.copies ctx.seedCount ctx.defaultWord)
    (unary ctx.seedCount) [] ctx.alphabetRecords

@[simp] theorem output_remaining (ctx : Context) :
    ((outputState ctx).stacks 11).length = ctx.seedCount := by
  simp [outputState, state, unary]

end SubexponentialSAT.Subexp.AssignmentInitProgram

end OAI.Algorithms
end


