-- Prove2me | Definitions.Def_OAIQ081S091
-- name    : OAIQ081S091
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:11:27.742845+00:00
-- url     : https://prove2.me/theorems/43c0f7ef-8f1a-4eef-b656-8e515badb4aa
-- title:
--   Definitions bundle OAIQ081S091 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 52 declarations of OpenAI's Lean: 33 definitions, 1 inductive type or structure and 18 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.NumeratorData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheAfterRead`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.numeratorState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutScalarEmitter.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutScalarEmitter.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Local.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native.Clean`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.buildQuery`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.pairBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRowBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.uniformRowBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.cacheState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.readResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentSetupProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentSetupProgram.cleared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.sourceRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.offset`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.records`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.relation`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.valid`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsSemantics.neutralIndex`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.addressedEntries`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.nodeUnits`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Data`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheCell`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCountsPrimitives`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarNumerator`, `SubexponentialSAT_SqrtLog_LayoutProgramTypeCompare`, `SubexponentialSAT_SqrtLog_LayoutScalarEmitter`, `SubexponentialSAT_SqrtLog_LayoutScaledMatrices`, `SubexponentialSAT_SqrtLog_LayoutSourcePlanLookup`, `SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupBasic`, `SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupLocal`, `SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupPorts`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramRow`, `SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram`, `SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgramBasic`, `SubexponentialSAT_SqrtLog_LeafAssignmentSetupProgramBase`, `SubexponentialSAT_SqrtLog_LeafFactorDispatchProgram`, `SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramSemantics`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeContract`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeInputs`, `SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsFactor`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputAddressed`, `SubexponentialSAT_SqrtLog_RingModelNodes`, `SubexponentialSAT_SubexpAnnihilation`, `SubexponentialSAT_SubexpRowInterpolation`, `SubexponentialSAT_Subexp_PackingExtractionOuter`, `SubexponentialSAT_Subexp_PackingLeftoverEmitter`, `SubexponentialSAT_Subexp_PackingLeftovers`, `SubexponentialSAT_Subexp_SelectorOutput`, `SubexponentialSAT_Subexp_SelectorProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S067`, `OAIQ081S070`, `OAIQ081S071`, `OAIQ081S072`, `OAIQ081S073`, `OAIQ081S074` and `OAIQ081S075` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S106`, `OAIQ081S107`, `OAIQ081S108`, `OAIQ081S109`, `OAIQ081S114` and `OAIQ081S115`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.source_max_le_of_energy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native.command_eval_found`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Scan.command_eval_found`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.loop_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.prepareProgram_factored_runsIn`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.source_max_le_of_energy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Scan.command_eval_found`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.loop_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.prepareProgram_factored_runsIn`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S070
import Definitions.Def_OAIQ081S071
import Definitions.Def_OAIQ081S072
import Definitions.Def_OAIQ081S073
import Definitions.Def_OAIQ081S074
import Definitions.Def_OAIQ081S075

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native full-key computation for the resumable attained-signature scan

One invocation preserves the assignment and all raw integer constraint rows.
Its local polynomial-time bound controls every scratch stack at every source
prefix. The generator retains candidate and predecessor cursors separately.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

abbrev Data := State 8 16

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutScalarEmitter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserving signed-pair emission into a reverse buffer. The existing exact
pair serializer is called on paid copies, and its output is transferred once.
All source words survive; the four work stacks are restored to empty. -/
namespace SubexponentialSAT.SqrtLog.LayoutScalarEmitter
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.MatrixProgramSupport

abbrev Data := State 8 7

def Ready (d : Data) : Prop :=
  d.stacks 3 = [] ∧ d.stacks 4 = [] ∧ d.stacks 5 = [] ∧ d.stacks 6 = []

end SubexponentialSAT.SqrtLog.LayoutScalarEmitter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheCell
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The unsigned cache recurrence is executed by a one-bit shift followed by
the original finite little-endian adder. Its representation growth is linear
in the number of cells; no canonical-word assumption is used. -/

/-! One complete cache-row transform, including record parsing and preserving
emission of every newly computed value. -/

/-! Complete reusable cache pass: read one encoded row, compute and emit its
new row, append the end marker, reverse the output, and clear the carry. -/

/-! The number of coefficient-cache rows is runtime unary data. This fixed
loop invokes the complete paid row pass and preserves the current encoded row.
-/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

def cacheAfterRead (regs : Fin 8 → Bool) (counter : List Bool)
    (xs : List (List Bool)) : Data :=
  state (readRegs regs 7 6 counter.head?) ([],counter.tail) ([],[]) ([],[])
    (pairEncoding (xs.map fun x => (x,[])))

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! The physical unsigned cache computes the original coefficient recurrence's
natural magnitudes, in ascending degree order. -/

/-! A fixed loop builds the initial all-one cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/

/-! One fixed program builds the complete unsigned H cache from the unary
runtime parameters A and R. No coefficient or initial cache is free input. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCountsPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

abbrev Data := State 9 40

end SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed port assignments for cache access and triple serialization. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 9 20

def readResult (d : Data) (p n : List Bool) : Fin 20 → List Bool :=
  Function.update (Function.update d.stacks 11 (p++d.stacks 11)) 12 (n++d.stacks 12)

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

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
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def cacheState (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer queue parity : List Bool)
    (work : RowSelectionProgram.WordPair := ([],[])) : Data :=
  ⟨regs,![c.Hpositive.flatten,c.Hnegative.flatten,c.Bpositive.flatten,c.Bnegative.flatten,
    c.width,c.power.1,c.power.2,counter,hindex,kindex,[],work.1,work.2,[],[],[],[],
    buffer,queue,parity]⟩

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramStep.lean

/-! One real triple-production iteration: two scans, three serializers and
paid cleanup. Only a parity bit is kept outside the subroutine registers. -/

/-! A fixed, paid iteration producing the three real scalar operands. -/

/-! The native unary loop produces all triples in increasing binomial index. -/

/-! Initial unary copy/parity and final stream reversal are native paid calls. -/

/-! Complete cache-to-triple primitive program with all scans and copies paid. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarNumerator
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The complete cached scalar call preserves both arrays, the width and the
clearing power. It constructs its operand stream and performs every signed
arithmetic operation on the primitive machine. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open LayoutTriplePreparationProgram

abbrev NumeratorData := State 9 25

def numeratorState (c : Cache) (regs : Fin 9 → Bool)
    (counter parity queue : List Bool) (result : WordPair) : NumeratorData :=
  ⟨regs,![c.Hpositive.flatten,c.Hnegative.flatten,c.Bpositive.flatten,c.Bnegative.flatten,
    c.width,c.power.1,c.power.2,counter,[],[],[],[],[],[],[],[],[],[],queue,parity,
    [],[],[],result.1,result.2]⟩

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramTypeCompare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserving comparison of the two type words using scratch0..3. All cache
ports42..48 remain intact. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev Data := State 10 64

end SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowInterpolation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit mismatch interpolation for the multi-color layout

Section 3.3 of `subexponential-sat.txt`. All inverse data are supplied as
units. The polynomials are finite sums and products, not chosen witnesses.
Their scalar evaluation functions are executable from the supplied ring
operations and units; the semantic polynomial definitions use mathlib's
noncomputable polynomial representation.
-/

namespace SubexponentialSAT.SubexpRowInterpolation

open scoped BigOperators

variable {E I V C : Type*} [CommRing E] [DecidableEq I]

variable {node : I → E}

variable [DecidableEq V]

section Mismatches

variable [Fintype I] [Fintype V] [DecidableEq C]

theorem mismatchRowPath_eval_zero (v : V) (head : V → I → C) (σ : I → C) (R : ℕ)
    (u : NodeUnits node) (d : V → I → E) :
    (fun y => (mismatchRowPath v head σ R u d y).eval 0) = Pi.single v (1 : E) :=
  rowPath_eval_zero v _ (mismatchCorrection_eval_zero head σ R u d)

theorem mismatchRowPath_natDegree_le (v : V) (head : V → I → C) (σ : I → C) (R : ℕ)
    (u : NodeUnits node) (d : V → I → E) (y : V) :
    (mismatchRowPath v head σ R u d y).natDegree ≤ R :=
  rowPath_natDegree_le v _ (mismatchCorrection_natDegree_le head σ R u d) y

end Mismatches

/-! ## Executable finite expression codes

The following constructors produce polynomial expression data using only
finite `List.ofFn` traversals. Their denotations are the proved polynomials
above. This supplies a concrete path representation in addition to the
executable scalar evaluator.
-/

end SubexponentialSAT.SubexpRowInterpolation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpAnnihilation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Simultaneous row annihilation for the multicolor layout

Section 3.3 of `source/subexponential-sat.txt`.  At a fixed interpolation
position, the same row annihilates every color different from its slot color.
The old two-color modules are preserved and used only for generic finite-sum
lemmas.
-/

namespace SubexponentialSAT.SubexpAnnihilation

open scoped BigOperators
open Matrix

section InterpolatedRows

open MulticolorTypes SubexpRowInterpolation

variable {F E : Type*} [Ring F] [CommRing E] {r Q Δ : ℕ}
variable {node : Fin Q → E}

theorem rowForMatrices_origin (φ : F →+* E)
    (M : (t : Fin Q) → (g : Fin r) → (i : Fin Δ) →
      Matrix (Joint t g i) (Joint t g i) F)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ)
    (units : NodeUnits node) :
    (fun y => (rowForMatrices φ M u i R units y).eval 0) = Pi.single u 1 :=
  mismatchRowPath_eval_zero _ _ _ _ _ _

theorem rowForMatrices_degree (φ : F →+* E)
    (M : (t : Fin Q) → (g : Fin r) → (i : Fin Δ) →
      Matrix (Joint t g i) (Joint t g i) F)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ)
    (units : NodeUnits node) (y : UniversalType r Q Δ) :
    (rowForMatrices φ M u i R units y).natDegree ≤ R :=
  mismatchRowPath_natDegree_le _ _ _ _ _ _ _

end InterpolatedRows

end SubexponentialSAT.SubexpAnnihilation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutScaledMatrices
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Cleared integer matrices and exact ring-valued source rows

The rational spectral argument will supply integer numerators `N` and a
power-of-two denominator `d`. Over the target coefficient ring only the
unit representing `d` is inverted. Exact integer equations `d I - N`
therefore imply the fixed-vector equations needed by the original
multicolor row construction, without a map from `ℚ` to the target ring.
-/

namespace SubexponentialSAT.SqrtLog.LayoutScaledMatrices

open scoped BigOperators
open Matrix

section SourceRows

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpRowInterpolation

variable {O : Type*} [CommRing O] {r Q Δ : ℕ}
variable {node : Fin Q → O}

theorem sourceRow_origin (N : Numerators r Q Δ) (denom : Oˣ)
    (a : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ) (units : NodeUnits node) :
    (fun y => (sourceRow N denom a i R units y).eval 0) = Pi.single a 1 :=
  SubexponentialSAT.SubexpAnnihilation.rowForMatrices_origin _ _ _ _ _ _

theorem sourceRow_degree (N : Numerators r Q Δ) (denom : Oˣ)
    (a : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ) (units : NodeUnits node)
    (y : UniversalType r Q Δ) :
    (sourceRow N denom a i R units y).natDegree ≤ R :=
  SubexponentialSAT.SubexpAnnihilation.rowForMatrices_degree _ _ _ _ _ _ _

end SourceRows

end SubexponentialSAT.SqrtLog.LayoutScaledMatrices

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-code lookup with fallback for local read plans

The table is a raw sequence of framed key/payload pairs. The query and table
are runtime bit strings. The program reuses the verified key comparison and
record parsing routines, retaining the first matching payload.
-/

namespace SubexponentialSAT.Subexp.SelectorProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

/-- An actual first-match scan of the encoded table. All scratch strings are
cleared by the existing record routine before the next iteration. -/
theorem scan_eval (query : List Bool) (records : List (List Bool × List Bool))
    (regs : Fin 5 → Bool) (hflag : regs 4 = false) :
    ∃ n ≤ scanBudget query records, ∃ regs' tail,
      Eval scan n (ready regs records query)
        (recordState regs' tail [] query.reverse [] [] (framedResult (records.lookup query))) ∧
      regs' 4 = (records.lookup query).isSome := by
  induction records generalizing regs with
  | nil =>
      refine ⟨1, le_rfl, readRegs regs 0 1 none, [], ?_, ?_⟩
      · simpa [scan, ready, rawRecords, framedResult] using
          (Eval.while_false (test := (1 : Fin 5)) (body := body)
            (a := ready regs [] query) (ready_nil_guard regs query))
      · first | (simpa [readRegs, -OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.status_read] using hflag) | (simpa [readRegs] using hflag)
  | cons p records ih =>
      rcases p with ⟨key, value⟩
      let rr := readRegs regs 0 1 (rawRecords ((key, value) :: records)).head?
      obtain ⟨n, hn, middle, hrecord, hanswer⟩ :=
        oneRecord_eval rr key query value (rawRecords records) []
      have hstart : recordState rr
          (Encoding.frame key ++ (Encoding.frame value ++ rawRecords records))
          [] query.reverse [] [] [] = ready regs ((key, value) :: records) query := by
        simp [ready, rr, rawRecords, List.append_assoc]
      rw [hstart] at hrecord
      by_cases hkey : key = query
      · subst key
        have hm : middle 4 = true := by simpa using hanswer
        have hrec : Eval oneRecord n (ready regs ((query, value) :: records) query)
            (recordState middle (rawRecords records) [] query.reverse [] [] (Encoding.frame value)) := by
          simpa using hrecord
        have hcontrol : Eval continueOrStop 2
            (recordState middle (rawRecords records) [] query.reverse [] [] (Encoding.frame value))
            (recordState (Function.update middle 1 false) (rawRecords records)
              [] query.reverse [] [] (Encoding.frame value)) := by
          exact Eval.ite_true hm (stop_eval middle _ _ _)
        have hend : Eval scan 1
            (recordState (Function.update middle 1 false) (rawRecords records)
              [] query.reverse [] [] (Encoding.frame value))
            (recordState (Function.update middle 1 false) (rawRecords records)
              [] query.reverse [] [] (Encoding.frame value)) := by
          apply Eval.while_false
          simp []
        have hrun := Eval.while_true (ready_cons_guard regs query value query records)
          (Eval.seq hrec hcontrol) hend
        refine ⟨(n + 2) + 1 + 1, ?_, Function.update middle 1 false, rawRecords records, ?_, ?_⟩
        · simp only [scanBudget]
          omega
        · simpa only [scan, body, lookup_cons_eq, framedResult, Option.map_some, Option.getD_some]
            using hrun
        · simpa [lookup_cons_eq] using hm
      · have hm : middle 4 = false := by simpa [hkey] using hanswer
        have hrec : Eval oneRecord n (ready regs ((key, value) :: records) query)
            (recordState middle (rawRecords records) [] query.reverse [] [] []) := by
          simpa [hkey] using hrecord
        have hcontrol : Eval continueOrStop 2
            (recordState middle (rawRecords records) [] query.reverse [] [] [])
            (ready middle records query) := by
          exact Eval.ite_false hm (peek_eval middle _ _ _)
        obtain ⟨m, hmBound, final, tail, hrest, hfinal⟩ := ih middle hm
        have hrun := Eval.while_true (ready_cons_guard regs key value query records)
          (Eval.seq hrec hcontrol) hrest
        refine ⟨(n + 2) + m + 1, ?_, final, tail, ?_, ?_⟩
        · simp only [scanBudget]
          omega
        · simpa only [scan, body, lookup_cons_ne query key value records hkey] using hrun
        · simpa only [lookup_cons_ne query key value records hkey] using hfinal

end SubexponentialSAT.Subexp.SelectorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The output boundary for the fixed first-match selector. A matching payload
is parsed onto the output port; an absent key copies the original query. -/

namespace SubexponentialSAT.Subexp.SelectorProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

theorem materialize_eval (query : List Bool) (result : Option (List Bool))
    (regs : Fin 5 → Bool) (tail : List Bool) (hflag : regs 4 = result.isSome) :
    ∃ regs', Eval materialize (materializeBudget query result)
      (recordState regs tail [] query.reverse [] [] (framedResult result))
      (recordState regs' tail (result.getD query).reverse query.reverse [] [] []) := by
  cases result with
  | none =>
      let d := recordState regs tail [] query.reverse [] [] []
      have hc := copy_eval d 2 1 4 (by decide) (by decide) (by decide) (by rfl)
      have hc' : Eval (.call (StackRoutines.copyProgram 2 1 4 (0 : Fin 5) 1))
          (7 * query.length + 5) d
          (recordState (readRegs regs 0 1 none) tail query.reverse query.reverse [] [] []) := by
        simpa [d, afterCopy, StackRoutines.copyStacks, recordState] using hc
      refine ⟨readRegs regs 0 1 none, ?_⟩
      simpa [materialize, materializeBudget, framedResult, d, Nat.add_assoc] using
        (Eval.ite_false (by simpa [d, recordState] using hflag) hc')
  | some value =>
      let d := recordState regs tail [] query.reverse [] [] (Encoding.frame value)
      have hp := parseFrame_eval d 5 1 (by decide) value [] (by simp [d ])
      have hp' : Eval (.call (parseFrame 5 1)) (6 * value.length + 4) d
          (recordState (readRegs regs 0 1 (some false)) tail value.reverse query.reverse [] [] []) := by
        simpa [d, afterFrame, recordState] using hp
      refine ⟨readRegs regs 0 1 (some false), ?_⟩
      simpa [materialize, materializeBudget, framedResult, d, Nat.add_assoc] using
        (Eval.ite_true (by simpa [d, recordState] using hflag) hp')

/-- The full selector executes only the existing finite parser, equality,
copy, and Boolean control instructions. -/
theorem command_eval (query : List Bool) (records : List (List Bool × List Bool))
    (regs : Fin 5 → Bool) :
    ∃ n ≤ budget query records - 1, ∃ regs' tail,
      Eval command n
        (recordState regs (rawRecords records) [] query.reverse [] [] [])
        (recordState regs' tail ((records.lookup query).getD query).reverse
          query.reverse [] [] []) := by
  let reset := Function.update regs 4 false
  have hset : Eval (atom (.set 4 false)) 1
      (recordState regs (rawRecords records) [] query.reverse [] [] [])
      (recordState reset (rawRecords records) [] query.reverse [] [] []) := by
    simpa [atom, reset, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, recordState]
      using (Eval.base (StructuredProgram.Eval.atom
        (StructuredProgram.Atom.set (4 : Fin 5) false)
        (recordState regs (rawRecords records) [] query.reverse [] [] [])))
  have hpeek : Eval peek 1
      (recordState reset (rawRecords records) [] query.reverse [] [] [])
      (ready reset records query) := peek_eval reset _ _ _
  obtain ⟨ns, hns, middle, tail, hs, hflag⟩ := scan_eval query records reset (by simp [reset])
  obtain ⟨final, hf⟩ := materialize_eval query (records.lookup query) middle tail hflag
  refine ⟨1 + (1 + (ns + materializeBudget query (records.lookup query))), ?_,
    final, tail, Eval.seq hset (Eval.seq hpeek (Eval.seq hs hf))⟩
  dsimp [budget]
  omega

theorem program_trace (query : List Bool) (records : List (List Bool × List Bool))
    (regs : Fin 5 → Bool) :
    ∃ n ≤ budget query records, ∃ regs' tail,
      Trace program n
        ((recordState regs (rawRecords records) [] query.reverse [] [] []).withPC
          (some program.entry))
        ((recordState regs' tail ((records.lookup query).getD query).reverse
          query.reverse [] [] []).withPC none) := by
  obtain ⟨n, hn, regs', tail, ht⟩ := command_eval query records regs
  refine ⟨n + 1, ?_, regs', tail, compiled_halt_trace ht 0 1⟩
  have hb : 0 < budget query records := by dsimp [budget]; omega
  omega

end SubexponentialSAT.Subexp.SelectorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed twelve-stack workspace for a full pair-key lookup. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 16 12

def data (regs : Fin 16 → Bool)
    (literal ambient factor master count query field frameTmp scan payload work tmp : List Bool) : Data :=
  ⟨regs,![literal,ambient,factor,master,count,query,field,frameTmp,scan,payload,work,tmp]⟩

def buildQuery : Code :=
  .seq (copy 2 6) (.seq (copy 1 6) (.seq (push 5 false)
    (.seq (LayoutMatrixProgram.frame 6 5 7 (by decide)) (.seq (push 5 true)
      (.seq (copy 0 6) (.seq (LayoutMatrixProgram.frame 6 5 7 (by decide))
        (.seq (push 5 true) (LayoutMatrixProgram.frame 5 6 7 (by decide)))))))))

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupLocal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

namespace Local

def command : Code := .seq buildQuery (.seq Scan.command (clear 6))

end Local
end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupPorts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 16 340

def Clean (d : Data) : Prop :=
  ∀ i ∈ ([304,315,316,317,318,319,338,339] : List (Fin 340)), d.stacks i=[]

abbrev command : Cmd 16 340 := liftCommand Local.command 0 4 id stack

def budget (d : Data) (nodes : List (List Bool)) : ℕ :=
  Local.budget (d.stacks 233) (d.stacks 212) (d.stacks 216) nodes+1

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Full pair-plan lookup at the source-row ABI. All query construction, record
comparison, index increments and cleanup are native paid instructions. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT BitProgram StructuredCalls

/-- Includes the final halt instruction. -/
def pairBudget (literal ambient factor : ℕ) (ps : List (ℕ × ℕ)) : ℕ :=
  39*(literal+ambient+factor)+115+
    (36*(literal+ambient+factor)+179)*((LayoutOwnerFiberProgram.stream ps).length+1)

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One source row: actual owner scan, native per-incidence source generation,
postfix summation, and native polynomial evaluation. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def sourceRowBudget (query : ℕ) (ps : List (ℕ × ℕ)) (I K L D d B a b : ℕ) : ℕ :=
  let F := (LayoutOwnerFiberProgram.fiberIndices query 0 ps).length
  let S := 2+F*(L+2)
  LayoutOwnerFiberProgram.budget query ps+F*(K+5*I+3*L+15)+
    300000*(S+1)*(D+1)^3*(d+1)^3*(B+1)^2+18*(D*(d*B))+
    6*a+6*b+3*S+67

def uniformRowBudget (N : ℕ) (ps : List (ℕ × ℕ)) (I K L D d B a b : ℕ) : ℕ :=
  let S := 2+ps.length*(L+2)
  1000*((LayoutOwnerFiberProgram.stream ps).length+N+1)^2+
    ps.length*(K+5*I+3*L+15)+
    300000*(S+1)*(D+1)^3*(d+1)^3*(B+1)^2+18*(D*(d*B))+
    6*a+6*b+3*S+67

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafAssignmentSetupProgramBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete storage and framed service calls for each head assignment. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafAssignmentSetupProgram
open SubexponentialSAT BitProgram StructuredCalls StackRoutines

abbrev Data := State 40 768
def cleared (a : Data) (src : Fin 768) : Data :=
  ⟨readRegs a.regs 0 1 none, Function.update a.stacks src []⟩

end SubexponentialSAT.SqrtLog.LeafAssignmentSetupProgram
end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid factor classification and source lookup. IDs are runtime data. -/
namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 8 16

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical row predicate selects exactly the computed factor colors. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls MulticolorTypes

variable {I : Type*} [Fintype I] [DecidableEq I] {A N r Q : ℕ}

/-- Exactly the row list flattened by the existing assignment controller. -/
def sourceRows (owner : I → Fin A) (factor : I → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I (Fin A) Q)) (w : PackingProgram.Weights) :
    List (List Bool) :=
  (PackingProgram.selectedValues owner factor a tail terms (indices A N) w).reverse.map
    Subexp.ReadPlan.encodeWord

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed outer loop extracts all complete blocks in block-major order. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open BitProgram StructuredCalls MatrixProgramSupport

theorem popRemaining_eval (regs : Fin 8 → Bool) (c : Context) :
    Eval popRemaining 1 (base regs c)
      (base (readRegs regs 3 4 c.remaining.head?) { c with remaining := c.remaining.tail }) := by
  have h : Eval popRemaining 1 (base regs c)
      ((StructuredProgram.Atom.pop (16 : Fin 19) (3 : Fin 8) 4).eval (base regs c)) :=
    .base (.atom _ _)
  have he : (StructuredProgram.Atom.pop (16 : Fin 19) (3 : Fin 8) 4).eval (base regs c) =
      base (readRegs regs 3 4 c.remaining.head?) { c with remaining := c.remaining.tail } := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    funext j
    fin_cases j <;> simp [base, ready, state, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]
  rw [he] at h
  exact h

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingLeftoverEmitter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual emission and covered-key lookup for the leftover packing pass. -/

namespace SubexponentialSAT.Subexp.PackingCoveredQuery

open BitProgram StructuredCalls

/-- The actual selector is followed by physical cleanup. Only its found flag
survives, so no fallback value can be mistaken for a covered vertex. -/
theorem command_eval (query : List Bool) (records : List (List Bool × List Bool))
    (regs : Fin 5 → Bool) :
    ∃ n ≤ budget query records, ∃ rf,
      Eval command n (state regs (SelectorProgram.rawRecords records) query.reverse [])
        (state rf [] [] []) ∧ rf 4 = (records.lookup query).isSome := by
  let r0 := Function.update regs 4 false
  let a := state regs (SelectorProgram.rawRecords records) query.reverse []
  have h0 : Eval (SelectorProgram.atom (.set 4 false)) 1 a
      (state r0 (SelectorProgram.rawRecords records) query.reverse []) := by
    exact .base (.atom _ _)
  have hp := SelectorProgram.peek_eval r0 (SelectorProgram.rawRecords records) query.reverse []
  obtain ⟨n,hn,rs,tail,hs,hflag⟩ := SelectorProgram.scan_eval query records r0 (by simp [r0])
  let result := SelectorProgram.framedResult (records.lookup query)
  let b := state rs tail query.reverse result
  have hcore : Eval core (1+(1+n)) a b := h0.seq (hp.seq hs)
  have ht := compiled_halt_trace hcore 0 5
  have htail : tail.length ≤ (SelectorProgram.rawRecords records).length+n+3 := by
    have h := SequentialProgram.trace_stack_length_le ht 0
    change tail.length ≤ (SelectorProgram.rawRecords records).length+(1+(1+n)+1) at h
    omega
  have hresult : result.length ≤ n+3 := by
    have h := SequentialProgram.trace_stack_length_le ht 5
    change result.length ≤ 0+(1+(1+n)+1) at h
    omega
  let r1 := readRegs rs 0 1 none
  let c := state r1 [] query.reverse result
  have h1 : Eval (.call (StackRoutines.clearProgram (0 : Fin 6) (0 : Fin 5) 1))
      (2*tail.length+3) b c := by
    have h := TupleProgram.clear_eval (0 : Fin 6) (0 : Fin 5) 1 b
    have he : (⟨readRegs b.regs 0 1 none,StackRoutines.clearStacks 0 b.stacks⟩ : Data) = c := by
      apply congrArg₂ StructuredProgram.State.mk rfl
      funext j
      fin_cases j <;> simp [b,state,SubexpRecordScan.recordState,StackRoutines.clearStacks]
    rw [he] at h
    exact h
  let r2 := readRegs r1 0 1 none
  let d := state r2 [] [] result
  have h2 : Eval (.call (StackRoutines.clearProgram (2 : Fin 6) (0 : Fin 5) 1))
      (2*query.length+3) c d := by
    have h := TupleProgram.clear_eval (2 : Fin 6) (0 : Fin 5) 1 c
    have he : (⟨readRegs c.regs 0 1 none,StackRoutines.clearStacks 2 c.stacks⟩ : Data) = d := by
      apply congrArg₂ StructuredProgram.State.mk rfl
      funext j
      fin_cases j <;> simp [c,state,SubexpRecordScan.recordState,StackRoutines.clearStacks]
    rw [he] at h
    simpa [c,state,SubexpRecordScan.recordState] using h
  let r3 := readRegs r2 0 1 none
  let e := state r3 [] [] []
  have h3 : Eval (.call (StackRoutines.clearProgram (5 : Fin 6) (0 : Fin 5) 1))
      (2*result.length+3) d e := by
    have h := TupleProgram.clear_eval (5 : Fin 6) (0 : Fin 5) 1 d
    have he : (⟨readRegs d.regs 0 1 none,StackRoutines.clearStacks 5 d.stacks⟩ : Data) = e := by
      apply congrArg₂ StructuredProgram.State.mk rfl
      funext j
      fin_cases j <;> simp [d,state,SubexpRecordScan.recordState,StackRoutines.clearStacks]
    rw [he] at h
    exact h
  refine ⟨_,?_,r3,hcore.seq (h1.seq (h2.seq h3)),?_⟩
  · dsimp [budget]
    omega
  · simpa [r3,r2,r1,readRegs, SqrtLog.LayoutOwnerFiberProgram.status] using hflag

theorem program_trace (query : List Bool) (records : List (List Bool × List Bool))
    (regs : Fin 5 → Bool) :
    ∃ n ≤ budget query records+1, ∃ rf,
      Trace program n
        ((state regs (SelectorProgram.rawRecords records) query.reverse []).withPC (some program.entry))
        ((state rf [] [] []).withPC none) ∧ rf 4 = (records.lookup query).isSome := by
  obtain ⟨n,hn,rf,he,hf⟩ := command_eval query records regs
  exact ⟨n+1,by omega,rf,compiled_halt_trace he 0 5,hf⟩

end SubexponentialSAT.Subexp.PackingCoveredQuery


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingLeftovers
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual leftover packing pass

The immutable covered table is searched for every original vertex. A found
vertex is skipped. A missing vertex is appended to reversed storage and both
lookup tables, with actual unary rank/address increments.
-/
namespace SubexponentialSAT.Subexp.PackingLeftovers

open BitProgram StructuredCalls MatrixProgramSupport

theorem query_eval (records : Records) (query : List Bool) (regs : Fin 8 → Bool)
    (source payload rank address storage metadata addresses vertex : List Bool) :
    ∃ n ≤ PackingCoveredQuery.budget query records+1, ∃ rf,
      Eval queryCall n
        (data regs (SelectorProgram.rawRecords records) query.reverse
          (SelectorProgram.rawRecords records) source payload rank address storage metadata addresses vertex)
        (data rf [] [] (SelectorProgram.rawRecords records) source payload rank address storage metadata addresses vertex) ∧
      rf 4 = (records.lookup query).isSome := by
  let a := data regs (SelectorProgram.rawRecords records) query.reverse
    (SelectorProgram.rawRecords records) source payload rank address storage metadata addresses vertex
  obtain ⟨n,hn,rs,ht,hflag⟩ := PackingCoveredQuery.program_trace query records (regs ∘ queryRegs)
  let rf := mergeRegs regs rs
  let b := data rf [] [] (SelectorProgram.rawRecords records) source payload rank address storage metadata addresses vertex
  have ha : embedState queryRegs queryStacks a
      (PackingCoveredQuery.state (regs ∘ queryRegs) (SelectorProgram.rawRecords records) query.reverse []) = a := by
    apply SelectorMapProgram.embed_eq _ _ queryRegs_injective queryStacks_injective
    · intros; rfl
    · intro i
      fin_cases i <;> rfl
    · intros; rfl
    · intros; rfl
  have hb : embedState queryRegs queryStacks a (PackingCoveredQuery.state rs [] [] []) = b := by
    apply SelectorMapProgram.embed_eq _ _ queryRegs_injective queryStacks_injective
    · intro i
      simp [b,rf,mergeRegs,queryRegs,PackingCoveredQuery.state,SubexpRecordScan.recordState,data,i.isLt]
    · intro i
      fin_cases i <;> rfl
    · intro i hi
      have hn : ¬ i.val < 5 := by
        intro h
        exact hi ⟨⟨i.val,h⟩,Fin.ext rfl⟩
      simp [b,rf,mergeRegs,hn,a,data]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
      have h2 : i ≠ 2 := fun h => hi ⟨2,h.symm⟩
      simp only [a,b,data_stacks,ite_eq_right h0,ite_eq_right h2]
  have he := eval_call_lifted PackingCoveredQuery.program queryRegs queryStacks a
    queryRegs_injective queryStacks_injective ht
  rw [ha,hb] at he
  refine ⟨n,hn,rf,he,?_⟩
  simpa [rf,mergeRegs] using hflag

end SubexponentialSAT.Subexp.PackingLeftovers

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeInputs
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime source facts for the closed head setup. No cache output, matrix,
entry evaluator, or running-time witness is supplied in this interface. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking RowSelectionProgram

structure Inputs where
  n : ℕ
  N : ℕ
  r : ℕ
  Q : ℕ
  D : ℕ
  R : ℕ
  occurrence : ℕ
  packing : PackingData (Fin D) (UniversalType r Q 1)
  node : Fin Q
  plans : List (ℕ × ℕ)
  rows : List (List Bool)
  low : List Bool
  height : List Bool
  width : List Bool
  plans_length : plans.length=D
  rows_length : n+N ≤ rows.length
  rows_width : ∀ row∈rows,row.length=Q*r
  height_le : height.length ≤ Q
  width_boot : 1+2*height.length*R ≤ width.length
  width_node : Q+1 ≤ width.length
  fiber_degree : ∀ v < n,(LayoutOwnerFiberProgram.fiberIndices v 0 plans).length ≤ occurrence

def Inputs.records (s : Inputs) : List (List Bool) :=
  s.plans.map (fun p=>LayoutOwnerFiberProgram.pairPayload p.1 p.2)
def Inputs.offset (s : Inputs) : ℕ := 2*s.occurrence*(8*s.Q)^(2*s.R)
def Inputs.relation (s : Inputs) : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop :=
  BucketProgram.ProducedRank.FiberRel s.plans
    (BucketProgram.ProducedRank.entryNat s.packing s.height.length s.R s.node) s.offset

@[simp] theorem Inputs.records_length (s : Inputs) : s.records.length=s.D := by
  simp [Inputs.records,s.plans_length]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeContract
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Close the only service premise of the head loop using the actual entry
machine and the bootstrap's produced caches. All budgets are explicit. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def Inputs.valid (s : Inputs) (j v : ℕ) : Prop := j < s.D ∧ v < s.n

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsFactor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The exact native neutral ID is the rank of its uncovered original owner.
This is an explicit indexing equivalence, not just equality of cardinalities. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open PackingIncidenceInput LeafStatisticsProgram HighIncidence

theorem uncovered_owner_mem (scopes : List (List ℕ)) (mask : List Bool)
    (v : uncovered (residualScope scopes mask)) :
    v.val.val.val ∈ neutralOwners scopes 0 mask := by
  apply (neutralOwners_mem scopes 0 _ mask).mpr
  refine ⟨free_mem_lowOwners mask v.val, ?_⟩
  have hd : Incidence.degree (residualScope scopes mask) v.val = 0 :=
    (Finset.mem_filter.mp v.property).2
  rw [residual_degree] at hd
  exact List.length_eq_zero_iff.mp hd

def neutralIndex (scopes : List (List ℕ)) (mask : List Bool)
    (v : uncovered (residualScope scopes mask)) :
    Fin (neutralOwners scopes 0 mask).length :=
  ⟨(neutralOwners scopes 0 mask).idxOf v.val.val.val,
    List.idxOf_lt_length_iff.mpr (uncovered_owner_mem scopes mask v)⟩

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputAddressed
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The saved stream contains word addresses, so its second component is the
ambient-offset factor address. Incidence positions and owner fibers are unchanged. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput
open SubexponentialSAT.Subexp

def addressedEntries (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) : List (ℕ × ℕ) :=
  (Semantics.nativeEntries scopes mask).map (fun p => (p.1,n+p.2))

end SubexponentialSAT.SqrtLog.PackingIncidenceInput

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingModelNodes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit radix-indexed nodes for the supplied-polynomial ring model. -/

noncomputable section
namespace SubexponentialSAT.SqrtLog.RingModel.Data

variable {d : ℕ} (a : RingModel.Data d) (t Q : ℕ)

theorem residueNode_ne_zero (hQ : Q < 3 ^ d) (i : Fin Q) :
    a.residueNode Q hQ i ≠ 0 := by
  intro he
  have hh := congrArg a.fieldIndex he
  simp only [residueNode, Equiv.apply_symm_apply, fieldIndex_zero] at hh
  have hv := congrArg Fin.val hh
  simp only [Fin.val_zero] at hv
  omega

theorem residueNode_injective (hQ : Q < 3 ^ d) :
    Function.Injective (a.residueNode Q hQ) := by
  intro i j hij
  have hh := congrArg a.fieldIndex hij
  simp only [residueNode, Equiv.apply_symm_apply] at hh
  have hv : i.val + 1 = j.val + 1 := congrArg (fun z : Fin (3 ^ d) => z.val) hh
  apply Fin.ext
  omega

def nodeUnits (ht : 0 < t) (hQ : Q < 3 ^ d) :
    SubexpRowInterpolation.NodeUnits (a.node t Q ht hQ) where
  nodeUnit i := a.unitOfResidue t ht (a.node t Q ht hQ i) (by
    rw [rho_node]; exact a.residueNode_ne_zero Q hQ i)
  nodeUnit_val _ := rfl
  differenceUnit i j hij := a.unitOfResidue t ht (a.node t Q ht hQ i - a.node t Q ht hQ j) (by
    rw [map_sub, rho_node, rho_node]
    exact sub_ne_zero.mpr (fun he => hij (a.residueNode_injective Q hQ he)))
  differenceUnit_val _ _ _ := rfl

end SubexponentialSAT.SqrtLog.RingModel.Data

end
end OAI.Algorithms
end


