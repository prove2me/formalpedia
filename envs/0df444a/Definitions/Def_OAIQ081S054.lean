-- Prove2me | Definitions.Def_OAIQ081S054
-- name    : OAIQ081S054
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:42:57.690466+00:00
-- url     : https://prove2.me/theorems/01138fc4-db33-44ae-8f4f-e67e5d896172
-- title:
--   Definitions bundle OAIQ081S054 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 50 declarations of OpenAI's Lean: 29 definitions, 1 inductive type or structure and 20 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.Layout.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Layout.Data.Head`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Layout.Data.bucketLabel`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Layout.Data.localValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Layout.Data.nodeValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Layout.Data.restrict`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Layout.ofIndexed`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBlocks.RowIndex`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBlocks.constraints`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBlocks.copyHead`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBlocks.embedHead`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.clearColumn`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.normalizeAt`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.parse`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutScalarEmitter.emitPair`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutScalarEmitter.finishList`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutScalarEmitter.pairCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.finish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.Entries.emitOne`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.Entries.emitPair`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.clearedAt`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.clearedList`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.negativeReader`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.parsePair`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.positiveReader`, `OAI.Algorithms.SubexponentialSAT.Subexp.ActivePlanProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.columnCorrection`, `OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.correctionPolynomial`, `OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.mismatchCorrection`, `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.copyManyCost`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramCompare`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramPrefix`, `SubexponentialSAT_SqrtLog_LayoutBlocks`, `SubexponentialSAT_SqrtLog_LayoutFiberSumProgramBasic`, `SubexponentialSAT_SqrtLog_LayoutIndexed`, `SubexponentialSAT_SqrtLog_LayoutInterface`, `SubexponentialSAT_SqrtLog_LayoutProgramNormalize`, `SubexponentialSAT_SqrtLog_LayoutProgramScalar`, `SubexponentialSAT_SqrtLog_LayoutScalarEmitter`, `SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram`, `SubexponentialSAT_SqrtLog_ProgramTapeReplayFootprint`, `SubexponentialSAT_SqrtLog_ProgramTapeReplayMacros`, `SubexponentialSAT_SqrtLog_RowSelectionProgramEntriesEmit`, `SubexponentialSAT_SqrtLog_RowSelectionProgramParser`, `SubexponentialSAT_SqrtLog_RowSelectionProgramResources`, `SubexponentialSAT_SubexpRowInterpolation`, `SubexponentialSAT_SubexpSetupStorage`, `SubexponentialSAT_Subexp_ActivePlanProgram`, `SubexponentialSAT_Subexp_BlockSearchProgram`, `SubexponentialSAT_Subexp_TupleProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S023`, `OAIQ081S024`, `OAIQ081S025`, `OAIQ081S026`, `OAIQ081S027`, `OAIQ081S028`, `OAIQ081S029`, `OAIQ081S033`, `OAIQ081S034` and `OAIQ081S035` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S071`, `OAIQ081S072`, `OAIQ081S073`, `OAIQ081S075`, `OAIQ081S077`, `OAIQ081S079`, `OAIQ081S080` and `OAIQ081S081`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.actualMax_rank_budget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.command_eval`.
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
import Definitions.Def_OAIQ081S033
import Definitions.Def_OAIQ081S034
import Definitions.Def_OAIQ081S035

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

/-! The fixed ABI uses ten Boolean registers and nine Boolean stacks:
0 prior tuples, 1 saved alphabet, 2 current reversed tuple, 3 alphabet cursor,
4 reversed word, 5 output, 6 copied tuple, 7 copy scratch, 8 unary depth.
Registers 0--2 and 3--5 belong to the two framed iterators, 6--7 are scratch,
and 8--9 belong to the eventual depth loop. -/

theorem transfer_eval {r s : ℕ} (src dst : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hvp : value ≠ present) (a : State r s) :
    Eval (.call (StackRoutines.transferProgram src dst value present))
      (3 * (a.stacks src).length + 3) a
      ⟨readRegs a.regs value present none, StackRoutines.transferStacks src dst a.stacks⟩ := by
  apply Eval.call
  have h := StackRoutines.halt_after_trace _
    (StackRoutines.transferProgram_trace src dst value present hsd hvp a.regs a.stacks)
    3 rfl rfl
  simpa [StructuredProgram.State.withPC, StackRoutines.transferResult,
    StackRoutines.transferProgram, Nat.add_assoc] using h

end SubexponentialSAT.Subexp.TupleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramCompare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-control equality of equally long serialized coefficient arrays.
Both inputs are consumed. The length premise is supplied by the explicit
coefficient-count invariants, never by an unchecked array access. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram

theorem compare_round (regs : Fin 4 → Bool) (a b : Bool) (left right : List Bool) :
    Trace compareProgram 6 (compareCfg (some 1) regs (a :: left) (b :: right))
      (compareCfg (some 1) (compareRoundRegs regs a b) left right) := by
  cases a <;> cases b <;> apply Computation.Trace.of_iterate <;>
    simp [Function.iterate_succ_apply, step, compareProgram, compareCfg,
      compareRoundRegs, execInstr, readRegs, Function.update_apply] <;>
    funext i <;> fin_cases i <;> simp

theorem compare_exit (regs : Fin 4 → Bool) :
    Trace compareProgram 3 (compareCfg (some 1) regs [] [])
      (compareCfg none (readRegs regs 0 1 none) [] []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, compareProgram, compareCfg,
    execInstr, readRegs, Function.update_apply]

theorem compare_loop (left right : List Bool) (hlen : left.length = right.length)
    (regs : Fin 4 → Bool) :
    ∃ finalRegs, Trace compareProgram (6 * left.length + 3)
      (compareCfg (some 1) regs left right) (compareCfg none finalRegs [] []) ∧
      finalRegs 3 = (regs 3 && decide (left = right)) := by
  induction left generalizing right regs with
  | nil =>
      have hr : right = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst right
      exact ⟨readRegs regs 0 1 none, compare_exit regs, by simp [readRegs]⟩
  | cons a left ih =>
      cases right with
      | nil => simp at hlen
      | cons b right =>
          obtain ⟨last, ht, hv⟩ := ih right (by simpa using hlen) (compareRoundRegs regs a b)
          refine ⟨last, ?_, ?_⟩
          · have he := (compare_round regs a b left right).trans ht
            convert he using 1 ; simp ; omega
          · cases a <;> cases b <;> simpa [compareRoundRegs, Bool.and_assoc] using hv

theorem compare_run (left right : List Bool) (hlen : left.length = right.length)
    (regs : Fin 4 → Bool) :
    ∃ finalRegs, Trace compareProgram (6 * left.length + 4)
      (compareCfg (some 0) regs left right) (compareCfg none finalRegs [] []) ∧
      finalRegs 3 = decide (left = right) := by
  have hi : Trace compareProgram 1 (compareCfg (some 0) regs left right)
      (compareCfg (some 1) (Function.update regs 3 true) left right) := by
    apply Computation.Trace.of_iterate
    simp [ step, compareProgram, compareCfg, execInstr]
  obtain ⟨last, ht, hv⟩ := compare_loop left right hlen (Function.update regs 3 true)
  refine ⟨last, ?_, by simpa using hv⟩
  have he := hi.trans ht
  simpa only [show 1 + (6 * left.length + 3) = 6 * left.length + 4 by omega] using he

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramPrefix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-length padded prefixes, with reversal by coefficient rather
than by bit. This is the physical stream preparation needed before a
convolution dot product. A unary count controls one fixed eight-label
program; exhaustion of the coefficient source supplies the zero cell. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram

theorem prefix_exit (regs : Fin 6 → Bool) (source output : List Bool) :
    Trace prefixReverseProgram 3
      (prefixCfg (some 0) regs source [] output)
      (prefixCfg none (readRegs regs 4 5 none) source [] output) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, prefixReverseProgram, prefixCfg,
    execInstr, readRegs, Function.update_apply]

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowInterpolation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

@[simp] theorem basis_eval_self (u : NodeUnits node) (s : Finset I) (i : I) :
    (basis u s i).eval (node i) = 1 := by
  simp only [basis, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_prod, u.nodeInverse_mul, one_mul]
  apply Finset.prod_eq_one
  intro j hj
  exact basisDivisor_eval_left u (Finset.ne_of_mem_erase hj).symm

/-- Explicit correction polynomial, including the empty-constraint case. -/
noncomputable def correctionPolynomial (u : NodeUnits node) (s : Finset I) (d : I → E) :
    Polynomial E :=
  ∑ i ∈ s, Polynomial.C (d i) * basis u s i

@[simp] theorem correctionPolynomial_eval_zero (u : NodeUnits node) (s : Finset I) (d : I → E) :
    (correctionPolynomial u s d).eval 0 = 0 := by
  simp [correctionPolynomial, Polynomial.eval_finsetSum]

@[simp] theorem correctionPolynomial_coeff_zero (u : NodeUnits node) (s : Finset I) (d : I → E) :
    (correctionPolynomial u s d).coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, correctionPolynomial_eval_zero]

variable [DecidableEq V]

/-- One correction for each selected column, and the zero polynomial elsewhere. -/
noncomputable def columnCorrection (Y : Finset V) (A : V → Finset I)
    (u : NodeUnits node) (d : V → I → E) (y : V) : Polynomial E :=
  if y ∈ Y then correctionPolynomial u (A y) (d y) else 0

@[simp] theorem columnCorrection_of_not_mem (Y : Finset V) (A : V → Finset I)
    (u : NodeUnits node) (d : V → I → E) {y : V} (hy : y ∉ Y) :
    columnCorrection Y A u d y = 0 := by
  simp [columnCorrection, hy]

@[simp] theorem columnCorrection_eval_zero (Y : Finset V) (A : V → Finset I)
    (u : NodeUnits node) (d : V → I → E) (y : V) :
    (columnCorrection Y A u d y).eval 0 = 0 := by
  by_cases hy : y ∈ Y <;> simp [columnCorrection, hy]

section Mismatches

variable [Fintype I] [Fintype V] [DecidableEq C]

/-- Simultaneous correction values: one polynomial is reused for every other color. -/
noncomputable def mismatchCorrection (head : V → I → C) (σ : I → C) (R : ℕ)
    (u : NodeUnits node) (d : V → I → E) : V → Polynomial E :=
  columnCorrection (correctionColumns head σ R) (mismatchPositions head σ) u d

@[simp] theorem mismatchCorrection_eval_zero (head : V → I → C) (σ : I → C) (R : ℕ)
    (u : NodeUnits node) (d : V → I → E) (y : V) :
    (mismatchCorrection head σ R u d y).eval 0 = 0 :=
  columnCorrection_eval_zero _ _ _ _ _

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutInterface
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Exact integer-bucket interface for the new incidence layout

This interface does not assert existence or a running time. Concrete
construction is assembled from the new packing, integer numerator, and
incidence-pullback modules. Unlike the old residue-only interface, its
locality conclusion is an exact equality in the coefficient ring.
-/

namespace SubexponentialSAT.SqrtLog.Layout

open scoped BigOperators
open LayoutExactBuckets

variable {V I F G O : Type*}
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G]
variable [CommRing O]

structure Data (owner : I → V) (factor : I → F) (Q R : ℕ) where
  node : Fin Q → O
  units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node
  head : Fin Q → V → G
  color : F → Fin Q → G
  row : I → V → Polynomial O
  row_origin : ∀ i v, (row i v).eval 0 = if v = owner i then 1 else 0
  row_degree : ∀ i v, (row i v).natDegree ≤ R
  rowCount : Fin Q → G → ℕ
  constraints : (t : Fin Q) → (g : G) → Fin (rowCount t g) →
    {v : V // head t v = g} → ℤ
  locality : ∀ (t : Fin Q) (i : I) (g : G), g ≠ color (factor i) t →
    KillsIntegerKernel
      (fun v : {v : V // head t v = g} => (row i v.val).eval (node t))
      (constraints t g)

namespace Data

variable {owner : I → V} {factor : I → F} {Q R : ℕ}
variable (L : Data (O := O) (G := G) owner factor Q R)

abbrev Head (t : Fin Q) (g : G) := {v : V // L.head t v = g}

def restrict (t : Fin Q) (g : G) (x : V → ℤ) : L.Head t g → ℤ :=
  fun v => x v.val

def bucketLabel (t : Fin Q) (g : G) (x : L.Head t g → ℤ) :
    Fin (L.rowCount t g) → ℤ := signature (L.constraints t g) x

def localValue (t : Fin Q) (i : I) (g : G) (x : L.Head t g → ℤ) : O :=
  value (fun v : L.Head t g => (L.row i v.val).eval (L.node t)) x

def nodeValue (t : Fin Q) (i : I) (x : V → ℤ) : O :=
  value (fun v => (L.row i v).eval (L.node t)) x

end Data

end SubexponentialSAT.SqrtLog.Layout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutIndexed
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A finite row-indexed constructor for the exact layout interface. -/
namespace SubexponentialSAT.SqrtLog.Layout

open LayoutExactBuckets

variable {V I F G O : Type*}
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G]
variable [CommRing O]

/-- Reindex a concrete finite integer row family by its exact cardinality.
This changes no row values or bucket equivalence. -/
noncomputable def ofIndexed {owner : I → V} {factor : I → F} {Q R : ℕ}
    (node : Fin Q → O) (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node)
    (head : Fin Q → V → G) (color : F → Fin Q → G)
    (row : I → V → Polynomial O)
    (origin : ∀ i v, (row i v).eval 0 = if v = owner i then 1 else 0)
    (degree : ∀ i v, (row i v).natDegree ≤ R)
    (J : Fin Q → G → Type*) [∀ t g, Fintype (J t g)]
    (constraints : (t : Fin Q) → (g : G) → J t g → {v : V // head t v = g} → ℤ)
    (locality : ∀ (t : Fin Q) (i : I) (g : G), g ≠ color (factor i) t →
      KillsIntegerKernel (fun v : {v : V // head t v = g} =>
        (row i v.val).eval (node t)) (constraints t g)) :
    Data (O := O) (G := G) owner factor Q R where
  node := node
  units := units
  head := head
  color := color
  row := row
  row_origin := origin
  row_degree := degree
  rowCount := fun t g => Fintype.card (J t g)
  constraints := fun t g j => constraints t g ((Fintype.equivFin (J t g)).symm j)
  locality := by
    intro t i g hg z hz
    apply locality t i g hg z
    intro j
    simpa [signature] using hz ((Fintype.equivFin (J t g)) j)

end SubexponentialSAT.SqrtLog.Layout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutBlocks
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Assemble complete copies of an actual universal block, with singleton
constraints on uncovered incidences. The scalar ring is arbitrary. -/
namespace SubexponentialSAT.SqrtLog.LayoutBlocks

open scoped BigOperators
open LayoutPullback LayoutExactBuckets

variable {U I F G O : Type*}
variable [Fintype U] [DecidableEq U] [Fintype I] [DecidableEq I]
variable [Fintype G] [DecidableEq G] [CommRing O]
variable {Q R b : ℕ} {label : I → U}

omit [DecidableEq U] [Fintype I] in
@[simp] theorem assembledRow_outside (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b)
    (rows : U → U → Polynomial O) (i : I) (hi : i ∉ Set.range P.embed) :
    assembledRow P rows i = (fun v => Polynomial.C (if v = i then 1 else 0)) :=
  Function.extend_apply' _ _ i hi

def copyHead
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (label : I → U) (t : Fin Q) (i : I) : G := C.head t (label i)

abbrev RowIndex
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b) (t : Fin Q) (g : G) :=
  (Fin b × Fin (C.rowCount t g)) ⊕
    {v : {i : I // copyHead C label t i = g} // v.val ∉ Set.range P.embed}

def embedHead
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b) (t : Fin Q) (g : G) (j : Fin b) :
    {u : U // C.head t u = g} → {i : I // copyHead C label t i = g} :=
  fun u => ⟨P.embed (j,u.val), by simpa [copyHead, P.type_eq] using u.property⟩

noncomputable def constraints
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b) (t : Fin Q) (g : G) :
    RowIndex C P t g → {i : I // copyHead C label t i = g} → ℤ
  | Sum.inl jk => row (embedHead C P t g jk.1) (C.constraints t g jk.2)
  | Sum.inr v => Pi.single v.val 1

end SubexponentialSAT.SqrtLog.LayoutBlocks

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramResources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Stack-size accounting and fixed cleanup loops for signed minor arithmetic. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def clearedAt (j : Fin 15) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks j []⟩

def clearedList : List (Fin 15) → Data → Data
  | [], d => d
  | j :: js, d => clearedList js (clearedAt j d)

@[simp] theorem clearedList_stack (js : List (Fin 15)) (d : Data) (j : Fin 15) :
    (clearedList js d).stacks j = if j ∈ js then [] else d.stacks j := by
  induction js generalizing d with
  | nil => simp [clearedList]
  | cons i js ih =>
    simp only [clearedList, ih, List.mem_cons, clearedAt]
    by_cases h : j = i
    · subst j; simp
    · by_cases hj : j ∈ js <;> simp_all

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

def positiveReader : RecordPrograms.Ports 8 16 :=
  ⟨0,1,7,15,2, by decide, by decide, by decide, by decide⟩
def negativeReader : RecordPrograms.Ports 8 16 :=
  ⟨0,1,7,15,3, by decide, by decide, by decide, by decide⟩

abbrev parsePair : Cmd 8 16 :=
  .seq (.base (.atom (.pop 15 7 6)))
    (.ite 7 (.seq (RecordPrograms.reader positiveReader)
      (RecordPrograms.reader negativeReader)) (.base .skip))

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native owner-fiber summation helpers. The remaining fiber is a stream of
actual unary index fields, never an array of precomputed matrix entries. -/
namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open RowSelectionProgram

def clearColumn : Code := .call (StackRoutines.clearProgram 253 0 1)

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-width normalization for signed-component matrix words. This uses
only the existing padding, clear and transfer bit programs. In particular,
normalizing a component never invokes modular integer arithmetic. -/

namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ModularArithmetic SubexponentialSAT.StackRoutines
open SubexponentialSAT.ModularRingPrograms

variable {s : ℕ}

/-- Local normalization ports: input/output 0, consumed unary width 7;
port 5 is preserved data. Ports 1,2,3,4,6 are empty work stacks. -/
abbrev normalizeAt (ports : Fin 8 ↪ Fin s) : Cmd 8 s :=
  .call (ProgramLinking.liftProgram normalizeProgram id ports)

end SubexponentialSAT.SqrtLog.LayoutProgram

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

abbrev parse : Cmd 8 18 := workCall parsePair

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramEntriesEmit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual signed-pair framing, with every unrelated stack preserved. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram.Entries
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev emitOne (negative : Bool) : Cmd 3 6 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram id
    (emitPorts negative))

/-- Prepend a positive and negative frame with one outer pair tag. Inputs 0,1
are consumed; output 2 is extended; ports 3--5 are preserved. -/
abbrev emitPair : Cmd 3 6 :=
  .seq (emitOne true) (.seq (.base (.atom (.pop 2 0 1))) (emitOne false))

end SubexponentialSAT.SqrtLog.RowSelectionProgram.Entries

end OAI.Algorithms
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

def pairCall : Code := liftCommand RowSelectionProgram.Entries.emitPair 0 2 pairRegisters pairPorts

/-- P0,N1 survive. Buffer2 is extended. Scratch3--6 starts and ends empty. -/
def emitPair : Code :=
  .seq (copy 0 3 5) (.seq (copy 1 4 5) (.seq pairCall (transfer 6 2)))

/-- Append the final false tag, then reverse the complete accumulated list. -/
def finishList : Code :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.push 2 0))) (transfer 2 6))

end SubexponentialSAT.SqrtLog.LayoutScalarEmitter

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

def finish : Code := liftCommand LayoutScalarEmitter.finishList 2 6 workRegisters finishPorts

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgram.lean

/-! Complete cache-to-triple primitive program with all scans and copies paid. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProgramTapeReplayFootprint
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Compositional certificates for the tape footprint of compiled finite programs. -/
namespace SubexponentialSAT.SqrtLog.ProgramTapeReplay
open SubexponentialSAT BitProgram StructuredCalls
variable {r s l R S L : ℕ}

theorem avoids_clearProgram (H : Fin s → Prop) (src : Fin s) (value present : Fin r)
    (hs : ¬ H src) : AvoidsProgram H (StackRoutines.clearProgram src value present) := by
  intro q
  fin_cases q <;> simp [AvoidsInstr,hs]

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

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

theorem copyState_frame {S : ℕ} (src dst i : Fin S) (a : Data S) (hi : i ≠ dst) :
    (copyState src dst a).stacks i = a.stacks i := by
  simp [copyState, StackRoutines.copyStacks, hi]

def copyManyCost {S : ℕ} : List (Fin S × Fin S) → Data S → ℕ
  | [], _ => 0
  | (src, dst) :: ps, a => 7 * (a.stacks src).length + 5 +
      copyManyCost ps (copyState src dst a)

theorem copyMany_frame {S : ℕ} (ps : List (Fin S × Fin S)) (a : Data S) (i : Fin S)
    (hi : ∀ p ∈ ps, i ≠ p.2) : (copyManyState ps a).stacks i = a.stacks i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨src, dst⟩ := p
    exact (ih (copyState src dst a) (fun p hp => hi p (by simp [hp]))).trans
      (copyState_frame src dst i a (hi (src, dst) (by simp)))

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProgramTapeReplayMacros
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Footprints of the fixed storage and scan controllers used by the leaf. -/
namespace SubexponentialSAT.SqrtLog.ProgramTapeReplay
open SubexponentialSAT BitProgram StructuredCalls
variable {r s : ℕ}

theorem avoids_copyCmd (H : Fin s → Prop) (src dst tmp : Fin s)
    (hs : ¬ H src) (hd : ¬ H dst) (ht : ¬ H tmp) :
    AvoidsCmd H (SubexpSetupStorage.copyCmd src dst tmp) :=
  avoids_copyProgram H src dst tmp 0 1 hs hd ht

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ActivePlanProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Computing the active completion positions

A fixed program filters a runtime list of unary seed positions. It retains a
position precisely when it is at least the runtime threshold and belongs to
the runtime pair read plan. The plan and threshold are preserved. Applying the
program to the complete ascending seed list gives a duplicate-free completion
plan in ascending order.
-/

namespace SubexponentialSAT.Subexp.ActivePlanProgram

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 10 12

end SubexponentialSAT.Subexp.ActivePlanProgram

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

theorem set_present_eval {r s : ℕ} (p : RecordPrograms.Ports r s)
    (base : State r s) (v pr found pr' : Bool) (src out : List Bool) :
    Eval (RecordPrograms.atom (.set p.present pr')) 1
      (RecordPrograms.state p base v pr found src out)
      (RecordPrograms.state p base v pr' found src out) := by
  have he : (StructuredProgram.Atom.set p.present pr').eval
      (RecordPrograms.state p base v pr found src out) =
      RecordPrograms.state p base v pr' found src out := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      by_cases hv : i = p.tag <;> by_cases hp : i = p.present <;> by_cases hf : i = p.found <;>
        simp_all [StructuredProgram.Atom.instr, execInstr,
          RecordPrograms.state, p.found_ne_present,
          p.tag_ne_present, Ne.symm p.tag_ne_present, p.found_ne_tag,
          Ne.symm p.found_ne_tag, Ne.symm p.found_ne_present]
    · rfl
  rw [← he]
  exact .base (.atom _ _)

theorem unread_length_le (test : List Bool → Bool) (records : List (List Bool)) :
    (RecordPrograms.unread test records []).length ≤ (ProgramEncoding.encodeRecords records).length := by
  induction records with
  | nil => simp [RecordPrograms.unread]
  | cons bits records ih =>
      cases h : test bits <;>
        simp [RecordPrograms.unread, h, ProgramEncoding.encodeRecords,
          Encoding.encodeList] at * <;> omega

/-! A full-dimensional candidate needs only universal scalar tests. -/

open scoped BigOperators
open SubexponentialSAT.QuarticSearch

end SubexponentialSAT.Subexp.BlockSearchProgram

end OAI.Algorithms
end


