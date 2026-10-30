-- Prove2me | Definitions.Def_OAIQ081S076
-- name    : OAIQ081S076
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:59:10.465431+00:00
-- url     : https://prove2.me/theorems/e4006e7d-fd76-43f5-862c-123e291df1ba
-- title:
--   Definitions bundle OAIQ081S076 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 83 declarations of OpenAI's Lean: 48 definitions and 35 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Constants.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Constants.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FoldContract`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.fixedHighCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.hashPath`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.indicatorJet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.liftedHashes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.markedPath`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.queryExpansion`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.queryPolynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.selectedExpression`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.sourceHash`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.target`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.ternaryAccepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.ternaryFixedHighCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount.fullCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.TernaryLift.coefficient`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.rowValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.counterStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.incidenceJet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.incidenceZ`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments.variableZ`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.reindexPacking`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbedding.jet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbedding.poly`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbedding.supportMap`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.finishPowers`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.finishVector`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.initializeVector`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.literalLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.literalScan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.literalStep`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.load`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionStreamProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SubexpArgumentProgram.writer`, `OAI.Algorithms.SubexponentialSAT.SubexpArgumentProgram.writerStacks`, `OAI.Algorithms.SubexponentialSAT.SubexpBasePUnranking.command`, `OAI.Algorithms.SubexponentialSAT.SubexpBasePUnranking.extractionStep`, `OAI.Algorithms.SubexponentialSAT.SubexpBasePUnranking.loop` and 8 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LeafParameterArithmeticQuotient`, `SubexponentialSAT_SqrtLog_LeafParametersProgramLog`, `SubexponentialSAT_SqrtLog_LeafProgramConstants`, `SubexponentialSAT_SqrtLog_LeafProgramHash`, `SubexponentialSAT_SqrtLog_LeafProgramLift`, `SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsCount`, `SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsCountSource`, `SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsFactors`, `SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsGroups`, `SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsJets`, `SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsSource`, `SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsTarget`, `SubexponentialSAT_SqrtLog_LeafProgramPreparedBranchCount`, `SubexponentialSAT_SqrtLog_LeafProgramRecords`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramLowFrame`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_MomentsPerturbation`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputPackingTransport`, `SubexponentialSAT_SqrtLog_ResidualEmbedding`, `SubexponentialSAT_SqrtLog_ResidualEmbeddingMoments`, `SubexponentialSAT_SqrtLog_ResidualEmbeddingSource`, `SubexponentialSAT_SqrtLog_ResidualEmbeddingStored`, `SubexponentialSAT_SqrtLog_RingProgramTableBasic`, `SubexponentialSAT_SqrtLog_RingProgramTableFinish`, `SubexponentialSAT_SqrtLog_RingProgramTableInitial`, `SubexponentialSAT_SqrtLog_RingProgramTableSetup`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramBasic`, `SubexponentialSAT_SubexpArgumentProgram`, `SubexponentialSAT_SubexpBasePUnranking`, `SubexponentialSAT_SubexpEnumerationProgram`, `SubexponentialSAT_SubexpFieldRowPreparation`, `SubexponentialSAT_SubexpGuardProgram`, `SubexponentialSAT_SubexpTaylorFrames`, `SubexponentialSAT_Subexp_CollisionStreamProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S045`, `OAIQ081S046`, `OAIQ081S047`, `OAIQ081S048`, `OAIQ081S050`, `OAIQ081S051`, `OAIQ081S052`, `OAIQ081S058` and `OAIQ081S059` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S092`, `OAIQ081S093`, `OAIQ081S094`, `OAIQ081S095`, `OAIQ081S097`, `OAIQ081S098` and `OAIQ081S099`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.branch_target_degree` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.queryPolynomial_origin`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWord_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.MassPreserve.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.branch_target_degree` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.queryPolynomial_origin`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S045
import Definitions.Def_OAIQ081S046
import Definitions.Def_OAIQ081S047
import Definitions.Def_OAIQ081S048
import Definitions.Def_OAIQ081S050
import Definitions.Def_OAIQ081S051
import Definitions.Def_OAIQ081S052
import Definitions.Def_OAIQ081S058
import Definitions.Def_OAIQ081S059

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParameterArithmeticQuotient
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A source-preserving floor quotient call using the audited finite binary
long-division program. Operands are runtime padded Boolean words. -/
namespace SubexponentialSAT.SqrtLog.LeafParameterArithmetic

open BitProgram StructuredCalls
open BinaryArithmetic (toNat)

theorem quotient_embed_start {S : ℕ} (p : QuotientPorts S) (d : Data S)
    (hd : QuotientReady p d) :
    embedState id (quotientStackMap p) d
      ⟨(ArithmeticCalls.afterCopy p.left (p.work 5) d).regs,
        ModularQuotientPrograms.quotientStacks [] (d.stacks p.right) (d.stacks p.left) []⟩ =
      ArithmeticCalls.afterCopy p.left (p.work 5) d := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id
    (quotientStackMap_injective p)
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> simp [ArithmeticCalls.afterCopy, quotientStackMap,
      ModularQuotientPrograms.quotientStacks, p.work.injective.eq_iff, hd.1, hd.2]
  · intro i hi
    have hn : i ≠ p.work 5 := fun h => hi ⟨6, h.symm⟩
    simp [ArithmeticCalls.afterCopy, hn]

theorem quotient_embed_finish {S : ℕ} (p : QuotientPorts S) (d : Data S)
    (hd : QuotientReady p d) (rf : Fin 8 → Bool) (rem word : List Bool) :
    embedState id (quotientStackMap p) d
      ⟨rf, ModularQuotientPrograms.quotientStacks rem (d.stacks p.right) [] word⟩ =
      (⟨rf, Function.update (Function.update d.stacks p.out word) (p.work 0) rem⟩ : Data S) := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id
    (quotientStackMap_injective p)
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> simp [quotientStackMap, ModularQuotientPrograms.quotientStacks,
      p.work.injective.eq_iff, p.work_ne_out, hd.2]
  · intro i hi
    have h0 : i ≠ p.work 0 := fun h => hi ⟨0, h.symm⟩
    have ho : i ≠ p.out := fun h => hi ⟨7, h.symm⟩
    simp [h0, ho]

end SubexponentialSAT.SqrtLog.LeafParameterArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramLog
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The extension-degree operation is a fixed instruction table, working on
arbitrary padded binary input. The zero case is guarded separately. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

theorem resetLog_eval (d : LogData) :
    Eval resetLog 3 d ⟨fun _ => false, d.stacks⟩ := by
  have h := SubexpParameterProgram.atoms_eval
    ([.set 0 false, .set 1 false, .set 2 false] : List (StructuredProgram.Atom 3 3)) d
  have he : SubexpParameterProgram.runAtoms
      [.set 0 false, .set 1 false, .set 2 false] d = ⟨fun _ => false, d.stacks⟩ := by
    apply congrArg₂ StructuredProgram.State.mk
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · rfl
  exact .base (he ▸ h)

end SubexponentialSAT.SqrtLog.LeafParametersProgram

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

theorem clear_eval (d : Data) (dst : Fin 27) :
    Eval (clear dst) (2 * (d.stacks dst).length + 3) d (afterClear d dst) :=
  .call _ (ListRegisterProgram.clear_run dst 1 3 d.regs d.stacks)

theorem transfer_eval (d : Data) (src dst : Fin 27) (hne : src ≠ dst) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d (afterTransfer d src dst) :=
  .call _ (ListRegisterProgram.transfer_run src dst 1 3 hne (by decide) d.regs d.stacks)

abbrev load (src dst : Fin 27) : Cmd 8 27 := .call
  (ProgramLinking.liftProgram RingScan.loadWordProgram loadRegisters (loadPorts src dst))

theorem clear_store_eval (s t : Store) (regs : Fin 8 → Bool) (dst : Fin 27)
    (heq : clearStacks dst (tapes s) = tapes t) :
    Eval (clear dst) (2 * (tapes s dst).length + 3) (state regs s)
      (state (readRegs regs 1 3 none) t) := by
  have h := clear_eval (state regs s) dst
  simpa only [afterClear, state, heq] using h

theorem transfer_store_eval (s t : Store) (regs : Fin 8 → Bool) (src dst : Fin 27)
    (hne : src ≠ dst) (heq : transferStacks src dst (tapes s) = tapes t) :
    Eval (transfer src dst) (3 * (tapes s src).length + 3) (state regs s)
      (state (readRegs regs 1 3 none) t) := by
  have h := transfer_eval (state regs s) src dst hne
  simpa only [afterTransfer, state, heq] using h

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

/-- Restore forward coefficient order, cache the final coefficient, and append
the vector to the reversed power-table accumulator. -/
abbrev finishVector : Cmd 8 27 :=
  .seq (clear 0) (.seq (transfer 20 15) (.seq (clear 18)
    (.seq (copy 19 18) (.seq (clear 19) (.seq (copy 15 9) (transfer 9 25))))))

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableInitial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

abbrev literalStep : Cmd 8 27 :=
  .seq (clear 19) (.seq (copy 0 19) (.seq (transfer 0 20) (copy 24 0)))

abbrev literalLoop : Cmd 8 27 := .while 3 (.seq literalStep popCount)
abbrev literalScan : Cmd 8 27 := .seq popCount literalLoop

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramConstants
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical dynamic-dimension constants. The same fixed loop emits a scalar
seed in coordinate zero followed by scalar zero in every other coordinate. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Constants

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing RingProgramTable

abbrev command : Cmd 8 27 :=
  .seq (copy 22 11) (.seq literalScan
    (.seq (transfer 20 15) (.seq (clear 0) (clear 19))))

def program := compiled command 0 15

end SubexponentialSAT.SqrtLog.LeafProgram.Constants

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

def rowValue (alg : Algebra A) (decode : C → A) (value : V → A) : SparseRow V C → A
  | [] => alg.zero
  | (c, ls) :: rest =>
      alg.add (alg.mul (decode c) (clauseValue alg value ls))
        (rowValue alg decode value rest)

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramLift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer representative lifting of the ternary selector coefficients.
Only reduction is a ring homomorphism. The lift itself is a finite choice of
0, 1, or 2, and no ring homomorphism from `ZMod 3` into the thickened ring is
assumed. All statements use the supplied irreducible polynomial. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram

namespace TernaryLift

variable {d : ℕ} (a : RingModel.Data d) (t : ℕ)

/-- The actual coefficient value used by the hash circuit. -/
noncomputable def coefficient (c : ZMod 3) : a.O t := (c.val : a.O t)

@[simp] theorem reduction_coefficient (ht : 0 < t) (c : ZMod 3) :
    a.rho t ht (coefficient a t c) = LiftRing.of a.residuePolynomial c := by
  rw [coefficient, map_natCast]
  conv_rhs => rw [← ZMod.natCast_zmod_val c]
  rw [map_natCast]

end TernaryLift
end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ResidualEmbedding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Injective padding of residual squarefree variables into their original
ambient coordinate universe. This is a semantic map, not runtime renumbering. -/
namespace SubexponentialSAT.SqrtLog.ResidualEmbedding

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators
noncomputable section

variable {V W R : Type*} [DecidableEq V] [DecidableEq W] [CommSemiring R]

def supportMap (e : V ↪ W) : Support V →* Support W where
  toFun s := ⟨s.vars.map e⟩
  map_one' := by apply Support.ext; simp
  map_mul' a b := by apply Support.ext; exact Finset.map_union _ _

def poly (e : V ↪ W) : Poly V R →+* Poly W R :=
  MonoidAlgebra.mapDomainRingHom R (supportMap e)

@[simp] theorem poly_monomial (e : V ↪ W) (s : Finset V) (c : R) :
    poly e (monomial s c) = monomial (s.map e) c :=
  MonoidAlgebra.mapDomain_single

def jet (e : V ↪ W) : Jet V R →+* Jet W R :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (poly e))

@[simp] theorem jet_coeff (e : V ↪ W) (f : Jet V R) (u z : ℕ) :
    ((jet e f).coeff u).coeff z = poly e ((f.coeff u).coeff z) := by
  simp [jet]

@[simp] theorem jet_canonical (e : V ↪ W) (t J : ℕ) (f : Jet V R) :
    jet e (canonical t J f) = canonical t J (jet e f) := by
  apply Polynomial.ext
  intro u
  apply Polynomial.ext
  intro z
  by_cases h : u < t ∧ z < J <;> simp [h]

end
end SubexponentialSAT.SqrtLog.ResidualEmbedding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ResidualEmbeddingStored
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Padding a sparse dictionary preserves its exact coefficients, key
uniqueness, validity, and list length. The ambient bit representation need
not compact or renumber the residual variables. -/
namespace SubexponentialSAT.SqrtLog.ResidualEmbedding

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
variable {V W R : Type*} [DecidableEq V] [DecidableEq W] [CommSemiring R]

@[simp] theorem index_join (e : V ↪ W) (a b : Index V) :
    index e (a.join b) = (index e a).join (index e b) := by
  simp [index, Index.join, Finset.map_union]

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem index_kept (e : V ↪ W) (a : Index V) (t J : ℕ) :
    (index e a).Kept t J ↔ a.Kept t J := Iff.rfl

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem index_valid (e : V ↪ W) (a : Index V) :
    (index e a).Valid ↔ a.Valid := by simp [Index.Valid, index]

noncomputable section

@[simp] theorem jet_atom (e : V ↪ W) (a : Index V) (c : R) :
    jet e (Sparse.atom a c) = Sparse.atom (index e a) c := by
  simp [jet, Sparse.atom, index]

end
end SubexponentialSAT.SqrtLog.ResidualEmbedding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsTarget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

/-- A row is evaluated as the supplied sparse clause circuit. -/
abbrev hashPath (hashes : List (SparseRow V R))
    (path : ℕ → V → R[X]) (i : Fin hashes.length) : R[X] :=
  rowValue (ringAlgebra R[X]) Polynomial.C (path i.val) hashes[i]

def markedPath (hashes : List (SparseRow V R)) (marked : Bool)
    (clause : List (SAT.Literal V)) (path : ℕ → V → R[X]) : R[X] :=
  if marked then clauseValue (ringAlgebra R[X]) (path hashes.length) clause else 1

def queryPolynomial (t : ℕ) (digits : Fin t → R[X])
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (path : ℕ → V → R[X]) : R[X] :=
  TotalOrder.output Finset.univ t
    (fun i => digitAt digits (hashPath hashes path i))
    (fun i => IdempotentProgram.hValue (hashPath hashes path i)) *
      markedPath hashes marked clause path

def target (H : Finset V) (t : ℕ) (digits : Fin t → R[X])
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (path : (ResidualEmbedding.Free H → Bool) → ℕ → V → R[X]) : R[X] :=
  ∑ x, queryPolynomial t digits hashes marked clause (path x)

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

def sourceHash (hashes : List (SparseRow V R)) (x : V → Bool)
    (i : Fin hashes.length) : R :=
  rowValue (ringAlgebra R) id (fun v => HashInput.boolValue (x v)) hashes[i]

def accepted (rho : R →+* K) (hashes : List (SparseRow V R))
    (marked : Bool) (clause : List (SAT.Literal V)) (x : V → Bool) : Prop :=
  (∀ i, rho (sourceHash hashes x i) = 0) ∧ (marked = true → violates clause x = true)

def fixedHighCount (rho : R →+* K) (H : Finset V) (high : H → Bool)
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V)) : ℕ :=
  ∑ x : ResidualEmbedding.Free H → Bool,
    if accepted rho hashes marked clause (HighIncidence.glue H high x) then 1 else 0

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CollisionStreamProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed collision callback with a persistent output stream

The runtime ABI reserves stack 0 for a packed row table, stack 3 for its unary
word width, stacks 8 and 10 for the two read plans, and stack 11 for the output
stream. Stacks 1 and 12 hold the two gathered type encodings. The remaining
stacks are gathering scratch. All sizes, plans, and encoded words are data.

The equality stage below uses the existing fixed equality program, clears its
possibly unconsumed input suffixes, and pushes one collision bit. In particular,
an early mismatch cannot leave stale type bytes in the next callback's scratch.
-/

namespace SubexponentialSAT.Subexp.CollisionStreamProgram

open BitProgram StackRoutines StructuredCalls

abbrev Data := StructuredProgram.State 5 13

end SubexponentialSAT.Subexp.CollisionStreamProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ResidualEmbeddingMoments
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ambient support enumeration may include supports meeting fixed high
coordinates. Their coefficients are zero, so the output equals the residual
moment computation without any additional Boolean assignments. -/
namespace SubexponentialSAT.SqrtLog.ResidualEmbedding

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators
noncomputable section

variable {V W R : Type*} [DecidableEq V] [DecidableEq W] [CommSemiring R]

@[simp] theorem poly_scalar (e : V ↪ W) (c : R) :
    poly e (Squarefree.scalar c) = Squarefree.scalar c := by
  change poly e (monomial ∅ c) = monomial ∅ c
  simp

@[simp] theorem jet_ringScalar (e : V ↪ W) (c : R) :
    jet e (Moments.ringScalar c) = Moments.ringScalar c := by
  simp [jet, Moments.ringScalar]

end
end SubexponentialSAT.SqrtLog.ResidualEmbedding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsJets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual dense readout and attained-bucket sum supply jets of the one
specified source target. The local bucket identity is kept explicit, so a
native parser or assignment service is never assumed to be correct. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
noncomputable section

variable {R : Type*} [CommRing R]

/-- U-polynomial before the one shared cutoff. Marking has U-degree zero. -/
def queryExpansion {V : Type*} (t : ℕ) (digits : Fin t → R[X])
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (path : ℕ → V → R[X]) : Polynomial R[X] :=
  TotalOrder.fullProduct Finset.univ t
    (fun i => digitAt digits (hashPath hashes path i))
    (fun i => IdempotentProgram.hValue (hashPath hashes path i)) *
      Polynomial.C (markedPath hashes marked clause path)

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsPerturbation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual row perturbations, rather than an assumed support invariant.
Every formal Boolean coordinate is multiplied by a polynomial with zero
constant term in Z. The construction is valid over any commutative ring. -/

namespace SubexponentialSAT.SqrtLog.Moments

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators

variable {V R : Type*} [DecidableEq V] [CommRing R]

noncomputable def variableZ (v : V) (p : Polynomial R) : ZJet V R :=
  p.map Squarefree.scalar * Polynomial.C (Squarefree.monomial {v} 1)

noncomputable def incidenceZ [Fintype V] (row : V → Polynomial R) (theta beta : R) :
    ZJet V R :=
  Polynomial.C (Squarefree.scalar beta) + ∑ v, variableZ v (rowDelta (row v) theta)

noncomputable def incidenceJet [Fintype V] (row : V → Polynomial R) (theta beta : R) :
    Jet V R := Polynomial.C (incidenceZ row theta beta)

end SubexponentialSAT.SqrtLog.Moments

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

/-- Local callbacks are required to operate on encoded records only. The
machine must consume the parsed reversed payload and preserve the unread tail.
The accumulator's semantic decoder is used only in the specification. -/
abbrev FoldContract (ports : Ports r s) (callback : Cmd r s)
    (read : State r s → A) (step : List Bool → A → A)
    (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (validPayload : List Bool → Prop) : Prop :=
  CallbackContractWithOn ports callback (fun _ => false) cost invariant
    (foldEffect read step) validPayload

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

def writerStacks (outer : Bool) : Fin 4 → Fin 6 :=
  SubexpPostfixControl.quadruple 0 2 (destination outer) 1

theorem writerStacks_injective (outer : Bool) : Function.Injective (writerStacks outer) := by
  cases outer <;> intro i j h <;> fin_cases i <;> fin_cases j <;>
    simp_all [writerStacks, destination, SubexpPostfixControl.quadruple]

/-- The existing postfix literal encoder, relocated to the key/body buffers. -/
abbrev writer (outer : Bool) : Program 5 6 17 :=
  ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram writerRegs (writerStacks outer)

end SubexponentialSAT.SubexpArgumentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ResidualEmbeddingSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Original literal identifiers may differ from the residual formal-variable
type. High-variable literals are branch constants, and the sparse row circuit
commutes with padding the remaining formal supports into ambient masks. -/
namespace SubexponentialSAT.SqrtLog.ResidualEmbedding

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree LeafProgram
noncomputable section

variable {I V W R : Type*} [DecidableEq V] [DecidableEq W] [CommRing R]

@[simp] theorem jet_scalarJet (e : V ↪ W) (c : R) :
    jet e (scalarJet c) = scalarJet c := by
  rw [scalarJet, jet_atom]
  rfl

end
end SubexponentialSAT.SqrtLog.ResidualEmbedding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsFactors
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial naturality for the actual H-adic indicator expression. U
remains formal throughout; only its final retained coefficient sum is read. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
noncomputable section

variable {R : Type*} [CommRing R] {V : Type*} [DecidableEq V]

/-- Same finite expression as the code-derived assignment indicator. -/
def indicatorJet (t : ℕ) (digits : Fin t → R[X])
    (H : Squarefree.Jet V R) : Squarefree.Jet V R :=
  ∑ s : Fin t, Polynomial.X^s.val *
    (digits s).eval₂ Moments.ringScalar H * IdempotentProgram.hValue H^s.val

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsGroups
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact assembly of all colored factor lists, including optional marking
and neutral IDs. Neither list order nor neutral padding changes the target. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
noncomputable section

variable {A : Type*} [CommMonoid A]

variable {R : Type*} [CommRing R] {n : ℕ}

def selectedExpression (u : ℕ) (digits : Fin u → R[X])
    (hashes : List (SparseRow (Fin n) R)) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) (path : ℕ → Fin n → R[X]) (id : ℕ) :
    Polynomial R[X] :=
  if h : id < hashes.length then
    TotalOrder.row u (digitAt digits (hashPath hashes path ⟨id,h⟩))
      (IdempotentProgram.hValue (hashPath hashes path ⟨id,h⟩))
  else if marked && decide (id=hashes.length) then
    Polynomial.C (clauseValue (ringAlgebra R[X]) (path id) clause)
  else 1

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

/-- Lift a sparse input row coefficient by coefficient, not by a nonexistent
ring homomorphism from the residue field into the thickened ring. -/
def liftedHashes {d : ℕ} (a : RingModel.Data d) (t : ℕ)
    (hashes : List (SparseRow V (ZMod 3))) : List (SparseRow V (a.O t)) :=
  hashes.map (fun ws => ws.map (fun w => (TernaryLift.coefficient a t w.1,w.2)))

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsCountSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The recovered constant counts the original ternary row constraints.
The extension-ring residue test introduces no additional acceptance rule. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

def ternaryAccepted (hashes : List (SparseRow V (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal V)) (x : V → Bool) : Prop :=
  (∀ ws∈hashes,rowValue (ringAlgebra (ZMod 3)) id
    (fun v => HashInput.boolValue (x v)) ws=0) ∧
  (marked=true → violates clause x=true)

def ternaryFixedHighCount (H : Finset V) (high : H → Bool)
    (hashes : List (SparseRow V (ZMod 3))) (marked : Bool) (clause : List (SAT.Literal V)) : ℕ :=
  ∑ x : ResidualEmbedding.Free H → Bool,
    if ternaryAccepted hashes marked clause (HighIncidence.glue H high x) then 1 else 0

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramPreparedBranchCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact original-coordinate interpretation of the physical high tuple.
The order is descending original ID, and every rank including the unique
empty tuple participates in the count. No coordinate compaction is used. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount
open HighIncidenceProgram
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def fullCount (hashes : List (SparseRow (Fin n) (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) : ℕ :=
  ∑ x : Fin n → Bool, if NodeSemantics.ternaryAccepted hashes marked clause x then 1 else 0

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedBranchCount

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpGuardProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete binary guard control for the subexponential schedule

The comparator below has a fixed instruction table, reads arbitrary-width
little-endian binary words, and uses only Boolean operations and stack pops.
Schedule arithmetic is not an instruction of this program.
-/

namespace SubexponentialSAT.SubexpGuardProgram

open BitProgram BinaryArithmetic

open StructuredProgram

/-- A measured comparison call on fixed injective ports, with every other
caller register and stack preserved. -/
theorem compare_call {R S : ℕ} (register : Fin 8 → Fin R) (stack : Fin 2 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack) (a : State R S) :
    ∃ b : State R S,
      StructuredCalls.Eval (.call (ProgramLinking.liftProgram Compare.program register stack))
        (10 * max (a.stacks (stack 0)).length (a.stacks (stack 1)).length + 6) a b ∧
      (b.regs (register 0) = true ↔ BinaryArithmetic.toNat (a.stacks (stack 0)) < BinaryArithmetic.toNat (a.stacks (stack 1))) ∧
      (∀ i, (¬ ∃ j, register j = i) → b.regs i = a.regs i) ∧
      (∀ i, (¬ ∃ j, stack j = i) → b.stacks i = a.stacks i) ∧
      (∀ j, b.stacks (stack j) = []) := by
  obtain ⟨rf, hrun, hcmp⟩ := Compare.run (fun i => a.regs (register i))
    (a.stacks (stack 0)) (a.stacks (stack 1))
  have hstack := pair_eta (fun i => a.stacks (stack i))
  have hempty : Compare.operandStacks [] [] = (fun _ : Fin 2 => []) := by
    simpa using pair_eta (fun _ : Fin 2 => [])
  simp only [Compare.cfg, hstack, hempty] at hrun
  let localOut : State 8 2 := ⟨rf, fun _ => []⟩
  let b := StructuredCalls.embedState register stack a localOut
  refine ⟨b, ?_, ?_, ?_, ?_, ?_⟩
  · have h := StructuredCalls.eval_call_lifted Compare.program register stack a hr hs
      (a := restrictState register stack a) (b := localOut) hrun
    rw [embed_restrict register stack hr hs a] at h
    exact h
  · simpa only [b, StructuredCalls.embedState_register register stack a localOut hr,
      localOut] using hcmp
  · exact fun i hi => StructuredCalls.embedState_register_frame register stack a localOut i hi
  · exact fun i hi => StructuredCalls.embedState_stack_frame register stack a localOut i hi
  · exact fun j => StructuredCalls.embedState_stack register stack a localOut hs j


end SubexponentialSAT.SubexpGuardProgram

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

abbrev writeRecord : Cmd 5 9 :=
  .call (ProgramLinking.liftProgram (SubexpArgumentProgram.writer true) id writerStacks)

abbrev one : Cmd 5 9 :=
  .seq (.call (StackRoutines.copyProgram 1 2 7 (0 : Fin 5) 1))
    (.seq paddedRead (.seq writeRecord
      (.call (StackRoutines.transferProgram 5 6 (0 : Fin 5) 1))))

abbrev loop : Cmd 5 9 := .while 1 (.seq popCount (.seq one guard))
abbrev command : Cmd 5 9 := .seq guard (.seq loop finish)
abbrev program : Program 5 9 (size command + 1) := compiled command 0 8

theorem guard_eval (regs : Fin 5 → Bool) (w : Words) :
    Eval guard 1 (state regs w) (state (readRegs regs 0 1 w.todo.head?) w) := by
  exact .base (.atom _ _)

theorem popCount_eval (regs : Fin 5 → Bool) (w : Words) (bit : Bool) (rest : List Bool)
    (hc : w.todo = bit :: rest) :
    Eval popCount 1 (state regs w)
      (state (readRegs regs 0 1 (some bit)) {w with todo := rest}) := by
  have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (3 : Fin 9) (0 : Fin 5) 1)
    (state regs w)
  apply Eval.base
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply state_ext
  · simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, state, store, hc]
  · funext i; fin_cases i <;> simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, state, store, hc]

theorem finish_eval (regs : Fin 5 → Bool) (w : Words) (ho : w.output = []) :
    Eval finish (3 * w.packed.length + 8) (state regs w)
      (state (readRegs (Function.update regs 0 false) 0 1 none)
        {w with packed := [], output := w.packed.reverse ++ [false]}) := by
  let rr := Function.update regs 0 false
  let w1 := {w with packed := false :: w.packed}
  have h1 : Eval (.base (.atom (.set 0 false))) 1 (state regs w) (state rr w) := by
    exact .base (.atom _ _)
  have h2 : Eval (.base (.atom (.push 6 0))) 1 (state rr w) (state rr w1) := by
    have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.push (6 : Fin 9) (0 : Fin 5))
      (state rr w)
    apply Eval.base
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr,
        state, store, w1, rr]
  have h3 := transfer_eval (state rr w1) 6 8 0 1 (by decide) (by decide)
  have e3 : afterTransfer (state rr w1) 6 8 0 1 =
      state (readRegs rr 0 1 none) {w with packed := [], output := w.packed.reverse ++ [false]} := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterTransfer, StackRoutines.transferStacks,
        state, store, w1, ho, List.reverse_cons]
  rw [e3] at h3
  convert h1.seq (h2.seq h3) using 1
  all_goals try with_reducible_and_instances rfl
  simp [ rr, w1, state, store]
  omega

end SubexponentialSAT.SubexpTaylorFrames

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEnumerationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Encoded interval enumeration by fixed finite control

A current label and a remaining count live on little-endian Boolean stacks.
The program invokes an actual body command once per label and advances using
verified finite-table increment/decrement routines.  Mathematical state
embeddings below occur only in execution proofs; no instruction evaluates an
arbitrary semantic function.
-/

namespace SubexponentialSAT.SubexpEnumerationProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram
open SubexponentialSAT.CounterPrograms

variable {R S : ℕ}

theorem install_self (p : Ports R S) (q : Bool) (d : Data R S) :
    install p q d (d.regs (p.register 0)) (d.regs (p.register 1))
      (d.regs (p.register 2)) (d.stacks (target p q)) (d.stacks p.scratch) = d := by
  apply data_ext
  · change Function.extend p.register
      (counterRegs (d.regs (p.register 0)) (d.regs (p.register 1))
        (d.regs (p.register 2))) d.regs = d.regs
    have h : counterRegs (d.regs (p.register 0)) (d.regs (p.register 1))
        (d.regs (p.register 2)) = d.regs ∘ p.register := by
      first | done | (funext i; fin_cases i <;> rfl)
    rw [h, extend_restrict]
  · change Function.extend (stackPorts p q)
      (counterStacks (d.stacks (target p q)) (d.stacks p.scratch)) d.stacks = d.stacks
    have h : counterStacks (d.stacks (target p q)) (d.stacks p.scratch) =
        d.stacks ∘ stackPorts p q := by
      first | done | (funext i; fin_cases i <;> rfl)
    rw [h, extend_restrict]

end SubexponentialSAT.SubexpEnumerationProgram

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

theorem nextRank_value (modulus rank : List Bool) (hm : 0 < BinaryArithmetic.toNat modulus) :
    BinaryArithmetic.toNat (nextRank modulus rank) = BinaryArithmetic.toNat rank / BinaryArithmetic.toNat modulus :=
  divide_quotient_correct modulus rank hm

abbrev extractionStep : Cmd 8 13 :=
  .seq (.call (ModularQuotientLift.programAt divisionPorts)) collectDigit

abbrev loop : Cmd 8 13 := .while 3 (.seq extractionStep popArity)

abbrev command : Cmd 8 13 :=
  .seq popArity (.seq loop (.call (transferProgram 11 12 1 3)))

abbrev program : Program 8 13 (size command + 1) := compiled command 6 12

end SubexponentialSAT.SubexpBasePUnranking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFieldRowPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

open BitProgram StructuredCalls StackRoutines

abbrev unrank : Cmd 8 15 :=
  .call (ProgramLinking.liftProgram SubexpBasePUnranking.program id stackPort)

abbrev command : Cmd 8 15 :=
  .seq (.call (copyProgram 13 6 10 1 3))
    (.seq (.call (copyProgram 14 8 10 1 3))
      (.seq unrank (.call (clearProgram 6 1 3))))

end SubexponentialSAT.SubexpFieldRowPreparation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev initializeVector : Cmd 8 27 := .seq (copy 22 11) (.seq literalScan finishVector)

/-- Put the accumulated power vectors back in forward order on port25. -/
abbrev finishPowers : Cmd 8 27 := .seq (transfer 25 9) (.seq (copy 9 25) (clear 9))

theorem finishPowers_eval (s : Store) (regs : Fin 8 → Bool) (hempty : s.source = []) :
    Eval finishPowers (12*s.powers.length+11) (state regs s)
      (state (readRegs regs 1 3 none) {s with powers := s.powers.reverse}) := by
  let s1 := {s with source := s.powers.reverse, powers := []}
  let s2 := {s1 with powers := s.powers.reverse}
  let s3 := {s2 with source := []}
  let rr := readRegs regs 1 3 none
  have h1 := transfer_store_eval s s1 regs 25 9 (by decide) (by
    funext i; fin_cases i <;> simp [transferStacks, tapes, s1, hempty])
  have h2 := copy_store_eval s1 s2 rr 9 25 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s2, s1])
  have h3 := clear_store_eval s2 s3 rr 9 (by
    funext i; fin_cases i <;> simp [clearStacks, tapes, s3])
  simp only [rr, readRegs_reset] at h2 h3
  convert h1.seq (h2.seq h3) using 1
  · simp [s1, s2, tapes]; omega
  · simp [s1, s2, s3, hempty]

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

theorem clear_eval (d : Data) (dst : Fin 18) :
    Eval (clear dst) (2 * (d.stacks dst).length + 3) d (afterClear d dst) :=
  .call _ (ListRegisterProgram.clear_run dst 0 1 d.regs d.stacks)

theorem transfer_eval (d : Data) (src dst : Fin 18) (hne : src ≠ dst) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d (afterTransfer d src dst) :=
  .call _ (ListRegisterProgram.transfer_run src dst 0 1 hne (by decide) d.regs d.stacks)

end SubexponentialSAT.SqrtLog.RingTableLayout

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
open BitProgram StructuredCalls

def counterStacks : List (Fin 640 × Fin 640) → (Fin 640 → List Bool) → (Fin 640 → List Bool)
  | [],s => s
  | p::ps,s => counterStacks ps (counterStack s p)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramLowFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The ring producer can clear low arithmetic workspace, but never inserts
data there.  Thus initially blank low node-work tapes stay blank.  This is a
property of the existing program, not an additional cleanup operation. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.LowFrame
open BitProgram StructuredCalls

theorem trace_empty {r s l : ℕ} (p : Program r s l) (i : Fin s)
    (hp : ∀ q c, c.stacks i=[] → (execInstr (p.code q) c).stacks i=[])
    {n : ℕ} {a b : Cfg r s l} (h : Trace p n a b) (hz : a.stacks i=[]) :
    b.stacks i=[] := by
  induction h with
  | refl => exact hz
  | @cons k a z b hs ht ih =>
    apply ih
    cases hpc : a.pc with
    | none => simp [step,hpc] at hs
    | some q =>
      have he : execInstr (p.code q) a=z := by simpa [step,hpc] using hs
      exact he ▸ hp q a hz

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.LowFrame

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputPackingTransport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Changing only the displayed incidence-list length transports the same
packing; numeric positions, labels, metadata bytes, and matrix values agree. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes

variable {D E : ℕ} {U : Type*}

def reindexPacking (h : D = E) (P : PackingData (Fin D) U) : PackingData (Fin E) U := h ▸ P

@[simp] theorem reindexPacking_rfl (P : PackingData (Fin D) U) : reindexPacking rfl P = P := rfl

@[simp] theorem reindexPacking_label (h : D = E) (P : PackingData (Fin D) U) (i : Fin E) :
    (reindexPacking h P).label i = P.label (Fin.cast h.symm i) := by
  cases h
  rfl

@[simp] theorem reindexPacking_label_cast (h : D = E) (P : PackingData (Fin D) U) (i : Fin D) :
    (reindexPacking h P).label (Fin.cast h i) = P.label i := by
  cases h
  rfl

@[simp] theorem reindexPacking_types (h : D = E) (P : PackingData (Fin D) U) :
    (reindexPacking h P).types = P.types := by
  cases h
  rfl

@[simp] theorem reindexPacking_blockCount [DecidableEq U] (h : D = E)
    (P : PackingData (Fin D) U) : (reindexPacking h P).blockCount = P.blockCount := by
  cases h
  rfl

@[simp] theorem reindexPacking_metadataValue [DecidableEq U] (h : D = E)
    (P : PackingData (Fin D) U) (encodeType : U → List Bool) (i : Fin E) :
    PackingMetadata.value (reindexPacking h P) encodeType i =
      PackingMetadata.value P encodeType (Fin.cast h.symm i) := by
  cases h
  rfl

end SubexponentialSAT.SqrtLog.PackingIncidenceInput

end OAI.Algorithms
end


