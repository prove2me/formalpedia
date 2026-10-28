-- Prove2me | Definitions.Def_OAIQ086U007
-- name    : OAIQ086U007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T16:21:55.842097+00:00
-- url     : https://prove2.me/theorems/d455abb2-9102-4011-9d89-b7053e3fbd28
-- title:
--   Definitions bundle OAIQ086U007 of the split of OpenAI, The Unique Games Theorem
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniqueGamesTheorem.theorem11`, carved from OpenAI's openai/math development (OpenAI, *The Unique Games Theorem*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 828 declarations of OpenAI's Lean: 343 definitions, 11 inductive types or structures, 2 instances and 472 theorems. The definitions and types are `OAI.UniqueGamesTheorem.Explicit.ProductTarget.render_simpleBipartite`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFCleanup.cleanupExecution`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFCleanup.completedMachine`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFCleanup.completedProgram`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFCleanup.embeddedCfg`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFCleanup.outputsInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.LoopInvariant`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.LoopRun`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.RawRun`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.emitInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.emittedBytes`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.emittedTapes`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.endpointTapes`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.endpointsInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.finalTimePolynomial`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.finishInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.finishTapes`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.guardEndInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.guardRowInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headPhaseInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.initializedTableHeaderInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.literalPlan`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.loopInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.machine`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.patternPlan`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.phaseTimePolynomial`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.preparedTapes`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.program`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rawBudget`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rawRun`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.relationInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowPlan`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowRest`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResultTapes`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowTime` and 314 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `UniqueGames_Games_ProductTarget`, `UniqueGames_Machines_FinalCNFLoopLemmas`, `UniqueGames_Machines_FinalCNFMachineLemmas`, `UniqueGames_Machines_FinalCNFOutputLemmas`, `UniqueGames_Machines_FinalCNFRowPlanLemmas`, `UniqueGames_Machines_FinalCNFStream`, `UniqueGames_Machines_FinalCNFTemplate`, `UniqueGames_Machines_MachineCanonicalOutputLemmas`, `UniqueGames_Machines_MachineCeilingPower`, `UniqueGames_Machines_MachineCloudCount`, `UniqueGames_Machines_MachineCloudPadding`, `UniqueGames_Machines_MachineCloudPrefix`, `UniqueGames_Machines_MachineCloudRankLemmas`, `UniqueGames_Machines_MachineDrainManyLemmas`, `UniqueGames_Machines_MachineExpanderFamily`, `UniqueGames_Machines_MachineExpanderFamilyBoundsLemmas`, `UniqueGames_Machines_MachineExpanderFamilyLoop`, `UniqueGames_Machines_MachineExpanderFamilyTapes`, `UniqueGames_Machines_MachineExpanderFamilyTransferLemmas`, `UniqueGames_Machines_MachineExpanderRow`, `UniqueGames_Machines_MachineExpanderRowCleanup`, `UniqueGames_Machines_MachineExpanderRowDivision`, `UniqueGames_Machines_MachineExpanderRowEmitLemmas`, `UniqueGames_Machines_MachineExpanderRowFrames`, `UniqueGames_Machines_MachineExpanderTable`, `UniqueGames_Machines_MachineExpanderTableLoop`, `UniqueGames_Machines_MachineExpanderTableProgramLemmas`, `UniqueGames_Machines_MachineExpanderTableReverse`, `UniqueGames_Machines_MachineExpanderTableRows`, `UniqueGames_Machines_MachineLazyCodec`, `UniqueGames_Machines_MachineLazyRows`, `UniqueGames_Machines_MachineLazyTable`, `UniqueGames_Machines_MachineLazyTableRuntime`, `UniqueGames_Machines_MachineLookupDiscard`, `UniqueGames_Machines_MachineLookupLemmas`, `UniqueGames_Machines_MachineOverlayRows`, `UniqueGames_Machines_MachineOverlayTable`, `UniqueGames_Machines_MachinePaddedExpanderFamilyBoundsLemmas`, `UniqueGames_Machines_MachinePaddedOverlay`, `UniqueGames_Machines_MachinePortReindex`, `UniqueGames_Machines_MachineProductGatherBoundsLemmas`, `UniqueGames_Machines_MachineRegularFamily`, `UniqueGames_Machines_MachineRegularTable`, `UniqueGames_Machines_MachineTableSplit`, `UniqueGames_Machines_MachineVertexPadding`, `UniqueGames_PCP_AlphabetTableBoundsLemmas`, `UniqueGames_PCP_CleanupLemmas`, `UniqueGames_PCP_Emitter`, `UniqueGames_PCP_FinalBooleanVerifier`, `UniqueGames_PCP_InitialGraphLemmas`, `UniqueGames_PCP_RawInitialMachineReadClause`, `UniqueGames_PCP_RawInitialTablesLemmas`, `UniqueGames_PCP_SourceContextLoad`, `UniqueGames_PCP_SourceDescriptorEmissionLemmas`, `UniqueGames_PCP_SourceHeaderAccumulate`, `UniqueGames_PCP_SourceOccurrences`, `UniqueGames_PCP_SourceQueryOrderLemmas`, `UniqueGames_PCP_SourceSignaturePrepareLemmas`, `UniqueGames_PCP_SourceTupleBody`, `UniqueGames_PCP_TableIteration`, `UniqueGames_Reduction_RealTargetLemmas`.
--
--   **Imports.** It imports the published bundle `Def_UniqueGamesTheorem`; the bundles `OAIQ086U003` and `OAIQ086U004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ086U010` and `OAIQ086U011`.
-- source:
--   OpenAI, The Unique Games Theorem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Unique-Games-Theorem-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_UniqueGamesTheorem
import Definitions.Def_OAIQ086U003
import Definitions.Def_OAIQ086U004

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_RealTargetLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The value of the actual finite Unique Games instance is its maximum satisfied
constraint fraction. Maximization ranges over every finite vertex labeling;
the denominator counts stored constraint occurrences, including repetitions.
The natural-number maximum totalizes an empty labeling type at zero. The
attainment and threshold equivalences require a positive alphabet.
-/

namespace UniqueGamesTheorem.Integration.InstanceValue

open UniqueGamesTheorem.Foundations
open Target

theorem value_attained {q : Nat} (g : Instance q) (hq : 0 < q) :
    ∃ labeling : Fin g.vertices → Fin q,
      (countSatisfied labeling g.constraints : ℝ) / g.constraints.length = value g := by
  obtain ⟨labeling, hlabeling⟩ := maxSatisfied_attained g hq
  exact ⟨labeling, by rw [hlabeling]; rfl⟩

/-- Existential real completeness is precisely a lower bound on instance value. -/
theorem exists_rate_ge_iff {q : Nat} (g : Instance q) (hq : 0 < q) (a : ℝ) :
    (∃ labeling : Fin g.vertices → Fin q,
      a ≤ (countSatisfied labeling g.constraints : ℝ) / g.constraints.length) ↔
      a ≤ value g := by
  constructor
  · rintro ⟨labeling, hlabeling⟩
    exact hlabeling.trans (labeling_rate_le_value g labeling)
  · intro hvalue
    obtain ⟨labeling, hlabeling⟩ := value_attained g hq
    exact ⟨labeling, hlabeling.symm ▸ hvalue⟩

/-- Universal real soundness is precisely an upper bound on instance value. -/
theorem forall_rate_le_iff {q : Nat} (g : Instance q) (hq : 0 < q) (b : ℝ) :
    (∀ labeling : Fin g.vertices → Fin q,
      (countSatisfied labeling g.constraints : ℝ) / g.constraints.length ≤ b) ↔
      value g ≤ b := by
  constructor
  · intro hall
    obtain ⟨labeling, hlabeling⟩ := value_attained g hq
    exact hlabeling ▸ hall labeling
  · intro hvalue labeling
    exact (labeling_rate_le_value g labeling).trans hvalue

end UniqueGamesTheorem.Integration.InstanceValue

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Games_ProductTarget
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Explicit numbered permutation-table outputs for bipartite graphs and products.
All numbering maps are supplied as actual equivalences; the product uses the
computable radix equivalence with division/remainder inverse, never an arbitrary
finite-type enumeration. The value bridge preserves every list occurrence.
-/

namespace UniqueGamesTheorem.Explicit.ProductTarget

open UniqueGamesTheorem.Foundations
open Target
open MachineOutputContract
open scoped BigOperators

variable {L R E : Type*} {q N M : ℕ}

theorem render_get (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (i : Fin (render G vertices edges tables hM).constraints.length) :
    (render G vertices edges tables hM).constraints[i] =
      row G vertices edges tables ⟨i.val, by simpa using i.isLt⟩ := by
  change (List.ofFn (row G vertices edges tables))[i.val]'(by simpa using i.isLt) = _
  exact List.getElem_ofFn (by simpa using i.isLt)

def render_simpleBipartite (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M) :
    SimpleBipartite (render G vertices edges tables hM) where
  side v := Sum.elim (fun _ => false) (fun _ => true) (vertices.symm v)
  sourceSide i := by simp only [render_get, row, Equiv.symm_apply_apply, Sum.elim_inl]
  targetSide i := by simp only [render_get, row, Equiv.symm_apply_apply, Sum.elim_inr]
  endpoints_injective := by
    intro i j hij
    have hi : i.val < M := by simpa using i.isLt
    have hj : j.val < M := by simpa using j.isLt
    have hrows :
        ((row G vertices edges tables ⟨i.val, hi⟩).source,
          (row G vertices edges tables ⟨i.val, hi⟩).target) =
        ((row G vertices edges tables ⟨j.val, hj⟩).source,
          (row G vertices edges tables ⟨j.val, hj⟩).target) := by
      simpa only [render_get] using! hij
    have hedge : edges ⟨i.val, hi⟩ = edges ⟨j.val, hj⟩ := by
      apply G.simple
      apply Prod.ext
      · exact Sum.inl.inj (vertices.injective (congrArg Prod.fst hrows))
      · exact Sum.inr.inj (vertices.injective (congrArg Prod.snd hrows))
    exact Fin.ext (congrArg (fun k : Fin M => k.val) (edges.injective hedge))

section Value

variable [Fintype E]

/-- A full vertex labeling pulls back to two independently local labelings. -/
theorem render_count (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (htable : ∀ e, permutationEquiv (tables e) = G.permutation e)
    (labeling : Fin N → Fin q) :
    countSatisfied labeling (render G vertices edges tables hM).constraints =
      G.satisfiedCount (fun x => labeling (vertices (Sum.inl x)))
        (fun y => labeling (vertices (Sum.inr y))) := by
  classical
  have ht (e : E) (a : Fin q) : (tables e).images[a] = G.permutation e a :=
    congrArg (fun p : Equiv.Perm (Fin q) => p a) (htable e)
  change countSatisfied labeling (List.ofFn (row G vertices edges tables)) = _
  rw [Integration.GapSemantics.countSatisfied_ofFn]
  unfold BipartiteGame.satisfiedCount
  apply Fintype.sum_equiv edges
  intro i
  simp [row, Constraint.satisfied, ht]

theorem render_count_merge (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (htable : ∀ e, permutationEquiv (tables e) = G.permutation e)
    (left : L → Fin q) (right : R → Fin q) :
    countSatisfied (mergeLabelings vertices left right)
      (render G vertices edges tables hM).constraints = G.satisfiedCount left right := by
  simpa only [mergeLabelings_left, mergeLabelings_right] using
    render_count G vertices edges tables hM htable (mergeLabelings vertices left right)

variable [Fintype L] [Fintype R]

theorem render_maxSatisfied (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (htable : ∀ e, permutationEquiv (tables e) = G.permutation e) :
    Integration.InstanceValue.maxSatisfied (render G vertices edges tables hM) =
      G.maxSatisfied := by
  classical
  apply Nat.le_antisymm
  · unfold Integration.InstanceValue.maxSatisfied
    apply Finset.sup_le
    intro labeling _
    erw [render_count G vertices edges tables hM htable]
    exact G.satisfiedCount_le_maxSatisfied _ _
  · unfold BipartiteGame.maxSatisfied
    apply Finset.sup_le
    intro labeling _
    rw [← render_count_merge G vertices edges tables hM htable]
    exact Integration.InstanceValue.countSatisfied_le_maxSatisfied
      (render G vertices edges tables hM) (mergeLabelings vertices labeling.1 labeling.2)

theorem render_value (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (htable : ∀ e, permutationEquiv (tables e) = G.permutation e) :
    Integration.InstanceValue.value (render G vertices edges tables hM) = G.value := by
  unfold Integration.InstanceValue.value BipartiteGame.value
  rw [render_maxSatisfied G vertices edges tables hM htable, render_length]
  have hcard : M = Fintype.card E := by simpa using Fintype.card_congr edges
  rw [hcard]

end Value

end UniqueGamesTheorem.Explicit.ProductTarget

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineDrainManyLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual cleanup of a finite list of work tapes

Each list position supplies one fixed drain label. The finite-sequence theorem
composes the checked physical drains; neither the list nor a runtime tape index
is stored in the register. Repeated tape names are allowed. The cleanup bound
uses the lengths before cleanup, since draining can only shorten a tape.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineDrainMany

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

/-- With a clean register, complete work-tape cleanup reaches the standard
halted shape, preserving the output word and the ambient state exactly. -/
theorem cleanupTrace {N : Nat} (enumeration : Fin N ≃ K) (output : K)
    (labels : Label (workTapes enumeration output) → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) =
      instruction (workTapes enumeration output) labels none l)
    (base : Tapes K) (ambient : σ) :
    (advance (TM2.step program))^[steps (workTapes enumeration output) base]
      (some ⟨entry (workTapes enumeration output) labels none, (ambient, none), base⟩) =
    some ⟨none, (ambient, none), haltTapes output (base output)⟩ := by
  simpa only [finalRegister_none, finalTapes_workTapes] using
    trace (workTapes enumeration output) labels none program atLabels base ambient none

end UniqueGamesTheorem.Foundations.Complexity.MachineDrainMany

/-!
Preserved comparisons of actual field stacks and their finite equality profile.
All whole-word equalities below are specifications of finite-head comparison.
-/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineLookupDiscard
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Execution of the destructive field-discard loop in an arbitrary ambient TM2
program. The scanner consumes a unary payload and its delimiter, preserves the
ambient state and other tapes, and clears its head register on return. At EOF it
returns immediately, leaving the tapes unchanged.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

/-- The same exact trace packaged for composition with ambient machine phases. -/
def discardInTime (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (hinput : base source = encodeWord n ++ suffix)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, register), base⟩
      (some ⟨some returnLabel, (ambient, none), Function.update base source suffix⟩)
      (n + 1) where
  steps := n + 1
  evals_in_steps := discardTrace source loopLabel returnLabel program atLoop
    base n suffix hinput ambient register
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Foundations.Complexity.MachineLookup

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineLookupLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual traces for the fixed unary lookup machine. Successful lookup preserves
an arbitrary unread table suffix. Rejection relative to a list's end is stated
only for its complete, unframed encoding, so no hidden endpoint is assumed.
-/

/-! Actual lookup from a preserved table. A fresh copy is prefixed to the scan
stack before each access. The old scan suffix is retained and need not be
cleared between accesses. No graph/table data occurs in finite control. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePreservingLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def program (tape : Fin 5 → K) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (σ × Option Bool)
  | .copyFirst => Reduction.MachineTransfer.loopAt (tape 0) (tape 4) id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop (tape 4) (tape 0) (tape 2) false .copySecond (some (.lookup .guard))
  | .lookup l => MachineSubroutine.statement Label.lookup none
      (MachineLookup.program (tape 1) (tape 2) (tape 3) l)

end UniqueGamesTheorem.Foundations.Complexity.MachinePreservingLookup

namespace UniqueGamesTheorem.Foundations.Complexity.MachineAffineLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem steps_le_table (values : List Nat) (a coefficient offset value : Nat)
    (selected : values[coefficient * a + offset]? = some value)
    (ha : a ≤ (encodeWords values).length) :
    steps values a coefficient offset ≤ 7 * (encodeWords values).length + 6 := by
  have h := steps_le values a coefficient offset value selected
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineAffineLookup

/-!
A fixed-width gather from an input-resident table. Every coordinate index lives
on a unary tape. The coefficient and coordinate-dependent offsets alone live
in finite control. Actual preserving affine lookup instructions read each
requested field, and the proof below composes their traces. This is the gather
phase of product-row construction, before the fixed-width Horner phase.
-/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_CleanupLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-stack cleanup. Each selected stack is drained using the
checked pop loop, followed by one transition resetting the finite state.
Repeated selections are allowed; they only reduce the cost upper bound. -/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Lookup

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K]

/-- Six fixed control labels implement row selection. `q` fixes the finite
predicate parser; no data-dependent number is placed in the program syntax. -/
def statement (q : Nat) (counter source destination : K) (labels : Label → Λ)
    (exit : Option Λ) : Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .guard => MachineUnaryCounter.guard counter (labels .skipTail) (labels .select)
  | .skipTail => MachineLookup.discard source (labels .skipTail) (labels .skipReverse)
  | .skipReverse => MachineLookup.discard source (labels .skipReverse) (labels .skipPredicate)
  | .skipPredicate => skipBits source (q * q) (.goto fun _ => labels .guard)
  | .select => Hastad.SourceMachine.fieldStart destination (labels .copy)
  | .copy => Hastad.SourceMachine.fieldLoop source destination (labels .copy) exit

section Ambient

variable {q n m : Nat} (counter source destination : K) (labels : Label → Λ)
  (exit : Option Λ)
  (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
  (atStatement : ∀ label, P (labels label) = statement q counter source destination labels exit label)

include atStatement

/-- One skipped row: two actual unary scans followed by one finite predicate
statement. All registers are reset and every other tape is untouched. -/
theorem skipRowTrace (base : K → List Bool) (row : DartRow q n m) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[row.tail.val + row.reverseIndex.val + 3]
      (some ⟨some (labels .skipTail), (ambient, register),
        Function.update base source (rowBits row ++ suffix)⟩) =
      some ⟨some (labels .guard), (ambient, none), Function.update base source suffix⟩ := by
  have ht := MachineLookup.discardTrace_update source (labels .skipTail) (labels .skipReverse)
    P (atStatement .skipTail) base row.tail.val
    (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
    ambient register
  have hr := MachineLookup.discardTrace_update source (labels .skipReverse) (labels .skipPredicate)
    P (atStatement .skipReverse) base row.reverseIndex.val
    (encodeWords (relationWords row.relation) ++ suffix) ambient none
  have hp : TM2.step P
      ⟨some (labels .skipPredicate), (ambient, none), Function.update base source
        (encodeWords (relationWords row.relation) ++ suffix)⟩ =
      some ⟨some (labels .guard), (ambient, none), Function.update base source suffix⟩ := by
    change some (TM2.stepAux (P (labels .skipPredicate)) _ _) = _
    rw [atStatement .skipPredicate]
    have h := congrArg some (stepAux_skipBits source row.relation.toList
      (.goto fun _ => labels .guard) base suffix ambient none)
    simpa only [statement, Vector.length_toList, relationWords, TM2.stepAux] using h
  rw [rowBits_eq]
  simp only [List.append_assoc]
  rw [show row.tail.val + row.reverseIndex.val + 3 =
    1 + ((row.reverseIndex.val + 1) + (row.tail.val + 1)) by omega,
    Function.iterate_add_apply, Function.iterate_add_apply, ht, hr,
    Function.iterate_one, advance_some, hp]

theorem skipRowTrace_fromTapes (base : K → List Bool) (row : DartRow q n m)
    (suffix : List Bool) (hinput : base source = rowBits row ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[row.tail.val + row.reverseIndex.val + 3]
      (some ⟨some (labels .skipTail), (ambient, register), base⟩) =
      some ⟨some (labels .guard), (ambient, none), Function.update base source suffix⟩ := by
  have h := skipRowTrace counter source destination labels exit P atStatement
    base row suffix ambient register
  have hb : Function.update base source (rowBits row ++ suffix) = base := by
    rw [← hinput]
    exact Function.update_eq_self source base
  rw [hb] at h
  exact h

theorem selectTrace (hsd : source ≠ destination) (base : K → List Bool)
    (row : DartRow q n m) (suffix : List Bool)
    (hinput : base source = rowBits row ++ suffix) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[row.tail.val + 2]
      (some ⟨some (labels .select), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), Hastad.SourceMachine.fieldTapes source destination base
        (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
        (encodeWord row.tail.val ++ base destination)⟩ := by
  let ht := Hastad.SourceMachine.fieldInTime source destination hsd
    (labels .select) (labels .copy) exit P (atStatement .select) (atStatement .copy)
    base row.tail.val
    (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
    (by simpa only [rowBits_eq, List.append_assoc] using hinput) ambient register
  have hsteps : ht.steps = row.tail.val + 2 := rfl
  have htrace := ht.evals_in_steps
  rw [hsteps] at htrace
  exact htrace

/-- Exact successful row lookup. The only data premise is the literal table
prefix; no lookup result or whole execution is postulated. -/
theorem lookupTailTrace
    (hcs : counter ≠ source) (hcd : counter ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (prior : List (DartRow q n m)) (row : DartRow q n m)
    (counterSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[lookupCost prior row]
      (some ⟨some (labels .guard), (ambient, register),
        MachineLookup.tapes counter source destination base
          (encodeWord prior.length ++ counterSuffix)
          (rowsBits prior ++ (rowBits row ++ suffix)) output⟩) =
      some ⟨exit, (ambient, none),
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix)
          (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
          (encodeWord row.tail.val ++ output)⟩ := by
  induction prior generalizing register with
  | nil =>
    simp only [lookupCost, prefixCost, List.map_nil, List.sum_nil, Nat.zero_add,
      List.length_nil, rowsBits_nil, List.nil_append]
    rw [show row.tail.val + 3 = (row.tail.val + 2) + 1 by omega,
      Function.iterate_succ_apply]
    have hg := MachineUnaryCounter.guardStep_zero counter (labels .guard)
      (labels .skipTail) (labels .select) P (atStatement .guard)
      (MachineLookup.tapes counter source destination base
        (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output)
      counterSuffix ambient register
    have hcounter : MachineUnaryCounter.counterTapes counter
        (MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output) 0 counterSuffix =
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output := by
      simp only [MachineUnaryCounter.counterTapes, MachineLookup.update_index _ _ _ hcs hcd]
    rw [hcounter] at hg
    simp only [advance_some]
    rw [hg]
    have hs := selectTrace counter source destination labels exit P atStatement hsd
      (MachineLookup.tapes counter source destination base
        (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output)
      row suffix (by simp [hsd]) ambient none
    simpa only [MachineLookup.tapes_destination,
      MachineLookup.fieldTapes_eq _ _ _ hsd] using hs
  | cons first prior ih =>
    simp only [lookupCost, prefixCost, List.map_cons, List.sum_cons, List.length_cons,
      rowsBits_cons, List.append_assoc]
    rw [show skipCost first + (prior.map skipCost).sum + row.tail.val + 3 =
      ((prior.map skipCost).sum + row.tail.val + 3) +
        (first.tail.val + first.reverseIndex.val + 3) + 1 by simp only [skipCost]; omega,
      Function.iterate_succ_apply]
    have hg := MachineUnaryCounter.guardStep_succ counter (labels .guard)
      (labels .skipTail) (labels .select) P (atStatement .guard)
      (MachineLookup.tapes counter source destination base
        (encodeWord prior.length ++ counterSuffix)
        (rowBits first ++ (rowsBits prior ++ (rowBits row ++ suffix))) output)
      prior.length counterSuffix ambient register
    simp only [MachineUnaryCounter.counterTapes,
      MachineLookup.update_index _ _ _ hcs hcd] at hg
    simp only [advance_some]
    rw [hg, Function.iterate_add_apply]
    have hs := skipRowTrace_fromTapes counter source destination labels exit P atStatement
      (MachineLookup.tapes counter source destination base
        (encodeWord prior.length ++ counterSuffix)
        (rowBits first ++ (rowsBits prior ++ (rowBits row ++ suffix))) output)
      first (rowsBits prior ++ (rowBits row ++ suffix)) (by simp [hsd]) ambient none
    rw [hs]
    simp only [MachineLookup.update_source _ _ _ hsd]
    exact ih none

end Ambient

/-- The input's actual stored row vector determines the selected row. This
specialization derives the literal lookup prefix from the checked codec. -/
theorem tableTailTrace {q : Nat}
    (counter source destination : K) (labels : Label → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStatement : ∀ label, P (labels label) = statement q counter source destination labels exit label)
    (hcs : counter ≠ source) (hcd : counter ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (table : Table q) (e : Fin table.darts)
    (counterSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[lookupCost ((rowList table).take e.val) table.rows[e]]
      (some ⟨some (labels .guard), (ambient, register),
        MachineLookup.tapes counter source destination base
          (encodeWord e.val ++ counterSuffix) (rowsBits (rowList table) ++ suffix) output⟩) =
      some ⟨exit, (ambient, none),
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix)
          (encodeWord table.rows[e].reverseIndex.val ++
            (encodeWords (relationWords table.rows[e].relation) ++
              (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix)))
          (encodeWord table.rows[e].tail.val ++ output)⟩ := by
  have h := lookupTailTrace counter source destination labels exit P atStatement
    hcs hcd hsd base ((rowList table).take e.val) table.rows[e] counterSuffix
    (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix) output ambient register
  have hlength : ((rowList table).take e.val).length = e.val := by
    simp only [List.length_take, rowList_length, Nat.min_eq_left (Nat.le_of_lt e.isLt)]
  have hsplit : rowsBits (rowList table) ++ suffix =
      rowsBits ((rowList table).take e.val) ++
        (rowBits table.rows[e] ++ (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix)) := by
    have hrow : table.rows[e.val] = table.rows[e] := rfl
    simpa only [rowsBits, rowBits, rowList, Vector.getElem_toList, hrow] using
      Input.rowsBits_append_split (rowList table) e.val (by simp) suffix
  rw [hlength, ← hsplit] at h
  exact h

/-- Two real delimiter-scanning loops remove the header of the copied table
before the row counter starts. The protected original table can occupy any
other tape in `base` and is unchanged. -/
theorem fullTableTailTrace {q : Nat}
    (counter source destination : K) (labels : Label → Λ) (exit : Option Λ)
    (headerVertices headerDarts : Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStatement : ∀ label, P (labels label) = statement q counter source destination labels exit label)
    (atVertices : P headerVertices = MachineLookup.discard source headerVertices headerDarts)
    (atDarts : P headerDarts = MachineLookup.discard source headerDarts (labels .guard))
    (hcs : counter ≠ source) (hcd : counter ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (table : Table q) (e : Fin table.darts)
    (counterSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[lookupCost ((rowList table).take e.val) table.rows[e] +
        (table.darts + 1) + (table.vertices + 1)]
      (some ⟨some headerVertices, (ambient, register),
        MachineLookup.tapes counter source destination base
          (encodeWord e.val ++ counterSuffix) (tableBits table ++ suffix) output⟩) =
      some ⟨exit, (ambient, none),
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix)
          (encodeWord table.rows[e].reverseIndex.val ++
            (encodeWords (relationWords table.rows[e].relation) ++
              (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix)))
          (encodeWord table.rows[e].tail.val ++ output)⟩ := by
  have hv := MachineLookup.discardTrace source headerVertices headerDarts P atVertices
    (MachineLookup.tapes counter source destination base
      (encodeWord e.val ++ counterSuffix) (tableBits table ++ suffix) output)
    table.vertices (encodeWord table.darts ++ (rowsBits (rowList table) ++ suffix))
    (by simp only [MachineLookup.tapes_source _ _ _ hsd, Input.tableBits_header,
      rowsBits, List.append_assoc]) ambient register
  rw [Function.iterate_add_apply, hv]
  simp only [MachineLookup.update_source _ _ _ hsd]
  have hd := MachineLookup.discardTrace source headerDarts (labels .guard) P atDarts
    (MachineLookup.tapes counter source destination base
      (encodeWord e.val ++ counterSuffix)
      (encodeWord table.darts ++ (rowsBits (rowList table) ++ suffix)) output)
    table.darts (rowsBits (rowList table) ++ suffix) (by simp [hsd]) ambient none
  rw [Function.iterate_add_apply, hd]
  simp only [MachineLookup.update_source _ _ _ hsd]
  exact tableTailTrace counter source destination labels exit P atStatement hcs hcd hsd
    base table e counterSuffix suffix output ambient none

def headLookupInTime {q : Nat}
    (tape : HeadTapes K) (hinj : Function.Injective tape)
    (tableFirst tableSecond indexFirst indexSecond headerVertices headerDarts : Λ)
    (labels : Label → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atTableFirst : P tableFirst = Reduction.MachineTransfer.loopAt
      (tape 0) (tape 5) id false tableFirst (some tableSecond))
    (atTableSecond : P tableSecond = MachineCopy.forkLoop
      (tape 5) (tape 0) (tape 2) false tableSecond (some indexFirst))
    (atIndexFirst : P indexFirst = Reduction.MachineTransfer.loopAt
      (tape 1) (tape 5) id false indexFirst (some indexSecond))
    (atIndexSecond : P indexSecond = MachineCopy.forkLoop
      (tape 5) (tape 1) (tape 3) false indexSecond (some headerVertices))
    (atVertices : P headerVertices = MachineLookup.discard (tape 2) headerVertices headerDarts)
    (atDarts : P headerDarts = MachineLookup.discard (tape 2) headerDarts (labels .guard))
    (atStatement : ∀ label,
      P (labels label) = statement q (tape 3) (tape 2) (tape 4) labels exit label)
    (base : K → List Bool) (table : Table q) (e : Fin table.darts)
    (hTable : base (tape 0) = tableBits table)
    (hReverse : base (tape 1) = encodeWord (headIndex table e).val)
    (hHead : base (tape 4) = []) (hScratch : base (tape 5) = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some tableFirst, (ambient, register), base⟩
      (some ⟨exit, (ambient, none), headLookupTapes tape base table e⟩)
      (headTimePolynomial.eval (tableBits table).length) := by
  have hne (i j : Fin 6) (h : i ≠ j) : tape i ≠ tape j := fun heq => h (hinj heq)
  let t₁ := Function.update base (tape 2) (tableBits table ++ base (tape 2))
  let t₂ := Function.update t₁ (tape 3) (encodeWord (headIndex table e).val ++ base (tape 3))
  have run₁ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some tableFirst, (ambient, register), base⟩
      (some ⟨some indexFirst, (ambient, none), t₁⟩)
      (2 * ((tableBits table).length + 1)) := by
    simpa only [hTable, t₁] using MachineCopy.copyInTime (tape 0) (tape 2) (tape 5)
      (hne 0 2 (by decide)) (hne 0 5 (by decide)) (hne 2 5 (by decide)) false
      tableFirst tableSecond (some indexFirst) P atTableFirst atTableSecond
      base hScratch ambient register
  have hsrc : t₁ (tape 1) = encodeWord (headIndex table e).val := by
    simp only [t₁, Function.update_of_ne (hne 1 2 (by decide)), hReverse]
  have hdst : t₁ (tape 3) = base (tape 3) := by
    simp only [t₁, Function.update_of_ne (hne 3 2 (by decide))]
  have hscratch₁ : t₁ (tape 5) = [] := by
    simp only [t₁, Function.update_of_ne (hne 5 2 (by decide)), hScratch]
  have run₂ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some indexFirst, (ambient, none), t₁⟩
      (some ⟨some headerVertices, (ambient, none), t₂⟩)
      (2 * ((encodeWord (headIndex table e).val).length + 1)) := by
    simpa only [hsrc, hdst, t₂] using MachineCopy.copyInTime (tape 1) (tape 3) (tape 5)
      (hne 1 3 (by decide)) (hne 1 5 (by decide)) (hne 3 5 (by decide)) false
      indexFirst indexSecond (some headerVertices) P atIndexFirst atIndexSecond
      t₁ hscratch₁ ambient none
  have ht₂ : t₂ = MachineLookup.tapes (tape 3) (tape 2) (tape 4) base
      (encodeWord (headIndex table e).val ++ base (tape 3))
      (tableBits table ++ base (tape 2)) [] := by
    funext k
    by_cases hi : k = tape 3
    · subst k
      simp [t₂, MachineLookup.tapes, hne 3 2 (by decide), hne 3 4 (by decide)]
    · by_cases hs : k = tape 2
      · subst k
        simp [t₂, t₁, MachineLookup.tapes, hne 2 3 (by decide), hne 2 4 (by decide)]
      · by_cases hh : k = tape 4
        · subst k
          simp [t₂, t₁, MachineLookup.tapes, hne 4 3 (by decide),
            hne 4 2 (by decide), hHead]
        · simp [t₂, t₁, MachineLookup.tapes, hi, hs, hh]
  let run₃ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some headerVertices, (ambient, none), t₂⟩
      (some ⟨exit, (ambient, none), headLookupTapes tape base table e⟩)
      (tableTailCost table (headIndex table e)) := {
    steps := tableTailCost table (headIndex table e)
    evals_in_steps := by
      change (advance (TM2.step P))^[tableTailCost table (headIndex table e)]
        (some ⟨some headerVertices, (ambient, none), t₂⟩) =
          some ⟨exit, (ambient, none), headLookupTapes tape base table e⟩
      rw [ht₂]
      simpa only [headLookupTapes, headValue, tableTailCost, List.append_nil] using
        fullTableTailTrace (tape 3) (tape 2) (tape 4) labels exit
          headerVertices headerDarts P atStatement atVertices atDarts
          (hne 3 2 (by decide)) (hne 3 4 (by decide)) (hne 2 4 (by decide))
          base table (headIndex table e) (base (tape 3)) (base (tape 2)) [] ambient none
    steps_le_m := Nat.le_refl _ }
  let run₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁₂ run₃
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have ht := run.steps_le_m
  have hb := headLookupCost_le table e
  simp only [headTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  unfold headLookupCost at hb
  omega

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Lookup

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_Emitter
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual finite TM2 templates for affine unary fields and finite relation bits.
Commands write in forward bit order onto a stack, so their concatenated result
appears reversed in the accumulator. Every unbounded operand is read from an
isolated unary tape and restored by the checked preserving transducer.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Emitter

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} {h bound : Nat} [DecidableEq K]

/-- A literal Boolean is emitted by a real finite branch. A bounded offset is
dispatched to a finite label, whose push chain has a fixed length. -/
def commandStatement (sources : Fin h → K) (scratch output : K)
    (labels : Phase bound → Λ) (next : Λ) (command : Command h σ bound) :
    Phase bound → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .entry => match command with
    | .literal word => pushWord output word
        (.load (fun state => (state.1, none)) (.goto fun _ => next))
    | .bit value => .branch (fun state => value state.1.1)
        (pushWord output [true, false]
          (.load (fun state => (state.1, none)) (.goto fun _ => next)))
        (pushWord output [false]
          (.load (fun state => (state.1, none)) (.goto fun _ => next)))
    | .bounded value => .goto fun state => labels (.offset (value state.1.1))
    | .scaled source _ => MachineTransducerCopy.scanLoop (sources source) scratch ()
        (fun _ symbol => labels (.emit symbol)) (labels .restore)
    | .scaledIf _ _ active => .goto fun state => labels (.scanIf (active state.1.1))
  | .emit symbol => match command with
    | .scaled _ coefficient => MachineTransducerCopy.emitter output transition
        (payload coefficient) (labels .entry) () symbol
    | _ => .goto fun _ => next
  | .restore => match command with
    | .scaled source _ | .scaledIf source _ _ => Reduction.MachineTransfer.loopAt scratch (sources source)
        id false (labels .restore) (some next)
    | _ => .goto fun _ => next
  | .offset value => pushWord output (List.replicate value.val true)
      (.load (fun state => (state.1, none)) (.goto fun _ => next))
  | .scanIf active => match command with
    | .scaledIf source _ _ => MachineTransducerCopy.scanLoop (sources source) scratch ()
        (fun _ symbol => labels (.emitIf active symbol)) (labels .restore)
    | _ => .goto fun _ => next
  | .emitIf active symbol => match command with
    | .scaledIf _ coefficient _ => MachineTransducerCopy.emitter output transition
        (payload (if active then coefficient else 0)) (labels (.scanIf active)) () symbol
    | _ => .goto fun _ => next

/-- Exact execution of one command of the supplied actual program. The only
program hypotheses are equations for its concrete finite statements. -/
theorem commandTrace (sources : Fin h → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Phase bound → Λ) (next : Λ) (command : Command h σ bound)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ phase,
      program (labels phase) = commandStatement sources scratch output labels next command phase)
    (values : Fin h → Nat) (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (values i))
    (scratchEmpty : base scratch = []) (ambient : σ) :
    (MachineComposition.advance (TM2.step program))^[commandSteps values command]
      (some ⟨some (labels .entry), ((ambient, ()), none), base⟩) =
      some ⟨some next, ((ambient, ()), none),
        Function.update base output ((commandBits values ambient command).reverse ++ base output)⟩ := by
  cases command with
  | literal word =>
    change some (TM2.stepAux (program (labels .entry)) ((ambient, ()), none) base) = _
    rw [atLabels]
    simp only [commandStatement, stepAux_pushWord, TM2.stepAux, commandBits]
  | bit value =>
    change some (TM2.stepAux (program (labels .entry)) ((ambient, ()), none) base) = _
    rw [atLabels]
    cases hb : value ambient <;>
      simp [commandStatement, TM2.stepAux, pushWord, commandBits, hb, encodeWord]
  | bounded value =>
    change (TM2.step program ⟨some (labels .entry), ((ambient, ()), none), base⟩).bind
      (TM2.step program) = _
    have first : TM2.step program ⟨some (labels .entry), ((ambient, ()), none), base⟩ =
        some ⟨some (labels (.offset (value ambient))), ((ambient, ()), none), base⟩ := by
      change some (TM2.stepAux (program (labels .entry)) _ _) = _
      rw [atLabels]
      rfl
    rw [first]
    change some (TM2.stepAux (program (labels (.offset (value ambient)))) _ _) = _
    rw [atLabels]
    simp only [commandStatement, stepAux_pushWord, TM2.stepAux, commandBits]
  | scaled source coefficient =>
    have emitAt : ∀ control symbol, program (labels (.emit symbol)) =
        MachineTransducerCopy.emitter output transition (payload coefficient)
          (labels .entry) control symbol := by
      intro control symbol
      cases control
      exact atLabels (.emit symbol)
    have run := MachineTransducerCopy.transduceCopyTrace (sources source) scratch output
      (sourceScratch source) (sourceOutput source) scratchOutput () transition (payload coefficient)
      (labels .entry) (labels .restore) (fun _ symbol => labels (.emit symbol)) (some next)
      program (atLabels .entry) emitAt (atLabels .restore) base scratchEmpty ambient () none
    rw [operands source, encodeWord_length, output_encodeWord] at run
    exact run
  | scaledIf source coefficient active =>
    have first : TM2.step program ⟨some (labels .entry), ((ambient, ()), none), base⟩ =
        some ⟨some (labels (.scanIf (active ambient))), ((ambient, ()), none), base⟩ := by
      change some (TM2.stepAux (program (labels .entry)) _ _) = _
      rw [atLabels]
      rfl
    have emitAt : ∀ control symbol, program (labels (.emitIf (active ambient) symbol)) =
        MachineTransducerCopy.emitter output transition
          (payload (if active ambient then coefficient else 0))
          (labels (.scanIf (active ambient))) control symbol := by
      intro control symbol
      cases control
      exact atLabels (.emitIf (active ambient) symbol)
    have run := MachineTransducerCopy.transduceCopyTrace (sources source) scratch output
      (sourceScratch source) (sourceOutput source) scratchOutput () transition
      (payload (if active ambient then coefficient else 0))
      (labels (.scanIf (active ambient))) (labels .restore)
      (fun _ symbol => labels (.emitIf (active ambient) symbol)) (some next)
      program (atLabels (.scanIf (active ambient))) emitAt (atLabels .restore)
      base scratchEmpty ambient () none
    rw [operands source, encodeWord_length, output_encodeWord] at run
    change (MachineComposition.advance (TM2.step program))^[
      (3 * (values source + 1) + 2) + 1] _ = _
    rw [Function.iterate_succ_apply]
    simp only [MachineComposition.advance_some]
    rw [first]
    exact run

def statement {count : Nat} (commands : Fin count → Command h σ bound)
    (sources : Fin h → K) (scratch output : K)
    (labels : Label count bound → Λ) (exit : Option Λ) (label : Label count bound) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  if label.1.val < count then
    commandStatement sources scratch output (fun phase => labels (labelAt count bound label.1.val phase))
      (labels (labelAt count bound (label.1.val + 1) .entry))
      (commandAt commands label.1.val) label.2
  else Reduction.MachineTransfer.exitAt output exit

/-- Composition of the actual finite command traces, with preserved operand
stacks available again at every command boundary. -/
theorem prefixTrace {count : Nat} (commands : Fin count → Command h σ bound)
    (sources : Fin h → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Label count bound → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement commands sources scratch output labels exit label)
    (values : Fin h → Nat) (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (values i))
    (scratchEmpty : base scratch = []) (ambient : σ) (r : Nat) (hr : r ≤ count) :
    (MachineComposition.advance (TM2.step p))^[prefixSteps commands values r]
      (some ⟨some (labels (labelAt count bound 0 .entry)), ((ambient, ()), none), base⟩) =
      some ⟨some (labels (labelAt count bound r .entry)), ((ambient, ()), none),
        resultTapes output base (prefixBits commands values ambient r)⟩ := by
  induction r with
  | zero => simp [prefixSteps, prefixBits, resultTapes]
  | succ r ih =>
    have hrc : r < count := by omega
    let prior := resultTapes output base (prefixBits commands values ambient r)
    have priorOperands : ∀ i, prior (sources i) = encodeWord (values i) := by
      intro i
      simpa [prior, resultTapes, sourceOutput i] using operands i
    have priorScratch : prior scratch = [] := by
      simpa [prior, resultTapes, scratchOutput] using scratchEmpty
    have commandAtLabels : ∀ phase, p (labels (labelAt count bound r phase)) =
        commandStatement sources scratch output (fun phase => labels (labelAt count bound r phase))
          (labels (labelAt count bound (r + 1) .entry)) (commandAt commands r) phase := by
      intro phase
      rw [atLabels]
      simp only [statement, labelAt, Nat.min_eq_left (Nat.le_of_lt hrc), hrc, ite_true, if_true]
    have one := commandTrace sources scratch output sourceScratch sourceOutput scratchOutput
      (fun phase => labels (labelAt count bound r phase))
      (labels (labelAt count bound (r + 1) .entry)) (commandAt commands r)
      p commandAtLabels values prior priorOperands priorScratch ambient
    rw [prefixSteps, Nat.add_comm, Function.iterate_add_apply, ih (by omega)]
    rw [one]
    congr 2
    simp [prior, prefixBits, resultTapes, List.reverse_append, List.append_assoc]

/-- The complete callable program, including its actual final jump or halt. -/
theorem planTrace {count : Nat} (commands : Fin count → Command h σ bound)
    (sources : Fin h → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Label count bound → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement commands sources scratch output labels exit label)
    (values : Fin h → Nat) (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (values i))
    (scratchEmpty : base scratch = []) (ambient : σ) :
    (MachineComposition.advance (TM2.step p))^[prefixSteps commands values count + 1]
      (some ⟨some (labels (labelAt count bound 0 .entry)), ((ambient, ()), none), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        resultTapes output base (prefixBits commands values ambient count)⟩ := by
  rw [Function.iterate_succ_apply', prefixTrace commands sources scratch output sourceScratch
    sourceOutput scratchOutput labels exit p atLabels values base operands scratchEmpty ambient count
    (Nat.le_refl _)]
  change some (TM2.stepAux (p (labels (labelAt count bound count .entry))) _ _) = _
  rw [atLabels]
  cases exit <;> simp [statement, labelAt, Reduction.MachineTransfer.exitAt, TM2.stepAux]

/-- A linear bound in the largest unary input field; plan size is fixed. -/
def planInTime {count : Nat} (commands : Fin count → Command h σ bound)
    (sources : Fin h → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Label count bound → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement commands sources scratch output labels exit label)
    (values : Fin h → Nat) (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (values i))
    (scratchEmpty : base scratch = []) (ambient : σ)
    (N : Nat) (bounded : ∀ i, values i ≤ N) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (labelAt count bound 0 .entry)), ((ambient, ()), none), base⟩
      (some ⟨exit, ((ambient, ()), none),
        resultTapes output base (prefixBits commands values ambient count)⟩)
      (count * (3 * (N + 1) + 3) + 1) where
  steps := prefixSteps commands values count + 1
  evals_in_steps := planTrace commands sources scratch output sourceScratch sourceOutput
    scratchOutput labels exit p atLabels values base operands scratchEmpty ambient
  steps_le_m := Nat.add_le_add_right (prefixSteps_le commands values N bounded count) 1

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Emitter

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_InitialGraphLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The initial finite constraint graph of an arbitrary concrete 3CNF formula.
Clause and variable vertices use one eight-element alphabet. Variable labels
are the canonical triples `(bit, false, false)`; clause labels are arbitrary
triples. Every incidence has two directed darts, including repeated names.
A tautological dummy loop keeps the graph nonempty for empty formulas.

Name compaction precedes the public construction. The resulting vertex count
is at most `4*m+1`, and the dart count is exactly `6*m+1`. Unsatisfiability gives
an inverse-size gap, not a constant gap. No PCP theorem is assumed or claimed.
-/

namespace UniqueGamesTheorem.Foundations.PCP.InitialGraph

open Target

abbrev Dart (F : Formula) := (RandomEvent F × Bool) ⊕ Unit

def reverse (F : Formula) : Dart F → Dart F
  | .inl (event, orientation) => .inl (event, !orientation)
  | .inr _ => .inr ()

theorem reverse_involutive (F : Formula) : Function.Involutive (reverse F) := by
  intro d
  cases d with
  | inl pair => rcases pair with ⟨e, b⟩; cases b <;> rfl
  | inr u => cases u; rfl

def reverseEquiv (F : Formula) : Dart F ≃ Dart F where
  toFun := reverse F
  invFun := reverse F
  left_inv := reverse_involutive F
  right_inv := reverse_involutive F

def tail (F : Formula) : Dart F → Vertex F
  | .inl (event, false) => clauseVertex F event.1
  | .inl (event, true) => variableVertex F (nameAt (clauseAt F event.1) event.2)
  | .inr _ => dummyVertex F

def incidenceAccept (F : Formula) (event : RandomEvent F)
    (clauseLabel variableAnswer : Label) : Bool :=
  variableValid variableAnswer &&
    (localSatisfies (clauseAt F event.1) (toClauseAnswer clauseLabel) &&
      decide (answerAt (toClauseAnswer clauseLabel) event.2 = variableAnswer.1))

def predicate (F : Formula) : Dart F → Label → Label → Bool
  | .inl (event, false), a, b => incidenceAccept F event a b
  | .inl (event, true), a, b => incidenceAccept F event b a
  | .inr _, _, _ => true

def raw (F : Formula) : ConstraintGraph (Vertex F) (Dart F) Label where
  reverse := reverseEquiv F
  reverse_involutive := reverse_involutive F
  tail := tail F
  accepts := predicate F
  reverse_accepts := by
    intro d a b
    cases d with
    | inl pair => rcases pair with ⟨event, orientation⟩; cases orientation <;> rfl
    | inr u => rfl

@[simp] theorem card_dart (F : Formula) :
    Fintype.card (Dart F) = 6 * F.clauses.length + 1 := by
  simp [Dart, RandomEvent, Fintype.card_sum, Fintype.card_prod]
  omega

end UniqueGamesTheorem.Foundations.PCP.InitialGraph

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_AlphabetTableBoundsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.VerifierToCNF

open Target

def splitLong {n : Nat} : List (Literal n) → List (Fin n) → List (Clause n)
  | [a, b, c], [] => [#v[a, b, c]]
  | a :: b :: rest, y :: ys =>
      #v[a, b, ⟨y, true⟩] :: splitLong (⟨y, false⟩ :: rest) ys
  | _, _ => []

def tautology {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events) :
    Clause (outputVariables V) :=
  let v := oldIndex V (V.query e ⟨0, by omega⟩)
  #v[⟨v, true⟩, ⟨v, false⟩, ⟨v, true⟩]

def block {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events)
    (p : PatternIndex q) : List (Clause (outputVariables V)) :=
  if V.accepts e (patternAt q p) then List.replicate (q - 2) (tautology V hq e)
  else splitLong (forbiddenClause V e p) (auxiliaryNames V e p)

def eventBlock {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events) :
    List (Clause (outputVariables V)) :=
  (List.finRange (patterns q).length).flatMap (block V hq e)

def convert {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) : Formula where
  «variables» := outputVariables V
  clauses := (List.finRange V.events).flatMap (eventBlock V hq)

theorem splitLong_values {n : Nat} (ls : List (Literal n)) (ys : List (Fin n))
    (A : Fin n → Bool) :
    (splitLong ls ys).map (fun c => c.eval A) =
      (chainView (ls.map (fun l => l.eval A)) (ys.map A)).map tripleValue := by
  induction ys generalizing ls with
  | nil =>
    match ls with
    | [] => rfl
    | [_] => rfl
    | [_, _] => rfl
    | [a, b, c] => rfl
    | _ :: _ :: _ :: _ :: _ => rfl
  | cons y ys ih =>
    match ls with
    | [] => rfl
    | [_] => rfl
    | a :: b :: rest =>
      have h := ih (⟨y, false⟩ :: rest)
      simp only [splitLong, List.map_cons, chainView]
      apply congrArg₂ List.cons
      · rfl
      · simpa only [List.map_cons, Literal.eval, Bool.false_eq_true, ↓reduceIte] using h

theorem splitLong_length {n : Nat} (ls : List (Literal n)) (ys : List (Fin n))
    (size : ls.length = ys.length + 3) : (splitLong ls ys).length = ys.length + 1 := by
  have values := congrArg List.length (splitLong_values ls ys (fun _ => false))
  simp only [List.length_map] at values
  rw [values]
  have h := chainView_length (ls.map (fun l => l.eval (fun _ => false)))
    (ys.map (fun _ => false)) (by simpa only [List.length_map] using size)
  simpa only [List.length_map] using h

theorem block_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) (p : PatternIndex q) : (block V hq e p).length = q - 2 := by
  by_cases accepted : V.accepts e (patternAt q p) = true
  · simp [block, accepted]
  · simp only [block, accepted, Bool.false_eq_true, ↓reduceIte]
    have size : (forbiddenClause V e p).length = (auxiliaryNames V e p).length + 3 := by
      simp only [forbiddenClause, auxiliaryNames, List.length_ofFn]
      omega
    have h := splitLong_length (forbiddenClause V e p) (auxiliaryNames V e p) size
    have auxLength : (auxiliaryNames V e p).length = q - 3 := by simp [auxiliaryNames]
    rw [auxLength] at h
    omega

theorem eventBlock_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) : (eventBlock V hq e).length = 2 ^ q * (q - 2) := by
  rw [eventBlock, length_flatMap_constant _ _ (q - 2) (fun p _ => block_length V hq e p)]
  simp only [List.length_finRange, patterns_length]

theorem convert_clause_count {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) :
    (convert V hq).clauses.length = V.events * (2 ^ q * (q - 2)) := by
  change ((List.finRange V.events).flatMap (eventBlock V hq)).length = _
  rw [length_flatMap_constant _ _ _ (fun e _ => eventBlock_length V hq e)]
  rw [List.length_finRange]

theorem twelve_query_clause_count (V : FiniteVerifier 12) :
    (convert V (by decide)).clauses.length = V.events * 40960 := by
  simpa only [twelve_query_factor] using convert_clause_count V (by decide)

end UniqueGamesTheorem.Foundations.PCP.VerifierToCNF

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_FinalBooleanVerifier
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.FinalBooleanVerifier

open Target

variable {V E : Type*} {n m : Nat}

def cnf (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n) (edges : E ≃ Fin m) : Formula :=
  VerifierToCNF.convert (verifier G vertices edges) (by decide)

theorem cnf_clause_count (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) : (cnf G vertices edges).clauses.length = m * 40960 :=
  VerifierToCNF.twelve_query_clause_count (verifier G vertices edges)

theorem cnf_variable_count (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) : (cnf G vertices edges).variables = n * 6 + m * 36864 := by
  change n * 6 + m * (VerifierToCNF.patterns 12).length * (12 - 3) = _
  rw [VerifierToCNF.patterns_length, Nat.mul_assoc, twelve_query_auxiliary_factor]

end UniqueGamesTheorem.Foundations.PCP.FinalBooleanVerifier

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_FinalCNFMachineLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual finite-machine phases for the final twelve-query verifier conversion.
The graph codec stores a relation bit as the unary natural 0 or 1. The reader
below consumes those variable-length codewords, rather than treating the row
as an already available raw Boolean block. Its finite register size is fixed
at 4096 for the final alphabet, independent of the graph input size.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine

open Turing
open PCP

namespace Program

open PCP.AlphabetTable

/-- The actual finite program. All graph-dependent naturals remain on unary
stacks. The only buffered graph data is one fixed 4096-bit relation table. -/
def program (headerPlan rowPlan : Plan) :
    Label headerPlan.length rowPlan.length →
      TM2.Stmt (fun _ : Tape => Bool) (Label headerPlan.length rowPlan.length) (State Unit)
  | .copyFirst => Reduction.MachineTransfer.loopAt .input .scratch id false .copyFirst
      (some .copySecond)
  | .copySecond => MachineCopy.forkLoop .scratch .input .archive false .copySecond
      (some .startVertices)
  | .startVertices => Hastad.SourceMachine.fieldStart .vertices .readVertices
  | .readVertices => Hastad.SourceMachine.fieldLoop .input .vertices .readVertices (some .startDarts)
  | .startDarts => Hastad.SourceMachine.fieldStart .darts .readDarts
  | .readDarts => Hastad.SourceMachine.fieldLoop .input .darts .readDarts (some .seedIndex)
  | .seedIndex => .push .rowIndex (fun _ => false)
      (.push .tail (fun _ => false) (.push .head (fun _ => false)
        (.goto fun _ => .header (Emitter.labelAt headerPlan.length 36864 0 .entry))))
  | .header label => Emitter.statement (Emitter.listCommands headerPlan)
      source .scratch .accumulator Label.header (some .headerClearTail) label
  | .headerClearTail => MachineLookup.discard .tail .headerClearTail .headerClearHead
  | .headerClearHead => MachineLookup.discard .head .headerClearHead .guard
  | .guard => guard .startTail .reverseOutput
  | .startTail => Hastad.SourceMachine.fieldStart .tail .readTail
  | .readTail => Hastad.SourceMachine.fieldLoop .input .tail .readTail (some .startReverse)
  | .startReverse => Hastad.SourceMachine.fieldStart .reverseIndex .readReverse
  | .readReverse => Hastad.SourceMachine.fieldLoop .input .reverseIndex .readReverse
      (some .headTableFirst)
  | .headTableFirst => Reduction.MachineTransfer.loopAt .archive .scratch id false
      .headTableFirst (some .headTableSecond)
  | .headTableSecond => MachineCopy.forkLoop .scratch .archive .scanWork false
      .headTableSecond (some .headIndexFirst)
  | .headIndexFirst => Reduction.MachineTransfer.loopAt .reverseIndex .scratch id false
      .headIndexFirst (some .headIndexSecond)
  | .headIndexSecond => MachineCopy.forkLoop .scratch .reverseIndex .indexWork false
      .headIndexSecond (some .headHeaderVertices)
  | .headHeaderVertices => MachineLookup.discard .scanWork .headHeaderVertices .headHeaderDarts
  | .headHeaderDarts => MachineLookup.discard .scanWork .headHeaderDarts (.headLookup .guard)
  | .headLookup label => Lookup.statement 64 .indexWork .scanWork .head Label.headLookup
      (some .readRelation) label
  | .readRelation => readRelationAt .input
      (.row (Emitter.labelAt rowPlan.length 36864 0 .entry))
  | .row label => Emitter.statement (Emitter.listCommands rowPlan)
      source .scratch .accumulator Label.row (some .clearTail) label
  | .clearTail => MachineLookup.discard .tail .clearTail .clearHead
  | .clearHead => MachineLookup.discard .head .clearHead .clearReverse
  | .clearReverse => MachineLookup.discard .reverseIndex .clearReverse .nextRow
  | .nextRow => .push .rowIndex (fun _ => true) (.goto fun _ => .guard)
  | .reverseOutput => Reduction.MachineTransfer.loopAt .accumulator .output id false
      .reverseOutput none

def machine (headerPlan rowPlan : Plan) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label headerPlan.length rowPlan.length
  main := .copyFirst
  σ := State Unit
  initialState := ((((), fun _ => false), ()), none)
  m := program headerPlan rowPlan

/-- The head-access call is part of this concrete program, with its actual
finite labels and framed tape effects. Its data are read from the table. -/
def headPhaseInTime (headerPlan rowPlan : Plan) (base : Tape → List Bool)
    (table : GenericGraphTables.Table 64) (e : Fin table.darts)
    (hTable : base .archive = GenericGraphTables.tableBits table)
    (hReverse : base .reverseIndex = encodeWord (Lookup.headIndex table e).val)
    (hHead : base .head = []) (hScratch : base .scratch = []) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .headTableFirst, ((ambient, ()), none), base⟩
      (some ⟨some .readRelation, ((ambient, ()), none),
        Lookup.headLookupTapes headRoles base table e⟩)
      (Lookup.headTimePolynomial.eval (GenericGraphTables.tableBits table).length) :=
  Lookup.headLookupInTime headRoles headRoles_injective
    .headTableFirst .headTableSecond .headIndexFirst .headIndexSecond
    .headHeaderVertices .headHeaderDarts Label.headLookup (some .readRelation)
    (program headerPlan rowPlan) rfl rfl rfl rfl rfl rfl (fun _ => rfl)
    base table e hTable hReverse hHead hScratch (ambient, ()) none

end Program

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFCleanup

open Turing MachineComposition
open FinalCNFMachine (State)
open FinalCNFMachine.Program (Tape Plan)

def completedProgram (headerPlan rowPlan : Plan) : Label headerPlan rowPlan →
    TM2.Stmt (fun _ : Tape => Bool) (Label headerPlan rowPlan) (State Unit)
  | .inl label => redirectStmt Sum.inl (cleanupEntry headerPlan rowPlan)
      (FinalCNFMachine.Program.program headerPlan rowPlan label)
  | .inr (.inl label) => MachineDrainMany.instruction chosen (cleanupLabel headerPlan rowPlan)
      (some (resetLabel headerPlan rowPlan)) label
  | .inr (.inr _) => .load (fun _ => (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState) .halt

def completedMachine (headerPlan rowPlan : Plan) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label headerPlan rowPlan
  main := .inl .copyFirst
  σ := State Unit
  initialState := (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState
  m := completedProgram headerPlan rowPlan

def embeddedCfg (headerPlan rowPlan : Plan)
    (cfg : (FinalCNFMachine.Program.machine headerPlan rowPlan).Cfg) :
    (completedMachine headerPlan rowPlan).Cfg :=
  redirectCfg Sum.inl (cleanupEntry headerPlan rowPlan) cfg

theorem step_simulation (headerPlan rowPlan : Plan)
    (a b : (FinalCNFMachine.Program.machine headerPlan rowPlan).Cfg)
    (step : (FinalCNFMachine.Program.machine headerPlan rowPlan).step a = some b) :
    (completedMachine headerPlan rowPlan).step (embeddedCfg headerPlan rowPlan a) =
      some (embeddedCfg headerPlan rowPlan b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => simp [FinTM2.step, TM2.step] at step
    | some label =>
      have hb : TM2.stepAux (FinalCNFMachine.Program.program headerPlan rowPlan label)
          state tapes = b := Option.some.inj step
      rw [← hb]
      change some (TM2.stepAux
        (redirectStmt Sum.inl (cleanupEntry headerPlan rowPlan)
          (FinalCNFMachine.Program.program headerPlan rowPlan label)) state tapes) = _
      erw [stepAux_redirect]
      rfl

@[simp] theorem embedded_init (headerPlan rowPlan : Plan) (input : List Bool) :
    embeddedCfg headerPlan rowPlan (initList (FinalCNFMachine.Program.machine headerPlan rowPlan) input) =
      initList (completedMachine headerPlan rowPlan) input := rfl

theorem finalTapes_eq (base : Tape → List Bool) :
    MachineDrainMany.finalTapes chosen base = MachineDrainMany.haltTapes .output (base .output) := by
  funext tape
  rw [MachineDrainMany.finalTapes_apply]
  simp only [mem_chosen]
  by_cases h : tape = .output
  · subst tape
    simp [MachineDrainMany.haltTapes]
  · simp [MachineDrainMany.haltTapes, h]

theorem haltList_eq (headerPlan rowPlan : Plan) (output : List Bool) :
    haltList (completedMachine headerPlan rowPlan) output =
      ⟨none, (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState,
        MachineDrainMany.haltTapes .output output⟩ := by
  congr 1

/-- Actual drains followed by a real state-reset instruction reach canonical halt. -/
def cleanupExecution (headerPlan rowPlan : Plan) (state : State Unit) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (completedMachine headerPlan rowPlan).step
      ⟨cleanupEntry headerPlan rowPlan, state, base⟩
      (some (haltList (completedMachine headerPlan rowPlan) (base .output)))
      (MachineDrainMany.steps chosen base + 1) := by
  let after : (completedMachine headerPlan rowPlan).Cfg :=
    ⟨some (resetLabel headerPlan rowPlan),
      (state.1, MachineDrainMany.finalRegister chosen state.2),
      MachineDrainMany.finalTapes chosen base⟩
  have drains : StateTransition.EvalsToInTime (completedMachine headerPlan rowPlan).step
      ⟨cleanupEntry headerPlan rowPlan, state, base⟩ (some after)
      (MachineDrainMany.steps chosen base) := {
    steps := MachineDrainMany.steps chosen base
    evals_in_steps := MachineDrainMany.trace chosen (cleanupLabel headerPlan rowPlan)
      (some (resetLabel headerPlan rowPlan)) (completedProgram headerPlan rowPlan)
      (fun _ => rfl) base state.1 state.2
    steps_le_m := le_rfl }
  have reset : StateTransition.EvalsToInTime (completedMachine headerPlan rowPlan).step
      after (some (haltList (completedMachine headerPlan rowPlan) (base .output))) 1 := {
    steps := 1
    evals_in_steps := by
      change some (⟨none, (FinalCNFMachine.Program.machine headerPlan rowPlan).initialState,
        MachineDrainMany.finalTapes chosen base⟩ : (completedMachine headerPlan rowPlan).Cfg) =
          some (haltList (completedMachine headerPlan rowPlan) (base .output))
      erw [finalTapes_eq, haltList_eq]
      rfl
    steps_le_m := le_rfl }
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans _ (MachineDrainMany.steps chosen base) 1
      _ after _ drains reset

/-- The extra cost is bounded from the actual raw execution, independently of
the contents of its dirty private tapes and finite state. -/
def outputsInTime (headerPlan rowPlan : Plan) (input output : List Bool)
    (state : State Unit) (base : Tape → List Bool) (budget : Nat)
    (raw : StateTransition.EvalsToInTime
      (FinalCNFMachine.Program.machine headerPlan rowPlan).step
      (initList (FinalCNFMachine.Program.machine headerPlan rowPlan) input)
      (some ⟨none, state, base⟩) budget)
    (correctOutput : base .output = output) :
    TM2OutputsInTime (completedMachine headerPlan rowPlan) input (some output)
      (budget + 12 * (input.length + budget *
        Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan) + 1) + 1) := by
  let lifted := liftExecutionInTime
    (FinalCNFMachine.Program.machine headerPlan rowPlan).step
    (completedMachine headerPlan rowPlan).step (embeddedCfg headerPlan rowPlan)
    (step_simulation headerPlan rowPlan) raw
  have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ lifted
    (cleanupExecution headerPlan rowPlan state base)
  have stackBound : ∀ tape, (base tape).length ≤ input.length + budget *
      Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan) := by
    intro tape
    have h := Runtime.executionSizeBound
      (FinalCNFMachine.Program.machine headerPlan rowPlan).step
      (fun cfg => (cfg.stk tape).length)
      (Runtime.programPushBound (FinalCNFMachine.Program.machine headerPlan rowPlan))
      (Runtime.stepStackLength (FinalCNFMachine.Program.machine headerPlan rowPlan) tape) raw
    exact h.trans (Nat.add_le_add_right
      (Runtime.initialStackLength (FinalCNFMachine.Program.machine headerPlan rowPlan) input tape) _)
  have cleanupBound := MachineDrainMany.steps_le_uniform chosen base _ stackBound
  rw [chosen_length] at cleanupBound
  rw [embedded_init, correctOutput] at joined
  exact { toEvalsTo := joined.toEvalsTo
          steps_le_m := joined.steps_le_m.trans (by omega) }

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFCleanup

/-!
The concrete final-CNF machine's entry phase. It archives its complete input,
reads the two unary size fields, emits the exact formula header, and reaches
the row guard. The transition witness is assembled from actual program calls.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

open Turing
open PCP.AlphabetTable

@[simp] theorem headerResultTapes_input (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .input = rowsBits := rfl

@[simp] theorem headerResultTapes_archive (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .archive = encodeWords [n, m] ++ rowsBits := rfl

@[simp] theorem headerResultTapes_accumulator (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .accumulator =
      (encodeWords [6 * n + 36864 * m, 40960 * m]).reverse := rfl

@[simp] theorem headerResultTapes_rowIndex (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .rowIndex = encodeWord 0 := rfl

@[simp] theorem headerTimePolynomial_eval (length : Nat) :
    headerTimePolynomial.eval length = 25 * length + 52 := by
  simp [headerTimePolynomial]

/-- An actual entry-to-guard trace, valid for any unread row suffix and every
finite ambient buffer. No execution premise is supplied by the caller. -/
def headerInTime (rowPlan : Plan) (n m : Nat) (rowsBits : List Bool) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .copyFirst, ((ambient, ()), none),
        headerInputTapes (encodeWords [n, m] ++ rowsBits)⟩
      (some ⟨some .guard, ((ambient, ()), none), headerResultTapes n m rowsBits⟩)
      (headerTimePolynomial.eval (encodeWords [n, m] ++ rowsBits).length) := by
  let word := encodeWords [n, m] ++ rowsBits
  let bits := encodeWords [6 * n + 36864 * m, 40960 * m]
  let b₀ := headerInputTapes word
  let b₁ := headerFrame word word [] [] [] [] [] []
  let b₂ := headerFrame (encodeWord m ++ rowsBits) word (encodeWord n) [] [] [] [] []
  let b₃ := headerFrame rowsBits word (encodeWord n) (encodeWord m) [] [] [] []
  let b₄ := headerFrame rowsBits word (encodeWord n) (encodeWord m)
    (encodeWord 0) (encodeWord 0) (encodeWord 0) []
  let b₅ := headerFrame rowsBits word (encodeWord n) (encodeWord m)
    (encodeWord 0) (encodeWord 0) (encodeWord 0) bits.reverse
  let b₆ := headerFrame rowsBits word (encodeWord n) (encodeWord m)
    (encodeWord 0) [] (encodeWord 0) bits.reverse
  let b₇ := headerResultTapes n m rowsBits
  have h₀ : Function.update b₀ Tape.archive (b₀ .input ++ b₀ .archive) = b₁ := by
    funext tape; cases tape <;> simp [b₀, b₁, headerInputTapes, headerFrame]
  have h₁ : Hastad.SourceMachine.fieldTapes Tape.input Tape.vertices b₁
      (encodeWord m ++ rowsBits) (encodeWord n ++ b₁ .vertices) = b₂ := by
    funext tape; cases tape <;> simp [Hastad.SourceMachine.fieldTapes, b₁, b₂, headerFrame]
  have h₂ : Hastad.SourceMachine.fieldTapes Tape.input Tape.darts b₂
      rowsBits (encodeWord m ++ b₂ .darts) = b₃ := by
    funext tape; cases tape <;> simp [Hastad.SourceMachine.fieldTapes, b₂, b₃, headerFrame]
  have h₄ : Emitter.resultTapes Tape.accumulator b₄
      (Emitter.prefixBits (Emitter.listCommands headerPlan) (values n m 0 0 0)
        ambient headerPlan.length) = b₅ := by
    rw [Emitter.bits_listCommands, headerPlan_bits]
    funext tape; cases tape <;> simp [Emitter.resultTapes, b₄, b₅, bits, headerFrame]
  have h₅ : Function.update b₅ Tape.tail [] = b₆ := by
    funext tape; cases tape <;> simp [b₅, b₆, headerFrame]
  have h₆ : Function.update b₆ Tape.head [] = b₇ := by
    funext tape; cases tape <;> simp [b₆, b₇, headerResultTapes, bits, word, headerFrame]
  have hn : n ≤ word.length := by
    simp only [word, List.length_append, encodeWords_length, List.sum_cons,
      List.sum_nil, List.length_cons, List.length_nil] ; omega
  have hm : m ≤ word.length := by
    simp only [word, List.length_append, encodeWords_length, List.sum_cons,
      List.sum_nil, List.length_cons, List.length_nil] ; omega
  let p₀ := MachineCopy.copyInTime Tape.input Tape.archive Tape.scratch
    (by decide) (by decide) (by decide) false .copyFirst .copySecond (some .startVertices)
    (program headerPlan rowPlan) rfl rfl b₀ (by rfl) (ambient, ()) none
  have p₀' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .copyFirst, ((ambient, ()), none), b₀⟩
      (some ⟨some .startVertices, ((ambient, ()), none), b₁⟩) (2 * (word.length + 1)) := by
    have h := p₀
    rw [h₀] at h
    simpa only [show b₀ .input = word from rfl] using h
  let p₁ := Hastad.SourceMachine.fieldInTime Tape.input Tape.vertices (by decide)
    .startVertices .readVertices (some .startDarts) (program headerPlan rowPlan)
    rfl rfl b₁ n (encodeWord m ++ rowsBits)
    (by simp [b₁, headerFrame, word, encodeWords, List.append_assoc]) (ambient, ()) none
  have p₁' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .startVertices, ((ambient, ()), none), b₁⟩
      (some ⟨some .startDarts, ((ambient, ()), none), b₂⟩) (n + 2) := by
    simpa only [h₁] using p₁
  let p₂ := Hastad.SourceMachine.fieldInTime Tape.input Tape.darts (by decide)
    .startDarts .readDarts (some .seedIndex) (program headerPlan rowPlan)
    rfl rfl b₂ m rowsBits rfl (ambient, ()) none
  have p₂' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .startDarts, ((ambient, ()), none), b₂⟩
      (some ⟨some .seedIndex, ((ambient, ()), none), b₃⟩) (m + 2) := by
    simpa only [h₂] using p₂
  let p₃ : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .seedIndex, ((ambient, ()), none), b₃⟩
      (some ⟨some (.header (Emitter.labelAt headerPlan.length 36864 0 .entry)),
        ((ambient, ()), none), b₄⟩) 1 := {
    steps := 1
    evals_in_steps := by
      simp only [Function.iterate_one]
      change TM2.step (program headerPlan rowPlan)
        ⟨some .seedIndex, ((ambient, ()), none), b₃⟩ = _
      have ht : Function.update (Function.update (Function.update b₃ Tape.rowIndex [false])
          Tape.tail [false]) Tape.head [false] = b₄ := by
        funext tape; cases tape <;> simp [b₃, b₄, headerFrame, encodeWord]
      simp only [TM2.step, program, TM2.stepAux]
      apply congrArg some
      exact congrArg (TM2.Cfg.mk _ _) ht
    steps_le_m := Nat.le_refl _ }
  let p₄ := Emitter.planInTime (Emitter.listCommands headerPlan) source Tape.scratch
    Tape.accumulator source_ne_scratch source_ne_accumulator (by decide)
    Label.header (some .headerClearTail) (program headerPlan rowPlan) (fun _ => rfl)
    (values n m 0 0 0) b₄
    (by intro i; fin_cases i <;> rfl) rfl ambient word.length
    (by
      intro i
      fin_cases i
      · exact hn
      · exact hm
      · exact Nat.zero_le _
      · exact Nat.zero_le _
      · exact Nat.zero_le _)
  have p₄' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some (.header (Emitter.labelAt headerPlan.length 36864 0 .entry)),
        ((ambient, ()), none), b₄⟩
      (some ⟨some .headerClearTail, ((ambient, ()), none), b₅⟩)
      (7 * (3 * (word.length + 1) + 3) + 1) := by
    have h := p₄
    rw [h₄] at h
    simpa only [headerPlan_length] using h
  let p₅ := MachineLookup.discardInTime Tape.tail .headerClearTail .headerClearHead
    (program headerPlan rowPlan) rfl b₅ 0 [] (by simp [b₅, headerFrame]) (ambient, ()) none
  have p₅' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .headerClearTail, ((ambient, ()), none), b₅⟩
      (some ⟨some .headerClearHead, ((ambient, ()), none), b₆⟩) 1 := by
    simpa only [h₅] using p₅
  let p₆ := MachineLookup.discardInTime Tape.head .headerClearHead .guard
    (program headerPlan rowPlan) rfl b₆ 0 [] (by simp [b₆, headerFrame]) (ambient, ()) none
  have p₆' : StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .headerClearHead, ((ambient, ()), none), b₆⟩
      (some ⟨some .guard, ((ambient, ()), none), b₇⟩) 1 := by
    simpa only [h₆] using p₆
  let p₀₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀' p₁'
  let p₀₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁ p₂'
  let p₀₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂ p₃
  let p₀₁₂₃₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃ p₄'
  let p₀₁₂₃₄₅ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄ p₅'
  let p := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄₅ p₆'
  exact {
    toEvalsTo := p.toEvalsTo
    steps_le_m := by
      have h := p.steps_le_m
      change _ ≤ headerTimePolynomial.eval word.length
      rw [headerTimePolynomial_eval]
      omega }

/-- The unread graph rows in the actual graph codec. -/
def tableRowsBits (table : PCP.GenericGraphTables.Table 64) : List Bool :=
  encodeWords ((PCP.GenericGraphTables.rowList table).flatMap PCP.GenericGraphTables.rowWords)

theorem tableBits_header_rows (table : PCP.GenericGraphTables.Table 64) :
    PCP.GenericGraphTables.tableBits table =
      encodeWords [table.vertices, table.darts] ++ tableRowsBits table := by
  simp only [PCP.GenericGraphTables.tableBits, PCP.GenericGraphTables.tableWords,
    encodeWords_append, tableRowsBits]

/-- Specialization to the entire input of the actual numbered graph codec. -/
def tableHeaderInTime (rowPlan : Plan) (table : PCP.GenericGraphTables.Table 64)
    (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .copyFirst, ((ambient, ()), none),
        headerInputTapes (PCP.GenericGraphTables.tableBits table)⟩
      (some ⟨some .guard, ((ambient, ()), none),
        headerResultTapes table.vertices table.darts (tableRowsBits table)⟩)
      (headerTimePolynomial.eval (PCP.GenericGraphTables.tableBits table).length) := by
  rw [tableBits_header_rows]
  exact headerInTime rowPlan table.vertices table.darts (tableRowsBits table) ambient

theorem headerInput_configuration (rowPlan : Plan) (input : List Bool) :
    initList (machine headerPlan rowPlan) input =
      ⟨some .copyFirst, ((((), fun _ => false), ()), none), headerInputTapes input⟩ := by
  have ht : (initList (machine headerPlan rowPlan) input).stk = headerInputTapes input := by
    funext tape
    cases tape <;> simp [initList, machine, headerInputTapes, headerFrame]
    rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

/-- The same bounded phase begins at the machine's genuine initial configuration. -/
def initializedTableHeaderInTime (rowPlan : Plan) (table : PCP.GenericGraphTables.Table 64) :
    StateTransition.EvalsToInTime (machine headerPlan rowPlan).step
      (initList (machine headerPlan rowPlan) (PCP.GenericGraphTables.tableBits table))
      (some ⟨some .guard, ((((), fun _ => false), ()), none),
        headerResultTapes table.vertices table.darts (tableRowsBits table)⟩)
      (headerTimePolynomial.eval (PCP.GenericGraphTables.tableBits table).length) := by
  rw [headerInput_configuration]
  exact tableHeaderInTime rowPlan table ((), fun _ => false)

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_FinalCNFTemplate
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Fixed literal templates for the twelve-query converter. All control data have
constant size: twelve query references, nine auxiliary references, ten clauses,
and three literal slots. Pattern bits remain symbolic throughout the proof.

These templates specify the actual serialized rows.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFTemplate

open Target PCP

variable (V : VerifierToCNF.FiniteVerifier 12) (e : Fin V.events)
  (p : VerifierToCNF.PatternIndex 12)

def instantiateClause (clause : ClauseTemplate) : Clause (VerifierToCNF.outputVariables V) :=
  #v[instantiateLiteral V e p clause[0], instantiateLiteral V e p clause[1],
    instantiateLiteral V e p clause[2]]

/-- A symbolic twelve-input chain expands to exactly these ten clauses. -/
theorem splitLong_twelve {n : Nat} (ls : Fin 12 → Literal n) (ys : Fin 9 → Fin n) :
    VerifierToCNF.splitLong (List.ofFn ls) (List.ofFn ys) =
      [#v[ls 0, ls 1, ⟨ys 0, true⟩],
       #v[⟨ys 0, false⟩, ls 2, ⟨ys 1, true⟩],
       #v[⟨ys 1, false⟩, ls 3, ⟨ys 2, true⟩],
       #v[⟨ys 2, false⟩, ls 4, ⟨ys 3, true⟩],
       #v[⟨ys 3, false⟩, ls 5, ⟨ys 4, true⟩],
       #v[⟨ys 4, false⟩, ls 6, ⟨ys 5, true⟩],
       #v[⟨ys 5, false⟩, ls 7, ⟨ys 6, true⟩],
       #v[⟨ys 6, false⟩, ls 8, ⟨ys 7, true⟩],
       #v[⟨ys 7, false⟩, ls 9, ⟨ys 8, true⟩],
       #v[⟨ys 8, false⟩, ls 10, ls 11]] := by
  simp only [List.ofFn_succ, List.ofFn_zero, VerifierToCNF.splitLong]
  rfl

/-- Instantiating the fixed plan reproduces the actual converter's entire block. -/
theorem instantiate_templates :
    (templates (V.accepts e (VerifierToCNF.patternAt 12 p))
      (VerifierToCNF.patternAt 12 p)).map (instantiateClause V e p) =
        VerifierToCNF.block V (by decide) e p := by
  cases h : V.accepts e (VerifierToCNF.patternAt 12 p) with
  | false =>
      simp only [h, templates_false, VerifierToCNF.block, Bool.false_eq_true, ↓reduceIte,
        VerifierToCNF.forbiddenClause, VerifierToCNF.auxiliaryNames]
      rw [splitLong_twelve]
      rfl
  | true =>
      simp only [h, templates_true, VerifierToCNF.block, ↓reduceIte, List.map_replicate]
      rfl

theorem instantiateClause_words (clause : ClauseTemplate) :
    Complexity.clauseWords (instantiateClause V e p clause) =
      clauseWords (fun r => (resolve V e p r).val) clause := rfl

/-- The finite plan's sixty natural fields are the converter's actual row words. -/
theorem words_eq_block :
    words (V.accepts e (VerifierToCNF.patternAt 12 p)) (VerifierToCNF.patternAt 12 p)
      (fun r => (resolve V e p r).val) =
        (VerifierToCNF.block V (by decide) e p).flatMap Complexity.clauseWords := by
  rw [← instantiate_templates V e p]
  simp only [List.flatMap_map, instantiateClause_words]
  rfl

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFTemplate

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_FinalCNFRowPlanLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
The fixed finite emission plan for one directed graph row. All choices based
on the relation are functions of its 4096-bit finite register. Vertex counts,
endpoint names and row indices are read by preserving unary scans.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable

section Templates

open FinalCNFTemplate

/-- Seven real commands for the two unary fields of a literal. -/
def literalPlan (p : VerifierToCNF.PatternIndex 12) (literal : Ambient → LiteralTemplate) : Plan :=
  [.scaledIf 0 6 (fun state => auxiliaryFlag (literal state).reference),
   .scaledIf 2 6 (fun state => tailFlag (literal state).reference),
   .scaledIf 3 6 (fun state => headFlag (literal state).reference),
   .scaledIf 4 36864 (fun state => auxiliaryFlag (literal state).reference),
   .bounded (fun state => referenceOffset p (literal state).reference),
   .literal [false],
   .bit (fun state => (literal state).positive)]

theorem literalPlan_length (p : VerifierToCNF.PatternIndex 12)
    (literal : Ambient → LiteralTemplate) : (literalPlan p literal).length = 7 := rfl

theorem literalPlan_bits (p : VerifierToCNF.PatternIndex 12)
    (literal : Ambient → LiteralTemplate) (vertices darts tail head row : Nat)
    (ambient : Ambient) :
    (literalPlan p literal).flatMap
      (Emitter.commandBits (values vertices darts tail head row) ambient) =
      encodeWords (FinalCNFTemplate.literalWords
        (referenceValue vertices tail head row p.val) (literal ambient)) := by
  rcases h : literal ambient with ⟨reference, positive⟩
  cases reference with
  | query i =>
      by_cases hi : i.val < 6
      · simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
          referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
          hi, show ¬ 6 ≤ i.val by omega, encodeWords, encodeWord, List.replicate_add,
          List.append_assoc, -List.replicate_append_replicate]
        rfl
      · simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
          referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
          hi, show 6 ≤ i.val by omega, encodeWords, encodeWord, List.replicate_add,
          List.append_assoc, -List.replicate_append_replicate]
        rfl
  | auxiliary j =>
      simp [literalPlan, Emitter.commandBits, h, auxiliaryFlag, tailFlag, headFlag,
        referenceOffset, referenceValue, FinalCNFTemplate.literalWords, values,
        encodeWords, encodeWord, List.replicate_add, List.append_assoc,
        -List.replicate_append_replicate]
      rfl

def patternPlan (p : VerifierToCNF.PatternIndex 12) : Plan :=
  (List.finRange 10).flatMap fun clause =>
    (List.finRange 3).flatMap fun slot => literalPlan p (patternLiteral p clause slot)

def rowPlan : Plan :=
  (List.finRange (VerifierToCNF.patterns 12).length).flatMap patternPlan

theorem patternPlan_length (p : VerifierToCNF.PatternIndex 12) :
    (patternPlan p).length = 210 := by
  unfold patternPlan
  rw [VerifierToCNF.length_flatMap_constant _ _ 21]
  · simp
  · intro clause hclause
    rw [VerifierToCNF.length_flatMap_constant _ _ 7]
    · simp
    · intro slot hslot
      exact literalPlan_length _ _

theorem rowPlan_length : rowPlan.length = 860160 := by
  unfold rowPlan
  rw [VerifierToCNF.length_flatMap_constant _ _ 210]
  · rw [List.length_finRange, VerifierToCNF.patterns_length]
    norm_num
  · intro p hp
    exact patternPlan_length p

theorem encodeWords_flatMap {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem patternPlan_bits (p : VerifierToCNF.PatternIndex 12)
    (vertices darts tail head row : Nat) (ambient : Ambient) :
    (patternPlan p).flatMap
      (Emitter.commandBits (values vertices darts tail head row) ambient) =
      encodeWords (FinalCNFTemplate.words
        (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p) (referenceValue vertices tail head row p.val)) := by
  unfold patternPlan
  simp only [List.flatMap_assoc]
  simp_rw [literalPlan_bits]
  have hclauses :
      (List.finRange 10).map
        (fun c => (blockTemplates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
          (VerifierToCNF.patternAt 12 p))[c]) =
      templates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p) := by
    rw [← List.ofFn_eq_map]
    change List.ofFn (fun c : Fin 10 =>
      (blockTemplates (ambient.2 (FinalCNFPattern.patternRelationIndex p))
        (VerifierToCNF.patternAt 12 p))[c.val]) = _
    rw [← Vector.toList_ofFn, Vector.ofFn_getElem]
    rfl
  unfold FinalCNFTemplate.words
  rw [← hclauses, List.flatMap_map, encodeWords_flatMap]
  apply List.flatMap_congr
  intro clause hclause
  simp only [List.finRange, List.ofFn_succ, List.ofFn_zero, List.flatMap_cons,
    List.flatMap_nil, patternLiteral, literalAt, FinalCNFTemplate.clauseWords,
    encodeWords_append, List.append_nil, List.append_assoc]
  rfl

theorem rowPlan_bits (table : GraphTables.Table) (e : Fin table.darts) :
    rowPlan.flatMap (Emitter.commandBits
      (values table.vertices table.darts table.rows[e].tail.val
        table.rows[table.rows[e].reverseIndex].tail.val e.val)
      ((), fun i => table.rows[e].relation[i])) =
      encodeWords ((VerifierToCNF.eventBlock (FinalCNFPattern.tableVerifier table)
        (by decide) e).flatMap Complexity.clauseWords) := by
  unfold rowPlan VerifierToCNF.eventBlock
  simp only [List.flatMap_assoc]
  rw [encodeWords_flatMap]
  apply List.flatMap_congr
  intro p hp
  rw [patternPlan_bits]
  dsimp only
  rw [FinalCNFPattern.pattern_lookup_eq_verifier_accepts]
  have href := funext (referenceValue_eq_resolve table e p)
  rw [href]
  exact congrArg encodeWords (words_eq_block (FinalCNFPattern.tableVerifier table) e p)

end Templates

/-!
Actual finite-machine execution of the final converter's row phases. These
certificates use the concrete program statements, preserve all other tapes,
and expose the precise concatenated output of the fixed emission plan.
-/

open Turing

def endpointTapes (base : Tape → List Bool) (tail reverse : Nat) (rest : List Bool) :=
  Hastad.SourceMachine.fieldTapes Tape.input Tape.reverseIndex
    (Hastad.SourceMachine.fieldTapes Tape.input Tape.tail base
      (encodeWord reverse ++ rest) (encodeWord tail ++ base .tail))
    rest (encodeWord reverse ++ base .reverseIndex)

/-- Read the two fields actually stored in a graph row: tail and reverse dart. -/
def endpointsInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (tail reverse : Nat) (rest : List Bool)
    (hinput : base .input = encodeWord tail ++ encodeWord reverse ++ rest)
    (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .startTail, ((ambient, ()), none), base⟩
      (some ⟨some .headTableFirst, ((ambient, ()), none),
        endpointTapes base tail reverse rest⟩) (tail + reverse + 4) := by
  let first := Hastad.SourceMachine.fieldTapes Tape.input Tape.tail base
    (encodeWord reverse ++ rest) (encodeWord tail ++ base .tail)
  let run₁ := Hastad.SourceMachine.fieldInTime Tape.input Tape.tail (by decide)
    .startTail .readTail (some .startReverse) (program headerPlan plan) rfl rfl
    base tail (encodeWord reverse ++ rest) (by simpa only [List.append_assoc] using hinput)
    (ambient, ()) none
  have input₁ : first .input = encodeWord reverse ++ rest := by
    simp [first, Hastad.SourceMachine.fieldTapes]
  have reverse₁ : first .reverseIndex = base .reverseIndex := by
    simp [first, Hastad.SourceMachine.fieldTapes]
  let run₂ := Hastad.SourceMachine.fieldInTime Tape.input Tape.reverseIndex (by decide)
    .startReverse .readReverse (some .headTableFirst) (program headerPlan plan) rfl rfl
    first reverse rest input₁ (ambient, ()) none
  have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  simpa only [first, reverse₁, endpointTapes, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm] using joined

/-- The fixed unary relation reader occupies one finite TM2 statement. -/
def relationInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (relation : GraphTables.RelationTable) (rest : List Bool)
    (hinput : base .input = encodeWords (GraphTables.relationWords relation) ++ rest)
    (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .readRelation, ((ambient, ()), none), base⟩
      (some ⟨some (.row (Emitter.labelAt plan.length 36864 0 .entry)),
        ((((), fun i => relation[i]), ()), none), Function.update base .input rest⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program headerPlan plan .readRelation) _ _) = _
    rw [program, stepAux_readRelationAt _ _ _ _ _ _ _ _ _ hinput]
  steps_le_m := Nat.le_refl _

/-- Execute the complete fixed row emission plan against physical unary tapes. -/
def emitInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (operands : Fin 5 → Nat) (hoperands : ∀ i, base (source i) = encodeWord (operands i))
    (hscratch : base .scratch = []) (ambient : Ambient)
    (N : Nat) (hbounded : ∀ i, operands i ≤ N) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some (.row (Emitter.labelAt plan.length 36864 0 .entry)),
        ((ambient, ()), none), base⟩
      (some ⟨some .clearTail, ((ambient, ()), none),
        Function.update base .accumulator
          ((plan.flatMap (Emitter.commandBits operands ambient)).reverse ++ base .accumulator)⟩)
      (plan.length * (3 * (N + 1) + 3) + 1) := by
  have run := Emitter.planInTime (Emitter.listCommands plan)
    source Tape.scratch Tape.accumulator source_ne_scratch source_ne_accumulator (by decide)
    Label.row (some .clearTail) (program headerPlan plan) (fun _ => rfl)
    operands base hoperands hscratch ambient N hbounded
  simpa only [Emitter.bits_listCommands, Emitter.resultTapes] using run

def finishTapes (base : Tape → List Bool) (row : Nat) : Tape → List Bool :=
  Function.update
    (Function.update (Function.update (Function.update base Tape.tail []) Tape.head [])
      Tape.reverseIndex []) Tape.rowIndex (encodeWord (row + 1))

/-- Clear precisely the three isolated temporary fields and increment the
physical row counter before returning to the input guard. -/
def finishInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (tail head reverse row : Nat)
    (htail : base .tail = encodeWord tail) (hhead : base .head = encodeWord head)
    (hreverse : base .reverseIndex = encodeWord reverse)
    (hrow : base .rowIndex = encodeWord row) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .clearTail, ((ambient, ()), none), base⟩
      (some ⟨some .guard, ((ambient, ()), none), finishTapes base row⟩)
      (tail + head + reverse + 4) := by
  let t₁ := Function.update base Tape.tail []
  let t₂ := Function.update t₁ Tape.head []
  let t₃ := Function.update t₂ Tape.reverseIndex []
  let run₁ := MachineLookup.discardInTime Tape.tail .clearTail .clearHead
    (program headerPlan plan) rfl base tail [] (by simpa using htail) (ambient, ()) none
  have hhead₁ : t₁ .head = encodeWord head := by simp [t₁, hhead]
  let run₂ := MachineLookup.discardInTime Tape.head .clearHead .clearReverse
    (program headerPlan plan) rfl t₁ head [] (by simpa using hhead₁) (ambient, ()) none
  have hreverse₂ : t₂ .reverseIndex = encodeWord reverse := by simp [t₂, t₁, hreverse]
  let run₃ := MachineLookup.discardInTime Tape.reverseIndex .clearReverse .nextRow
    (program headerPlan plan) rfl t₂ reverse [] (by simpa using hreverse₂) (ambient, ()) none
  let run₄ : StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .nextRow, ((ambient, ()), none), t₃⟩
      (some ⟨some .guard, ((ambient, ()), none), finishTapes base row⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change some (TM2.stepAux (program headerPlan plan .nextRow) _ _) = _
      simp only [program, TM2.stepAux]
      congr 2
      simp [t₃, t₂, t₁, finishTapes, hrow, encodeWord, List.replicate_succ]
    steps_le_m := Nat.le_refl _ }
  let r₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  let r₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂ run₃
  have run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂₃ run₄
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using run

open FinalCNFTableAdapter

@[simp] theorem headRoles_zero : headRoles 0 = Tape.archive := rfl
@[simp] theorem headRoles_one : headRoles 1 = Tape.reverseIndex := rfl
@[simp] theorem headRoles_two : headRoles 2 = Tape.scanWork := rfl
@[simp] theorem headRoles_three : headRoles 3 = Tape.indexWork := rfl
@[simp] theorem headRoles_four : headRoles 4 = Tape.head := rfl
@[simp] theorem headRoles_five : headRoles 5 = Tape.scratch := rfl

def rowRest (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) : List Bool :=
  encodeWords (GraphTables.relationWords table.rows[e].relation) ++ rest

def preparedTapes (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) : Tape → List Bool :=
  Lookup.headLookupTapes headRoles
    (endpointTapes base table.rows[e].tail.val table.rows[e].reverseIndex.val
      (rowRest table e rest)) (genericTable table) e

theorem prepared_input (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .input = rowRest table e rest := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes]

theorem prepared_head (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .head =
      encodeWord table.rows[table.rows[e].reverseIndex].tail.val := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes,
    genericTable_headValue, GraphTables.semantics, ConstraintGraph.head,
    GraphTables.reverseAt]

theorem prepared_tail (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .tail = encodeWord table.rows[e].tail.val ++ base .tail := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes]

theorem prepared_reverse (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) :
    preparedTapes base table e rest .reverseIndex =
      encodeWord table.rows[e].reverseIndex.val ++ base .reverseIndex := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes]

theorem prepared_frame (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) (tape : Tape)
    (hi : tape ≠ .input) (ht : tape ≠ .tail) (hr : tape ≠ .reverseIndex)
    (hh : tape ≠ .head) (hs : tape ≠ .scanWork) (hx : tape ≠ .indexWork) :
    preparedTapes base table e rest tape = base tape := by
  simp [preparedTapes, Lookup.headLookupTapes, MachineLookup.tapes, endpointTapes,
    Hastad.SourceMachine.fieldTapes, hi, ht, hr, hh, hs, hx]

def emittedTapes (plan : Plan) (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) : Tape → List Bool :=
  Function.update (Function.update (preparedTapes base table e rest) Tape.input rest)
    Tape.accumulator ((plan.flatMap (Emitter.commandBits (rowOperands table e)
      (rowRelation table e))).reverse ++ base .accumulator)

def rowResultTapes (plan : Plan) (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) : Tape → List Bool :=
  finishTapes (emittedTapes plan base table e rest) e.val

@[simp] theorem rowResult_input (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .input = rest := by
  simp [rowResultTapes, finishTapes, emittedTapes]

@[simp] theorem rowResult_tail (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .tail = [] := by
  simp [rowResultTapes, finishTapes]

@[simp] theorem rowResult_head (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .head = [] := by
  simp [rowResultTapes, finishTapes]

@[simp] theorem rowResult_reverse (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .reverseIndex = [] := by
  simp [rowResultTapes, finishTapes]

@[simp] theorem rowResult_index (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .rowIndex = encodeWord (e.val + 1) := by
  simp [rowResultTapes, finishTapes]

@[simp] theorem rowResult_accumulator (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .accumulator =
      (plan.flatMap (Emitter.commandBits (rowOperands table e) (rowRelation table e))).reverse ++
        base .accumulator := by
  simp [rowResultTapes, finishTapes, emittedTapes]

theorem rowResult_frame (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) (tape : Tape)
    (hi : tape ≠ .input) (ht : tape ≠ .tail) (hr : tape ≠ .reverseIndex)
    (hh : tape ≠ .head) (hs : tape ≠ .scanWork) (hx : tape ≠ .indexWork)
    (ha : tape ≠ .accumulator) (hc : tape ≠ .rowIndex) :
    rowResultTapes plan base table e rest tape = base tape := by
  simp only [rowResultTapes, finishTapes, emittedTapes, Function.update_of_ne hi,
    Function.update_of_ne ht, Function.update_of_ne hr, Function.update_of_ne hh,
    Function.update_of_ne ha, Function.update_of_ne hc]
  exact prepared_frame base table e rest tape hi ht hr hh hs hx

def guardRowInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (ambient : Ambient) (hinput : base .input ≠ []) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .guard, ((ambient, ()), none), base⟩
      (some ⟨some .startTail, ((ambient, ()), none), base⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program headerPlan plan .guard) _ _) = _
    cases hb : base .input with
    | nil => exact False.elim (hinput hb)
    | cons b bs => simp [program, guard, TM2.stepAux, hb]
  steps_le_m := Nat.le_refl _

def guardEndInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (ambient : Ambient) (hinput : base .input = []) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .guard, ((ambient, ()), none), base⟩
      (some ⟨some .reverseOutput, ((ambient, ()), none), base⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program headerPlan plan .guard) _ _) = _
    simp [program, guard, TM2.stepAux, hinput]
  steps_le_m := Nat.le_refl _

/-- All five unbounded operands remain isolated encoded naturals after the
row parser and head lookup, including both independently retrieved endpoints. -/
theorem prepared_operands (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool)
    (hn : base .vertices = encodeWord table.vertices)
    (hm : base .darts = encodeWord table.darts)
    (hr : base .rowIndex = encodeWord e.val)
    (ht : base .tail = []) :
    ∀ i, (Function.update (preparedTapes base table e rest) Tape.input rest) (source i) =
      encodeWord (rowOperands table e i) := by
  intro i
  fin_cases i
  · simpa [source, rowOperands, values] using
      prepared_frame base table e rest .vertices (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) |>.trans hn
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.darts = _
    simp only [Function.update_of_ne (show Tape.darts ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .darts (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hm
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.tail = _
    simp only [Function.update_of_ne (show Tape.tail ≠ Tape.input by decide), prepared_tail,
      ht, List.append_nil]
    rfl
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.head = _
    simp only [Function.update_of_ne (show Tape.head ≠ Tape.input by decide), prepared_head]
    rfl
  · change (Function.update (preparedTapes base table e rest) Tape.input rest) Tape.rowIndex = _
    simp only [Function.update_of_ne (show Tape.rowIndex ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .rowIndex (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hr

theorem rowOperands_bounded (table : GraphTables.Table) (e : Fin table.darts) :
    ∀ i, rowOperands table e i ≤ (GraphTables.tableBits table).length := by
  intro i
  fin_cases i
  · exact GraphTables.vertices_le_tableBits_length table
  · exact GraphTables.darts_le_tableBits_length table
  · exact table.rows[e].tail.isLt.le.trans (GraphTables.vertices_le_tableBits_length table)
  · exact table.rows[table.rows[e].reverseIndex].tail.isLt.le.trans
      (GraphTables.vertices_le_tableBits_length table)
  · exact e.isLt.le.trans (GraphTables.darts_le_tableBits_length table)

def rowTime (plan : Plan) (N : Nat) : Nat :=
  plan.length * (3 * (N + 1) + 3) + 12 * N + 15

/-- Run one complete stored row, including the actual table-based head lookup.
The only hypotheses describe the physical input tapes; no execution or
serialization correctness of a caller-provided body is assumed. -/
noncomputable def rowInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool)
    (hinput : base .input = encodeWords (GraphTables.rowWords table.rows[e]) ++ rest)
    (harchive : base .archive = GraphTables.tableBits table)
    (hn : base .vertices = encodeWord table.vertices)
    (hm : base .darts = encodeWord table.darts)
    (hrow : base .rowIndex = encodeWord e.val)
    (ht : base .tail = []) (hh : base .head = []) (hr : base .reverseIndex = [])
    (hscratch : base .scratch = []) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .startTail, ((ambient, ()), none), base⟩
      (some ⟨some .guard, ((rowRelation table e, ()), none),
        rowResultTapes plan base table e rest⟩)
      (rowTime plan (GraphTables.tableBits table).length) := by
  let parsed := endpointTapes base table.rows[e].tail.val table.rows[e].reverseIndex.val
    (rowRest table e rest)
  let ready := preparedTapes base table e rest
  let read := Function.update ready Tape.input rest
  let output := emittedTapes plan base table e rest
  let run₁ := endpointsInTime headerPlan plan base table.rows[e].tail.val
    table.rows[e].reverseIndex.val (rowRest table e rest)
    (by simpa [GraphTables.rowWords, encodeWords, List.append_assoc, rowRest] using hinput) ambient
  have parsed_archive : parsed .archive = GenericGraphTables.tableBits (genericTable table) := by
    simpa [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes] using harchive
  have parsed_reverse : parsed .reverseIndex =
      encodeWord (Lookup.headIndex (genericTable table) e).val := by
    simp [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes, hr]
  have parsed_head : parsed .head = [] := by
    simp [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes, hh]
  have parsed_scratch : parsed .scratch = [] := by
    simp [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes, hscratch]
  let run₂ := headPhaseInTime headerPlan plan parsed (genericTable table) e
    parsed_archive parsed_reverse parsed_head parsed_scratch ambient
  let run₃ := relationInTime headerPlan plan ready table.rows[e].relation rest
    (prepared_input base table e rest) ambient
  have read_operands : ∀ i, read (source i) = encodeWord (rowOperands table e i) :=
    prepared_operands base table e rest hn hm hrow ht
  have read_scratch : read .scratch = [] := by
    simp only [read, Function.update_of_ne (show Tape.scratch ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .scratch (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hscratch
  have read_acc : read .accumulator = base .accumulator := by
    simp only [read, Function.update_of_ne (show Tape.accumulator ≠ Tape.input by decide)]
    exact prepared_frame base table e rest .accumulator (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have run₄ : StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some (.row (Emitter.labelAt plan.length 36864 0 .entry)),
        ((rowRelation table e, ()), none), read⟩
      (some ⟨some .clearTail, ((rowRelation table e, ()), none), output⟩)
      (plan.length * (3 * ((GraphTables.tableBits table).length + 1) + 3) + 1) := by
    simpa only [read_acc, output, emittedTapes, read, ready] using
      emitInTime headerPlan plan read (rowOperands table e) read_operands read_scratch
        (rowRelation table e) (GraphTables.tableBits table).length (rowOperands_bounded table e)
  have output_tail : output .tail = encodeWord table.rows[e].tail.val := by
    simp [output, emittedTapes, prepared_tail, ht]
  have output_head : output .head = encodeWord table.rows[table.rows[e].reverseIndex].tail.val := by
    simp [output, emittedTapes, prepared_head]
  have output_reverse : output .reverseIndex = encodeWord table.rows[e].reverseIndex.val := by
    simp [output, emittedTapes, prepared_reverse, hr]
  have output_row : output .rowIndex = encodeWord e.val := by
    simp only [output, emittedTapes,
      Function.update_of_ne (show Tape.rowIndex ≠ Tape.accumulator by decide),
      Function.update_of_ne (show Tape.rowIndex ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .rowIndex (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hrow
  let run₅ := finishInTime headerPlan plan output table.rows[e].tail.val
    table.rows[table.rows[e].reverseIndex].tail.val table.rows[e].reverseIndex.val e.val
    output_tail output_head output_reverse output_row (rowRelation table e)
  let r₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  let r₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂ run₃
  let r₁₂₃₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂₃ run₄
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂₃₄ run₅
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have hb := run.steps_le_m
  have htbound := rowOperands_bounded table e 2
  have hhbound := rowOperands_bounded table e 3
  have hrbound := table.rows[e].reverseIndex.isLt.le.trans (GraphTables.darts_le_tableBits_length table)
  change table.rows[e].tail.val ≤ _ at htbound
  change table.rows[table.rows[e].reverseIndex].tail.val ≤ _ at hhbound
  simp only [Lookup.headTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, genericTable_tableBits] at hb
  unfold rowTime
  omega

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_FinalCNFStream
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Exact row enumeration and input/output stream identities for the concrete
final-CNF machine. Rows occur in stored order, including repeated rows.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable FinalCNFTableAdapter

/-- The actual unprocessed suffix of the finite table's stored row indices. -/
def remainingEvents (table : GraphTables.Table) (r : Nat) : List (Fin table.darts) :=
  (List.finRange table.darts).drop r

def inputStream (table : GraphTables.Table) (events : List (Fin table.darts)) : List Bool :=
  events.flatMap (fun e => encodeWords (GraphTables.rowWords table.rows[e]))

def outputStream (plan : Plan) (table : GraphTables.Table)
    (events : List (Fin table.darts)) : List Bool :=
  events.flatMap (fun e => plan.flatMap (Emitter.commandBits (rowOperands table e)
    (rowRelation table e)))

@[simp] theorem remainingEvents_zero (table : GraphTables.Table) :
    remainingEvents table 0 = List.finRange table.darts := by
  simp [remainingEvents]

@[simp] theorem remainingEvents_length (table : GraphTables.Table) (r : Nat) :
    (remainingEvents table r).length = table.darts - r := by
  simp [remainingEvents]

@[simp] theorem remainingEvents_done (table : GraphTables.Table) :
    remainingEvents table table.darts = [] := by
  simp [remainingEvents]

theorem remainingEvents_cons (table : GraphTables.Table) (r : Nat) (h : r < table.darts) :
    remainingEvents table r = ⟨r, h⟩ :: remainingEvents table (r + 1) := by
  unfold remainingEvents
  rw [List.drop_eq_getElem_cons (l := List.finRange table.darts) (i := r)
    (by simpa using h)]
  simp

@[simp] theorem inputStream_nil (table : GraphTables.Table) : inputStream table [] = [] := rfl

@[simp] theorem inputStream_cons (table : GraphTables.Table) (e : Fin table.darts)
    (events : List (Fin table.darts)) :
    inputStream table (e :: events) =
      encodeWords (GraphTables.rowWords table.rows[e]) ++ inputStream table events := rfl

@[simp] theorem inputStream_append (table : GraphTables.Table)
    (first rest : List (Fin table.darts)) :
    inputStream table (first ++ rest) = inputStream table first ++ inputStream table rest := by
  simp only [inputStream, List.flatMap_append]

@[simp] theorem outputStream_nil (plan : Plan) (table : GraphTables.Table) :
    outputStream plan table [] = [] := rfl

@[simp] theorem outputStream_cons (plan : Plan) (table : GraphTables.Table)
    (e : Fin table.darts) (events : List (Fin table.darts)) :
    outputStream plan table (e :: events) =
      plan.flatMap (Emitter.commandBits (rowOperands table e) (rowRelation table e)) ++
        outputStream plan table events := rfl

@[simp] theorem outputStream_append (plan : Plan) (table : GraphTables.Table)
    (first rest : List (Fin table.darts)) :
    outputStream plan table (first ++ rest) =
      outputStream plan table first ++ outputStream plan table rest := by
  simp only [outputStream, List.flatMap_append]

theorem inputStream_remaining_cons (table : GraphTables.Table) (r : Nat)
    (h : r < table.darts) :
    inputStream table (remainingEvents table r) =
      encodeWords (GraphTables.rowWords table.rows[(⟨r, h⟩ : Fin table.darts)]) ++
        inputStream table (remainingEvents table (r + 1)) := by
  rw [remainingEvents_cons table r h, inputStream_cons]

theorem outputStream_remaining_cons (plan : Plan) (table : GraphTables.Table) (r : Nat)
    (h : r < table.darts) :
    outputStream plan table (remainingEvents table r) =
      plan.flatMap (Emitter.commandBits (rowOperands table ⟨r, h⟩)
        (rowRelation table ⟨r, h⟩)) ++
          outputStream plan table (remainingEvents table (r + 1)) := by
  rw [remainingEvents_cons table r h, outputStream_cons]

theorem encodeWords_flatMap_rows {α : Type} (rows : List α) (words : α → List Nat) :
    encodeWords (rows.flatMap words) = rows.flatMap (fun row => encodeWords (words row)) := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem rowList_eq_finRange_map (table : GraphTables.Table) :
    GraphTables.rowList table = (List.finRange table.darts).map (fun e => table.rows[e]) := by
  rw [← List.ofFn_eq_map, ← Vector.toList_ofFn]
  change table.rows.toList = (Vector.ofFn (fun i => table.rows[i.val])).toList
  rw [Vector.ofFn_getElem]

/-- The stream starts at exactly the row suffix left by the checked header phase. -/
theorem inputStream_all (table : GraphTables.Table) :
    inputStream table (List.finRange table.darts) = tableRowsBits (genericTable table) := by
  rw [tableRowsBits, genericTable_rowList]
  erw [List.flatMap_map]
  have words : (fun row : GraphTables.DartRow table.vertices table.darts =>
      GenericGraphTables.rowWords (genericRow row)) = GraphTables.rowWords :=
    funext genericRow_words
  erw [words]
  rw [rowList_eq_finRange_map, List.flatMap_map, encodeWords_flatMap_rows]
  rfl

theorem inputStream_remaining_zero (table : GraphTables.Table) :
    inputStream table (remainingEvents table 0) = tableRowsBits (genericTable table) := by
  rw [remainingEvents_zero, inputStream_all]

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineProductGatherBoundsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds on the actual work stacks left by the preserving gather. These
bounds justify clearing the query/scan remnants after each product field;
they are consequences of the exact tape formulas, not runtime assumptions. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePreservingLookupClean

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

/-- Tape roles: 0 original table, 1 unary index, 2 working copy, 3 output,
4 copy/restore scratch. The embedded halt enters the explicit cleanup loop. -/
def statement (tape : Fin 5 → K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .run label => MachineSubroutine.statement (fun label => labels (.run label))
      (some (labels .cleanup)) (MachinePreservingLookup.program tape label)
  | .cleanup => MachineDrain.drain (tape 2) (labels .cleanup) exit

theorem steps_le (values : List Nat) (index value : Nat)
    (selected : values[index]? = some value) :
    steps values index ≤ 6 * (encodeWords values).length + 4 := by
  have hc := MachinePreservingLookup.preservingLookup_steps_le values index value selected
  have hd := remaining_length_le values index
  unfold steps
  omega

/-- Actual ambient-program execution. `code` fixes the concrete instructions
at each placed label; it does not assume any execution or semantic behavior.
The frame records an empty working copy at both endpoints. -/
theorem traceAt (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (code : ∀ label, target (labels label) = statement tape labels exit label)
    (base : K → List Bool) (values : List Nat)
    (tableWord : base (tape 0) = encodeWords values)
    (scratchEmpty : base (tape 4) = [])
    (index value : Nat) (selected : values[index]? = some value)
    (indexSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[steps values index]
      (some ⟨some (labels (.run .copyFirst)), (ambient, register),
        MachinePreservingLookup.initialTapes tape base index indexSuffix [] output⟩) =
      some ⟨exit, (ambient, none),
        MachinePreservingLookup.initialTapes tape base 0 indexSuffix []
          (encodeWord value ++ output)⟩ := by
  have hd (a b : Fin 5) (hne : a ≠ b) : tape a ≠ tape b :=
    fun h => hne (distinct h)
  have raw := MachinePreservingLookup.preservingLookupTrace tape distinct
    MachinePreservingLookup.Label.copyFirst MachinePreservingLookup.Label.copySecond
    MachinePreservingLookup.Label.lookup none (MachinePreservingLookup.program tape)
    rfl rfl (fun _ => rfl) base values tableWord scratchEmpty index value selected
    indexSuffix [] output ambient register
  have run := MachineSubroutine.trace (fun label => labels (.run label))
    (some (labels .cleanup)) (MachinePreservingLookup.program tape) target
    (fun label => code (.run label))
    (2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values index + 1)
    _ _ raw
  simp only [MachineSubroutine.configuration, MachineSubroutine.label] at run
  have cleanup := MachineDrain.drainTrace (tape 2) (labels .cleanup) exit target
    (code .cleanup)
    (MachinePreservingLookup.finalTapes tape base values index value indexSuffix [] output)
    (encodeWords (values.drop (index + 1))) ambient none
  have word : MachinePreservingLookup.finalTapes tape base values index value
      indexSuffix [] output (tape 2) = encodeWords (values.drop (index + 1)) := by
    simp only [MachinePreservingLookup.finalTapes,
      MachineLookup.tapes_source _ _ _ (hd 2 3 (by decide)), List.append_nil]
  have start : Function.update
      (MachinePreservingLookup.finalTapes tape base values index value indexSuffix [] output)
      (tape 2) (encodeWords (values.drop (index + 1))) =
      MachinePreservingLookup.finalTapes tape base values index value indexSuffix [] output := by
    rw [← word, Function.update_eq_self]
  have finish : Function.update
      (MachinePreservingLookup.finalTapes tape base values index value indexSuffix [] output)
      (tape 2) [] = MachinePreservingLookup.initialTapes tape base 0 indexSuffix []
        (encodeWord value ++ output) := by
    unfold MachinePreservingLookup.finalTapes MachinePreservingLookup.initialTapes
    rw [MachineLookup.update_source _ _ _ (hd 2 3 (by decide))]
  rw [start, finish] at cleanup
  rw [show steps values index =
      ((encodeWords (values.drop (index + 1))).length + 1) +
        (2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values index + 1) by
        unfold steps
        omega,
    Function.iterate_add_apply, run]
  exact cleanup

/-- The framing representation is the caller's exact tape state whenever its
index and work tape contain the specified index and an empty list. -/
theorem initialTapes_eq (tape : Fin 5 → K) (base : K → List Bool)
    (index : Nat) (indexSuffix : List Bool)
    (counterWord : base (tape 1) = encodeWord index ++ indexSuffix)
    (workEmpty : base (tape 2) = []) :
    MachinePreservingLookup.initialTapes tape base index indexSuffix [] (base (tape 3)) =
      base := by
  simp only [MachinePreservingLookup.initialTapes, MachineLookup.tapes,
    ← counterWord, ← workEmpty, Function.update_eq_self]

/-- A convenience interface starting from the caller's exact configuration. -/
theorem traceAt_fromTapes (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (code : ∀ label, target (labels label) = statement tape labels exit label)
    (base : K → List Bool) (values : List Nat)
    (tableWord : base (tape 0) = encodeWords values)
    (scratchEmpty : base (tape 4) = [])
    (index value : Nat) (selected : values[index]? = some value)
    (indexSuffix : List Bool)
    (counterWord : base (tape 1) = encodeWord index ++ indexSuffix)
    (workEmpty : base (tape 2) = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[steps values index]
      (some ⟨some (labels (.run .copyFirst)), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        MachinePreservingLookup.initialTapes tape base 0 indexSuffix []
          (encodeWord value ++ base (tape 3))⟩ := by
  have h := traceAt tape distinct labels exit target code base values tableWord scratchEmpty
    index value selected indexSuffix (base (tape 3)) ambient register
  rw [initialTapes_eq tape base index indexSuffix counterWord workEmpty] at h
  exact h

end UniqueGamesTheorem.Foundations.Complexity.MachinePreservingLookupClean

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_FinalCNFLoopLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

section

open Turing PCP PCP.AlphabetTable

structure LoopInvariant (table : GraphTables.Table) (r : Nat) (base : Tape → List Bool) : Prop where
  input : base .input = inputStream table (remainingEvents table r)
  archive : base .archive = GraphTables.tableBits table
  vertices : base .vertices = encodeWord table.vertices
  darts : base .darts = encodeWord table.darts
  index : base .rowIndex = encodeWord r
  tail : base .tail = []
  head : base .head = []
  reverse : base .reverseIndex = []
  scratch : base .scratch = []

structure LoopRun (headerPlan plan : Plan) (table : GraphTables.Table) (r remaining : Nat)
    (base : Tape → List Bool) (ambient : Ambient) where
  finalAmbient : Ambient
  finalTapes : Tape → List Bool
  execution : StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
    ⟨some .guard, ((ambient, ()), none), base⟩
    (some ⟨some .reverseOutput, ((finalAmbient, ()), none), finalTapes⟩)
    (remaining * (rowTime plan (GraphTables.tableBits table).length + 1) + 1)
  accumulator : finalTapes .accumulator =
    (outputStream plan table (remainingEvents table r)).reverse ++ base .accumulator
  output : finalTapes .output = base .output

theorem rowInvariant_succ (plan : Plan) (table : GraphTables.Table) (r : Nat)
    (hr : r < table.darts) (base : Tape → List Bool) (invariant : LoopInvariant table r base) :
    LoopInvariant table (r + 1)
      (rowResultTapes plan base table ⟨r, hr⟩
        (inputStream table (remainingEvents table (r + 1)))) := by
  constructor
  · exact rowResult_input _ _ _ _ _
  · exact (rowResult_frame _ _ _ _ _ .archive (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.archive
  · exact (rowResult_frame _ _ _ _ _ .vertices (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.vertices
  · exact (rowResult_frame _ _ _ _ _ .darts (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.darts
  · exact rowResult_index _ _ _ _ _
  · exact rowResult_tail _ _ _ _ _
  · exact rowResult_head _ _ _ _ _
  · exact rowResult_reverse _ _ _ _ _
  · exact (rowResult_frame _ _ _ _ _ .scratch (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.scratch

theorem rowWords_nonempty (table : GraphTables.Table) (e : Fin table.darts) :
    encodeWords (GraphTables.rowWords table.rows[e]) ≠ [] := by
  simp [GraphTables.rowWords, encodeWords, encodeWord]

/-- Induction follows the actual unary row counter and the actual unconsumed
input suffix. Every iteration invokes the checked row program. -/
noncomputable def loopInTime (headerPlan plan : Plan) (table : GraphTables.Table)
    (remaining : Nat) :
    ∀ (r : Nat), r + remaining = table.darts → ∀ (base : Tape → List Bool)
      (ambient : Ambient), LoopInvariant table r base →
        LoopRun headerPlan plan table r remaining base ambient := by
  induction remaining with
  | zero =>
      intro r hcount base ambient invariant
      have hr : r = table.darts := by omega
      have hinput : base .input = [] := by
        simpa only [hr, remainingEvents_done, inputStream_nil] using invariant.input
      refine {
        finalAmbient := ambient
        finalTapes := base
        execution := ?_
        accumulator := ?_
        output := rfl }
      · simpa only [Nat.zero_mul, Nat.zero_add] using
          guardEndInTime headerPlan plan base ambient hinput
      · simp only [hr, remainingEvents_done, outputStream_nil, List.reverse_nil, List.nil_append]
  | succ remaining ih =>
      intro r hcount base ambient invariant
      have hr : r < table.darts := by omega
      let e : Fin table.darts := ⟨r, hr⟩
      let rest := inputStream table (remainingEvents table (r + 1))
      let next := rowResultTapes plan base table e rest
      have hinput : base .input = encodeWords (GraphTables.rowWords table.rows[e]) ++ rest := by
        rw [invariant.input, inputStream_remaining_cons table r hr]
      have hnonempty : base .input ≠ [] := by
        rw [hinput]
        exact List.append_ne_nil_of_left_ne_nil (rowWords_nonempty table e) rest
      let guardRun := guardRowInTime headerPlan plan base ambient hnonempty
      let rowRun := rowInTime headerPlan plan base table e rest hinput invariant.archive
        invariant.vertices invariant.darts invariant.index invariant.tail invariant.head
        invariant.reverse invariant.scratch ambient
      let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guardRun rowRun
      let later := ih (r + 1) (by omega) next (rowRelation table e)
        (rowInvariant_succ plan table r hr base invariant)
      let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first later.execution
      refine {
        finalAmbient := later.finalAmbient
        finalTapes := later.finalTapes
        execution := { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
        accumulator := ?_
        output := ?_ }
      · have hb := run.steps_le_m
        rw [Nat.succ_mul]
        omega
      · rw [later.accumulator, outputStream_remaining_cons plan table r hr]
        simp only [next, rowResult_accumulator, List.reverse_append, List.append_assoc]
        rfl
      · rw [later.output]
        exact rowResult_frame _ _ _ _ _ .output (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)

end

/-!
The complete actual output-producing trace of the final CNF machine. Its
terminal configuration still contains private work tapes; FinalCNFCleanup
supplies the subsequent canonical halt required by the machine interface.
-/

open Turing PCP PCP.AlphabetTable FinalCNFTableAdapter

def emittedBytes (plan : Plan) (table : GraphTables.Table) : List Bool :=
  encodeWords [6 * table.vertices + 36864 * table.darts, 40960 * table.darts] ++
    outputStream plan table (List.finRange table.darts)

noncomputable def rawBudget (plan : Plan) (table : GraphTables.Table) : Nat :=
  headerTimePolynomial.eval (GraphTables.tableBits table).length +
    table.darts * (rowTime plan (GraphTables.tableBits table).length + 1) + 1 +
      (emittedBytes plan table).length + 1

structure RawRun (plan : Plan) (table : GraphTables.Table) where
  finalAmbient : Ambient
  finalTapes : Tape → List Bool
  execution : StateTransition.EvalsToInTime (machine headerPlan plan).step
    (initList (machine headerPlan plan) (GraphTables.tableBits table))
    (some ⟨none, ((finalAmbient, ()), none), finalTapes⟩) (rawBudget plan table)
  output : finalTapes .output = emittedBytes plan table

theorem header_loopInvariant (table : GraphTables.Table) :
    LoopInvariant table 0 (headerResultTapes table.vertices table.darts
      (tableRowsBits (genericTable table))) := by
  constructor
  · rw [headerResultTapes_input, inputStream_remaining_zero]
  · rw [headerResultTapes_archive]
    exact (tableBits_header_rows (genericTable table)).symm.trans (genericTable_tableBits table)
  · rfl
  · rfl
  · exact headerResultTapes_rowIndex _ _ _
  · rfl
  · rfl
  · rfl
  · rfl

/-- The input is read from the genuine `initList` configuration. Header, every
row, final guard, and reversal are all actual transitions of this one program. -/
noncomputable def rawRun (plan : Plan) (table : GraphTables.Table) : RawRun plan table := by
  let base := headerResultTapes table.vertices table.darts (tableRowsBits (genericTable table))
  let ambient : Ambient := ((), fun _ => false)
  have headerRun : StateTransition.EvalsToInTime (machine headerPlan plan).step
      (initList (machine headerPlan plan) (GraphTables.tableBits table))
      (some ⟨some .guard, ((ambient, ()), none), base⟩)
      (headerTimePolynomial.eval (GraphTables.tableBits table).length) := by
    simpa only [genericTable_tableBits, genericTable_vertices, genericTable_darts, base, ambient]
      using initializedTableHeaderInTime plan (genericTable table)
  let loop := loopInTime headerPlan plan table table.darts 0 (by omega)
    base ambient (header_loopInvariant table)
  have acc : loop.finalTapes .accumulator = (emittedBytes plan table).reverse := by
    rw [loop.accumulator]
    simp only [remainingEvents_zero, base, headerResultTapes_accumulator, emittedBytes,
      List.reverse_append]
  have out : loop.finalTapes .output = [] := by
    rw [loop.output]
    rfl
  let finalTapes := Reduction.MachineTransfer.tapesAt Tape.accumulator Tape.output
    loop.finalTapes [] (emittedBytes plan table)
  have finish : StateTransition.EvalsToInTime (machine headerPlan plan).step
      ⟨some .reverseOutput, ((loop.finalAmbient, ()), none), loop.finalTapes⟩
      (some ⟨none, ((loop.finalAmbient, ()), none), finalTapes⟩)
      ((emittedBytes plan table).length + 1) := by
    have run := Reduction.MachineTransfer.transferAtInTime Tape.accumulator Tape.output
      (by decide) id false .reverseOutput none (program headerPlan plan) rfl
      loop.finalTapes (loop.finalAmbient, ()) none
    simpa only [acc, out, List.reverse_reverse, List.length_reverse, List.map_id,
      List.append_nil, finalTapes, machine, FinTM2.step] using! run
  let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ headerRun loop.execution
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first finish
  exact {
    finalAmbient := loop.finalAmbient
    finalTapes := finalTapes
    execution := {
      toEvalsTo := run.toEvalsTo
      steps_le_m := by
        have hb := run.steps_le_m
        unfold rawBudget
        omega }
    output := by simp [finalTapes, Reduction.MachineTransfer.tapesAt] }

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

def affinePlan {σ : Type} {bound : Nat} (coefficient : Nat) (offset : σ → Fin bound) :
    Fin 3 → PCP.AlphabetTable.Emitter.Command 1 σ bound :=
  PCP.AlphabetTable.Emitter.listCommands
    (PCP.AlphabetTable.Emitter.affineCommands [(0, coefficient)] offset)

def firstPlan (ρ : Type) (d : Nat) :
    Fin 3 → PCP.AlphabetTable.Emitter.Command 1 (Ambient ρ d × Fin (degree d)) (degree d) :=
  affinePlan (degree d) (fun s => firstOffset s.1.2)

def secondPlan (ρ : Type) (d : Nat) :
    Fin 3 → PCP.AlphabetTable.Emitter.Command 1 (Ambient ρ d × Fin (degree d)) (degree d) :=
  affinePlan (degree d) (fun s => secondOffset s.1.2)

def outputPlan (ρ : Type) (d : Nat) :
    Fin 3 → PCP.AlphabetTable.Emitter.Command 1 (Ambient ρ d × Fin (degree d)) (rowFactor d) :=
  affinePlan (rowFactor d) (fun s => outputOffset s.1.2)

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

/-- Every branch is a concrete finite TM2 statement. The fixed table `H`
is evaluated only on finite control values, never on an unbounded tape value. -/
def statement {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (labels : Label d → Λ) (exit : Option Λ) :
    Label d → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d)
  | .initialize_ =>
    .push (ports .quotientFirst) (fun _ => false)
      (.push (ports .quotientSecond) (fun _ => false)
        (.push (ports .remainderFirst) (fun _ => false)
          (.push (ports .remainderSecond) (fun _ => false)
            (.load (fun s => (s.1, none))
              (.goto fun _ => labels (.firstEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry)))))))
  | .firstEmit l =>
    PCP.AlphabetTable.Emitter.statement (firstPlan ρ d) (fun _ => ports .inputVertex)
      (ports .emitScratch) (ports .queryReverse) (fun k => labels (.firstEmit k))
      (some (labels .firstReverse)) l
  | .firstReverse =>
    Reduction.MachineTransfer.loopAt (ports .queryReverse) (ports .queryIndex)
      id false (labels .firstReverse)
      (some (labels (.firstLookup (.run .copyFirst))))
  | .firstLookup l =>
    MachinePreservingLookupClean.statement (ports ∘ lookupTape)
      (fun k => labels (.firstLookup k)) (some (labels .firstScan)) l
  | .firstScan =>
    MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.scanLoop (degree d) (Nat.mul_pos positive positive)
        (ports .lookupOutput) (ports .quotientFirst) (labels .firstScan)
        (fun r => labels (.firstResidue r)))
  | .firstResidue r =>
    MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.emitterWithFinish (degree d) (Nat.mul_pos positive positive)
        (ports .remainderFirst) (some (labels .clearQuery)) firstFinish r)
  | .clearQuery =>
    .pop (ports .queryIndex) (fun s _ => s)
      (.pop (ports .lookupOutput) (fun s _ => s)
        (.goto fun _ => labels (.secondEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))))
  | .secondEmit l =>
    PCP.AlphabetTable.Emitter.statement (secondPlan ρ d) (fun _ => ports .quotientFirst)
      (ports .emitScratch) (ports .queryReverse) (fun k => labels (.secondEmit k))
      (some (labels .secondReverse)) l
  | .secondReverse =>
    Reduction.MachineTransfer.loopAt (ports .queryReverse) (ports .queryIndex)
      id false (labels .secondReverse)
      (some (labels (.secondLookup (.run .copyFirst))))
  | .secondLookup l =>
    MachinePreservingLookupClean.statement (ports ∘ lookupTape)
      (fun k => labels (.secondLookup k)) (some (labels .secondScan)) l
  | .secondScan =>
    MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.scanLoop (degree d) (Nat.mul_pos positive positive)
        (ports .lookupOutput) (ports .quotientSecond) (labels .secondScan)
        (fun r => labels (.secondResidue r)))
  | .secondResidue r =>
    MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.emitterWithFinish (degree d) (Nat.mul_pos positive positive)
        (ports .remainderSecond)
        (some (labels (.outputEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))))
        (secondFinish H) r)
  | .outputEmit l =>
    PCP.AlphabetTable.Emitter.statement (outputPlan ρ d) (fun _ => ports .quotientSecond)
      (ports .emitScratch) (ports .output) (fun k => labels (.outputEmit k))
      (some (labels (.cleanup 0))) l
  | .cleanup i =>
    MachineDrain.drain (ports (dirtyTape i)) (labels (.cleanup i))
      (some (if hi : i.val + 1 < 6 then labels (.cleanup ⟨i.val + 1, hi⟩) else labels .done))
  | .done => Reduction.MachineTransfer.exitAt (ports .output) exit

def program {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d) :
    Label d → TM2.Stmt (fun _ : Tape => Bool) (Label d) (State ρ d) :=
  statement positive H id id none

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceOccurrences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Executable radix numbering of padded global long-code tables and an ordered
equation occurrence list. The code enumerates random tapes, not distinct
equations: coinciding equations and repeated variable occurrences are retained.
-/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences

open UniqueGamesTheorem.Reduction.CloneGap
open scoped BigOperators

section ConcreteSource

open SourceContexts
open UniqueGamesTheorem.Reduction.FiniteNoise

/-- A satisfiable totalization for the empty input formula, without changing
or diluting the occurrence list of a nonempty formula. -/
def emptyFormulaEquation (F : Target.Formula) (u : ℕ) : Equation (Fin (nBits F u)) :=
  ⟨dummyIndex F u, dummyIndex F u, dummyIndex F u, false⟩

def sourceList (F : Target.Formula) (u D : ℕ) : List (Equation (Fin (nBits F u))) :=
  if F.clauses.isEmpty then [emptyFormulaEquation F u] else rawSourceList F u D

theorem sourceList_empty (F : Target.Formula) (u D : ℕ) (h : F.clauses = []) :
    sourceList F u D = [emptyFormulaEquation F u] := by simp [sourceList, h]

theorem sourceList_nonempty (F : Target.Formula) (u D : ℕ) (h : F.clauses ≠ []) :
    sourceList F u D = rawSourceList F u D := by
  unfold sourceList
  rw [List.isEmpty_eq_false_iff.mpr h]
  rfl

theorem sourceList_ne_nil (F : Target.Formula) (u D : ℕ) (hD : 0 < D) :
    sourceList F u D ≠ [] := by
  by_cases h : F.clauses = []
  · rw [sourceList_empty F u D h]
    simp
  · rw [sourceList_nonempty F u D h]
    apply List.length_pos_iff.mp
    rw [rawSourceList_length]
    have hc : 0 < F.clauses.length := List.length_pos_iff.mpr h
    positivity

def sourceInput (F : Target.Formula) (u D : ℕ) (hD : 0 < D) :
    UniqueGamesTheorem.Reduction.SourceEncoding.Input :=
  ⟨nBits F u, sourceList F u D, sourceList_ne_nil F u D hD⟩

end ConcreteSource

end UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceContextLoad
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! A shared-arena context loader. Its finite program copies each selected
clause index, executes the checked lookup, and clears consumed scratch tapes.
Tuple digits and arbitrary extra tapes are protected throughout. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad

open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineComposition

variable {u : Nat} {Extra : Type}

variable [DecidableEq Extra]

def stageTapes (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) : Nat → Tape u Extra → List Bool
  | 0 => base
  | r + 1 => if h : r < u then
      coordinateOutput ⟨r, h⟩ F.clauses[(tuple ⟨r, h⟩).val] (stageTapes F tuple base r)
    else stageTapes F tuple base r

omit [DecidableEq Extra] in
theorem stageTapes_frame (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (r : Nat) (p : Tape u Extra)
    (hi : p ≠ .index) (hw : p ≠ .work) (hf : ∀ j s, p ≠ .field j s) :
    stageTapes F tuple base r p = base p := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [stageTapes]
    split
    · cases p <;> simp_all [coordinateOutput]
    · exact ih

end UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceDescriptorEmissionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.slotFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Emit one fixed descriptor equation from three preserved unary base registers.
The output order is first address, second address, third address, RHS. The actual
stack program emits those fields in reverse order. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceProfileBridge

open Target SourceContexts SourceOccurrences SourceLocalSignature
open Complexity

def positionEncoding (u : ℕ) : Encoding (Position u) :=
  (Encoding.fin u).prod slotEncoding

end UniqueGamesTheorem.Foundations.Hastad.SourceProfileBridge

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceSignaturePrepareLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.slotFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceSignaturePrepare

open Turing
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge
open UniqueGamesTheorem.Foundations.Complexity

abbrev Width (u : ℕ) := (positionEncoding u).size
abbrev Arena (u : ℕ) (Extra : Type) := SourceContextLoad.Tape u Extra
abbrev ProfileState (u : ℕ) := MachineCompare.State (MachineFieldProfile.Profile (Width u))
abbrev State (u : ℕ) (τ : Type) := ProfileState u × (Signature u × τ)

variable {u : ℕ} {Extra τ : Type}

def variableField (p : Position u) : Arena u Extra :=
  SourceContextLoad.variableField p.1 (slotEncoding.code p.2)

def place : MachineFieldProfile.Tape (Width u) → Arena u Extra
  | .inl i => variableField ((positionEncoding u).code.symm i)
  | .inr w => if w = 0 then .index else if w = 1 then .work else .scratch

def unplace : Arena u Extra → Option (MachineFieldProfile.Tape (Width u))
  | .index => some (.inr 0)
  | .work => some (.inr 1)
  | .scratch => some (.inr 2)
  | .field t s =>
    if s = 0 then some (.inl ((positionEncoding u).code (t, .first)))
    else if s = 2 then some (.inl ((positionEncoding u).code (t, .second)))
    else if s = 4 then some (.inl ((positionEncoding u).code (t, .third))) else none
  | _ => none

@[simp] theorem unplace_place (k : MachineFieldProfile.Tape (Width u)) :
    unplace (place (Extra := Extra) k) = some k := by
  cases k with
  | inl i =>
    obtain ⟨p, rfl⟩ := (positionEncoding u).code.surjective i
    rcases p with ⟨t, s⟩
    simp only [place, Equiv.symm_apply_apply]
    cases s <;> rfl
  | inr w =>
    obtain ⟨w, hw⟩ := w
    have h : w = 0 ∨ w = 1 ∨ w = 2 := by omega
    rcases h with rfl | rfl | rfl <;> rfl

theorem place_unplace (a : Arena u Extra) (k : MachineFieldProfile.Tape (Width u))
    (h : unplace a = some k) : place k = a := by
  cases a with
  | formula => simp [unplace] at h
  | index => cases Option.some.inj h; rfl
  | work => cases Option.some.inj h; rfl
  | scratch => cases Option.some.inj h; rfl
  | copyScratch => simp [unplace] at h
  | current t => simp [unplace] at h
  | remaining t => simp [unplace] at h
  | extra e => simp [unplace] at h
  | field t s =>
    by_cases h0 : s = 0
    · subst s
      simp only [unplace, ↓reduceIte] at h
      cases Option.some.inj h
      simp only [place, Equiv.symm_apply_apply]
      rfl
    · by_cases h2 : s = 2
      · subst s
        simp only [unplace, ↓reduceIte] at h
        cases Option.some.inj h
        simp only [place, Equiv.symm_apply_apply]
        rfl
      · by_cases h4 : s = 4
        · subst s
          simp only [unplace, ↓reduceIte] at h
          cases Option.some.inj h
          simp only [place, Equiv.symm_apply_apply]
          rfl
        · simp [unplace, h0, h2, h4] at h

def fill (base : Arena u Extra → List Bool)
    (localTapes : MachineFieldProfile.Tape (Width u) → List Bool) : Arena u Extra → List Bool :=
  fun a => match unplace a with
    | some k => localTapes k
    | none => base a

@[simp] theorem fill_place (base : Arena u Extra → List Bool)
    (localTapes : MachineFieldProfile.Tape (Width u) → List Bool)
    (k : MachineFieldProfile.Tape (Width u)) : fill base localTapes (place k) = localTapes k := by
  simp only [fill, unplace_place]

@[simp] theorem fill_self (base : Arena u Extra → List Bool) :
    fill base (base ∘ place) = base := by
  funext a
  cases h : unplace a with
  | none => simp only [fill, h]
  | some k =>
    simp only [fill, h, Function.comp_apply, place_unplace a k h]

end UniqueGamesTheorem.Foundations.Hastad.SourceSignaturePrepare

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContextPrepare

open Turing UniqueGamesTheorem.Foundations.Complexity
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge

abbrev PrepareState (u : Nat) (τ : Type) := SourceSignaturePrepare.State u τ
abbrev State (u : Nat) (τ : Type) := LoadState × PrepareState u τ

variable {u : Nat} {Extra τ : Type}

variable [DecidableEq Extra]

def initialState (initialProfile : MachineFieldProfile.Profile (SourceSignaturePrepare.Width u))
    (initial : Signature u) (ambient : τ) : State u τ :=
  (((), none), (MachineFieldProfile.normalState initialProfile, (initial, ambient)))

end UniqueGamesTheorem.Foundations.Hastad.SourceContextPrepare

/-! The actual numbered equation list has exactly the acceptance bounded by
the private Fourier decoder. Only the repeated base-game value is an input
here; list semantics and all finite sampling laws are supplied. -/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceHeaderAccumulate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate

open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

theorem trace (layout : Layout K) (labels : Bool → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = statement layout labels exit l)
    (base : K → List Bool) (nBits count : Nat)
    (hbits : base layout.bits = encodeWord nBits)
    (hcount : base layout.count = encodeWord count) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[nBits + count + 4]
      (some ⟨some (labels false), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), resultTapes layout base nBits count⟩ := by
  let middle := tapesAt layout.bits layout.accumulator base []
    ((encodeWord nBits).reverse ++ base layout.accumulator)
  have firstRun := transferAt_fromTapes layout.bits layout.accumulator layout.bits_accumulator
    id false (labels false) (some (labels true)) program (by simpa only [statement] using atLabels false) base ambient register
  change (advance (TM2.step program))^[(base layout.bits).length + 1]
    (some ⟨some (labels false), (ambient, register), base⟩) = _ at firstRun
  simp only [hbits, List.map_id, encodeWord_length] at firstRun
  have hc : middle layout.count = encodeWord count := by
    dsimp only [middle]
    rw [tapesAt_other _ _ _ layout.bits_count.symm layout.count_accumulator]
    exact hcount
  have ha : middle layout.accumulator =
      (encodeWord nBits).reverse ++ base layout.accumulator := by
    exact tapesAt_dst _ _ _ _ _
  have secondRun := transferAt_fromTapes layout.count layout.accumulator layout.count_accumulator
    id false (labels true) exit program (by simpa only [statement] using atLabels true) middle ambient none
  change (advance (TM2.step program))^[(middle layout.count).length + 1]
    (some ⟨some (labels true), (ambient, none), middle⟩) = _ at secondRun
  simp only [hc, ha, List.map_id, encodeWord_length] at secondRun
  have he : tapesAt layout.count layout.accumulator middle []
      ((encodeWord count).reverse ++ ((encodeWord nBits).reverse ++ base layout.accumulator)) =
      resultTapes layout base nBits count := by
    funext k
    by_cases hk : k = layout.accumulator
    · subst k
      simp [resultTapes, tapesAt, encodeWords, List.reverse_append, List.append_assoc]
    · by_cases hc : k = layout.count
      · subst k; simp [tapesAt, resultTapes, layout.count_accumulator]
      · by_cases hb : k = layout.bits
        · subst k
          simp [middle, tapesAt, resultTapes, layout.bits_count, layout.bits_accumulator]
        · simp [middle, tapesAt, resultTapes, hk, hc, hb]
  rw [he] at secondRun
  rw [show nBits + count + 4 = (count + 1 + 1) + (nBits + 1 + 1) by omega,
    Function.iterate_add_apply, firstRun]
  exact secondRun

def inTime (layout : Layout K) (labels : Bool → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = statement layout labels exit l)
    (base : K → List Bool) (nBits count : Nat)
    (hbits : base layout.bits = encodeWord nBits)
    (hcount : base layout.count = encodeWord count) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels false), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), resultTapes layout base nBits count⟩)
      (nBits + count + 4) where
  steps := nBits + count + 4
  evals_in_steps := trace layout labels exit program atLabels base nBits count hbits hcount ambient register
  steps_le_m := Nat.le_refl _

@[simp] theorem inTime_steps (layout : Layout K) (labels : Bool → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = statement layout labels exit l)
    (base : K → List Bool) (nBits count : Nat)
    (hbits : base layout.bits = encodeWord nBits)
    (hcount : base layout.count = encodeWord count) (ambient : σ) (register : Option Bool) :
    (inTime layout labels exit program atLabels base nBits count hbits hcount ambient register).steps =
      nBits + count + 4 := rfl

end UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceQueryOrderLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.slotFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeModel

open Turing Complexity SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge


abbrev QueryMetadata (u : Nat) := SourceContextPrepare.LoadState ×
  (SourceSignaturePrepare.ProfileState u × (Signature u × ArithmeticState))

variable {u D : Nat} {Extra : Type}

def canonicalSignature (u : Nat) : Signature u :=
  ⟨fun _ => false, fun _ _ => false, fun _ => .first⟩

end UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeModel



end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceTupleBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! One actual clause-tuple body. Its fixed finite control loads the context,
computes the shared right address base, traverses every selected-slot tuple and
query tape in their declared encoding order, and physically clears its work.
-/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceTupleBody

open Turing Complexity SourceContexts SourceOccurrences SourceLocalSignature
open SourceRuntimeModel SourceTupleTape


abbrev SlotCount (u : Nat) := (slotContextEncoding u).size

variable {u D : Nat} {Extra : Type}

def selected (index : Fin (SlotCount u)) : SlotContext u :=
  (slotContextEncoding u).code.symm index

end UniqueGamesTheorem.Foundations.Hastad.SourceTupleBody

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_FinalCNFOutputLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
The final machine's complete output stream is the exact serialization of its
actual formula. This identity includes the two size fields, every clause and
literal field, and all unary delimiters. No desired output equality is assumed.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

open PCP

theorem rowTimePolynomial_eval (N : Nat) :
    rowTimePolynomial.eval N = rowTime rowPlan N := by
  simp only [rowTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, rowTime, rowPlan_length]

/-- Header, at most `N` rows with guards, and the final output reversal. -/
noncomputable def phaseTimePolynomial : Polynomial Nat :=
  headerTimePolynomial +
    (Polynomial.X * (rowTimePolynomial + Polynomial.C 1) + Polynomial.C 1) +
    (FinalTableFormula.sizePolynomial + Polynomial.C 1)

theorem phaseTimePolynomial_eval (N : Nat) :
    phaseTimePolynomial.eval N =
      headerTimePolynomial.eval N + (N * (rowTime rowPlan N + 1) + 1) +
        (FinalTableFormula.sizePolynomial.eval N + 1) := by
  simp only [phaseTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, rowTimePolynomial_eval]

theorem phaseTime_le {N rows outputLength : Nat} (rowBound : rows ≤ N)
    (outputBound : outputLength ≤ FinalTableFormula.sizePolynomial.eval N) :
    headerTimePolynomial.eval N + (rows * (rowTime rowPlan N + 1) + 1) +
      (outputLength + 1) ≤ phaseTimePolynomial.eval N := by
  have hrows := Nat.mul_le_mul_right (rowTime rowPlan N + 1) rowBound
  rw [phaseTimePolynomial_eval]
  omega

/-- Twelve private stacks are drained, then the finite state is reset.
`C` is the fixed maximum number of pushes in a raw-program transition. -/
noncomputable def finalTimePolynomial (C : Nat) : Polynomial Nat :=
  phaseTimePolynomial + Polynomial.C 12 *
    (Polynomial.X + phaseTimePolynomial * Polynomial.C C + Polynomial.C 1) + Polynomial.C 1

theorem finalTimePolynomial_eval (C N : Nat) :
    (finalTimePolynomial C).eval N = phaseTimePolynomial.eval N +
      12 * (N + phaseTimePolynomial.eval N * C + 1) + 1 := by
  simp only [finalTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

/-!
The complete polynomial-time machine certificate for converting a validated
64-label graph table into its actual 3CNF formula. The proof composes the real
input parser, all row executions, output reversal, and private-tape cleanup.
-/

open Turing


end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineCanonicalOutputLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Canonical output for finite Boolean machines

A raw machine may halt with retained metadata and a changed finite state.
This wrapper redirects its halt to a fixed list of actual tape drains, then
executes one state-reset instruction. The output tape is preserved and the
result is literally `haltList`. Its cost follows from the raw execution and
the maximum number of pushes in a raw statement.

The cleanup list is fixed with the program, not selected from the input.
It may contain repetitions and may be empty when output is the only tape.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype σ]

def completedProgram (P : Program K Λ σ) (chosen : List K) :
    Label Λ chosen → TM2.Stmt (fun _ : K => Bool) (Label Λ chosen) (σ × Option Bool)
  | .inl label => extendedStmt Sum.inl (cleanupEntry chosen) (P.code label)
  | .inr (.inl label) => MachineDrainMany.instruction chosen (cleanupLabel chosen)
      (some (resetLabel chosen)) label
  | .inr (.inr _) => .load (fun _ => (P.initial, none)) .halt

/-- A fixed finite program over the same Boolean tapes as the raw machine. -/
def completedMachine (P : Program K Λ σ) (chosen : List K) : FinTM2 where
  K := K
  k₀ := P.input
  k₁ := P.output
  Γ _ := Bool
  Λ := Label Λ chosen
  main := .inl P.main
  σ := σ × Option Bool
  initialState := (P.initial, none)
  m := completedProgram P chosen

theorem finiteAlphabet (P : Program K Λ σ) (chosen : List K) :
    MachineFiniteAlphabet.FiniteAlphabet (completedMachine P chosen) := by
  intro k
  exact inferInstanceAs (Finite Bool)

def embeddedCfg (P : Program K Λ σ) (chosen : List K)
    (cfg : (sourceMachine P).Cfg) : (completedMachine P chosen).Cfg :=
  extendedCfg Sum.inl (cleanupEntry chosen) none cfg

theorem step_simulation (P : Program K Λ σ) (chosen : List K)
    (a b : (sourceMachine P).Cfg) (step : (sourceMachine P).step a = some b) :
    (completedMachine P chosen).step (embeddedCfg P chosen a) =
      some (embeddedCfg P chosen b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => simp [FinTM2.step, TM2.step] at step
    | some label =>
      have hb : TM2.stepAux (P.code label) state tapes = b := Option.some.inj step
      rw [← hb]
      change some (TM2.stepAux
        (extendedStmt Sum.inl (cleanupEntry chosen) (P.code label)) (state, none) tapes) = _
      erw [stepAux_extended]
      rfl

@[simp] theorem embedded_init (P : Program K Λ σ) (chosen : List K) (input : List Bool) :
    embeddedCfg P chosen (initList (sourceMachine P) input) =
      initList (completedMachine P chosen) input := rfl

omit [Fintype K] [Fintype Λ] [Fintype σ] in
theorem finalTapes_eq (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output) (base : K → List Bool) :
    MachineDrainMany.finalTapes chosen base =
      MachineDrainMany.haltTapes P.output (base P.output) := by
  funext k
  rw [MachineDrainMany.finalTapes_apply]
  by_cases h : k = P.output
  · subst k
    simp [MachineDrainMany.haltTapes, complete]
  · simp [MachineDrainMany.haltTapes, complete, h]

theorem haltList_eq (P : Program K Λ σ) (chosen : List K) (output : List Bool) :
    haltList (completedMachine P chosen) output =
      ⟨none, (P.initial, none), MachineDrainMany.haltTapes P.output output⟩ := by
  congr 1

/-- The cleanup path consists of actual drains and one physical state reset. -/
def cleanupExecution (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output) (state : σ)
    (register : Option Bool) (base : K → List Bool) :
    StateTransition.EvalsToInTime (completedMachine P chosen).step
      ⟨cleanupEntry chosen, (state, register), base⟩
      (some (haltList (completedMachine P chosen) (base P.output)))
      (MachineDrainMany.steps chosen base + 1) := by
  let after : (completedMachine P chosen).Cfg :=
    ⟨some (resetLabel chosen), (state, MachineDrainMany.finalRegister chosen register),
      MachineDrainMany.finalTapes chosen base⟩
  have drains : StateTransition.EvalsToInTime (completedMachine P chosen).step
      ⟨cleanupEntry chosen, (state, register), base⟩ (some after)
      (MachineDrainMany.steps chosen base) := {
    steps := MachineDrainMany.steps chosen base
    evals_in_steps := MachineDrainMany.trace chosen (cleanupLabel chosen)
      (some (resetLabel chosen)) (completedProgram P chosen) (fun _ => rfl) base state register
    steps_le_m := le_rfl }
  have reset : StateTransition.EvalsToInTime (completedMachine P chosen).step
      after (some (haltList (completedMachine P chosen) (base P.output))) 1 := {
    steps := 1
    evals_in_steps := by
      change some (⟨none, (P.initial, none), MachineDrainMany.finalTapes chosen base⟩ :
          (completedMachine P chosen).Cfg) =
        some (haltList (completedMachine P chosen) (base P.output))
      erw [finalTapes_eq P chosen complete, haltList_eq]
      rfl
    steps_le_m := le_rfl }
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans _ (MachineDrainMany.steps chosen base) 1
      _ after _ drains reset

/-- No assumption about cleanup execution or clean raw work tapes is required. -/
def outputsInTime (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output)
    (input output : List Bool) (state : σ) (base : K → List Bool) (budget : Nat)
    (raw : StateTransition.EvalsToInTime (sourceMachine P).step
      (initList (sourceMachine P) input) (some ⟨none, state, base⟩) budget)
    (correctOutput : base P.output = output) :
    TM2OutputsInTime (completedMachine P chosen) input (some output)
      (budget + chosen.length *
        (input.length + budget * Runtime.programPushBound (sourceMachine P) + 1) + 1) := by
  let lifted := liftExecutionInTime (sourceMachine P).step
    (completedMachine P chosen).step (embeddedCfg P chosen) (step_simulation P chosen) raw
  have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ lifted
    (cleanupExecution P chosen complete state none base)
  have stackBound : ∀ k, (base k).length ≤
      input.length + budget * Runtime.programPushBound (sourceMachine P) := by
    intro k
    have h := Runtime.executionSizeBound (sourceMachine P).step
      (fun cfg => (cfg.stk k).length) (Runtime.programPushBound (sourceMachine P))
      (Runtime.stepStackLength (sourceMachine P) k) raw
    exact h.trans (Nat.add_le_add_right (Runtime.initialStackLength (sourceMachine P) input k) _)
  have cleanupBound := MachineDrainMany.steps_le_uniform chosen base _ stackBound
  rw [embedded_init, correctOutput] at joined
  exact { toEvalsTo := joined.toEvalsTo
          steps_le_m := joined.steps_le_m.trans (by omega) }

noncomputable def completedTime (P : Program K Λ σ) (chosen : List K)
    (rawTime : Polynomial Nat) : Polynomial Nat :=
  rawTime + Polynomial.C chosen.length *
    (Polynomial.X + rawTime * Polynomial.C (Runtime.programPushBound (sourceMachine P)) + 1) + 1

theorem completedTime_eval (P : Program K Λ σ) (chosen : List K)
    (rawTime : Polynomial Nat) (n : Nat) :
    (completedTime P chosen rawTime).eval n =
      rawTime.eval n + chosen.length *
        (n + rawTime.eval n * Runtime.programPushBound (sourceMachine P) + 1) + 1 := by
  simp [completedTime]

/-- An actual raw terminal execution, with arbitrary remaining state and tapes. -/
structure TerminalRun (P : Program K Λ σ) (input output : List Bool) (budget : Nat) where
  state : σ
  tapes : K → List Bool
  execution : StateTransition.EvalsToInTime (sourceMachine P).step
    (initList (sourceMachine P) input) (some ⟨none, state, tapes⟩) budget
  output_eq : tapes P.output = output

/-- A polynomial raw run becomes a full canonical-output computation certificate. -/
noncomputable def computableInPolyTime {α β : Type}
    (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output)
    (encodeIn : α → List Bool) (encodeOut : β → List Bool) (f : α → β)
    (rawTime : Polynomial Nat)
    (run : ∀ a, TerminalRun P (encodeIn a) (encodeOut (f a))
      (rawTime.eval (encodeIn a).length)) :
    TM2ComputableInPolyTime encodeIn encodeOut f where
  tm := completedMachine P chosen
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := completedTime P chosen rawTime
  outputsFun a := by
    change TM2OutputsInTime (completedMachine P chosen) ((encodeIn a).map id)
      (some ((encodeOut (f a)).map id)) ((completedTime P chosen rawTime).eval _)
    erw [List.map_id, List.map_id, completedTime_eval]
    exact outputsInTime P chosen complete _ _ (run a).state (run a).tapes _
      (run a).execution (run a).output_eq

theorem computableInPolyTime_finite_alphabet {α β : Type}
    (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output)
    (encodeIn : α → List Bool) (encodeOut : β → List Bool) (f : α → β)
    (rawTime : Polynomial Nat)
    (run : ∀ a, TerminalRun P (encodeIn a) (encodeOut (f a))
      (rawTime.eval (encodeIn a).length)) :
    MachineFiniteAlphabet.FiniteAlphabet
      (computableInPolyTime P chosen complete encodeIn encodeOut f rawTime run).tm :=
  finiteAlphabet P chosen

end UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTableRows

open Turing
open PCP.GraphTables

variable {K Λ σ : Type} [DecidableEq K]

omit [DecidableEq K] in
@[simp] theorem fieldBits_length (fields : Fin 3 → K) (base : K → List Bool) :
    (fieldBits fields base).length = fieldSize fields base := by
  simp [fieldBits, fieldSize, Nat.add_assoc]

def prefixTapes (fields : Fin 3 → K) (row : K) (base : K → List Bool) : K → List Bool :=
  Function.update base row (fieldBits fields base ++ base row)

/-- The three actual preserving-copy phases, with exact tape handoffs. -/
theorem prefixTrace (fields : Fin 3 → K) (row output scratch : K)
    (hfields : ∀ i, fields i ≠ row ∧ fields i ≠ scratch)
    (hrowScratch : row ≠ scratch) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (hprogram : ∀ label, program (labels label) = routine fields row output scratch labels exit label)
    (base : K → List Bool) (hscratch : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * (fieldSize fields base + 3)]
      (some ⟨some (labels .relationRead), (ambient, register), base⟩) =
      some ⟨some (labels .appendOld), (ambient, none), prefixTapes fields row base⟩ := by
  let afterRelation := Function.update base row (base (fields 2) ++ base row)
  let afterReverse := Function.update afterRelation row
    (base (fields 1) ++ afterRelation row)
  have hfirst := MachineCopy.copyTrace (fields 2) row scratch
    (hfields 2).1 (hfields 2).2 hrowScratch false
    (labels .relationRead) (labels .relationRestore) (some (labels .reverseRead))
    program (hprogram .relationRead) (hprogram .relationRestore) base hscratch ambient register
  change (MachineComposition.advance (TM2.step program))^[2 * ((base (fields 2)).length + 1)]
    (some ⟨some (labels .relationRead), (ambient, register), base⟩) =
    some ⟨some (labels .reverseRead), (ambient, none), afterRelation⟩ at hfirst
  have hsecond := MachineCopy.copyTrace (fields 1) row scratch
    (hfields 1).1 (hfields 1).2 hrowScratch false
    (labels .reverseRead) (labels .reverseRestore) (some (labels .tailRead))
    program (hprogram .reverseRead) (hprogram .reverseRestore) afterRelation
    (by simp [afterRelation, Ne.symm hrowScratch, hscratch]) ambient none
  have hrev : afterRelation (fields 1) = base (fields 1) := by
    simp [afterRelation, (hfields 1).1]
  rw [hrev] at hsecond
  change (MachineComposition.advance (TM2.step program))^[2 * ((base (fields 1)).length + 1)]
    (some ⟨some (labels .reverseRead), (ambient, none), afterRelation⟩) =
    some ⟨some (labels .tailRead), (ambient, none), afterReverse⟩ at hsecond
  have hthird := MachineCopy.copyTrace (fields 0) row scratch
    (hfields 0).1 (hfields 0).2 hrowScratch false
    (labels .tailRead) (labels .tailRestore) (some (labels .appendOld))
    program (hprogram .tailRead) (hprogram .tailRestore) afterReverse
    (by simp [afterReverse, afterRelation, Ne.symm hrowScratch, hscratch]) ambient none
  have htail : afterReverse (fields 0) = base (fields 0) := by
    simp [afterReverse, afterRelation, (hfields 0).1]
  rw [htail] at hthird
  have hfinal : Function.update afterReverse row
      (base (fields 0) ++ afterReverse row) = prefixTapes fields row base := by
    simp [afterReverse, afterRelation, prefixTapes, fieldBits, List.append_assoc]
  rw [hfinal] at hthird
  rw [show 2 * (fieldSize fields base + 3) =
    2 * ((base (fields 0)).length + 1) +
      (2 * ((base (fields 1)).length + 1) + 2 * ((base (fields 2)).length + 1)) by
        simp only [fieldSize]; omega,
    Function.iterate_add_apply,
    Function.iterate_add_apply (m := 2 * ((base (fields 1)).length + 1))
      (n := 2 * ((base (fields 2)).length + 1)), hfirst, hsecond]
  exact hthird

theorem appendTrace (fields : Fin 3 → K) (row output scratch : K)
    (hfields : ∀ i, fields i ≠ row ∧ fields i ≠ scratch)
    (hrowOutput : row ≠ output) (hrowScratch : row ≠ scratch)
    (houtputScratch : output ≠ scratch) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (hprogram : ∀ label, program (labels label) = routine fields row output scratch labels exit label)
    (base : K → List Bool) (hrow : base row = []) (hscratch : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[
        4 * fieldSize fields base + 2 * (base output).length + 9]
      (some ⟨some (labels .relationRead), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Function.update base output (base output ++ fieldBits fields base)⟩ := by
  have hprefix := prefixTrace fields row output scratch hfields hrowScratch
    labels exit program hprogram base hscratch ambient register
  have happend := MachineAppendAt.appendTrace row output scratch hrowOutput hrowScratch
    houtputScratch false (labels .appendOld) (labels .appendRow) (labels .appendBack)
    exit program (hprogram .appendOld) (hprogram .appendRow) (hprogram .appendBack)
    (prefixTapes fields row base)
    (by simp [prefixTapes, Ne.symm hrowScratch, hscratch]) ambient none
  have hrowbits : prefixTapes fields row base row = fieldBits fields base := by
    simp [prefixTapes, hrow]
  have hout : prefixTapes fields row base output = base output := by
    simp [prefixTapes, Ne.symm hrowOutput]
  rw [hrowbits, hout, fieldBits_length] at happend
  have hfinal : MachineAppendAt.appendTapes row output (prefixTapes fields row base) =
      Function.update base output (base output ++ fieldBits fields base) := by
    funext k
    by_cases ho : k = output
    · subst k
      simp [MachineAppendAt.appendTapes, hrowbits, hout]
    · by_cases hr : k = row
      · subst k
        simp [MachineAppendAt.appendTapes, Reduction.MachineTransfer.tapesAt,
          prefixTapes, hrowOutput, hrow]
      · simp [MachineAppendAt.appendTapes, Reduction.MachineTransfer.tapesAt,
          prefixTapes, ho, hr]
  rw [hfinal] at happend
  rw [show 4 * fieldSize fields base + 2 * (base output).length + 9 =
      (2 * (fieldSize fields base + (base output).length) + 3) +
        2 * (fieldSize fields base + 3) by omega,
    Function.iterate_add_apply, hprefix]
  exact happend

/-- The full existing graph codec, including all 4096 unary predicate fields. -/
theorem rowBits_eq {n m : Nat} (r : DartRow n m) :
    encodeWords (rowWords r) = encodeWord r.tail.val ++
      encodeWord r.reverseIndex.val ++ encodeWords (relationWords r.relation) := by
  simp [rowWords, encodeWords]

end UniqueGamesTheorem.Foundations.Complexity.MachineTableRows

/-!
Actual finite control for the dummy self-loop rows of one padded vertex.
The port count is a fixed program parameter. Vertex and reverse-dart indices
remain on unary tapes, and each row advances the reverse index by one actual
push. The all-true relation is a fixed literal field, initialized once.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineDummyRows

open Turing
open PCP.GraphTables
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

theorem rowBits_length (v e : Nat) : (rowBits v e).length = v + e + 8194 := by
  simp [rowBits, trueBits_length, encodeWord_length]
  omega

theorem rowBits_eq_graph_row {n m : Nat} (v : Fin n) (e : Fin m) :
    rowBits v.val e.val = encodeWords (rowWords (⟨v, e, trueRelation⟩ : DartRow n m)) := by
  rw [MachineTableRows.rowBits_eq]
  rfl

variable {σ : Type}

/-- The fixed literal relation is actually emitted by a finite push chain. -/
theorem initializeStep (d v e : Nat) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program d) ⟨some (start d), (ambient, register), initialTapes v e output⟩ =
      some ⟨entry d, (ambient, none), fieldTapes v e output⟩ := by
  change some (TM2.stepAux (program d (start d)) (ambient, register)
    (initialTapes v e output)) = _
  simp only [start, program, stepAux_pushWord, List.reverse_reverse, TM2.stepAux,
    initialTapes, Function.update_self, List.append_nil, Function.update_idem]
  have ht : Function.update (fieldTapes v e output) 2 trueBits = fieldTapes v e output := by
    funext i
    fin_cases i <;> simp [fieldTapes]
  rw [ht, stepAux_continueAt]

theorem rowTrace {d : Nat} (p : Fin d) (v e : Nat) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[
        4 * (v + e + 8194) + 2 * output.length + 9]
      (some ⟨some (rowLabel p .relationRead), (ambient, register), fieldTapes v e output⟩) =
      some ⟨some (bumpLabel p), (ambient, none), fieldTapes v e (output ++ rowBits v e)⟩ := by
  have hfields (i : Fin 3) : fields i ≠ (3 : Fin 6) ∧ fields i ≠ (5 : Fin 6) := by
    fin_cases i <;> decide
  have h := MachineTableRows.appendTrace fields (3 : Fin 6) 4 5 hfields
    (by decide) (by decide) (by decide) (rowLabel p) (some (bumpLabel p))
    (program d) (fun _ => rfl) (fieldTapes v e output) rfl rfl ambient register
  have hbits : MachineTableRows.fieldBits fields (fieldTapes v e output) = rowBits v e := by
    rfl
  have hsize : MachineTableRows.fieldSize fields (fieldTapes v e output) = v + e + 8194 := by
    rw [← MachineTableRows.fieldBits_length, hbits, rowBits_length]
  have ht : Function.update (fieldTapes v e output) 4 (output ++ rowBits v e) =
      fieldTapes v e (output ++ rowBits v e) := by
    funext i
    fin_cases i <;> simp [fieldTapes]
  simpa only [hsize, hbits, show fieldTapes v e output 4 = output from rfl, ht] using h

/-- The reverse index advances by pushing a real unary bit. The delimiter,
all input fields, output, and work tapes have their exact stated contents. -/
theorem bumpStep {d : Nat} (p : Fin d) (v e : Nat) (output : List Bool) (ambient : σ) :
    TM2.step (program d) ⟨some (bumpLabel p), (ambient, none), fieldTapes v e output⟩ =
      some ⟨afterPort p, (ambient, none), fieldTapes v (e + 1) output⟩ := by
  change some (TM2.stepAux (program d (bumpLabel p)) (ambient, none)
    (fieldTapes v e output)) = _
  simp only [bumpLabel, program, TM2.stepAux]
  rw [stepAux_continueAt]
  congr 2
  funext i
  fin_cases i <;> simp [fieldTapes, encodeWord, List.replicate_succ]

/-- The concrete row body and its actual index increment are consecutive
phases of one fixed program; no whole-body trace is supplied as a premise. -/
theorem rowAndBumpTrace {d : Nat} (p : Fin d) (v e : Nat) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[
        4 * (v + e + 8194) + 2 * output.length + 10]
      (some ⟨some (rowLabel p .relationRead), (ambient, register), fieldTapes v e output⟩) =
      some ⟨afterPort p, (ambient, none), fieldTapes v (e + 1) (output ++ rowBits v e)⟩ := by
  rw [show 4 * (v + e + 8194) + 2 * output.length + 10 =
      (4 * (v + e + 8194) + 2 * output.length + 9) + 1 by omega,
    Function.iterate_succ_apply', rowTrace, MachineComposition.advance_some]
  exact bumpStep p v e (output ++ rowBits v e) ambient

/-- Actual execution from any port boundary to the final halt. The finite
control index fixes the remaining number of rows; all unbounded values are
physically stored in `fieldTapes`. -/
theorem suffixTrace {d : Nat} (count : Nat) (p : Fin d) (hp : p.val + count = d)
    (v e : Nat) (output : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[steps v e output count]
      (some ⟨some (rowLabel p .relationRead), (ambient, register), fieldTapes v e output⟩) =
      some ⟨none, (ambient, none), fieldTapes v (e + count) (output ++ rowsBits v e count)⟩ := by
  induction count generalizing p v e output register with
  | zero =>
    have hlt := p.isLt
    omega
  | succ count ih =>
    rw [steps, Nat.add_comm (4 * (v + e + 8194) + 2 * output.length + 10),
      Function.iterate_add_apply, rowAndBumpTrace]
    by_cases hc : count = 0
    · subst count
      have hlast : ¬ p.val + 1 < d := by omega
      simp [afterPort, hlast, steps, rowsBits]
    · have hnext : p.val + 1 < d := by omega
      rw [afterPort, dite_eq_left hnext]
      have hh := ih ⟨p.val + 1, hnext⟩ (by change (p.val + 1) + count = d; omega)
        v (e + 1) (output ++ rowBits v e) none
      have he : (e + 1) + count = e + (count + 1) := by omega
      simpa only [rowsBits, List.append_assoc, he] using hh

/-- One fixed-relation initialization transition followed by all actual rows.
At zero ports initialization itself halts; no row is spuriously produced. -/
theorem allTrace (d v e : Nat) (output : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[steps v e output d + 1]
      (some ⟨some (start d), (ambient, register), initialTapes v e output⟩) =
      some ⟨none, (ambient, none), fieldTapes v (e + d) (output ++ rowsBits v e d)⟩ := by
  rw [Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step (program d)))^[steps v e output d]
    (TM2.step (program d) ⟨some (start d), (ambient, register), initialTapes v e output⟩) = _
  rw [initializeStep]
  by_cases hd : 0 < d
  · rw [entry, dite_eq_left hd]
    exact suffixTrace d ⟨0, hd⟩ (by simp) v e output ambient none
  · have hz : d = 0 := by omega
    subst d
    simp [entry, steps, rowsBits]

/-- Every actual row cost is bounded by the largest row and accumulated
output encountered during this finite loop. -/
theorem steps_le_bound (v e : Nat) (output : List Bool) (count : Nat) :
    steps v e output count ≤ count *
      (4 * (v + e + count + 8194) +
        2 * (output.length + count * (v + e + count + 8194)) + 10) := by
  induction count generalizing e output with
  | zero => simp [steps]
  | succ count ih =>
    let B := v + e + (count + 1) + 8194
    let C := 4 * B + 2 * (output.length + (count + 1) * B) + 10
    have hb : v + (e + 1) + count + 8194 = B := by dsimp [B]; omega
    have hi := ih (e + 1) (output ++ rowBits v e)
    rw [List.length_append, rowBits_length, hb] at hi
    have hrow : v + e + 8194 ≤ B := by dsimp [B]; omega
    have hout : output.length + (v + e + 8194) + count * B ≤
        output.length + (count + 1) * B := by
      calc
        _ ≤ output.length + B + count * B :=
          Nat.add_le_add_right (Nat.add_le_add_left hrow output.length) _
        _ = _ := by simp only [Nat.add_mul, Nat.one_mul]; omega
    have hconstant : 4 * B + 2 * (output.length + (v + e + 8194) + count * B) + 10 ≤ C := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hout) (4 * B)) 10
    have hremaining := hi.trans (Nat.mul_le_mul_left count hconstant)
    have hbody : 4 * (v + e + 8194) + 2 * output.length + 10 ≤ C := by
      exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 4 hrow)
        (Nat.mul_le_mul_left 2 (Nat.le_add_right output.length ((count + 1) * B)))) 10
    change (4 * (v + e + 8194) + 2 * output.length + 10) +
      steps v (e + 1) (output ++ rowBits v e) count ≤ (count + 1) * C
    calc
      _ ≤ C + count * C := Nat.add_le_add hbody hremaining
      _ = (count + 1) * C := by rw [Nat.add_mul, Nat.one_mul]; omega

end UniqueGamesTheorem.Foundations.Complexity.MachineDummyRows

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineCeilingPower
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCeilingPower

open Turing
open MachineComposition
open UniqueGamesTheorem.Foundations.PCP

variable {σ : Type}

theorem guardStep_succ (g k p e f : Nat) (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord (f + 1)) [] []⟩ =
      some ⟨some .copyFirst, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ := by
  have h := MachineUnaryCounter.guardStep_succ Tape.fuel Label.guard Label.copyFirst Label.cleanup
    (program g) rfl (memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) [] [] [])
    f [] (ambient, false) register
  simpa only [MachineUnaryCounter.counterTapes, List.append_nil, update_fuel] using h

theorem guardStep_zero (g k p e : Nat) (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord 0) [] []⟩ =
      some ⟨some .cleanup, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord 0) [] []⟩ := by
  have h := MachineUnaryCounter.guardStep_zero Tape.fuel Label.guard Label.copyFirst Label.cleanup
    (program g) rfl (memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) [] [] [])
    [] (ambient, false) register
  simpa only [MachineUnaryCounter.counterTapes, List.append_nil, update_fuel] using h

/-- The loop prefix is an actual guard, preserving copy, comparison,
restoration and finite decision, all in the same fixed program. -/
theorem prefixTrace (g k p e f : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[prefixTime k p]
      (some ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord (f + 1)) [] []⟩) =
      some ⟨some (if k ≤ p then Label.cleanup else Label.scale), ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ := by
  have hg : (advance (TM2.step (program g)))^[1]
      (some ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord (f + 1)) [] []⟩) =
      some ⟨some .copyFirst, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ :=
    guardStep_succ g k p e f ambient register
  have hc := MachineCopy.copyTrace Tape.input Tape.work Tape.spare
    (by decide) (by decide) (by decide) false Label.copyFirst Label.copySecond
    (some Label.compare) (program g) rfl rfl
    (memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] [])
    rfl (ambient, false) none
  simp only [memory, encodeWord_length, List.append_nil, update_work] at hc
  have hcmp := compareRestoredTrace g k p (encodeWord e) (encodeWord f) ambient none
  have hd : (advance (TM2.step (program g)))^[1]
      (some ⟨some .decide, ((ambient, decide (p < k)), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩) =
      some ⟨some (if k ≤ p then Label.cleanup else Label.scale), ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ :=
    decideStep g k p e f ambient
  exact appendTrace _ (appendTrace _ (appendTrace _ hg hc) hcmp) hd

/-- The fixed machine realizes the exact previously checked bounded loop.
Every initial fuel tally is either used or cleared before halting. -/
theorem coreTrace (g k f e p : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[coreTime g k f p]
      (some ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (encodeWord k) []
          (encodeWord (PreprocessingLevels.levelLoop g k f e p).2) []
          (encodeWord (PreprocessingLevels.levelLoop g k f e p).1) [] [] []⟩ := by
  induction f generalizing e p register with
  | zero =>
      have hg : (advance (TM2.step (program g)))^[1]
          (some ⟨some .guard, ((ambient, false), register),
            memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord 0) [] []⟩) =
          some ⟨some .cleanup, ((ambient, false), none),
            memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord 0) [] []⟩ :=
        guardStep_zero g k p e ambient register
      exact appendTrace _ hg (cleanupTrace g k p e 0 ambient none)
  | succ f ih =>
      have hpref := prefixTrace g k p e f ambient register
      by_cases h : k ≤ p
      · simp only [h, ite_true, if_true] at hpref
        have hrun := appendTrace _ hpref (cleanupTrace g k p e f ambient none)
        simpa only [coreTime, PreprocessingLevels.levelLoop, h, ite_true, if_true] using hrun
      · simp only [h, ite_false] at hpref
        have hscale := scaleTrace g k p e (encodeWord f) ambient none
        have hrun := appendTrace _ hpref (appendTrace _ hscale (ih (e + 1) (p * g) none))
        simpa only [coreTime, PreprocessingLevels.levelLoop, h, ite_false] using hrun

/-- Initialization writes one and zero, copies the actual input to the fuel
tape, and executes the proved loop. All auxiliary tapes are empty on exit. -/
theorem searchTrace (g k : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[totalTime g k]
      (some ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (encodeWord k) []
          (encodeWord (PreprocessingLevels.levelLoop g k k 0 1).2) []
          (encodeWord (PreprocessingLevels.levelLoop g k k 0 1).1) [] [] []⟩ := by
  have hi : (advance (TM2.step (program g)))^[1]
      (some ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩) =
      some ⟨some .fuelFirst, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord 1) [] (encodeWord 0) [] [] []⟩ :=
    initStep g k ambient register
  have hc := MachineCopy.copyTrace Tape.input Tape.fuel Tape.spare
    (by decide) (by decide) (by decide) false Label.fuelFirst Label.fuelSecond
    (some Label.guard) (program g) rfl rfl
    (memory (encodeWord k) [] (encodeWord 1) [] (encodeWord 0) [] [] [])
    rfl (ambient, false) register
  simp only [memory, encodeWord_length, List.append_nil, update_fuel] at hc
  exact appendTrace _ (appendTrace _ hi hc) (coreTrace g k k 0 1 ambient none)

/-- Instantiate the fixed program with the actual expander growth. This is
the exact executable result already identified with the ceiling logarithm. -/
theorem paddingTrace (k : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program ExpanderFamily.growth)))^[totalTime ExpanderFamily.growth k]
      (some ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord (PreprocessingLevels.paddedSize k)) []
          (encodeWord (PreprocessingLevels.boundedLevel k)) [] [] []⟩ := by
  exact searchTrace ExpanderFamily.growth k ambient register

def paddingInTime (k : Nat) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program ExpanderFamily.growth))
      ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩
      (some ⟨none, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord (PreprocessingLevels.paddedSize k)) []
          (encodeWord (PreprocessingLevels.boundedLevel k)) [] [] []⟩)
      ((timePolynomial ExpanderFamily.growth).eval (encodeWord k).length) where
  steps := totalTime ExpanderFamily.growth k
  evals_in_steps := paddingTrace k ambient register
  steps_le_m := by rw [timePolynomial_encoding]; exact totalTime_le _ _

end UniqueGamesTheorem.Foundations.Complexity.MachineCeilingPower

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineCloudCount
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudCount

open Turing
open MachineComposition

variable {Λ σ : Type}

/-- Consecutive concrete field-discard instructions consume a fixed list of
fields. The hypotheses specify code, not an abstract body execution. -/
theorem discardFieldsTrace (labels : Nat → Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (fields : List Nat) (offset : Nat)
    (atField : ∀ i, i < fields.length → program (labels (offset + i)) =
      MachineLookup.discard .work (labels (offset + i)) (labels (offset + i + 1)))
    (original suffix target scratch count spare : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[(encodeWords fields).length]
      (some ⟨some (labels offset), ((ambient, flag), register),
        memory original (encodeWords fields ++ suffix) target scratch count spare⟩) =
      some ⟨some (labels (offset + fields.length)),
        ((ambient, flag), if fields = [] then register else none),
        memory original suffix target scratch count spare⟩ := by
  induction fields generalizing offset register with
  | nil => simp only [encodeWords, List.length_nil, Function.iterate_zero_apply,
      List.nil_append, Nat.add_zero, ↓reduceIte]
  | cons x fields ih =>
      have hfirst := MachineLookup.discardTrace Tape.work (labels offset) (labels (offset + 1))
        program (by simpa only [Nat.add_zero] using atField 0 (by simp))
        (memory original (encodeWords (x :: fields) ++ suffix) target scratch count spare)
        x (encodeWords fields ++ suffix) (by simp only [memory_work, encodeWords, List.append_assoc])
        (ambient, flag) register
      simp only [update_memory_work] at hfirst
      have hrest := ih (offset + 1) (by
        intro i hi
        have h := atField (i + 1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hi)
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h) none
      rw [show (encodeWords (x :: fields)).length =
          (encodeWords fields).length + (x + 1) by
          simp only [encodeWords, List.length_append, encodeWord_length]
          omega,
        Function.iterate_add_apply, hfirst]
      simpa only [List.length_cons, List.cons_ne_nil,
        ite_false, ite_self, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest

/-- One complete stored row is consumed; the target and original are restored. -/
theorem rowTrace (r : Row) (hwidth : r.2.length = 4097) (v : Nat)
    (original suffix targetSuffix count spare : List Bool) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[rowTime v r]
      (some ⟨some .row, ((ambient, false), register),
        memory original (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix)
          [] count spare⟩) =
      some ⟨some .row, ((ambient, false), none),
        memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (if r.1 = v then 1 else 0) true ++ count) spare⟩ := by
  have hfield := preservingFieldTrace Label.field Label.restore (skipLabel 0)
    program rfl rfl original (encodeWords r.2 ++ suffix) targetSuffix count spare r.1 v ambient none
  have hskip := discardFieldsTrace skipLabel (program (σ := σ)) r.2 0
    (by intro i hi; simpa only [Nat.zero_add] using program_skip (hwidth ▸ hi))
    original suffix (encodeWord v ++ targetSuffix) []
    (List.replicate (if r.1 = v then 1 else 0) true ++ count) spare ambient false none
  have hnonempty : r.2 ≠ [] := by intro h; simp [h] at hwidth
  simp only [Nat.zero_add, hwidth, skipLabel, lt_self_iff_false, ↓reduceDIte,
    hnonempty, ite_false] at hskip
  have htime : rowTime v r = (encodeWords r.2).length + (r.1 + min r.1 v + 2) + 1 := by
    simp only [rowTime, rowWords, encodeWords, List.length_append, encodeWord_length]
    omega
  rw [htime, Function.iterate_succ_apply]
  change (advance (TM2.step (program (σ := σ))))^[
      (encodeWords r.2).length + (r.1 + min r.1 v + 2)]
    (TM2.step program ⟨some .row, ((ambient, false), register),
      memory original (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix)
        [] count spare⟩) = _
  rw [rowStep_nonempty original _ _ [] count spare
    (by simp [rowWords, encodeWords, encodeWord]) ambient false register,
    Function.iterate_add_apply]
  simp only [rowWords, encodeWords, List.append_assoc]
  rw [hfield]
  exact hskip

/-- The complete actual row scan halts with the number of matching tails. -/
theorem rowsTrace (rs : List Row) (hwidth : ∀ r ∈ rs, r.2.length = 4097) (v : Nat)
    (original targetSuffix count spare : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[rowsTime v rs]
      (some ⟨some .row, ((ambient, false), register),
        memory original (encodeWords (rs.flatMap rowWords)) (encodeWord v ++ targetSuffix)
          [] count spare⟩) =
      some ⟨none, ((ambient, false), none),
        memory original [] (encodeWord v ++ targetSuffix) []
          (List.replicate (rowsHits v rs) true ++ count) spare⟩ := by
  induction rs generalizing count register with
  | nil =>
      simpa only [rowsTime, List.flatMap_nil, encodeWords, Function.iterate_one, advance_some,
        rowsHits, List.replicate_zero, List.nil_append] using
        rowStep_empty original (encodeWord v ++ targetSuffix) [] count spare ambient false register
  | cons r rs ih =>
      have hrow := rowTrace r (hwidth r (by simp)) v original
        (encodeWords (rs.flatMap rowWords)) targetSuffix count spare ambient register
      have hrest := ih (by intro x hx; exact hwidth x (by simp [hx]))
        (List.replicate (if r.1 = v then 1 else 0) true ++ count) none
      simp only [rowsTime, List.flatMap_cons, encodeWords_append]
      rw [Function.iterate_add_apply, hrow]
      simpa only [rowsHits, ← List.append_assoc, List.replicate_append_replicate,
        Nat.add_comm] using hrest

/-- One preserving copy, the two concrete header discards, and the proved row
scan form the complete execution. The input and target tapes are unchanged. -/
theorem countTrace (n m v : Nat) (rs : List Row)
    (hwidth : ∀ r ∈ rs, r.2.length = 4097)
    (targetSuffix count : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[totalSteps n m v rs]
      (some ⟨some .copyFirst, ((ambient, false), register),
        memory (inputWord n m rs) [] (encodeWord v ++ targetSuffix) [] count []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (inputWord n m rs) [] (encodeWord v ++ targetSuffix) []
          (List.replicate (rowsHits v rs) true ++ count) []⟩ := by
  have hcopy := MachineCopy.copyTrace Tape.original Tape.work Tape.spare
    (by decide) (by decide) (by decide) false Label.copyFirst Label.copySecond
    (some Label.headerFirst) program rfl rfl
    (memory (inputWord n m rs) [] (encodeWord v ++ targetSuffix) [] count [])
    rfl (ambient, false) register
  simp only [memory_original, memory_work, List.append_nil, update_memory_work] at hcopy
  have hfirst := MachineLookup.discardTrace Tape.work Label.headerFirst Label.headerSecond
    program rfl
    (memory (inputWord n m rs) (inputWord n m rs) (encodeWord v ++ targetSuffix) [] count [])
    n (encodeWord m ++ encodeWords (rs.flatMap rowWords))
    (by exact inputWord_eq n m rs) (ambient, false) none
  simp only [update_memory_work] at hfirst
  have hsecond := MachineLookup.discardTrace Tape.work Label.headerSecond Label.row
    program rfl
    (memory (inputWord n m rs) (encodeWord m ++ encodeWords (rs.flatMap rowWords))
      (encodeWord v ++ targetSuffix) [] count [])
    m (encodeWords (rs.flatMap rowWords)) rfl (ambient, false) none
  simp only [update_memory_work] at hsecond
  have hrows := rowsTrace rs hwidth v (inputWord n m rs) targetSuffix count [] ambient none
  rw [show totalSteps n m v rs = rowsTime v rs + ((m + 1) + ((n + 1) +
      2 * ((inputWord n m rs).length + 1))) by unfold totalSteps; omega,
    Function.iterate_add_apply _ (rowsTime v rs),
    Function.iterate_add_apply _ (m + 1), Function.iterate_add_apply _ (n + 1),
    hcopy, hfirst, hsecond]
  exact hrows

open UniqueGamesTheorem.Foundations.PCP

/-- Cloud size is produced by reading the actual encoded tail fields, with
the complete graph input and unary vertex query preserved on their tapes. -/
theorem cloudCountTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (targetSuffix countSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[totalSteps t.vertices t.darts v.val (tableRows t)]
      (some ⟨some .copyFirst, ((ambient, false), register),
        memory (GraphTables.tableBits t) [] (encodeWord v.val ++ targetSuffix) []
          (encodeWord 0 ++ countSuffix) []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (GraphTables.tableBits t) [] (encodeWord v.val ++ targetSuffix) []
          (encodeWord (PreprocessingCloudIndex.cloudSize t v) ++ countSuffix) []⟩ := by
  have h := countTrace t.vertices t.darts v.val (tableRows t) (tableRows_width t)
    targetSuffix (encodeWord 0 ++ countSuffix) ambient register
  rw [tableRows_input, tableRows_hits, ← List.append_assoc, replicate_encodeWord, Nat.add_zero] at h
  exact h

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudCount

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineCloudPadding
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual cloud counting, geometric padding, and unary subtraction

One finite program places the checked cloud counter and geometric search on
shared tapes. Its final phase physically subtracts the preserved cloud size
from the computed power. A head test handles the empty cloud separately.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudPadding

open Turing
open MachineComposition
open UniqueGamesTheorem.Foundations.PCP

/- Static placement of homogeneous tapes, with an explicit finite partial
inverse. Complement tapes are preserved by every simulated transition. -/

variable {σ : Type}

theorem countTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineCloudCount.totalSteps t.vertices t.darts v.val
      (MachineCloudCount.tableRows t)]
      (some ⟨some (.countCode .copyFirst), ((ambient, false), register),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix)
          (encodeWord 0) [] [] [] [] [] [] []⟩) =
      some ⟨some .branch, ((ambient, false), none),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix)
          (encodeWord (PreprocessingCloudIndex.cloudSize t v)) [] [] [] [] [] [] []⟩ := by
  have h := Placement.trace countTape countView countView_left countView_right
    Label.countCode (some Label.branch) (fun _ => [])
    (MachineCloudCount.program (σ := σ)) program (fun _ => rfl) _ _ _
    (MachineCloudCount.cloudCountTrace t v suffix [] ambient register)
  simpa only [Placement.configuration, Placement.label, countTapes, List.append_nil] using h

theorem powerTrace (table query : List Bool) (k : Nat) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step program))^[MachineCeilingPower.totalTime ExpanderFamily.growth k]
      (some ⟨some (.powerCode .init), ((ambient, false), register),
        memory table query (encodeWord k) [] [] [] [] [] [] []⟩) =
      some ⟨some .subtract, ((ambient, false), none),
        memory table query (encodeWord k) [] [] []
          (encodeWord (PreprocessingLevels.paddedSize k))
          (encodeWord (PreprocessingLevels.boundedLevel k)) [] []⟩ := by
  have h := Placement.trace powerTape powerView powerView_left powerView_right
    Label.powerCode (some Label.subtract) (memory table query [] [] [] [] [] [] [] [])
    (MachineCeilingPower.program ExpanderFamily.growth (σ := σ)) program (fun _ => rfl)
    _ _ _ (MachineCeilingPower.paddingTrace k ambient register)
  simpa only [Placement.configuration, Placement.label, powerTapes, memory] using h

/-- Count zero is handled by a head test. Positive counts execute the exact
power search and subtraction traces on the shared count tape. -/
theorem postTrace (table query : List Bool) (k : Nat) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step program))^[postTime k]
      (some ⟨some .branch, ((ambient, false), register),
        memory table query (encodeWord k) [] [] [] [] [] [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory table query (encodeWord k) [] [] [] (encodeWord (padding k))
          (encodeWord (PreprocessingLevels.boundedLevel k)) [] []⟩ := by
  cases k with
  | zero =>
    simpa only [postTime, ite_eq_left rfl, ite_true, if_true, Nat.add_zero, Function.iterate_one, advance_some,
      padding, PreprocessingLevels.cloudPaddedSize_zero, Nat.sub_zero,
      PreprocessingLevels.boundedLevel_zero] using branchStep_zero table query ambient register
  | succ k =>
    have hb : (advance (TM2.step program))^[1]
        (some ⟨some .branch, ((ambient, false), register),
          memory table query (encodeWord (k + 1)) [] [] [] [] [] [] []⟩) =
        some ⟨some (.powerCode .init), ((ambient, false), none),
          memory table query (encodeWord (k + 1)) [] [] [] [] [] [] []⟩ :=
      branchStep_succ table query k ambient register
    have hp := powerTrace table query (k + 1) ambient none
    have hs := subtractTrace table query (encodeWord (PreprocessingLevels.boundedLevel (k + 1)))
      (k + 1) (PreprocessingLevels.paddedSize (k + 1))
      (PreprocessingLevels.le_paddedSize (k + 1)) ambient none
    have h := appendTrace _ hb (appendTrace _ hp hs)
    simpa only [postTime, Nat.succ_ne_zero, ite_false, padding,
      PreprocessingLevels.cloudPaddedSize_of_pos (Nat.succ_pos k)] using h

/-- One complete concrete program returns the cloud size, geometric level,
and required number of padding vertices, preserving input and query. -/
theorem cloudPaddingTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[totalTime t v]
      (some ⟨some .init, ((ambient, false), register),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix) [] [] [] [] [] [] [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix)
          (encodeWord (PreprocessingCloudIndex.cloudSize t v)) [] [] []
          (encodeWord (padding (PreprocessingCloudIndex.cloudSize t v)))
          (encodeWord (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v)))
          [] []⟩ := by
  have hi : (advance (TM2.step program))^[1]
      (some ⟨some .init, ((ambient, false), register),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix) [] [] [] [] [] [] [] []⟩) =
      some ⟨some (.countCode .copyFirst), ((ambient, false), register),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix)
          (encodeWord 0) [] [] [] [] [] [] []⟩ :=
    initStep _ _ ambient register
  exact appendTrace _ (appendTrace _ hi (countTrace t v suffix ambient register))
    (postTrace _ _ (PreprocessingCloudIndex.cloudSize t v) ambient none)

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudPadding

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineCloudPrefix
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.PCP
open scoped BigOperators

variable {σ : Type}

def program : Label → TM2.Stmt Alphabet Label (State σ)
  | .init => .push (.inner .query) (fun _ => false)
      (.push .total (fun _ => false) (.goto fun _ => .copyFirst))
  | .copyFirst => Reduction.MachineTransfer.loopAt
      .bound (.inner .scratch) id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop
      (.inner .scratch) .bound .remaining false .copySecond (some .guard)
  | .guard => MachineUnaryCounter.guard .remaining (.padding .init) .done
  | .done => .halt
  | .padding l => MachineCloudPadding.Placement.statement Tape.inner Label.padding (some .add) (MachineCloudPadding.program l)
  | .add => MachineUnaryAddAt.loop (.inner .power) .total .add (some .clearCount)
  | .clearCount => MachineLookup.discard (.inner .count) .clearCount .clearLevel
  | .clearLevel => MachineLookup.discard (.inner .level) .clearLevel .increment
  | .increment => .pop (.inner .power) (fun state _ => (state.1, none))
      (.push (.inner .query) (fun _ => true) (.goto fun _ => .guard))

/-- The inner program is embedded with its actual table scan and geometric
search; all three additional tapes are preserved by every inner transition. -/
theorem paddingTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (bound remaining total : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineCloudPadding.totalTime t v]
      (some ⟨some (.padding .init), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord v.val) [] [] [] bound remaining total⟩) =
      some ⟨some .add, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord v.val)
          (encodeWord (PreprocessingCloudIndex.cloudSize t v))
          (encodeWord (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v)))
          (encodeWord (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v)))
          bound remaining total⟩ := by
  have h := MachineCloudPadding.Placement.trace Tape.inner paddingView paddingView_left paddingView_right
    Label.padding (some Label.add) (frame [] [] [] [] [] bound remaining total)
    (MachineCloudPadding.program (σ := σ)) program (fun _ => rfl) _ _ _
    (MachineCloudPadding.cloudPaddingTrace t v [] ambient register)
  simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label, placedTapes,
    frame_bound, frame_remaining, frame_total, List.append_nil, frame, memory] using h

theorem incrementStep (table bound remaining total : List Bool) (v : Nat)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .increment, ((ambient, false), register),
        frame table (encodeWord v) [] (encodeWord 0) [] bound remaining total⟩ =
      some ⟨some .guard, ((ambient, false), none),
        frame table (encodeWord (v + 1)) [] [] [] bound remaining total⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord, List.replicate_succ]

/-- Padding tallies are consumed by unary addition; count and level fields
are scanned away, and the remaining zero padding delimiter is removed while
the physical vertex counter increases. -/
theorem bodyTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (bound remaining : List Bool) (acc : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[bodyTime t v]
      (some ⟨some (.padding .init), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord v.val) [] [] []
          bound remaining (encodeWord acc)⟩) =
      some ⟨some .guard, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord (v.val + 1)) [] [] []
          bound remaining (encodeWord (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v) + acc))⟩ := by
  let k := PreprocessingCloudIndex.cloudSize t v
  let p := MachineCloudPadding.padding k
  let l := PreprocessingLevels.boundedLevel k
  have hp := paddingTrace t v bound remaining (encodeWord acc) ambient register
  have ha := MachineUnaryAddAt.addFromTapes (Tape.inner .power) Tape.total (by decide)
    Label.add (some Label.clearCount) program rfl
    (frame (GraphTables.tableBits t) (encodeWord v.val) (encodeWord k)
      (encodeWord p) (encodeWord l) bound remaining (encodeWord acc))
    p acc [] [] (by simp) (by simp) (ambient, false) none
  simp only [MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt,
    List.append_nil, update_frame_power, update_frame_total] at ha
  have hc := MachineLookup.discardTrace (Tape.inner .count) Label.clearCount Label.clearLevel
    program rfl
    (frame (GraphTables.tableBits t) (encodeWord v.val) (encodeWord k)
      (encodeWord 0) (encodeWord l) bound remaining (encodeWord (p + acc)))
    k [] (by simp) (ambient, false) none
  simp only [update_frame_count] at hc
  have hl := MachineLookup.discardTrace (Tape.inner .level) Label.clearLevel Label.increment
    program rfl
    (frame (GraphTables.tableBits t) (encodeWord v.val) []
      (encodeWord 0) (encodeWord l) bound remaining (encodeWord (p + acc)))
    l [] (by simp) (ambient, false) none
  simp only [update_frame_level] at hl
  have hi : (advance (TM2.step program))^[1]
      (some ⟨some .increment, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord v.val) [] (encodeWord 0) []
          bound remaining (encodeWord (p + acc))⟩) =
      some ⟨some .guard, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord (v.val + 1)) [] [] []
          bound remaining (encodeWord (p + acc))⟩ :=
    incrementStep _ _ _ _ _ ambient none
  exact appendTrace _ (appendTrace _ (appendTrace _ (appendTrace _ hp ha) hc) hl) hi

theorem guardStep_succ (table bound suffix total : List Bool) (v n : Nat)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .guard, ((ambient, false), register),
        frame table (encodeWord v) [] [] [] bound (encodeWord (n + 1) ++ suffix) total⟩ =
      some ⟨some (.padding .init), ((ambient, false), none),
        frame table (encodeWord v) [] [] [] bound (encodeWord n ++ suffix) total⟩ := by
  simp [TM2.step, program, MachineUnaryCounter.guard, TM2.stepAux, encodeWord,
    List.replicate_succ]

theorem guardStep_zero (table bound suffix total : List Bool) (v : Nat)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .guard, ((ambient, false), register),
        frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩ =
      some ⟨some .done, ((ambient, false), none),
        frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩ := rfl

theorem zeroTrace (table bound suffix total : List Bool) (v : Nat)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[2]
      (some ⟨some .guard, ((ambient, false), register),
        frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩) =
      some ⟨none, ((ambient, false), none),
        frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩ := by
  rw [Function.iterate_succ_apply]
  change advance (TM2.step (program (σ := σ)))
    (TM2.step program ⟨some .guard, ((ambient, false), register),
      frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩) = _
  rw [guardStep_zero]
  rfl

theorem loopTrace (t : GraphTables.Table) (n v : Nat) (hvn : v + n ≤ t.vertices)
    (bound suffix : List Bool) (acc : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[loopTime t v n]
      (some ⟨some .guard, ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord v) [] [] []
          bound (encodeWord n ++ suffix) (encodeWord acc)⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord (v + n)) [] [] []
          bound (encodeWord 0 ++ suffix) (encodeWord (sumFrom t v n + acc))⟩ := by
  induction n generalizing v acc register with
  | zero =>
      simpa only [loopTime, sumFrom, Nat.add_zero, Nat.zero_add] using
        zeroTrace _ bound suffix (encodeWord acc) v ambient register
  | succ n ih =>
      have hv : v < t.vertices := by omega
      have hnext : v + 1 + n ≤ t.vertices := by omega
      have hg : (advance (TM2.step program))^[1]
          (some ⟨some .guard, ((ambient, false), register),
            frame (GraphTables.tableBits t) (encodeWord v) [] [] []
              bound (encodeWord (n + 1) ++ suffix) (encodeWord acc)⟩) =
          some ⟨some (.padding .init), ((ambient, false), none),
            frame (GraphTables.tableBits t) (encodeWord v) [] [] []
              bound (encodeWord n ++ suffix) (encodeWord acc)⟩ :=
        guardStep_succ _ bound suffix (encodeWord acc) v n ambient register
      have hb := bodyTrace t ⟨v, hv⟩ bound (encodeWord n ++ suffix) acc ambient none
      have ht := ih (v + 1) hnext
        (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t ⟨v, hv⟩) + acc) none
      have hall := appendTrace _ (appendTrace _ hg hb) ht
      simpa only [loopTime, cycleTime, dite_eq_left hv, sumFrom, amount,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

theorem initStep (table bound : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .init, ((ambient, false), register), frame table [] [] [] [] bound [] []⟩ =
      some ⟨some .copyFirst, ((ambient, false), register),
        frame table (encodeWord 0) [] [] [] bound [] (encodeWord 0)⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

def totalTime (t : GraphTables.Table) (b : Nat) (suffix : List Bool) : Nat :=
  (1 + 2 * ((encodeWord b ++ suffix).length + 1)) + loopTime t 0 b

theorem prefixTrace (t : GraphTables.Table) (b : Nat) (hb : b ≤ t.vertices)
    (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[totalTime t b suffix]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] (encodeWord b ++ suffix) [] []⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord b) [] [] []
          (encodeWord b ++ suffix) (encodeWord 0 ++ suffix)
          (encodeWord (PreprocessingPaddingOffsets.offset
            (PreprocessingRegularTables.padding t) b))⟩ := by
  have hi : (advance (TM2.step program))^[1]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] (encodeWord b ++ suffix) [] []⟩) =
      some ⟨some .copyFirst, ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord 0) [] [] []
          (encodeWord b ++ suffix) [] (encodeWord 0)⟩ :=
    initStep _ _ ambient register
  have hc := MachineCopy.copyTrace Tape.bound Tape.remaining (Tape.inner .scratch)
    (by decide) (by decide) (by decide) false Label.copyFirst Label.copySecond
    (some Label.guard) program rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord 0) [] [] []
      (encodeWord b ++ suffix) [] (encodeWord 0)) rfl (ambient, false) register
  simp only [frame_bound, frame_remaining, List.append_nil, update_frame_remaining] at hc
  have hl := loopTrace t b 0 (by simpa only [Nat.zero_add] using hb)
    (encodeWord b ++ suffix) suffix 0 ambient none
  simp only [Nat.zero_add, Nat.add_zero, sumFrom_eq_offset t b hb] at hl
  exact appendTrace _ (appendTrace _ hi hc) hl

theorem bodyTime_le (t : GraphTables.Table) (v : Fin t.vertices) (L : Nat)
    (hL : (GraphTables.tableBits t).length ≤ L) :
    1 + bodyTime t v ≤ cycleBudget L := by
  have hn := GraphTables.vertices_le_tableBits_length t
  have hv := v.isLt
  have hinput : MachineCloudPadding.inputLength t v [] ≤ 2 * L := by
    simp only [MachineCloudPadding.inputLength, List.append_nil, encodeWord_length]
    omega
  have hp := (MachineCloudPadding.totalTime_le t v []).trans
    (natPolynomial_eval_mono MachineCloudPadding.timePolynomial hinput)
  simp only [MachineCloudPadding.timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] at hp
  have hk : PreprocessingCloudIndex.cloudSize t v ≤ L :=
    (PreprocessingCloudIndex.cloudSize_le_darts t v).trans
      ((GraphTables.darts_le_tableBits_length t).trans hL)
  have hl := (PreprocessingLevels.boundedLevel_le_input
    (PreprocessingCloudIndex.cloudSize t v)).trans hk
  have hpad : MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v) ≤
      ExpanderFamily.growth * L := by
    have hsize := (PreprocessingLevels.cloudPaddedSize_bounds
      (PreprocessingCloudIndex.cloudSize t v)).2
    have hmul := Nat.mul_le_mul_left ExpanderFamily.growth hk
    unfold MachineCloudPadding.padding
    omega
  unfold bodyTime cycleBudget
  simp only [Nat.add_mul] at hp ⊢
  omega

theorem loopTime_le (t : GraphTables.Table) (n v : Nat) (hvn : v + n ≤ t.vertices)
    (L : Nat) (hL : (GraphTables.tableBits t).length ≤ L) :
    loopTime t v n ≤ n * cycleBudget L + 2 := by
  induction n generalizing v with
  | zero => simp only [loopTime, Nat.zero_mul, Nat.zero_add, le_refl]
  | succ n ih =>
      have hv : v < t.vertices := by omega
      have hnext : v + 1 + n ≤ t.vertices := by omega
      have hbody := bodyTime_le t ⟨v, hv⟩ L hL
      have htail := ih (v + 1) hnext
      simp only [loopTime, cycleTime, dite_eq_left hv, Nat.succ_mul]
      omega

def inputLength (t : GraphTables.Table) (b : Nat) (suffix : List Bool) : Nat :=
  (GraphTables.tableBits t).length + (encodeWord b ++ suffix).length

/-- The full execution has a cubic polynomial bound in the two actual
preserved input words. The accumulator is never scanned to perform addition. -/
theorem totalTime_le (t : GraphTables.Table) (b : Nat) (hb : b ≤ t.vertices)
    (suffix : List Bool) :
    totalTime t b suffix ≤ timePolynomial.eval (inputLength t b suffix) := by
  let L := inputLength t b suffix
  have htable : (GraphTables.tableBits t).length ≤ L := by
    unfold L inputLength
    omega
  have hbound : (encodeWord b ++ suffix).length ≤ L := by
    unfold L inputLength
    omega
  have hbL : b ≤ L := hb.trans ((GraphTables.vertices_le_tableBits_length t).trans htable)
  have hloop := loopTime_le t b 0 (by simpa only [Nat.zero_add] using hb) L htable
  have hmul := Nat.mul_le_mul_right (cycleBudget L) hbL
  have htotal : totalTime t b suffix ≤ L * cycleBudget L + 2 * (L + 1) + 3 := by
    unfold totalTime
    omega
  simpa only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat,
    Polynomial.eval_one, cycleBudget, L] using htotal

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineCloudRankLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudRank

open Turing MachineComposition MachineCloudCount

variable {σ : Type}

/-- One actual row comparison consumes one unit of fuel and restores the
entire vertex query before discarding the remaining fixed row fields. -/
theorem rankRowTrace (r : Row) (hwidth : r.2.length = 4097) (v k : Nat)
    (original suffix targetSuffix fuelSuffix count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[rowTime v r]
      (some ⟨some .row, ((ambient, false), register),
        memory original (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix)
          [] count (encodeWord (k + 1) ++ fuelSuffix)⟩) =
      some ⟨some .row, ((ambient, false), none),
        memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (if r.1 = v then 1 else 0) true ++ count)
          (encodeWord k ++ fuelSuffix)⟩ := by
  have hfield := preservingFieldTrace RankLabel.field RankLabel.restore (rankSkip 0)
    rankProgram rfl rfl original (encodeWords r.2 ++ suffix) targetSuffix count
    (encodeWord k ++ fuelSuffix) r.1 v ambient none
  have hskip := discardFieldsTrace rankSkip (rankProgram (σ := σ)) r.2 0
    (by intro i hi; simpa only [Nat.zero_add] using rankProgram_skip (hwidth ▸ hi))
    original suffix (encodeWord v ++ targetSuffix) []
    (List.replicate (if r.1 = v then 1 else 0) true ++ count)
    (encodeWord k ++ fuelSuffix) ambient false none
  have hnonempty : r.2 ≠ [] := by intro h; simp [h] at hwidth
  simp only [Nat.zero_add, hwidth, rankSkip, lt_self_iff_false, ↓reduceDIte,
    hnonempty, ite_false] at hskip
  have htime : rowTime v r = (encodeWords r.2).length + (r.1 + min r.1 v + 2) + 1 := by
    simp only [rowTime, rowWords, encodeWords, List.length_append, encodeWord_length]
    omega
  rw [htime, Function.iterate_succ_apply]
  change (advance (TM2.step (rankProgram (σ := σ))))^[
      (encodeWords r.2).length + (r.1 + min r.1 v + 2)]
    (TM2.step rankProgram ⟨some .row, ((ambient, false), register),
      memory original (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix)
        [] count (encodeWord (k + 1) ++ fuelSuffix)⟩) = _
  rw [rowGuard_succ, Function.iterate_add_apply]
  simp only [rowWords, encodeWords, List.append_assoc]
  rw [hfield]
  exact hskip

/-- The row loop runs for the unary fuel on spare, not until the input ends. -/
theorem prefixTrace (rs : List Row) (hwidth : ∀ r ∈ rs, r.2.length = 4097) (v : Nat)
    (original suffix targetSuffix fuelSuffix count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[prefixTime v rs]
      (some ⟨some .row, ((ambient, false), register),
        memory original (encodeWords (rs.flatMap rowWords) ++ suffix)
          (encodeWord v ++ targetSuffix) [] count (encodeWord rs.length ++ fuelSuffix)⟩) =
      some ⟨none, ((ambient, false), none),
        memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (rowsHits v rs) true ++ count) (encodeWord 0 ++ fuelSuffix)⟩ := by
  induction rs generalizing count register with
  | nil =>
      simpa only [prefixTime, List.flatMap_nil, encodeWords, List.nil_append,
        List.length_nil, rowsHits, List.replicate_zero] using
        zeroRowsTrace original suffix (encodeWord v ++ targetSuffix) [] count fuelSuffix
          ambient false register
  | cons r rs ih =>
      have hrow := rankRowTrace r (hwidth r (by simp)) v rs.length original
        (encodeWords (rs.flatMap rowWords) ++ suffix) targetSuffix fuelSuffix count ambient register
      have hrest := ih (by intro x hx; exact hwidth x (by simp [hx]))
        (List.replicate (if r.1 = v then 1 else 0) true ++ count) none
      simp only [prefixTime, List.flatMap_cons, encodeWords_append, List.append_assoc,
        List.length_cons]
      rw [Function.iterate_add_apply, hrow]
      simpa only [rowsHits, ← List.append_assoc, List.replicate_append_replicate,
        Nat.add_comm] using hrest

/-- The full finite trace copies the query, extracts its unary row fuel,
preserves the graph while copying it, skips both headers, and counts a prefix. -/
theorem rankTrace (n m v k : Nat) (rs : List Row) (hk : k ≤ rs.length)
    (hwidth : ∀ r ∈ rs, r.2.length = 4097) (querySuffix count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[rankSteps n m v k rs querySuffix]
      (some ⟨some .queryFirst, ((ambient, false), register),
        memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (inputWord n m rs) (encodeWords ((rs.drop k).flatMap rowWords))
          (queryWord v k querySuffix) []
          (List.replicate (rowsHits v (rs.take k)) true ++ count)
          (encodeWord 0 ++ querySuffix)⟩ := by
  have hquery := MachineCopy.copyTrace Tape.target Tape.spare Tape.scratch
    (by decide) (by decide) (by decide) false RankLabel.queryFirst RankLabel.querySecond
    (some RankLabel.querySkip) rankProgram rfl rfl
    (memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count [])
    rfl (ambient, false) register
  simp only [memory_target, memory_spare, List.append_nil, update_memory_spare] at hquery
  have hquerySkip := MachineLookup.discardTrace Tape.spare RankLabel.querySkip RankLabel.tableFirst
    rankProgram rfl
    (memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count (queryWord v k querySuffix))
    v (encodeWord k ++ querySuffix) rfl (ambient, false) none
  simp only [update_memory_spare] at hquerySkip
  have hcopy := MachineCopy.copyTrace Tape.original Tape.work Tape.scratch
    (by decide) (by decide) (by decide) false RankLabel.tableFirst RankLabel.tableSecond
    (some RankLabel.headerFirst) rankProgram rfl rfl
    (memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count
      (encodeWord k ++ querySuffix)) rfl (ambient, false) none
  simp only [memory_original, memory_work, List.append_nil, update_memory_work] at hcopy
  have hfirst := MachineLookup.discardTrace Tape.work RankLabel.headerFirst RankLabel.headerSecond
    rankProgram rfl
    (memory (inputWord n m rs) (inputWord n m rs) (queryWord v k querySuffix) [] count
      (encodeWord k ++ querySuffix))
    n (encodeWord m ++ encodeWords (rs.flatMap rowWords))
    (inputWord_eq n m rs) (ambient, false) none
  simp only [update_memory_work] at hfirst
  have hsecond := MachineLookup.discardTrace Tape.work RankLabel.headerSecond RankLabel.row
    rankProgram rfl
    (memory (inputWord n m rs) (encodeWord m ++ encodeWords (rs.flatMap rowWords))
      (queryWord v k querySuffix) [] count (encodeWord k ++ querySuffix))
    m (encodeWords (rs.flatMap rowWords)) rfl (ambient, false) none
  simp only [update_memory_work] at hsecond
  have hprefix := prefixTrace (rs.take k)
    (by intro r hr; exact hwidth r (List.mem_of_mem_take hr)) v
    (inputWord n m rs) (encodeWords ((rs.drop k).flatMap rowWords))
    (encodeWord k ++ querySuffix) querySuffix count ambient none
  have htake : (rs.take k).length = k := by
    simp only [List.length_take, Nat.min_eq_left hk]
  rw [htake, ← encoded_rows_split rs k] at hprefix
  rw [show rankSteps n m v k rs querySuffix = prefixTime v (rs.take k) +
      ((m + 1) + ((n + 1) + (2 * ((inputWord n m rs).length + 1) +
        ((v + 1) + 2 * ((queryWord v k querySuffix).length + 1))))) by
      unfold rankSteps; omega,
    Function.iterate_add_apply _ (prefixTime v (rs.take k)),
    Function.iterate_add_apply _ (m + 1), Function.iterate_add_apply _ (n + 1),
    Function.iterate_add_apply _ (2 * ((inputWord n m rs).length + 1)),
    Function.iterate_add_apply _ (v + 1), hquery, hquerySkip, hcopy, hfirst, hsecond]
  exact hprefix

open UniqueGamesTheorem.Foundations.PCP

/-- Full trace on a genuine stored graph and a genuine member of its cloud.
The complete input table and the entire vertex/dart query remain unchanged. -/
theorem cloudRankTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v)
    (querySuffix countSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[
        rankSteps t.vertices t.darts v.val e.val.val (tableRows t) querySuffix]
      (some ⟨some .queryFirst, ((ambient, false), register),
        memory (GraphTables.tableBits t) [] (queryWord v.val e.val.val querySuffix) []
          (encodeWord 0 ++ countSuffix) []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (GraphTables.tableBits t)
          (encodeWords (((tableRows t).drop e.val.val).flatMap rowWords))
          (queryWord v.val e.val.val querySuffix) []
          (encodeWord (PreprocessingCloudIndex.cloudRank t v e).val ++ countSuffix)
          (encodeWord 0 ++ querySuffix)⟩ := by
  have hk : e.val.val ≤ (tableRows t).length := by
    rw [tableRows_length]
    exact e.val.isLt.le
  have h := rankTrace t.vertices t.darts v.val e.val.val (tableRows t) hk
    (tableRows_width t) querySuffix (encodeWord 0 ++ countSuffix) ambient register
  rw [tableRows_input, ← cloudRank_eq_prefix_count t v e, ← List.append_assoc,
    replicate_encodeWord, Nat.add_zero] at h
  exact h

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudRank

/-! Actual inverse cloud numbering. The input table and query are copied
preservingly. A unary working rank decreases only on equal stored tail
fields; a separate unary row position increases on every skipped row.
Only finite phase flags and symbol registers occur in the control state. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudSelect

open Turing MachineComposition
open MachineCloudCount (Row rowWords rowTime rowsHits tableRows)

variable {σ : Type}

/-- The rest of a row is skipped field by field by the actual fixed program. -/
theorem skipTrace (fields : List Nat) (hwidth : fields.length = 4097)
    (original suffix target rank position : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[(encodeWords fields).length + 1]
      (some (cfg (some (.inl (skipLabel 0))) .advancing original
        (encodeWords fields ++ suffix) target [] rank position ambient none)) =
      some (cfg (some (.inr .dispatch)) .advancing
        original suffix target [] rank position ambient none) := by
  have h := MachineCloudCount.discardFieldsTrace skipLabel (baseProgram (σ := σ)) fields 0
    (by intro i hi; simpa only [Nat.zero_add] using baseProgram_skip (hwidth ▸ hi))
    original suffix target [] [] rank ambient false none
  have hnonempty : fields ≠ [] := by intro h; simp [h] at hwidth
  simp only [Nat.zero_add, hwidth, skipLabel, lt_self_iff_false, ↓reduceDIte,
    hnonempty, ite_false] at h
  have raw : (advance (TM2.step baseProgram))^[(encodeWords fields).length + 1]
      (some ⟨some (skipLabel 0), ((ambient, false), none),
        MachineCloudCount.memory original (encodeWords fields ++ suffix) target [] [] rank⟩) =
      some ⟨none, ((ambient, false), none),
        MachineCloudCount.memory original suffix target [] [] rank⟩ := by
    rw [Function.iterate_succ_apply']
    simp only [skipLabel, dite_eq_left (by decide : 0 < 4097)] at h ⊢
    rw [h, advance_some]
    rfl
  convert liftTrace Phase.advancing position _ _ _ raw using 1 <;> rfl

/-- One nonselected row, with enough remaining rank to pass this row when
it matches. Its global position is incremented on the output tape. -/
theorem rowSkipTrace (r : Row) (hwidth : r.2.length = 4097) (v rank position : Nat)
    (original suffix targetSuffix rankSuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[rowTime v r + 3]
      (some (cfg (some (.inl .field)) .checking original
        (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix) []
        (encodeWord (rank + if r.1 = v then 1 else 0) ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient register)) =
      some (cfg (some (.inl .field)) .checking original suffix
        (encodeWord v ++ targetSuffix) [] (encodeWord rank ++ rankSuffix)
        (encodeWord (position + 1) ++ outputSuffix) ambient none) := by
  have hcompare := compareTrace original (encodeWords r.2 ++ suffix) targetSuffix
    (encodeWord (rank + if r.1 = v then 1 else 0) ++ rankSuffix)
    (encodeWord position ++ outputSuffix) r.1 v ambient register
  have hdispatch : TM2.step program
      (cfg (some (.inr .dispatch)) .checking original (encodeWords r.2 ++ suffix)
        (encodeWord v ++ targetSuffix) (List.replicate (if r.1 = v then 1 else 0) true)
        (encodeWord (rank + if r.1 = v then 1 else 0) ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient none) =
      some (cfg (some (.inl (skipLabel 0))) .advancing original (encodeWords r.2 ++ suffix)
        (encodeWord v ++ targetSuffix) [] (encodeWord rank ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient none) := by
    by_cases hit : r.1 = v
    · simpa only [ite_eq_left hit, List.replicate_succ, List.replicate_zero] using
        dispatch_hit_succ original (encodeWords r.2 ++ suffix) (encodeWord v ++ targetSuffix)
          rankSuffix (encodeWord position ++ outputSuffix) rank ambient
    · simpa only [ite_eq_right hit, Nat.add_zero, List.replicate_zero] using
        dispatch_miss original (encodeWords r.2 ++ suffix) (encodeWord v ++ targetSuffix)
          (encodeWord rank ++ rankSuffix) (encodeWord position ++ outputSuffix) ambient
  have hskip := skipTrace r.2 hwidth original suffix (encodeWord v ++ targetSuffix)
    (encodeWord rank ++ rankSuffix) (encodeWord position ++ outputSuffix) ambient
  have ht : rowTime v r + 3 =
      1 + (((encodeWords r.2).length + 1) + (1 + (r.1 + min r.1 v + 3))) := by
    simp only [rowTime, rowWords, encodeWords, List.length_append, encodeWord_length]
    omega
  rw [ht, Function.iterate_add_apply _ 1,
    Function.iterate_add_apply _ ((encodeWords r.2).length + 1),
    Function.iterate_add_apply _ 1]
  simp only [rowWords, encodeWords, List.append_assoc]
  rw [hcompare, Function.iterate_one, advance_some, hdispatch, hskip,
    advance_some]
  exact advanceStep original suffix (encodeWord v ++ targetSuffix)
    (encodeWord rank ++ rankSuffix) outputSuffix position ambient

/-- A preceding consumes precisely its number of matching tails from unary
rank, while physically counting every original row on the position tape. -/
theorem prefixTrace (rs : List Row) (hwidth : ∀ r ∈ rs, r.2.length = 4097)
    (v rank position : Nat) (original suffix targetSuffix rankSuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[prefixTime v rs]
      (some (cfg (some (.inl .field)) .checking original
        (encodeWords (rs.flatMap rowWords) ++ suffix) (encodeWord v ++ targetSuffix) []
        (encodeWord (rowsHits v rs + rank) ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient register)) =
      some (cfg (some (.inl .field)) .checking original suffix
        (encodeWord v ++ targetSuffix) [] (encodeWord rank ++ rankSuffix)
        (encodeWord (position + rs.length) ++ outputSuffix) ambient
        (if rs = [] then register else none)) := by
  induction rs generalizing position register with
  | nil => simp [prefixTime, rowsHits, encodeWords]
  | cons r rs ih =>
    have hrow := rowSkipTrace r (hwidth r (by simp)) v (rowsHits v rs + rank) position
      original (encodeWords (rs.flatMap rowWords) ++ suffix) targetSuffix rankSuffix
      outputSuffix ambient register
    have hrest := ih (by intro x hx; exact hwidth x (by simp [hx])) (position + 1) none
    simp only [prefixTime, List.flatMap_cons, encodeWords_append, List.append_assoc]
    rw [Function.iterate_add_apply]
    have hi : (if r.1 = v then 1 else 0) + rowsHits v rs + rank =
        (rowsHits v rs + rank) + (if r.1 = v then 1 else 0) := by omega
    simp only [rowsHits, hi]
    rw [hrow]
    simpa only [ite_self, List.cons_ne_nil, ite_false, List.length_cons,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest

/-- Preserve the complete query and table while making the two working
copies; extract the rank and skip the two actual table header fields. -/
theorem prepareTrace (n m v rank : Nat) (rs : List Row)
    (querySuffix position : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[prepareSteps n m v rank rs querySuffix]
      (some (cfg (some (.inl .queryFirst)) .checking (MachineCloudCount.inputWord n m rs)
        [] (queryWord v rank querySuffix) [] [] position ambient register)) =
      some (cfg (some (.inl .field)) .checking (MachineCloudCount.inputWord n m rs)
        (encodeWords (rs.flatMap rowWords)) (queryWord v rank querySuffix) []
        (encodeWord rank ++ querySuffix) position ambient none) := by
  have hquery := MachineCopy.copyTrace MachineCloudCount.Tape.target MachineCloudCount.Tape.spare MachineCloudCount.Tape.scratch
    (by decide) (by decide) (by decide) false BaseLabel.queryFirst BaseLabel.querySecond
    (some BaseLabel.querySkip) baseProgram rfl rfl
    (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs) []
      (queryWord v rank querySuffix) [] [] []) rfl (ambient, false) register
  simp only [MachineCloudCount.memory_target, MachineCloudCount.memory_spare,
    List.append_nil, MachineCloudRank.update_memory_spare] at hquery
  have hquerySkip := MachineLookup.discardTrace MachineCloudCount.Tape.spare BaseLabel.querySkip BaseLabel.tableFirst
    baseProgram rfl (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs) []
      (queryWord v rank querySuffix) [] [] (queryWord v rank querySuffix))
    v (encodeWord rank ++ querySuffix) rfl (ambient, false) none
  simp only [MachineCloudRank.update_memory_spare] at hquerySkip
  have hcopy := MachineCopy.copyTrace MachineCloudCount.Tape.original MachineCloudCount.Tape.work MachineCloudCount.Tape.scratch
    (by decide) (by decide) (by decide) false BaseLabel.tableFirst BaseLabel.tableSecond
    (some BaseLabel.headerFirst) baseProgram rfl rfl
    (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs) []
      (queryWord v rank querySuffix) [] [] (encodeWord rank ++ querySuffix))
    rfl (ambient, false) none
  simp only [MachineCloudCount.memory_original, MachineCloudCount.memory_work,
    List.append_nil, MachineCloudCount.update_memory_work] at hcopy
  have hfirst := MachineLookup.discardTrace MachineCloudCount.Tape.work BaseLabel.headerFirst BaseLabel.headerSecond
    baseProgram rfl (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs)
      (MachineCloudCount.inputWord n m rs) (queryWord v rank querySuffix) [] []
      (encodeWord rank ++ querySuffix))
    n (encodeWord m ++ encodeWords (rs.flatMap rowWords))
    (MachineCloudCount.inputWord_eq n m rs) (ambient, false) none
  simp only [MachineCloudCount.update_memory_work] at hfirst
  have hsecond := MachineLookup.discardTrace MachineCloudCount.Tape.work BaseLabel.headerSecond BaseLabel.field
    baseProgram rfl (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs)
      (encodeWord m ++ encodeWords (rs.flatMap rowWords)) (queryWord v rank querySuffix)
      [] [] (encodeWord rank ++ querySuffix))
    m (encodeWords (rs.flatMap rowWords)) rfl (ambient, false) none
  simp only [MachineCloudCount.update_memory_work] at hsecond
  have raw : (advance (TM2.step baseProgram))^[prepareSteps n m v rank rs querySuffix]
      (some ⟨some .queryFirst, ((ambient, false), register),
        MachineCloudCount.memory (MachineCloudCount.inputWord n m rs) []
          (queryWord v rank querySuffix) [] [] []⟩) =
      some ⟨some .field, ((ambient, false), none),
        MachineCloudCount.memory (MachineCloudCount.inputWord n m rs)
          (encodeWords (rs.flatMap rowWords)) (queryWord v rank querySuffix) [] []
          (encodeWord rank ++ querySuffix)⟩ := by
    rw [show prepareSteps n m v rank rs querySuffix =
        (m + 1) + ((n + 1) + (2 * ((MachineCloudCount.inputWord n m rs).length + 1) +
          ((v + 1) + 2 * ((queryWord v rank querySuffix).length + 1)))) by
          unfold prepareSteps; omega,
      Function.iterate_add_apply _ (m + 1), Function.iterate_add_apply _ (n + 1),
      Function.iterate_add_apply _ (2 * ((MachineCloudCount.inputWord n m rs).length + 1)),
      Function.iterate_add_apply _ (v + 1), hquery, hquerySkip, hcopy, hfirst]
    exact hsecond
  convert liftTrace Phase.checking position _ _ _ raw using 1 <;> rfl

/-- A selected matching field is reached after precisely the matching count
of its actual preceding rows has been consumed from the copied query. -/
theorem prefixSelectedTrace (preceding : List Row)
    (hwidth : ∀ r ∈ preceding, r.2.length = 4097) (v position : Nat)
    (original work targetSuffix rankSuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[prefixTime v preceding + 2 * v + work.length + rankSuffix.length + 8]
      (some (cfg (some (.inl .field)) .checking original
        (encodeWords (preceding.flatMap rowWords) ++ (encodeWord v ++ work))
        (encodeWord v ++ targetSuffix) [] (encodeWord (rowsHits v preceding) ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient register)) =
      some (cfg none .checking original [] (encodeWord v ++ targetSuffix) [] []
        (encodeWord (position + preceding.length) ++ outputSuffix) ambient none) := by
  have hp := prefixTrace preceding hwidth v 0 position original (encodeWord v ++ work)
    targetSuffix rankSuffix outputSuffix ambient register
  simp only [Nat.add_zero] at hp
  have hs := selectedTrace v original work targetSuffix rankSuffix
    (encodeWord (position + preceding.length) ++ outputSuffix) ambient
    (if preceding = [] then register else none)
  rw [show prefixTime v preceding + 2 * v + work.length + rankSuffix.length + 8 =
      (2 * v + work.length + rankSuffix.length + 8) + prefixTime v preceding by omega,
    Function.iterate_add_apply, hp]
  exact hs

/-- Complete execution for the actual encoded preceding decomposition. The
decomposition is semantic data; every machine phase is proved above. -/
theorem fullTrace (n m v rank : Nat) (rs preceding : List Row) (work : List Bool)
    (hwidth : ∀ r ∈ preceding, r.2.length = 4097)
    (hword : encodeWords (rs.flatMap rowWords) =
      encodeWords (preceding.flatMap rowWords) ++ (encodeWord v ++ work))
    (hrank : rank = rowsHits v preceding) (querySuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[totalSteps n m v rank rs preceding work querySuffix]
      (some (cfg (some (.inr .initialize_)) .checking (MachineCloudCount.inputWord n m rs)
        [] (queryWord v rank querySuffix) [] [] outputSuffix ambient register)) =
      some (cfg none .checking (MachineCloudCount.inputWord n m rs) []
        (queryWord v rank querySuffix) [] [] (encodeWord preceding.length ++ outputSuffix) ambient none) := by
  have hp := prepareTrace n m v rank rs querySuffix (encodeWord 0 ++ outputSuffix) ambient none
  have hs := prefixSelectedTrace preceding hwidth v 0 (MachineCloudCount.inputWord n m rs) work
    (encodeWord rank ++ querySuffix) querySuffix outputSuffix ambient none
  simp only [Nat.zero_add] at hs
  rw [← hrank, ← hword] at hs
  rw [show totalSteps n m v rank rs preceding work querySuffix =
      (prefixTime v preceding + 2 * v + work.length + querySuffix.length + 8) +
        (prepareSteps n m v rank rs querySuffix + 1) by unfold totalSteps; omega,
    Function.iterate_add_apply _ (prefixTime v preceding + 2 * v + work.length + querySuffix.length + 8),
    Function.iterate_succ_apply _ (prepareSteps n m v rank rs querySuffix),
    advance_some, initializeStep, hp]
  exact hs

open UniqueGamesTheorem.Foundations.PCP

theorem cloudSelectTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v)) (querySuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[cloudSelectSteps t v i querySuffix]
      (some (cfg (some (.inr .initialize_)) .checking (GraphTables.tableBits t)
        [] (queryWord v.val i.val querySuffix) [] [] outputSuffix ambient register)) =
      some (cfg none .checking (GraphTables.tableBits t) [] (queryWord v.val i.val querySuffix)
        [] [] (encodeWord (PreprocessingCloudIndex.cloudSelect t v i).val.val ++ outputSuffix)
        ambient none) := by
  let e := PreprocessingCloudIndex.cloudSelect t v i
  have hword := tableWord_split t v e.val e.property
  have hrank : i.val = rowsHits v.val ((tableRows t).take e.val.val) := by
    simpa only [PreprocessingCloudIndex.cloudRank_cloudSelect] using
      MachineCloudRank.cloudRank_eq_prefix_count t v (PreprocessingCloudIndex.cloudSelect t v i)
  have h := fullTrace t.vertices t.darts v.val i.val (tableRows t)
    ((tableRows t).take e.val.val) (remainder t e.val)
    (by intro r hr; exact MachineCloudCount.tableRows_width t r (List.mem_of_mem_take hr))
    hword hrank querySuffix outputSuffix ambient register
  have htake : ((tableRows t).take e.val.val).length = e.val.val := by
    rw [List.length_take, MachineCloudRank.tableRows_length,
      Nat.min_eq_left e.val.isLt.le]
  rw [MachineCloudCount.tableRows_input, htake] at h
  exact h

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudSelect

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderRowDivision
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The two actual division phases of the expander-row program. Static state
conjugation connects the fixed-divisor machine to the common emitter state.
Only the concrete statement placement equations are premises; no phase trace
or whole-row execution is assumed. Each phase has exactly `n + 2` transitions.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

/-- Pull the actual target program into division-state coordinates, derive its
trace from its concrete statements, then transport every actual transition back. -/
theorem transportedDivision {K Λ σ τ : Type} [DecidableEq K] [Fintype σ]
    (q : Nat) (positive : 0 < q) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder)
    (states : MachineFixedDivMod.State σ q ≃ τ)
    (scanLabel : Λ) (emitterLabel : Fin q → Λ) (exit : Option Λ)
    (finish : σ → Fin q → σ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ τ)
    (atScan : target scanLabel = MachineControl.statement id states
      (MachineFixedDivMod.scanLoop q positive source quotient scanLabel emitterLabel))
    (atEmitter : ∀ r, target (emitterLabel r) = MachineControl.statement id states
      (MachineFixedDivMod.emitterWithFinish q positive remainder exit finish r))
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (sourceInput : base source = encodeWord n ++ sourceSuffix)
    (quotientInput : base quotient = encodeWord 0 ++ quotientSuffix)
    (remainderInput : base remainder = encodeWord 0 ++ remainderSuffix)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step target))^[n + 2]
      (some (MachineControl.configuration id states
        ⟨some scanLabel, ((ambient, MachineFixedDivMod.residue q positive 0), register), base⟩)) =
      some (MachineControl.configuration id states
        ⟨exit, ((finish ambient (MachineFixedDivMod.residue q positive n),
          MachineFixedDivMod.residue q positive 0), none),
          MachineFixedDivMod.unaryTapes source quotient remainder base 0 (n / q) (n % q)
            sourceSuffix quotientSuffix remainderSuffix⟩) := by
  let sourceProgram := MachineControl.program (Equiv.refl Λ) states.symm target
  have sourceScan : sourceProgram scanLabel =
      MachineFixedDivMod.scanLoop q positive source quotient scanLabel emitterLabel := by
    change MachineControl.statement id states.symm (target scanLabel) = _
    rw [atScan]
    exact controlStatement_inverse states _
  have sourceEmit : ∀ r, sourceProgram (emitterLabel r) =
      MachineFixedDivMod.emitterWithFinish q positive remainder exit finish r := by
    intro r
    change MachineControl.statement id states.symm (target (emitterLabel r)) = _
    rw [atEmitter]
    exact controlStatement_inverse states _
  have htrace := MachineFixedDivMod.divModFromTapesWithFinish q positive source quotient
    remainder sourceQuotient sourceRemainder quotientRemainder scanLabel emitterLabel exit
    finish sourceProgram sourceScan sourceEmit base n sourceSuffix quotientSuffix remainderSuffix
    sourceInput quotientInput remainderInput ambient register
  have roundtrip : MachineControl.program (Equiv.refl Λ) states sourceProgram = target := by
    funext label
    change MachineControl.statement id states
      (MachineControl.statement id states.symm (target label)) = target label
    exact controlStatement_inverse states.symm _
  have simulation : ∀ a b, TM2.step sourceProgram a = some b →
      TM2.step target (MachineControl.configuration id states a) =
        some (MachineControl.configuration id states b) := by
    intro a b hab
    have h := MachineControl.step_simulation (Equiv.refl Λ) states sourceProgram a
    rw [roundtrip, hab] at h
    exact h
  exact MachineComposition.liftSuccessfulTrace (TM2.step sourceProgram) (TM2.step target)
    (MachineControl.configuration id states) simulation (n + 2) _ _ htrace

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

/-- Exact first lookup-result division, including the receiveFirst control update. -/
theorem firstDivisionTrace {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atProgram : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (sourceInput : base (ports .lookupOutput) = encodeWord n ++ sourceSuffix)
    (quotientInput : base (ports .quotientFirst) = encodeWord 0 ++ quotientSuffix)
    (remainderInput : base (ports .remainderFirst) = encodeWord 0 ++ remainderSuffix)
    (ambient : ρ) (control : Control d) (register : Option Bool) :
    (MachineComposition.advance (TM2.step target))^[n + 2]
      (some ⟨some (labels .firstScan), divisionState positive ambient control register, base⟩) =
      some ⟨some (labels .clearQuery), divisionState positive ambient
        (receiveFirst control (MachineFixedDivMod.residue (degree d)
          (Nat.mul_pos positive positive) n)) none,
        divisionOutput d ports .quotientFirst .remainderFirst base n
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  have hsq : ports .lookupOutput ≠ ports .quotientFirst :=
    fun h => Tape.noConfusion (portsInjective h)
  have hsr : ports .lookupOutput ≠ ports .remainderFirst :=
    fun h => Tape.noConfusion (portsInjective h)
  have hqr : ports .quotientFirst ≠ ports .remainderFirst :=
    fun h => Tape.noConfusion (portsInjective h)
  have hs : target (labels .firstScan) = MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.scanLoop (degree d) (Nat.mul_pos positive positive)
        (ports .lookupOutput) (ports .quotientFirst) (labels .firstScan)
        (fun r => labels (.firstResidue r))) := atProgram .firstScan
  have he : ∀ r, target (labels (.firstResidue r)) =
      MachineControl.statement id (divisionStates ρ d)
        (MachineFixedDivMod.emitterWithFinish (degree d) (Nat.mul_pos positive positive)
          (ports .remainderFirst) (some (labels .clearQuery)) firstFinish r) :=
    fun r => atProgram (.firstResidue r)
  have h := transportedDivision (degree d) (Nat.mul_pos positive positive)
    (ports .lookupOutput) (ports .quotientFirst) (ports .remainderFirst) hsq hsr hqr
    (divisionStates ρ d) (labels .firstScan) (fun r => labels (.firstResidue r))
    (some (labels .clearQuery)) firstFinish target hs he base n sourceSuffix quotientSuffix
    remainderSuffix sourceInput quotientInput remainderInput ((ambient, control), ()) register
  simpa only [MachineControl.configuration, divisionStates_apply, firstFinish, divisionState,
    divisionOutput, Option.map_some, id_eq] using h

/-- Exact second division, including receiveSecond and the actual output-emitter entry label. -/
theorem secondDivisionTrace {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atProgram : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (sourceInput : base (ports .lookupOutput) = encodeWord n ++ sourceSuffix)
    (quotientInput : base (ports .quotientSecond) = encodeWord 0 ++ quotientSuffix)
    (remainderInput : base (ports .remainderSecond) = encodeWord 0 ++ remainderSuffix)
    (ambient : ρ) (control : Control d) (register : Option Bool) :
    (MachineComposition.advance (TM2.step target))^[n + 2]
      (some ⟨some (labels .secondScan), divisionState positive ambient control register, base⟩) =
      some ⟨some (labels (.outputEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient
          (receiveSecond H control (MachineFixedDivMod.residue (degree d)
            (Nat.mul_pos positive positive) n)) none,
        divisionOutput d ports .quotientSecond .remainderSecond base n
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  have hsq : ports .lookupOutput ≠ ports .quotientSecond :=
    fun h => Tape.noConfusion (portsInjective h)
  have hsr : ports .lookupOutput ≠ ports .remainderSecond :=
    fun h => Tape.noConfusion (portsInjective h)
  have hqr : ports .quotientSecond ≠ ports .remainderSecond :=
    fun h => Tape.noConfusion (portsInjective h)
  have hs : target (labels .secondScan) = MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.scanLoop (degree d) (Nat.mul_pos positive positive)
        (ports .lookupOutput) (ports .quotientSecond) (labels .secondScan)
        (fun r => labels (.secondResidue r))) := atProgram .secondScan
  have he : ∀ r, target (labels (.secondResidue r)) =
      MachineControl.statement id (divisionStates ρ d)
        (MachineFixedDivMod.emitterWithFinish (degree d) (Nat.mul_pos positive positive)
          (ports .remainderSecond)
          (some (labels (.outputEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))))
          (secondFinish H) r) := fun r => atProgram (.secondResidue r)
  have h := transportedDivision (degree d) (Nat.mul_pos positive positive)
    (ports .lookupOutput) (ports .quotientSecond) (ports .remainderSecond) hsq hsr hqr
    (divisionStates ρ d) (labels .secondScan) (fun r => labels (.secondResidue r))
    (some (labels (.outputEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))))
    (secondFinish H) target hs he base n sourceSuffix quotientSuffix remainderSuffix
    sourceInput quotientInput remainderInput ((ambient, control), ()) register
  simpa only [MachineControl.configuration, divisionStates_apply, secondFinish, divisionState,
    divisionOutput, Option.map_some, id_eq] using h

@[simp] theorem divisionOutput_source (d : Nat) (ports : Tape → K)
    (portsInjective : Function.Injective ports) (quotient remainder : Tape)
    (notSourceQuotient : Tape.lookupOutput ≠ quotient)
    (notSourceRemainder : Tape.lookupOutput ≠ remainder)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool) :
    divisionOutput d ports quotient remainder base n sourceSuffix quotientSuffix remainderSuffix
      (ports .lookupOutput) = encodeWord 0 ++ sourceSuffix := by
  exact MachineFixedDivMod.unaryTapes_source _ _ _
    (fun h => notSourceQuotient (portsInjective h))
    (fun h => notSourceRemainder (portsInjective h)) _ _ _ _ _ _ _

@[simp] theorem divisionOutput_quotient (d : Nat) (ports : Tape → K)
    (portsInjective : Function.Injective ports) (quotient remainder : Tape)
    (distinct : quotient ≠ remainder) (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool) :
    divisionOutput d ports quotient remainder base n sourceSuffix quotientSuffix remainderSuffix
      (ports quotient) = encodeWord (n / degree d) ++ quotientSuffix := by
  exact MachineFixedDivMod.unaryTapes_quotient _ _ _
    (fun h => distinct (portsInjective h)) _ _ _ _ _ _ _

@[simp] theorem divisionOutput_remainder (d : Nat) (ports : Tape → K)
    (quotient remainder : Tape) (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool) :
    divisionOutput d ports quotient remainder base n sourceSuffix quotientSuffix remainderSuffix
      (ports remainder) = encodeWord (n % degree d) ++ remainderSuffix := by
  exact MachineFixedDivMod.unaryTapes_remainder _ _ _ _ _ _ _ _ _ _

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderTableProgramLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

abbrev Tape := MachineExpanderRow.Tape ⊕ ExtraTape

abbrev Alphabet : Tape → Type :=
  MachineEmbedding.Alphabet (fun _ : MachineExpanderRow.Tape => Bool)
    (fun _ : ExtraTape => Bool)

instance alphabetFintype (tape : Tape) : Fintype (Alphabet tape) := by
  cases tape <;> exact inferInstanceAs (Fintype Bool)

abbrev RowStatePrefix (ρ : Type) (d : Nat) :=
  (MachineExpanderRow.Ambient ρ d × Fin (degree d)) × Unit

/-- Static movement of the bit register to the last product coordinate. -/
def guardStates (ρ : Type) (d : Nat) :
    ((RowStatePrefix ρ d × Position d) × Option Bool) ≃ State ρ d where
  toFun s := ((s.1.1, s.2), s.1.2)
  invFun s := ((s.1.1, s.2), s.1.2)
  left_inv := by rintro ⟨⟨a, p⟩, b⟩; rfl
  right_inv := by rintro ⟨⟨a, b⟩, p⟩; rfl

@[simp] theorem guardStates_apply (ρ : Type) (d : Nat)
    (s : (RowStatePrefix ρ d × Position d) × Option Bool) :
    guardStates ρ d s = ((s.1.1, s.2), s.1.2) := rfl

@[simp] theorem guardStates_symm_apply (ρ : Type) (d : Nat) (s : State ρ d) :
    (guardStates ρ d).symm s = ((s.1.1, s.2), s.1.2) := rfl

theorem rowFactor_pos {d : Nat} (positive : 0 < d) : 0 < rowFactor d := by
  have hq : 0 < degree d := Nat.mul_pos positive positive
  exact Nat.mul_pos (Nat.mul_pos hq hq) hq

def zeroPosition {d : Nat} (positive : 0 < d) : Position d :=
  ⟨0, rowFactor_pos positive⟩

def nextPosition {d : Nat} (positive : 0 < d) (p : Position d) : Position d :=
  ⟨(p.val + 1) % rowFactor d, Nat.mod_lt _ (rowFactor_pos positive)⟩

def positionPair {d : Nat} (p : Position d) : Fin (cloudSize d) × Fin (degree d) :=
  (rowIndex (cloudSize d) (degree d)).symm p

def caller {ρ : Type} {d : Nat} (s : State ρ d) : ρ := s.1.1.1.1.1

/-- A fresh row call, with its residue and bit register reset. -/
def boundaryState {ρ : Type} {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (ambient : ρ) (p : Position d) : State ρ d :=
  (MachineExpanderRow.divisionState positive ambient
    (start H (positionPair p).1 (positionPair p).2) none, p)

def initialState {ρ : Type} {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (ambient : ρ) : State ρ d :=
  boundaryState positive H ambient (zeroPosition positive)

def prepareState {ρ : Type} {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (s : State ρ d) : State ρ d :=
  boundaryState positive H (caller s) s.2

def resetState {ρ : Type} {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (s : State ρ d) : State ρ d :=
  initialState positive H (caller s)

def clearRegister {ρ : Type} {d : Nat} (s : State ρ d) : State ρ d :=
  ((s.1.1, none), s.2)

def advancePositionState {ρ : Type} {d : Nat} (positive : 0 < d)
    (s : State ρ d) : State ρ d := (s.1, nextPosition positive s.2)

def resetPositionState {ρ : Type} {d : Nat} (positive : 0 < d)
    (s : State ρ d) : State ρ d := (s.1, zeroPosition positive)

/-- The unary guard specialized to the concrete extra tape. The zero delimiter
is retained; both branches clear the bit register. Its dependent alphabet is
the same alphabet used by the embedded row program. -/
def vertexGuardCore {ρ : Type} {d : Nat} :
    TM2.Stmt Alphabet (Label d) ((RowStatePrefix ρ d × Position d) × Option Bool) :=
  .peek (.inr .vertexCount) (fun s head => (s.1, head))
    (.branch (fun s => s.2.getD false)
      (.pop (.inr .vertexCount) (fun s _ => (s.1, none))
        (.goto fun _ => .inr .prepareRow))
      (.load (fun s => (s.1, none)) (.goto fun _ => .inr .reverseOutput)))

variable {ρ : Type} [Fintype ρ]

/-- Actual statements for the table loop. No unbounded natural number is
stored in the state or evaluated by a state-update function. -/
def outerStatement {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d) :
    OuterLabel → TM2.Stmt Alphabet (Label d) (State ρ d)
  | .initialize_ =>
    .push (.inl .inputVertex) (fun _ => false)
      (.load (resetState positive H) (.goto fun _ => .inr .vertexGuard))
  | .vertexGuard => MachineControl.statement id (guardStates ρ d) vertexGuardCore
  | .prepareRow =>
    .load (prepareState positive H) (.goto fun _ => .inl .initialize_)
  | .afterRow =>
    .branch (fun s => decide (s.2.val + 1 < rowFactor d))
      (.load (advancePositionState positive) (.goto fun _ => .inr .prepareRow))
      (.push (.inl .inputVertex) (fun _ => true)
        (.load (resetPositionState positive) (.goto fun _ => .inr .vertexGuard)))
  | .reverseOutput =>
    MachineControl.statement id (guardStates ρ d)
      (Reduction.MachineTransfer.loopAt (Γ := Alphabet) (Λ := Label d)
        (σ := RowStatePrefix ρ d × Position d) (.inl .output) (.inr .result) id false
        (.inr .reverseOutput) (some (.inr .done)))
  | .done => .halt

/-- The complete finite program. The vertex count is supplied on a tape,
while the small table and all finite control types depend only on fixed `d`. -/
def program {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d) :
    Label d → TM2.Stmt Alphabet (Label d) (State ρ d) :=
  MachineEmbedding.program (rowReturn d) (MachineExpanderRow.program positive H)
    (outerStatement positive H)

@[simp] theorem program_row {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (label : MachineExpanderRow.Label d) :
    program (ρ := ρ) positive H (.inl label) =
      MachineEmbedding.statement (rowReturn d)
        (MachineExpanderRow.program positive H label) := rfl

@[simp] theorem program_outer {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (label : OuterLabel) :
    program (ρ := ρ) positive H (.inr label) = outerStatement positive H label := rfl

/-- Every transition of an actual row run embeds with its original cost,
preserving the position and both extra tapes, including its return jump. -/
def rowExecution {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (position : Position d) (extra : ExtraTape → List Bool)
    {a b : TM2.Cfg (fun _ : MachineExpanderRow.Tape => Bool)
      (MachineExpanderRow.Label d) (MachineExpanderRow.State ρ d)} {budget : Nat}
    (execution : StateTransition.EvalsToInTime
      (TM2.step (MachineExpanderRow.program positive H)) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      (MachineEmbedding.configuration (rowReturn d) position extra a)
      (some (MachineEmbedding.configuration (rowReturn d) position extra b)) budget :=
  MachineComposition.embeddedExecution (rowReturn d) position extra
    (MachineExpanderRow.program positive H) (outerStatement positive H) execution

@[simp] theorem rowExecution_steps {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (position : Position d) (extra : ExtraTape → List Bool)
    {a b : TM2.Cfg (fun _ : MachineExpanderRow.Tape => Bool)
      (MachineExpanderRow.Label d) (MachineExpanderRow.State ρ d)} {budget : Nat}
    (execution : StateTransition.EvalsToInTime
      (TM2.step (MachineExpanderRow.program positive H)) a (some b) budget) :
    (rowExecution positive H position extra execution).steps = execution.steps := rfl

def rowTapes (vertex : Nat) (oldTable output : List Bool) : MachineExpanderRow.Tape → List Bool
  | .inputVertex => encodeWord vertex
  | .table => oldTable
  | .output => output
  | _ => []

def extraTapes (remaining : Nat) (countSuffix result : List Bool) : ExtraTape → List Bool
  | .vertexCount => encodeWord remaining ++ countSuffix
  | .result => result

def boundaryTapes (vertex remaining : Nat) (oldTable output countSuffix result : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes (rowTapes vertex oldTable output) (extraTapes remaining countSuffix result)

/-- Before initialization, only the old table and remaining-count word are
populated. The program itself creates the initial vertex delimiter. -/
def initialTapes (vertices : Nat) (oldTable countSuffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes
    (fun tape => match tape with | .table => oldTable | _ => [])
    (extraTapes vertices countSuffix [])

def finalTapes (vertices : Nat) (oldTable output countSuffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  boundaryTapes vertices 0 oldTable [] countSuffix output

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

abbrev Tape := MachineExpanderTable.Tape ⊕ ExtraTape
abbrev Alphabet : Tape → Type :=
  MachineEmbedding.Alphabet MachineExpanderTable.Alphabet (fun _ : ExtraTape => Bool)
abbrev BoolAlphabet (_ : Tape) := Bool

/-- All physical tapes contain Booleans. This equality changes the static
type presentation only; no runtime symbol conversion is performed. -/
theorem alphabet_eq : Alphabet = BoolAlphabet := by
  funext tape
  cases tape with
  | inl tape => cases tape <;> rfl
  | inr tape => rfl

instance alphabetFintype (tape : Tape) : Fintype (Alphabet tape) := by
  rw [alphabet_eq]
  exact inferInstanceAs (Fintype Bool)

abbrev Label (d : Nat) := MachineExpanderTable.Label d ⊕ OuterLabel
abbrev State (ρ : Type) (d : Nat) := MachineExpanderTable.State ρ d × Unit
abbrev RegisterAmbient (ρ : Type) (d : Nat) :=
  (MachineExpanderTable.RowStatePrefix ρ d × MachineExpanderTable.Position d) × Unit

def registerStates (ρ : Type) (d : Nat) :
    (RegisterAmbient ρ d × Option Bool) ≃ State ρ d where
  toFun s := (((s.1.1.1, s.2), s.1.1.2), s.1.2)
  invFun s := (((s.1.1.1, s.1.2), s.2), s.1.1.2)
  left_inv := by rintro ⟨⟨⟨a, p⟩, u⟩, b⟩; rfl
  right_inv := by rintro ⟨⟨⟨a, b⟩, p⟩, u⟩; rfl

@[simp] theorem registerStates_apply (ρ : Type) (d : Nat)
    (s : RegisterAmbient ρ d × Option Bool) :
    registerStates ρ d s = (((s.1.1.1, s.2), s.1.1.2), s.1.2) := rfl

@[simp] theorem registerStates_symm_apply (ρ : Type) (d : Nat) (s : State ρ d) :
    (registerStates ρ d).symm s = (((s.1.1.1, s.1.2), s.2), s.1.1.2) := rfl

def caller {ρ : Type} {d : Nat} (s : State ρ d) : ρ :=
  MachineExpanderTable.caller s.1

def initialState {ρ : Type} {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (ambient : ρ) : State ρ d :=
  (MachineExpanderTable.initialState positive H ambient, ())

def normalizeState {ρ : Type} {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (s : State ρ d) : State ρ d :=
  initialState positive H (caller s)

def initialEncoding (d : Nat) : List Bool := encodeWords (rotationWords (initial d))

def tableTape : Tape := .inl (.inl .table)
def inputVertexTape : Tape := .inl (.inl .inputVertex)
def vertexCountTape : Tape := .inl (.inr .vertexCount)
def resultTape : Tape := .inl (.inr .result)

def affineSource : AffinePhase → Tape
  | .copyCount => .inr .currentSize
  | .multiplySize => inputVertexTape

def affineDestination : AffinePhase → Tape
  | .copyCount => vertexCountTape
  | .multiplySize => .inr .currentSize

def affineCoefficient (d : Nat) : AffinePhase → Nat
  | .multiplySize => cloudSize d
  | .copyCount => 1

def affineExit (d : Nat) : AffinePhase → Label d
  | .copyCount => .inl (.inr .initialize_)
  | .multiplySize => .inr .drainInputVertex

def affineStatement {ρ : Type} {d : Nat} (phase : AffinePhase) :
    AffineLabel → TM2.Stmt BoolAlphabet (Label d) (State ρ d)
  | .seed =>
    MachineControl.statement id (registerStates ρ d)
      (MachineUnaryAffineAt.seed (Λ := Label d) (σ := RegisterAmbient ρ d)
        (affineDestination phase) 0 (.inr (.affine phase .scan)))
  | .scan =>
    MachineControl.statement id (registerStates ρ d)
      (MachineUnaryAffineAt.scan (Λ := Label d) (σ := RegisterAmbient ρ d)
        (affineSource phase) (.inr .unaryScratch)
        (affineDestination phase) (affineCoefficient d phase)
        (.inr (.affine phase .scan)) (.inr (.affine phase .restore)))
  | .restore =>
    MachineControl.statement id (registerStates ρ d)
      (Reduction.MachineTransfer.loopAt (Γ := BoolAlphabet) (Λ := Label d)
        (σ := RegisterAmbient ρ d) (.inr .unaryScratch) (affineSource phase) id false
        (.inr (.affine phase .restore)) (some (affineExit d phase)))

def drainStatement {ρ : Type} {d : Nat} (tape : Tape) (again next : OuterLabel) :
    TM2.Stmt BoolAlphabet (Label d) (State ρ d) :=
  MachineControl.statement id (registerStates ρ d)
    (MachineDrain.drain (Λ := Label d) (σ := RegisterAmbient ρ d)
      tape (.inr again) (some (.inr next)))

variable {ρ : Type} [Fintype ρ]

/-- Uniform-alphabet presentation of the actual outer code. All arithmetic
parameters here are fixed program constants; runtime sizes are scanned. -/
def boolOuterStatement {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d) :
    OuterLabel → TM2.Stmt BoolAlphabet (Label d) (State ρ d)
  | .initialize_ =>
    Reduction.MachineSubstitution.pushWord tableTape (initialEncoding d).reverse
      (Reduction.MachineSubstitution.pushWord (.inr .currentSize) (encodeWord 1).reverse
        (.load (normalizeState positive H)
          (.goto fun _ => .inr .levelGuard)))
  | .levelGuard =>
    MachineControl.statement id (registerStates ρ d)
      (MachineUnaryCounter.guard (K := Tape) (Λ := Label d) (σ := RegisterAmbient ρ d)
        (.inr .remainingLevel) (.inr (.affine .copyCount .seed)) (.inr .done))
  | .affine phase label => affineStatement phase label
  | .clearOldTable => drainStatement tableTape .clearOldTable .reverseResult
  | .reverseResult =>
    MachineControl.statement id (registerStates ρ d)
      (Reduction.MachineTransfer.loopAt (Γ := BoolAlphabet) (Λ := Label d)
        (σ := RegisterAmbient ρ d) resultTape (.inr .tableReverse) id false
        (.inr .reverseResult) (some (.inr .reverseTable)))
  | .reverseTable =>
    MachineControl.statement id (registerStates ρ d)
      (Reduction.MachineTransfer.loopAt (Γ := BoolAlphabet) (Λ := Label d)
        (σ := RegisterAmbient ρ d) (.inr .tableReverse) tableTape id false
        (.inr .reverseTable) (some (.inr .clearCurrentSize)))
  | .clearCurrentSize =>
    drainStatement (.inr .currentSize) .clearCurrentSize (.affine .multiplySize .seed)
  | .drainInputVertex => drainStatement inputVertexTape .drainInputVertex .drainVertexCount
  | .drainVertexCount => drainStatement vertexCountTape .drainVertexCount .levelGuard
  | .done => .load (normalizeState positive H) .halt

def outerStatement {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (label : OuterLabel) : TM2.Stmt Alphabet (Label d) (State ρ d) :=
  MachineAlphabetTransport.statement alphabet_eq.symm (boolOuterStatement positive H label)

def tableReturn (d : Nat) : Option (Label d) := some (.inr .clearOldTable)

def program {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (_growth : 1 < cloudSize d) : Label d → TM2.Stmt Alphabet (Label d) (State ρ d) :=
  MachineEmbedding.program (tableReturn d) (MachineExpanderTable.program positive H)
    (outerStatement positive H)

@[simp] theorem program_table {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (label : MachineExpanderTable.Label d) :
    program (ρ := ρ) positive H growth (.inl label) =
      MachineEmbedding.statement (tableReturn d)
        (MachineExpanderTable.program positive H label) := rfl

@[simp] theorem program_outer {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (growth : 1 < cloudSize d) (label : OuterLabel) :
    program (ρ := ρ) positive H growth (.inr label) = outerStatement positive H label := rfl

def boolView {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) : Label d → TM2.Stmt BoolAlphabet (Label d) (State ρ d) :=
  MachineAlphabetTransport.program alphabet_eq (program positive H growth)

@[simp] theorem boolView_outer {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (growth : 1 < cloudSize d) (label : OuterLabel) :
    boolView (ρ := ρ) positive H growth (.inr label) =
      boolOuterStatement positive H label := by
  change MachineAlphabetTransport.statement alphabet_eq
    (MachineAlphabetTransport.statement alphabet_eq.symm
      (boolOuterStatement positive H label)) = _
  exact MachineAlphabetTransport.statement_roundtrip alphabet_eq _

def tableExecution {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (extra : ExtraTape → List Bool)
    {a b : TM2.Cfg MachineExpanderTable.Alphabet (MachineExpanderTable.Label d)
      (MachineExpanderTable.State ρ d)} {budget : Nat}
    (execution : StateTransition.EvalsToInTime
      (TM2.step (MachineExpanderTable.program positive H)) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      (MachineEmbedding.configuration (tableReturn d) () extra a)
      (some (MachineEmbedding.configuration (tableReturn d) () extra b)) budget :=
  MachineComposition.embeddedExecution (tableReturn d) () extra
    (MachineExpanderTable.program positive H) (outerStatement positive H) execution

@[simp] theorem tableExecution_steps {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (extra : ExtraTape → List Bool)
    {a b : TM2.Cfg MachineExpanderTable.Alphabet (MachineExpanderTable.Label d)
      (MachineExpanderTable.State ρ d)} {budget : Nat}
    (execution : StateTransition.EvalsToInTime
      (TM2.step (MachineExpanderTable.program positive H)) a (some b) budget) :
    (tableExecution positive H growth extra execution).steps = execution.steps := rfl

def tableFrame (word : List Bool) : (tape : MachineExpanderTable.Tape) →
    List (MachineExpanderTable.Alphabet tape)
  | .inl .table => word
  | .inl _ => []
  | .inr _ => []

def extraFrame (remaining current : Nat) (levelSuffix : List Bool) : ExtraTape → List Bool
  | .remainingLevel => encodeWord remaining ++ levelSuffix
  | .currentSize => encodeWord current
  | _ => []

def boundaryTapes (remaining current : Nat) (word levelSuffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes (tableFrame word) (extraFrame remaining current levelSuffix)

def initialTapes (level : Nat) (levelSuffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes (tableFrame [])
    (fun tape => match tape with
      | .remainingLevel => encodeWord level ++ levelSuffix
      | _ => [])

def familyTapes {d : Nat} (H : Table (cloudSize d) d) (level : Nat)
    (levelSuffix : List Bool) : (tape : Tape) → List (Alphabet tape) :=
  boundaryTapes 0 (vertexCount (degree d) level)
    (encodeWords (rotationWords (family H level))) levelSuffix

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderFamilyTapes
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Static, pointwise Boolean presentation of the actual family tape alphabet.
Every conversion below is an identity on symbols and has no machine runtime. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

open Turing

def boolWord : (tape : Tape) → List Bool → List (Alphabet tape)
  | .inl (.inl _), word => word
  | .inl (.inr _), word => word
  | .inr _, word => word

def toBoolWord : (tape : Tape) → List (Alphabet tape) → List Bool
  | .inl (.inl _), word => word
  | .inl (.inr _), word => word
  | .inr _, word => word

def fromBoolTapes (base : Tape → List Bool) : (tape : Tape) → List (Alphabet tape) :=
  fun tape => boolWord tape (base tape)

def toBoolTapes (base : (tape : Tape) → List (Alphabet tape)) : Tape → List Bool :=
  fun tape => toBoolWord tape (base tape)

@[simp] theorem toBoolWord_boolWord (tape : Tape) (word : List Bool) :
    toBoolWord tape (boolWord tape word) = word := by
  rcases tape with tape | tape
  · cases tape <;> rfl
  · rfl

@[simp] theorem boolWord_toBoolWord (tape : Tape) (word : List (Alphabet tape)) :
    boolWord tape (toBoolWord tape word) = word := by
  rcases tape with tape | tape
  · cases tape <;> rfl
  · rfl

@[simp] theorem toBool_fromBool (base : Tape → List Bool) :
    toBoolTapes (fromBoolTapes base) = base := by
  funext tape
  exact toBoolWord_boolWord tape (base tape)

@[simp] theorem fromBool_toBool (base : (tape : Tape) → List (Alphabet tape)) :
    fromBoolTapes (toBoolTapes base) = base := by
  funext tape
  exact boolWord_toBoolWord tape (base tape)

theorem toBoolTapes_eq_transport (base : (tape : Tape) → List (Alphabet tape)) :
    toBoolTapes base = MachineAlphabetTransport.tapes alphabet_eq base := by
  funext tape
  rw [transport_tapes_apply]
  rcases tape with tape | tape
  · cases tape <;> rfl
  · rfl

theorem fromBoolTapes_eq_transport (base : Tape → List Bool) :
    fromBoolTapes base = MachineAlphabetTransport.tapes alphabet_eq.symm base := by
  funext tape
  rw [transport_tapes_apply]
  rcases tape with tape | tape
  · cases tape <;> rfl
  · rfl

@[simp] theorem fromBoolTapes_update (base : Tape → List Bool) (tape : Tape) (word : List Bool) :
    fromBoolTapes (Function.update base tape word) =
      Function.update (fromBoolTapes base) tape (boolWord tape word) := by
  funext k
  by_cases h : k = tape
  · subst k
    simp [fromBoolTapes]
  · simp [fromBoolTapes, h]

@[simp] theorem toBoolTapes_update (base : (tape : Tape) → List (Alphabet tape))
    (tape : Tape) (word : List (Alphabet tape)) :
    toBoolTapes (Function.update base tape word) =
      Function.update (toBoolTapes base) tape (toBoolWord tape word) := by
  funext k
  by_cases h : k = tape
  · subst k
    simp [toBoolTapes]
  · simp [toBoolTapes, h]

theorem configuration_fromBool {ρ : Type} {d : Nat} (label : Option (Label d))
    (state : State ρ d) (base : Tape → List Bool) :
    MachineAlphabetTransport.configuration alphabet_eq.symm ⟨label, state, base⟩ =
      ⟨label, state, fromBoolTapes base⟩ := by
  rw [MachineAlphabetTransport.configuration_mk, fromBoolTapes_eq_transport]

theorem configuration_toBool {ρ : Type} {d : Nat} (label : Option (Label d))
    (state : State ρ d) (base : (tape : Tape) → List (Alphabet tape)) :
    MachineAlphabetTransport.configuration alphabet_eq ⟨label, state, base⟩ =
      ⟨label, state, toBoolTapes base⟩ := by
  rw [MachineAlphabetTransport.configuration_mk, toBoolTapes_eq_transport]

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderFamilyTransferLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
# Actual family-table installation and counter cleanup

Checked physical drain and transfer loops are placed in the family program
through its finite register equivalence. Alphabet equality transports their
actual traces back to the dependent alphabet of the full family machine.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

section Composition

open MachineComposition

section TransferVariables

variable {ρ : Type} {d : Nat}

def clearRegister (state : State ρ d) : State ρ d :=
  (MachineExpanderTable.clearRegister state.1, state.2)

@[simp] theorem registerStates_reset (state : State ρ d) :
    registerStates ρ d (((registerStates ρ d).symm state).1, none) =
      clearRegister state := rfl

@[simp] theorem clearRegister_idempotent (state : State ρ d) :
    clearRegister (clearRegister state) = clearRegister state := rfl

@[simp] theorem caller_clearRegister (state : State ρ d) :
    caller (clearRegister state) = caller state := rfl

@[simp] theorem clearRegister_position (state : State ρ d) :
    (clearRegister state).1.2 = state.1.2 := rfl

@[simp] theorem clearRegister_register (state : State ρ d) :
    (clearRegister state).1.1.2 = none := rfl

variable [Fintype ρ]

/-- The Boolean view is the same actual program under alphabet equality. -/
theorem boolTraceActual (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (n : Nat)
    (start finish : TM2.Cfg BoolAlphabet (Label d) (State ρ d))
    (run : (advance (TM2.step (boolView positive H growth)))^[n] (some start) = some finish) :
    (advance (TM2.step (program positive H growth)))^[n]
      (some (MachineAlphabetTransport.configuration alphabet_eq.symm start)) =
      some (MachineAlphabetTransport.configuration alphabet_eq.symm finish) := by
  have h := MachineAlphabetTransport.successfulTrace alphabet_eq.symm
    (boolView positive H growth) n start finish run
  simpa only [boolView, MachineAlphabetTransport.program_symm_roundtrip] using h

theorem drainBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (source : Tape) (again next : OuterLabel)
    (code : boolOuterStatement (ρ := ρ) positive H again = drainStatement source again next)
    (base : Tape → List Bool) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[(base source).length + 1]
      (some ⟨some (.inr again), state, base⟩) =
      some ⟨some (.inr next), clearRegister state, Function.update base source []⟩ := by
  have atLoop : boolView (ρ := ρ) positive H growth (.inr again) =
      MachineControl.statement id (registerStates ρ d)
        (MachineDrain.drain source (.inr again) (some (.inr next))) := by
    rw [boolView_outer, code]
    rfl
  have h := controlDrainTrace (registerStates ρ d) source (.inr again) (some (.inr next))
    (boolView positive H growth) atLoop base
    ((registerStates ρ d).symm state).1 ((registerStates ρ d).symm state).2
  simpa only [Prod.mk.eta, Equiv.apply_symm_apply, registerStates_reset] using h

theorem transferBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (source destination : Tape) (distinct : source ≠ destination)
    (again next : OuterLabel)
    (code : boolOuterStatement (ρ := ρ) positive H again =
      MachineControl.statement id (registerStates ρ d)
        (Reduction.MachineTransfer.loopAt (Γ := BoolAlphabet) source destination id false
          (.inr again) (some (.inr next))))
    (base : Tape → List Bool) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[(base source).length + 1]
      (some ⟨some (.inr again), state, base⟩) =
      some ⟨some (.inr next), clearRegister state,
        Reduction.MachineTransfer.tapesAt source destination base []
          ((base source).reverse ++ base destination)⟩ := by
  have atLoop : boolView (ρ := ρ) positive H growth (.inr again) =
      MachineControl.statement id (registerStates ρ d)
        (Reduction.MachineTransfer.loopAt source destination id false
          (.inr again) (some (.inr next))) := by
    rw [boolView_outer, code]
  have h := controlTransferTrace (registerStates ρ d) source destination distinct
    (.inr again) (some (.inr next)) (boolView positive H growth) atLoop base
    ((registerStates ρ d).symm state).1 ((registerStates ρ d).symm state).2
  simpa only [Prod.mk.eta, Equiv.apply_symm_apply, registerStates_reset] using h

/-- Only these four tape words change during installation. -/
def installedTapes (base : Tape → List Bool) (newWord : List Bool) : Tape → List Bool :=
  Function.update
    (Function.update
      (Function.update (Function.update base tableTape newWord) resultTape [])
      (.inr .tableReverse) [])
    (.inr .currentSize) []

def cleanedCounterTapes (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update base inputVertexTape []) vertexCountTape []

theorem installTableBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (newWord : List Bool)
    (resultWord : base resultTape = newWord) (reverseEmpty : base (.inr .tableReverse) = [])
    (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[
        (base tableTape).length + 2 * newWord.length + (base (.inr .currentSize)).length + 4]
      (some ⟨some (.inr .clearOldTable), state, base⟩) =
      some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state,
        installedTapes base newWord⟩ := by
  let b0 := Function.update base tableTape []
  let b1 := Function.update (Function.update b0 resultTape []) (.inr .tableReverse) newWord.reverse
  let b2 := Function.update (Function.update b1 (.inr .tableReverse) []) tableTape newWord
  let b3 := Function.update b2 (.inr .currentSize) []
  have h0 := drainBoolTrace positive H growth tableTape .clearOldTable .reverseResult rfl base state
  have b0Result : b0 resultTape = newWord := by
    simpa [b0, tableTape, resultTape] using resultWord
  have b0Reverse : b0 (.inr .tableReverse) = [] := by
    simpa [b0, tableTape] using reverseEmpty
  have h1 : (advance (TM2.step (boolView positive H growth)))^[newWord.length + 1]
      (some ⟨some (.inr .reverseResult), clearRegister state, b0⟩) =
      some ⟨some (.inr .reverseTable), clearRegister state, b1⟩ := by
    simpa only [b0Result, b0Reverse, List.append_nil, Reduction.MachineTransfer.tapesAt,
      clearRegister_idempotent] using
      transferBoolTrace positive H growth resultTape (.inr .tableReverse) (by decide)
        .reverseResult .reverseTable rfl b0 (clearRegister state)
  have b1Reverse : b1 (.inr .tableReverse) = newWord.reverse := by simp [b1]
  have b1Table : b1 tableTape = [] := by simp [b1, b0, tableTape, resultTape]
  have h2 : (advance (TM2.step (boolView positive H growth)))^[newWord.length + 1]
      (some ⟨some (.inr .reverseTable), clearRegister state, b1⟩) =
      some ⟨some (.inr .clearCurrentSize), clearRegister state, b2⟩ := by
    simpa only [b1Reverse, b1Table, List.reverse_reverse, List.length_reverse,
      List.append_nil, Reduction.MachineTransfer.tapesAt, clearRegister_idempotent] using
      transferBoolTrace positive H growth (.inr .tableReverse) tableTape (by decide)
        .reverseTable .clearCurrentSize rfl b1 (clearRegister state)
  have b2Current : b2 (.inr .currentSize) = base (.inr .currentSize) := by
    simp [b2, b1, b0, tableTape, resultTape]
  have h3 : (advance (TM2.step (boolView positive H growth)))^[
      (base (.inr .currentSize)).length + 1]
      (some ⟨some (.inr .clearCurrentSize), clearRegister state, b2⟩) =
      some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state, b3⟩ := by
    simpa only [b2Current, clearRegister_idempotent] using
      drainBoolTrace positive H growth (.inr .currentSize) .clearCurrentSize
        (.affine .multiplySize .seed) rfl b2 (clearRegister state)
  have final : b3 = installedTapes base newWord := by
    funext tape
    rcases tape with table | extra
    · rcases table with row | tableExtra
      · cases row <;> simp [b3, b2, b1, b0, installedTapes, tableTape, resultTape]
      · cases tableExtra <;> simp [b3, b2, b1, b0, installedTapes, tableTape, resultTape]
    · cases extra <;> simp [b3, b2, b1, b0, installedTapes, tableTape, resultTape]
  rw [show (base tableTape).length + 2 * newWord.length +
        (base (.inr .currentSize)).length + 4 =
      ((base (.inr .currentSize)).length + 1) +
        ((newWord.length + 1) + ((newWord.length + 1) + ((base tableTape).length + 1))) by omega,
    Function.iterate_add_apply _ ((base (.inr .currentSize)).length + 1),
    Function.iterate_add_apply _ (newWord.length + 1) ((newWord.length + 1) + ((base tableTape).length + 1)),
    Function.iterate_add_apply _ (newWord.length + 1) ((base tableTape).length + 1),
    h0, h1, h2, h3, final]

theorem cleanupCountersBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[
        (base inputVertexTape).length + (base vertexCountTape).length + 2]
      (some ⟨some (.inr .drainInputVertex), state, base⟩) =
      some ⟨some (.inr .levelGuard), clearRegister state, cleanedCounterTapes base⟩ := by
  have h0 := drainBoolTrace positive H growth inputVertexTape .drainInputVertex .drainVertexCount
    rfl base state
  have count : (Function.update base inputVertexTape []) vertexCountTape = base vertexCountTape := by
    simp [inputVertexTape, vertexCountTape]
  have h1 := drainBoolTrace positive H growth vertexCountTape .drainVertexCount .levelGuard
    rfl (Function.update base inputVertexTape []) (clearRegister state)
  simp only [count, clearRegister_idempotent] at h1
  rw [show (base inputVertexTape).length + (base vertexCountTape).length + 2 =
      ((base vertexCountTape).length + 1) + ((base inputVertexTape).length + 1) by omega,
    Function.iterate_add_apply, h0]
  exact h1

/-- Actual dependent-alphabet trace for draining the old table, installing the
new forward table by two physical reversals, and clearing the old size word. -/
theorem installTableTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (newWord : List Bool) (resultWord : toBoolTapes base resultTape = newWord)
    (reverseEmpty : toBoolTapes base (.inr .tableReverse) = []) (state : State ρ d) :
    (advance (TM2.step (program positive H growth)))^[
        (toBoolTapes base tableTape).length + 2 * newWord.length +
          (toBoolTapes base (.inr .currentSize)).length + 4]
      (some ⟨some (.inr .clearOldTable), state, base⟩) =
      some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state,
        fromBoolTapes (installedTapes (toBoolTapes base) newWord)⟩ := by
  have h := installTableBoolTrace positive H growth (toBoolTapes base) newWord resultWord reverseEmpty state
  simpa only [configuration_fromBool, fromBool_toBool] using boolTraceActual positive H growth _ _ _ h

/-- After the checked affine phase, both table-loop counters are physically
drained and the actual family level guard is reached. -/
theorem cleanupCountersTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (state : State ρ d) :
    (advance (TM2.step (program positive H growth)))^[
        (toBoolTapes base inputVertexTape).length + (toBoolTapes base vertexCountTape).length + 2]
      (some ⟨some (.inr .drainInputVertex), state, base⟩) =
      some ⟨some (.inr .levelGuard), clearRegister state,
        fromBoolTapes (cleanedCounterTapes (toBoolTapes base))⟩ := by
  have h := cleanupCountersBoolTrace positive H growth (toBoolTapes base) state
  simpa only [configuration_fromBool, fromBool_toBool] using boolTraceActual positive H growth _ _ _ h

def installTableInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (newWord : List Bool) (resultWord : toBoolTapes base resultTape = newWord)
    (reverseEmpty : toBoolTapes base (.inr .tableReverse) = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .clearOldTable), state, base⟩
      (some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state,
        fromBoolTapes (installedTapes (toBoolTapes base) newWord)⟩)
      ((toBoolTapes base tableTape).length + 2 * newWord.length +
        (toBoolTapes base (.inr .currentSize)).length + 4) where
  steps := (toBoolTapes base tableTape).length + 2 * newWord.length +
    (toBoolTapes base (.inr .currentSize)).length + 4
  evals_in_steps := installTableTrace positive H growth base newWord resultWord reverseEmpty state
  steps_le_m := Nat.le_refl _

def cleanupCountersInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .drainInputVertex), state, base⟩
      (some ⟨some (.inr .levelGuard), clearRegister state,
        fromBoolTapes (cleanedCounterTapes (toBoolTapes base))⟩)
      ((toBoolTapes base inputVertexTape).length + (toBoolTapes base vertexCountTape).length + 2) where
  steps := (toBoolTapes base inputVertexTape).length + (toBoolTapes base vertexCountTape).length + 2
  evals_in_steps := cleanupCountersTrace positive H growth base state
  steps_le_m := Nat.le_refl _

end TransferVariables

theorem affine_source_ne_scratch (phase : AffinePhase) :
    affineSource phase ≠ .inr .unaryScratch := by cases phase <;> decide

theorem affine_source_ne_destination (phase : AffinePhase) :
    affineSource phase ≠ affineDestination phase := by cases phase <;> decide

theorem affine_scratch_ne_destination (phase : AffinePhase) :
    (.inr .unaryScratch : Tape) ≠ affineDestination phase := by cases phase <;> decide

/-- Exact final dependent tape family, with all other tape contents retained. -/
def affineResultTapes (d : Nat) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) :
    (tape : Tape) → List (Alphabet tape) :=
  Function.update base (affineDestination phase)
    (boolWord (affineDestination phase)
      (encodeWord (affineCoefficient d phase * n) ++ toBoolTapes base (affineDestination phase)))

variable {ρ : Type} [Fintype ρ] {d : Nat}

/-- The concrete Boolean view is pulled into unary-affine state coordinates,
executed from its actual statements, and transported back without extra steps. -/
theorem affinePhaseBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (phase : AffinePhase) (base : Tape → List Bool)
    (n : Nat) (suffix : List Bool)
    (sourceWord : base (affineSource phase) = encodeWord n ++ suffix)
    (scratchEmpty : base (.inr .unaryScratch) = []) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[2 * (n + 1) + 1]
      (some ⟨some (.inr (.affine phase .seed)), state, base⟩) =
      some ⟨some (affineExit d phase), clearRegister state,
        Function.update base (affineDestination phase)
          (encodeWord (affineCoefficient d phase * n) ++ base (affineDestination phase))⟩ := by
  let states := registerStates ρ d
  let target := boolView (ρ := ρ) positive H growth
  let sourceProgram := MachineControl.program (Equiv.refl (Label d)) states.symm target
  have atSeed : sourceProgram (.inr (.affine phase .seed)) =
      MachineUnaryAffineAt.seed (affineDestination phase) 0 (.inr (.affine phase .scan)) := by
    change MachineControl.statement id states.symm
      (boolView positive H growth (.inr (.affine phase .seed))) = _
    rw [boolView_outer]
    exact controlStatementInverse states _
  have atScan : sourceProgram (.inr (.affine phase .scan)) =
      MachineUnaryAffineAt.scan (affineSource phase) (.inr .unaryScratch)
        (affineDestination phase) (affineCoefficient d phase)
        (.inr (.affine phase .scan)) (.inr (.affine phase .restore)) := by
    change MachineControl.statement id states.symm
      (boolView positive H growth (.inr (.affine phase .scan))) = _
    rw [boolView_outer]
    exact controlStatementInverse states _
  have atRestore : sourceProgram (.inr (.affine phase .restore)) =
      Reduction.MachineTransfer.loopAt (.inr .unaryScratch) (affineSource phase) id false
        (.inr (.affine phase .restore)) (some (affineExit d phase)) := by
    change MachineControl.statement id states.symm
      (boolView positive H growth (.inr (.affine phase .restore))) = _
    rw [boolView_outer]
    exact controlStatementInverse states _
  have raw := MachineUnaryAffineAt.seededAffineTrace
    (affineSource phase) (.inr .unaryScratch) (affineDestination phase)
    (affine_source_ne_scratch phase) (affine_source_ne_destination phase)
    (affine_scratch_ne_destination phase) (affineCoefficient d phase) 0
    (.inr (.affine phase .seed)) (.inr (.affine phase .scan)) (.inr (.affine phase .restore))
    (some (affineExit d phase)) sourceProgram atSeed atScan atRestore base n suffix
    sourceWord scratchEmpty (states.symm state).1 (states.symm state).2
  have run := controlTrace states target (2 * (n + 1) + 1) _ _ raw
  simpa only [states, target, MachineControl.configuration, Option.map_some, id_eq, Prod.mk.eta,
    Equiv.apply_symm_apply, Nat.add_zero, registerStates_reset] using run

/-- Actual family-program execution. Alphabet conversion is static equality
transport; the transition count is exactly the checked unary-affine count. -/
theorem affinePhaseTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) (suffix : List Bool)
    (sourceWord : toBoolTapes base (affineSource phase) = encodeWord n ++ suffix)
    (scratchEmpty : base (.inr .unaryScratch) = []) (state : State ρ d) :
    (advance (TM2.step (program positive H growth)))^[2 * (n + 1) + 1]
      (some ⟨some (.inr (.affine phase .seed)), state, base⟩) =
      some ⟨some (affineExit d phase), clearRegister state,
        affineResultTapes d phase base n⟩ := by
  have raw := affinePhaseBoolTrace positive H growth phase (toBoolTapes base) n suffix
    sourceWord scratchEmpty state
  have transported := boolTraceActual positive H growth (2 * (n + 1) + 1) _ _ raw
  simpa only [configuration_fromBool, fromBoolTapes_update, fromBool_toBool,
    affineResultTapes] using transported

def affinePhaseInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) (suffix : List Bool)
    (sourceWord : toBoolTapes base (affineSource phase) = encodeWord n ++ suffix)
    (scratchEmpty : base (.inr .unaryScratch) = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr (.affine phase .seed)), state, base⟩
      (some ⟨some (affineExit d phase), clearRegister state,
        affineResultTapes d phase base n⟩) (2 * (n + 1) + 1) where
  steps := 2 * (n + 1) + 1
  evals_in_steps := affinePhaseTrace positive H growth phase base n suffix sourceWord scratchEmpty state
  steps_le_m := Nat.le_refl _

def copyCountInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (n : Nat) (sourceWord : base (.inr .currentSize) = encodeWord n)
    (scratchEmpty : base (.inr .unaryScratch) = [])
    (destinationEmpty : base vertexCountTape = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr (.affine .copyCount .seed)), state, base⟩
      (some ⟨some (.inl (.inr .initialize_)), clearRegister state,
        Function.update base vertexCountTape (encodeWord n)⟩) (2 * (n + 1) + 1) := by
  have run := affinePhaseInTime positive H growth .copyCount base n []
    (by simpa only [affineSource, toBoolTapes, toBoolWord, List.append_nil] using sourceWord)
    scratchEmpty state
  change base (.inl (.inr .vertexCount)) = [] at destinationEmpty
  simpa only [affineExit, affineResultTapes, affineDestination, affineCoefficient,
    Nat.one_mul, vertexCountTape, boolWord, toBoolTapes, toBoolWord,
    destinationEmpty, List.append_nil] using run

def multiplySizeInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (n : Nat) (sourceWord : base inputVertexTape = encodeWord n)
    (scratchEmpty : base (.inr .unaryScratch) = [])
    (destinationEmpty : base (.inr .currentSize) = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr (.affine .multiplySize .seed)), state, base⟩
      (some ⟨some (.inr .drainInputVertex), clearRegister state,
        Function.update base (.inr .currentSize) (encodeWord (cloudSize d * n))⟩)
      (2 * (n + 1) + 1) := by
  have run := affinePhaseInTime positive H growth .multiplySize base n []
    (by simpa only [affineSource, inputVertexTape, toBoolTapes, toBoolWord,
      List.append_nil] using sourceWord)
    scratchEmpty state
  simpa only [affineExit, affineResultTapes, affineDestination, affineCoefficient,
    boolWord, toBoolTapes, toBoolWord, destinationEmpty, List.append_nil] using run

end Composition

variable {ρ : Type} {d : Nat}

@[simp] theorem caller_initialState (positive : 0 < d) (H : Table (cloudSize d) d)
    (ambient : ρ) : caller (initialState positive H ambient) = ambient := rfl

@[simp] theorem caller_normalizeState (positive : 0 < d) (H : Table (cloudSize d) d)
    (state : State ρ d) : caller (normalizeState positive H state) = caller state := rfl

@[simp] theorem clearRegister_initialState (positive : 0 < d)
    (H : Table (cloudSize d) d) (ambient : ρ) :
    clearRegister (initialState positive H ambient) = initialState positive H ambient := rfl

/-- The guard changes only the physical remaining-level word. -/
theorem boundaryTapes_update_level (remaining current next : Nat)
    (word suffix : List Bool) :
    Function.update (boundaryTapes remaining current word suffix)
      (.inr .remainingLevel) (encodeWord next ++ suffix) =
      boundaryTapes next current word suffix := by
  funext tape
  rcases tape with tape | extra
  · rcases tape with row | extra
    · cases row <;> simp [boundaryTapes, tableFrame, MachineEmbedding.tapes, Function.update]
    · cases extra <;> simp [boundaryTapes, tableFrame, MachineEmbedding.tapes, Function.update]
  · cases extra <;> simp [boundaryTapes, extraFrame, MachineEmbedding.tapes, Function.update]

/-- The two literal prefixes install the actual level-zero table and unary one. -/
theorem initialTapes_initialize (level : Nat) (suffix : List Bool) :
    Function.update
      (Function.update (initialTapes level suffix) tableTape (initialEncoding d))
      (.inr .currentSize) (encodeWord 1) =
      boundaryTapes level 1 (initialEncoding d) suffix := by
  funext tape
  rcases tape with tape | extra
  · rcases tape with row | extra
    · cases row <;> simp [initialTapes, boundaryTapes, tableFrame,
        MachineEmbedding.tapes, Function.update, tableTape]
    · cases extra <;> simp [initialTapes, boundaryTapes, tableFrame,
        MachineEmbedding.tapes, Function.update, tableTape]
  · cases extra <;> simp [initialTapes, boundaryTapes, extraFrame,
      MachineEmbedding.tapes, Function.update, tableTape]

variable [Fintype ρ]

/-- Static alphabet transport preserves this actual single transition. -/
theorem actualStep_of_boolStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d)
    (start finish : TM2.Cfg BoolAlphabet (Label d) (State ρ d))
    (run : TM2.step (boolView positive H growth) start = some finish) :
    TM2.step (program positive H growth)
      (MachineAlphabetTransport.configuration alphabet_eq.symm start) =
      some (MachineAlphabetTransport.configuration alphabet_eq.symm finish) := by
  have h := MachineAlphabetTransport.step_simulation alphabet_eq.symm
    (boolView positive H growth) start
  rw [run] at h
  simpa only [boolView, MachineAlphabetTransport.program_symm_roundtrip,
    Option.map_some] using h

theorem bool_initializeStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d) :
    TM2.step (boolView positive H growth) ⟨some (.inr .initialize_), state, base⟩ =
      some ⟨some (.inr .levelGuard), normalizeState positive H state,
        Function.update
          (Function.update base tableTape (initialEncoding d ++ base (.inl (.inl .table))))
          (.inr .currentSize) (encodeWord 1 ++ base (.inr .currentSize))⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .initialize_)) state base) = _
  rw [boolView_outer]
  simp only [boolOuterStatement, Reduction.MachineSubstitution.stepAux_pushWord,
    List.reverse_reverse, TM2.stepAux]
  rfl

theorem bool_levelGuard_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d)
    (remaining : Nat) (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord (remaining + 1) ++ suffix) :
    TM2.step (boolView positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr (.affine .copyCount .seed)), clearRegister state,
        Function.update base (.inr .remainingLevel) (encodeWord remaining ++ suffix)⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .levelGuard)) state base) = _
  rw [boolView_outer]
  simp [boolOuterStatement, MachineControl.statement, MachineUnaryCounter.guard,
    TM2.stepAux, registerStates, clearRegister, MachineExpanderTable.clearRegister,
    counter, encodeWord, List.replicate_succ]

theorem bool_levelGuard_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d)
    (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord 0 ++ suffix) :
    TM2.step (boolView positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr .done), clearRegister state, base⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .levelGuard)) state base) = _
  rw [boolView_outer]
  simp [boolOuterStatement, MachineControl.statement, MachineUnaryCounter.guard,
    TM2.stepAux, registerStates, clearRegister, MachineExpanderTable.clearRegister,
    counter, encodeWord]

theorem bool_doneStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d) :
    TM2.step (boolView positive H growth) ⟨some (.inr .done), state, base⟩ =
      some ⟨none, normalizeState positive H state, base⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .done)) state base) = _
  rw [boolView_outer]
  rfl

/-- The literal initialization executes in one transition of the actual program. -/
theorem initializeStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H growth) ⟨some (.inr .initialize_), state, base⟩ =
      some ⟨some (.inr .levelGuard), normalizeState positive H state,
        Function.update
          (Function.update base tableTape (initialEncoding d ++ base (.inl (.inl .table))))
          (.inr .currentSize) (encodeWord 1 ++ base (.inr .currentSize))⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_initializeStep positive H growth (toBoolTapes base) state)
  simp only [configuration_fromBool, fromBoolTapes_update, fromBool_toBool] at h
  exact h

/-- A positive level physically loses one true bit, retaining its delimiter and suffix. -/
theorem levelGuard_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (remaining : Nat) (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord (remaining + 1) ++ suffix) :
    TM2.step (program positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr (.affine .copyCount .seed)), clearRegister state,
        Function.update base (.inr .remainingLevel) (encodeWord remaining ++ suffix)⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_levelGuard_succStep positive H growth (toBoolTapes base) state
      remaining suffix counter)
  simpa only [configuration_fromBool, fromBoolTapes_update, fromBool_toBool,
    boolWord] using h

/-- The zero delimiter is retained when the family loop enters its final halt. -/
theorem levelGuard_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord 0 ++ suffix) :
    TM2.step (program positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr .done), clearRegister state, base⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_levelGuard_zeroStep positive H growth (toBoolTapes base) state suffix counter)
  simpa only [configuration_fromBool, fromBool_toBool] using h

theorem doneStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H growth) ⟨some (.inr .done), state, base⟩ =
      some ⟨none, normalizeState positive H state, base⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_doneStep positive H growth (toBoolTapes base) state)
  simpa only [configuration_fromBool, fromBool_toBool] using h

theorem initialize_boundaryStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (level : Nat) (suffix : List Bool) (state : State ρ d) :
    TM2.step (program positive H growth)
      ⟨some (.inr .initialize_), state, initialTapes level suffix⟩ =
      some ⟨some (.inr .levelGuard), initialState positive H (caller state),
        boundaryTapes level 1 (initialEncoding d) suffix⟩ := by
  have h := initializeStep positive H growth (initialTapes level suffix) state
  have ht : initialTapes level suffix (.inl (.inl .table)) = [] := rfl
  have hc : initialTapes level suffix (.inr .currentSize) = [] := rfl
  simp only [ht, hc, List.append_nil, normalizeState] at h
  exact h.trans (congrArg
    (fun tapes : ∀ tape, List (Alphabet tape) =>
      (some ⟨some (.inr .levelGuard), initialState positive H (caller state), tapes⟩ :
        Option (TM2.Cfg Alphabet (Label d) (State ρ d))))
    (initialTapes_initialize level suffix))

theorem levelGuard_boundary_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (remaining current : Nat)
    (word suffix : List Bool) (state : State ρ d) :
    TM2.step (program positive H growth)
      ⟨some (.inr .levelGuard), state, boundaryTapes (remaining + 1) current word suffix⟩ =
      some ⟨some (.inr (.affine .copyCount .seed)), clearRegister state,
        boundaryTapes remaining current word suffix⟩ := by
  simpa only [boundaryTapes_update_level] using
    levelGuard_succStep positive H growth
      (boundaryTapes (remaining + 1) current word suffix) state remaining suffix rfl

theorem levelGuard_boundary_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (current : Nat)
    (word suffix : List Bool) (state : State ρ d) :
    TM2.step (program positive H growth)
      ⟨some (.inr .levelGuard), state, boundaryTapes 0 current word suffix⟩ =
      some ⟨some (.inr .done), clearRegister state,
        boundaryTapes 0 current word suffix⟩ :=
  levelGuard_zeroStep positive H growth
    (boundaryTapes 0 current word suffix) state suffix rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily


/-!
# Concrete boundary steps of the expander-table machine

Every execution theorem below reduces the actual common program statement.
States and dependent tape frames are arbitrary; only the relevant unary word
or finite-position branch is specified. No phase execution is a premise.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

@[simp] theorem caller_boundaryState (positive : 0 < d) (H : Table (cloudSize d) d)
    (ambient : ρ) (position : Position d) :
    caller (boundaryState positive H ambient position) = ambient := rfl

@[simp] theorem prepareState_boundaryState (positive : 0 < d) (H : Table (cloudSize d) d)
    (ambient : ρ) (position : Position d) :
    prepareState positive H (boundaryState positive H ambient position) =
      boundaryState positive H ambient position := rfl

@[simp] theorem clearRegister_boundaryState (positive : 0 < d) (H : Table (cloudSize d) d)
    (ambient : ρ) (position : Position d) :
    clearRegister (boundaryState positive H ambient position) =
      boundaryState positive H ambient position := rfl

@[simp] theorem caller_prepareState (positive : 0 < d) (H : Table (cloudSize d) d)
    (state : State ρ d) : caller (prepareState positive H state) = caller state := rfl

@[simp] theorem caller_resetState (positive : 0 < d) (H : Table (cloudSize d) d)
    (state : State ρ d) : caller (resetState positive H state) = caller state := rfl

@[simp] theorem caller_clearRegister (state : State ρ d) :
    caller (clearRegister state) = caller state := rfl

@[simp] theorem caller_advancePositionState (positive : 0 < d) (state : State ρ d) :
    caller (advancePositionState positive state) = caller state := rfl

@[simp] theorem caller_resetPositionState (positive : 0 < d) (state : State ρ d) :
    caller (resetPositionState positive state) = caller state := rfl

theorem nextPosition_val_of_lt (positive : 0 < d) (position : Position d)
    (more : position.val + 1 < rowFactor d) :
    (nextPosition positive position).val = position.val + 1 := Nat.mod_eq_of_lt more

/-- Replacing the count word leaves the entire row frame and result unchanged. -/
theorem boundaryTapes_update_count (vertex remaining next : Nat)
    (oldTable output countSuffix result : List Bool) :
    Function.update (boundaryTapes vertex remaining oldTable output countSuffix result)
      (.inr .vertexCount) (encodeWord next ++ countSuffix) =
      boundaryTapes vertex next oldTable output countSuffix result := by
  funext tape
  rcases tape with row | extra
  · cases row <;> simp [boundaryTapes, rowTapes, MachineEmbedding.tapes, Function.update]
  · cases extra <;> simp [boundaryTapes, extraTapes, MachineEmbedding.tapes, Function.update]

/-- The last row's one actual push increments the unary vertex word. -/
theorem boundaryTapes_increment_vertex (vertex remaining : Nat)
    (oldTable output countSuffix result : List Bool) :
    Function.update (boundaryTapes vertex remaining oldTable output countSuffix result)
      (.inl .inputVertex) (true :: encodeWord vertex) =
      boundaryTapes (vertex + 1) remaining oldTable output countSuffix result := by
  funext tape
  rcases tape with row | extra
  · cases row <;>
      simp [boundaryTapes, rowTapes, MachineEmbedding.tapes, Function.update,
        encodeWord, List.replicate_succ]
  · cases extra <;>
      simp [boundaryTapes, extraTapes, MachineEmbedding.tapes, Function.update]

theorem initialTapes_initialize (vertices : Nat) (oldTable countSuffix : List Bool) :
    Function.update (initialTapes vertices oldTable countSuffix) (.inl .inputVertex) [false] =
      boundaryTapes 0 vertices oldTable [] countSuffix [] := by
  funext tape
  rcases tape with row | extra
  · cases row <;>
      simp [initialTapes, boundaryTapes, rowTapes, MachineEmbedding.tapes,
        Function.update, encodeWord]
  · cases extra <;>
      simp [initialTapes, boundaryTapes, extraTapes, MachineEmbedding.tapes,
        Function.update]

variable [Fintype ρ]

theorem initializeStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H) ⟨some (.inr .initialize_), state, base⟩ =
      some ⟨some (.inr .vertexGuard), resetState positive H state,
        Function.update base (.inl .inputVertex) (false :: base (.inl .inputVertex))⟩ := by
  change some (TM2.stepAux (program positive H (.inr .initialize_)) state base) = _
  rw [program_outer]
  rfl

theorem initialize_boundaryStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertices : Nat) (oldTable countSuffix : List Bool) (state : State ρ d) :
    TM2.step (program positive H)
      ⟨some (.inr .initialize_), state, initialTapes vertices oldTable countSuffix⟩ =
      some ⟨some (.inr .vertexGuard), initialState positive H (caller state),
        boundaryTapes 0 vertices oldTable [] countSuffix []⟩ := by
  have h := initializeStep positive H (initialTapes vertices oldTable countSuffix) state
  have input : initialTapes vertices oldTable countSuffix (.inl .inputVertex) = [] := rfl
  simp only [input, resetState] at h
  exact h.trans (congrArg
    (fun tapes : ∀ tape, List (Alphabet tape) =>
      (some ⟨some (.inr .vertexGuard), initialState positive H (caller state), tapes⟩ :
        Option (TM2.Cfg Alphabet (Label d) (State ρ d))))
    (initialTapes_initialize vertices oldTable countSuffix))

/-- A positive vertex counter is physically decremented; its suffix remains. -/
theorem vertexGuard_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (remaining : Nat) (suffix : List Bool)
    (counter : base (.inr .vertexCount) = encodeWord (remaining + 1) ++ suffix) :
    TM2.step (program positive H) ⟨some (.inr .vertexGuard), state, base⟩ =
      some ⟨some (.inr .prepareRow), clearRegister state,
        Function.update base (.inr .vertexCount) (encodeWord remaining ++ suffix)⟩ := by
  change some (TM2.stepAux (program positive H (.inr .vertexGuard)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, vertexGuardCore, TM2.stepAux,
    guardStates, clearRegister, counter, encodeWord, List.replicate_succ]

/-- The zero delimiter is retained when the loop enters output reversal. -/
theorem vertexGuard_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (suffix : List Bool)
    (counter : base (.inr .vertexCount) = encodeWord 0 ++ suffix) :
    TM2.step (program positive H) ⟨some (.inr .vertexGuard), state, base⟩ =
      some ⟨some (.inr .reverseOutput), clearRegister state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .vertexGuard)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, vertexGuardCore, TM2.stepAux,
    guardStates, clearRegister, counter, encodeWord]

theorem vertexGuard_boundary_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    TM2.step (program positive H)
      ⟨some (.inr .vertexGuard), state,
        boundaryTapes vertex (remaining + 1) oldTable output countSuffix result⟩ =
      some ⟨some (.inr .prepareRow), clearRegister state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩ := by
  simpa only [boundaryTapes_update_count] using
    vertexGuard_succStep positive H
      (boundaryTapes vertex (remaining + 1) oldTable output countSuffix result)
      state remaining countSuffix rfl

theorem vertexGuard_boundary_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex : Nat) (oldTable output countSuffix result : List Bool) (state : State ρ d) :
    TM2.step (program positive H)
      ⟨some (.inr .vertexGuard), state,
        boundaryTapes vertex 0 oldTable output countSuffix result⟩ =
      some ⟨some (.inr .reverseOutput), clearRegister state,
        boundaryTapes vertex 0 oldTable output countSuffix result⟩ :=
  vertexGuard_zeroStep positive H
    (boundaryTapes vertex 0 oldTable output countSuffix result) state countSuffix rfl

/-- Preparing a row modifies finite control only, preserving every tape. -/
theorem prepareRowStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H) ⟨some (.inr .prepareRow), state, base⟩ =
      some ⟨some (.inl .initialize_), prepareState positive H state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .prepareRow)) state base) = _
  rw [program_outer]
  rfl

/-- A nonfinal row advances the finite position without changing tapes. -/
theorem afterRow_moreStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (more : state.2.val + 1 < rowFactor d) :
    TM2.step (program positive H) ⟨some (.inr .afterRow), state, base⟩ =
      some ⟨some (.inr .prepareRow), advancePositionState positive state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .afterRow)) state base) = _
  rw [program_outer]
  simp [outerStatement, TM2.stepAux, more]

/-- The final row increments the tape vertex and resets the finite position. -/
theorem afterRow_lastStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (last : ¬ state.2.val + 1 < rowFactor d) :
    TM2.step (program positive H) ⟨some (.inr .afterRow), state, base⟩ =
      some ⟨some (.inr .vertexGuard), resetPositionState positive state,
        Function.update base (.inl .inputVertex) (true :: base (.inl .inputVertex))⟩ := by
  change some (TM2.stepAux (program positive H (.inr .afterRow)) state base) = _
  rw [program_outer]
  simp [outerStatement, TM2.stepAux, last]

theorem afterRow_last_boundaryStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) (last : ¬ state.2.val + 1 < rowFactor d) :
    TM2.step (program positive H)
      ⟨some (.inr .afterRow), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩ =
      some ⟨some (.inr .vertexGuard), resetPositionState positive state,
        boundaryTapes (vertex + 1) remaining oldTable output countSuffix result⟩ := by
  have input : boundaryTapes vertex remaining oldTable output countSuffix result
      (.inl .inputVertex) = encodeWord vertex := rfl
  have h := afterRow_lastStep positive H
    (boundaryTapes vertex remaining oldTable output countSuffix result) state last
  simp only [input] at h
  exact h.trans (congrArg
    (fun tapes : ∀ tape, List (Alphabet tape) =>
      (some ⟨some (.inr .vertexGuard), resetPositionState positive state, tapes⟩ :
        Option (TM2.Cfg Alphabet (Label d) (State ρ d))))
    (boundaryTapes_increment_vertex vertex remaining oldTable output countSuffix result))

/-- One reversal step moves an actual symbol and preserves the finite position. -/
theorem reverseOutput_consStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (symbol : Bool) (word : List Bool) (source : base (.inl .output) = symbol :: word) :
    TM2.step (program positive H) ⟨some (.inr .reverseOutput), state, base⟩ =
      some ⟨some (.inr .reverseOutput), ((state.1.1, some symbol), state.2),
        Function.update (Function.update base (.inl .output) word)
          (.inr .result) (symbol :: base (.inr .result))⟩ := by
  change some (TM2.stepAux (program positive H (.inr .reverseOutput)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, Reduction.MachineTransfer.loopAt,
    Reduction.MachineTransfer.exitAt, TM2.stepAux, guardStates, source]

theorem reverseOutput_nilStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (source : base (.inl .output) = []) :
    TM2.step (program positive H) ⟨some (.inr .reverseOutput), state, base⟩ =
      some ⟨some (.inr .done), clearRegister state, base⟩ := by
  have same : Function.update base (.inl .output) [] = base := by
    simpa only [source] using Function.update_eq_self (.inl .output) base
  change some (TM2.stepAux (program positive H (.inr .reverseOutput)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, Reduction.MachineTransfer.loopAt,
    Reduction.MachineTransfer.exitAt, TM2.stepAux, guardStates, clearRegister, source, same]

theorem doneStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H) ⟨some (.inr .done), state, base⟩ =
      some ⟨none, state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .done)) state base) = _
  rw [program_outer]
  rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderRowCleanup
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {K Λ ρ : Type} [DecidableEq K]

variable [Fintype ρ] {d : Nat}

/-- One cleanup phase follows the actual drain instruction at its placed label. -/
theorem cleanupOneTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (i : Fin 6) (base : K → List Bool) (state : State ρ d) :
    (advance (TM2.step target))^[((base (ports (dirtyTape i))).length + 1)]
      (some ⟨some (labels (.cleanup i)), state, base⟩) =
      some ⟨some (if hi : i.val + 1 < 6 then labels (.cleanup ⟨i.val + 1, hi⟩)
          else labels .done),
        (state.1, none), Function.update base (ports (dirtyTape i)) []⟩ := by
  have run := MachineDrain.drainTrace (ports (dirtyTape i)) (labels (.cleanup i))
    (some (if hi : i.val + 1 < 6 then labels (.cleanup ⟨i.val + 1, hi⟩)
      else labels .done)) target
    (by simpa only [statement] using code (.cleanup i))
    base (base (ports (dirtyTape i))) state.1 state.2
  simpa only [Function.update_eq_self] using run

/-- All six phases execute in the common program, with exactly the sum of
the six initial word lengths plus one empty-branch transition per tape. -/
theorem cleanupTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    (advance (TM2.step target))^[cleanupSteps ports base]
      (some ⟨some (labels (.cleanup 0)), state, base⟩) =
      some ⟨some (labels .done), (state.1, none), cleanupTapes ports base⟩ := by
  let t1 := Function.update base (ports .queryIndex) []
  let t2 := Function.update t1 (ports .lookupOutput) []
  let t3 := Function.update t2 (ports .quotientFirst) []
  let t4 := Function.update t3 (ports .quotientSecond) []
  let t5 := Function.update t4 (ports .remainderFirst) []
  have h0 := cleanupOneTraceAt positive H ports labels exit target code 0 base state
  have h1 := cleanupOneTraceAt positive H ports labels exit target code 1 t1 (state.1, none)
  have h2 := cleanupOneTraceAt positive H ports labels exit target code 2 t2 (state.1, none)
  have h3 := cleanupOneTraceAt positive H ports labels exit target code 3 t3 (state.1, none)
  have h4 := cleanupOneTraceAt positive H ports labels exit target code 4 t4 (state.1, none)
  have h5 := cleanupOneTraceAt positive H ports labels exit target code 5 t5 (state.1, none)
  simp [t1, t2, t3, t4, t5, distinct.eq_iff,
    -Function.iterate_succ] at h0 h1 h2 h3 h4 h5
  have finished := join_trace (join_trace (join_trace (join_trace (join_trace h0 h1) h2) h3) h4) h5
  simpa only [cleanupSteps, cleanupTapes] using finished

/-- The done label transfers control without inspecting or modifying any tape. -/
theorem doneStepAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    TM2.step target ⟨some (labels .done), state, base⟩ = some ⟨exit, state, base⟩ := by
  change some (TM2.stepAux (target (labels .done)) state base) = _
  rw [code]
  cases exit <;> rfl

/-- Cleanup followed by the actual done-to-caller transition. -/
theorem cleanupExitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    (advance (TM2.step target))^[cleanupSteps ports base + 1]
      (some ⟨some (labels (.cleanup 0)), state, base⟩) =
      some ⟨exit, (state.1, none), cleanupTapes ports base⟩ := by
  have cleaned := cleanupTraceAt positive H ports distinct labels exit target code base state
  have done : (advance (TM2.step target))^[1]
      (some ⟨some (labels .done), (state.1, none), cleanupTapes ports base⟩) =
      some ⟨exit, (state.1, none), cleanupTapes ports base⟩ := by
    simpa only [Function.iterate_one, advance_some] using
      doneStepAt positive H ports labels exit target code (cleanupTapes ports base) (state.1, none)
  exact join_trace cleaned done

/-- Initialization physically pushes four delimiters and resets the bit register. -/
theorem initializeStepAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    TM2.step target ⟨some (labels .initialize_), state, base⟩ =
      some ⟨some (labels (.firstEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))),
        (state.1, none), initializedTapes ports base⟩ := by
  change some (TM2.stepAux (target (labels .initialize_)) state base) = _
  rw [code]
  simp [statement, TM2.stepAux, initializedTapes, distinct.eq_iff]

/-- The query-clear phase removes one symbol from each of its two tapes and
preserves the complete finite state and every other tape. -/
theorem clearQueryStepAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    TM2.step target ⟨some (labels .clearQuery), state, base⟩ =
      some ⟨some (labels (.secondEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))),
        state, clearedQueryTapes ports base⟩ := by
  change some (TM2.stepAux (target (labels .clearQuery)) state base) = _
  rw [code]
  simp [statement, TM2.stepAux, clearedQueryTapes, distinct.eq_iff]

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderRowEmitLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

section

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.AlphabetTable

theorem affinePlan_bits {σ : Type} {bound : Nat} (coefficient : Nat)
    (offset : σ → Fin bound) (n : Nat) (ambient : σ) :
    Emitter.prefixBits (affinePlan coefficient offset) (fun _ : Fin 1 => n) ambient 3 =
      encodeWord (coefficient * n + (offset ambient).val) := by
  change Emitter.prefixBits
    (Emitter.listCommands (Emitter.affineCommands [((0 : Fin 1), coefficient)] offset))
    (fun _ : Fin 1 => n) ambient
    (Emitter.affineCommands [((0 : Fin 1), coefficient)] offset).length = _
  rw [Emitter.bits_listCommands, Emitter.affineCommands_bits]
  simp [Emitter.affineValue]

theorem affinePlan_steps {σ : Type} {bound : Nat} (coefficient : Nat)
    (offset : σ → Fin bound) (n : Nat) :
    Emitter.prefixSteps (affinePlan coefficient offset) (fun _ : Fin 1 => n) 3 + 1 =
      emitSteps n := by
  simp [affinePlan, Emitter.prefixSteps, Emitter.commandAt, Emitter.listCommands,
    Emitter.affineCommands, Emitter.commandSteps, emitSteps]

/-- Every tape except the accumulator is literally retained. -/
def emittedWord {K : Type} [DecidableEq K]
    (target : K) (base : K → List Bool) (value : Nat) : K → List Bool :=
  Function.update base target ((encodeWord value).reverse ++ base target)

@[simp] theorem emittedWord_target {K : Type} [DecidableEq K]
    (target : K) (base : K → List Bool) (value : Nat) :
    emittedWord target base value target = (encodeWord value).reverse ++ base target := by
  simp [emittedWord]

variable {ρ : Type} [Fintype ρ] {d : Nat}

@[simp] theorem program_firstEmit (positive : 0 < d) (H : Table (cloudSize d) d)
    (label : Emitter.Label 3 (degree d)) :
    program (ρ := ρ) positive H (.firstEmit label) =
      Emitter.statement (firstPlan ρ d) (fun _ : Fin 1 => Tape.inputVertex)
        .emitScratch .queryReverse Label.firstEmit (some Label.firstReverse) label := rfl

@[simp] theorem program_secondEmit (positive : 0 < d) (H : Table (cloudSize d) d)
    (label : Emitter.Label 3 (degree d)) :
    program (ρ := ρ) positive H (.secondEmit label) =
      Emitter.statement (secondPlan ρ d) (fun _ : Fin 1 => Tape.quotientFirst)
        .emitScratch .queryReverse Label.secondEmit (some Label.secondReverse) label := rfl

@[simp] theorem program_outputEmit (positive : 0 < d) (H : Table (cloudSize d) d)
    (label : Emitter.Label 3 (rowFactor d)) :
    program (ρ := ρ) positive H (.outputEmit label) =
      Emitter.statement (outputPlan ρ d) (fun _ : Fin 1 => Tape.quotientSecond)
        .emitScratch .output Label.outputEmit (some (Label.cleanup 0)) label := rfl

section Embedded

variable {K Λ : Type} [DecidableEq K]

/-- The code premise identifies concrete statements in a caller's program;
it does not assume any phase execution. -/
theorem firstEmitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .inputVertex) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step target))^[emitSteps n]
      (some ⟨some (labels (.firstEmit (Emitter.labelAt 3 _ 0 .entry))),
        ((ambient, ()), none), base⟩) =
      some ⟨some (labels .firstReverse), ((ambient, ()), none),
        emittedWord (ports .queryReverse) base (firstAddress n ambient.1.2)⟩ := by
  have code : ∀ l, target (labels (.firstEmit l)) =
      Emitter.statement (firstPlan ρ d) (fun _ : Fin 1 => ports .inputVertex)
        (ports .emitScratch) (ports .queryReverse) (fun k => labels (.firstEmit k))
        (some (labels .firstReverse)) l := by
    intro l
    rw [atLabels]
    rfl
  have run := Emitter.planTrace (firstPlan ρ d) (fun _ : Fin 1 => ports .inputVertex)
    (ports .emitScratch) (ports .queryReverse)
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro h; have h' := portsInjective h; cases h')
    (fun k => labels (.firstEmit k)) (some (labels .firstReverse)) target code
    (fun _ : Fin 1 => n) base (fun _ => source) scratch ambient
  simpa only [firstPlan, affinePlan_steps, affinePlan_bits, Emitter.resultTapes,
    emittedWord, firstAddress] using run

theorem secondEmitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .quotientFirst) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step target))^[emitSteps n]
      (some ⟨some (labels (.secondEmit (Emitter.labelAt 3 _ 0 .entry))),
        ((ambient, ()), none), base⟩) =
      some ⟨some (labels .secondReverse), ((ambient, ()), none),
        emittedWord (ports .queryReverse) base (secondAddress n ambient.1.2)⟩ := by
  have code : ∀ l, target (labels (.secondEmit l)) =
      Emitter.statement (secondPlan ρ d) (fun _ : Fin 1 => ports .quotientFirst)
        (ports .emitScratch) (ports .queryReverse) (fun k => labels (.secondEmit k))
        (some (labels .secondReverse)) l := by
    intro l
    rw [atLabels]
    rfl
  have run := Emitter.planTrace (secondPlan ρ d) (fun _ : Fin 1 => ports .quotientFirst)
    (ports .emitScratch) (ports .queryReverse)
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro h; have h' := portsInjective h; cases h')
    (fun k => labels (.secondEmit k)) (some (labels .secondReverse)) target code
    (fun _ : Fin 1 => n) base (fun _ => source) scratch ambient
  simpa only [secondPlan, affinePlan_steps, affinePlan_bits, Emitter.resultTapes,
    emittedWord, secondAddress] using run

theorem outputEmitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .quotientSecond) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step target))^[emitSteps n]
      (some ⟨some (labels (.outputEmit (Emitter.labelAt 3 _ 0 .entry))),
        ((ambient, ()), none), base⟩) =
      some ⟨some (labels (.cleanup 0)), ((ambient, ()), none),
        emittedWord (ports .output) base (outputAddress n ambient.1.2)⟩ := by
  have code : ∀ l, target (labels (.outputEmit l)) =
      Emitter.statement (outputPlan ρ d) (fun _ : Fin 1 => ports .quotientSecond)
        (ports .emitScratch) (ports .output) (fun k => labels (.outputEmit k))
        (some (labels (.cleanup 0))) l := by
    intro l
    rw [atLabels]
    rfl
  have run := Emitter.planTrace (outputPlan ρ d) (fun _ : Fin 1 => ports .quotientSecond)
    (ports .emitScratch) (ports .output)
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro h; have h' := portsInjective h; cases h')
    (fun k => labels (.outputEmit k)) (some (labels (.cleanup 0))) target code
    (fun _ : Fin 1 => n) base (fun _ => source) scratch ambient
  simpa only [outputPlan, affinePlan_steps, affinePlan_bits, Emitter.resultTapes,
    emittedWord, outputAddress] using run

end Embedded

end

/-!
# Actual lookup and reversal phases of the expander row program

The Boolean phase selector chooses the first or second occurrence of the same
preserving lookup. The selected word is proved to be the actual stored reverse
index of the supplied graph row. All execution facts follow from the concrete
program statements; no phase execution is assumed.
-/

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineComposition

def lookupPhaseLabel {d : Nat} (second : Bool)
    (l : MachinePreservingLookupClean.Label) : Label d :=
  if second then .secondLookup l else .firstLookup l

def scanPhaseLabel {d : Nat} (second : Bool) : Label d :=
  if second then .secondScan else .firstScan

def reversePhaseLabel {d : Nat} (second : Bool) : Label d :=
  if second then .secondReverse else .firstReverse

theorem lookupTape_injective : Function.Injective lookupTape := by decide

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

/-- The exact cleaned tape state produced by either lookup. -/
def lookupResultTapes (ports : Tape → K) (base : K → List Bool)
    (value : Nat) (indexSuffix : List Bool) : K → List Bool :=
  MachinePreservingLookup.initialTapes (ports ∘ lookupTape) base 0 indexSuffix []
    (encodeWord value ++ base (ports .lookupOutput))

section Lookup

variable {v d : Nat} (second : Bool) (positive : 0 < d)
    (H : Table (cloudSize d) d) (ports : Tape → K)
    (distinct : Function.Injective ports) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (base : K → List Bool) (G : Table v (degree d))
    (tableWord : base (ports .table) = encodeWords (rotationWords G))
    (scratchEmpty : base (ports .lookupRestore) = [])
    (x : Fin v × Fin (degree d)) (indexSuffix : List Bool)
    (counterWord : base (ports .queryIndex) =
      encodeWord (rowIndex v (degree d) x).val ++ indexSuffix)
    (workEmpty : base (ports .lookupWork) = [])
    (ambient : (Ambient ρ d × Fin (degree d)) × Unit) (register : Option Bool)

include positive H distinct exit code tableWord scratchEmpty counterWord workEmpty

/-- Actual first/second lookup execution on a stored graph row. The selected
reverse index is obtained from `rotationWords_getElem?`, not a caller premise. -/
theorem lookupPhaseTrace :
    (advance (TM2.step target))^[MachinePreservingLookupClean.steps
        (rotationWords G) (rowIndex v (degree d) x).val]
      (some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))),
        (ambient, register), base⟩) =
      some ⟨some (labels (scanPhaseLabel second)), (ambient, none),
        lookupResultTapes ports base (reverseIndex G (rowIndex v (degree d) x)).val
          indexSuffix⟩ := by
  apply MachinePreservingLookupClean.traceAt_fromTapes (ports ∘ lookupTape)
    (distinct.comp lookupTape_injective)
    (fun l => labels (lookupPhaseLabel second l)) (some (labels (scanPhaseLabel second)))
    target
  · intro l
    cases second
    · exact code (.firstLookup l)
    · exact code (.secondLookup l)
  · exact tableWord
  · exact scratchEmpty
  · exact rotationWords_getElem? G (rowIndex v (degree d) x)
  · exact counterWord
  · exact workEmpty

end Lookup

variable {d : Nat} (second : Bool) (positive : 0 < d)
    (H : Table (cloudSize d) d) (ports : Tape → K)
    (distinct : Function.Injective ports) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (base : K → List Bool)
    (ambient : (Ambient ρ d × Fin (degree d)) × Unit) (register : Option Bool)

include positive H distinct exit code

/-- The reversal consumes the reverse query word and prepends its forward
encoding to the index tape, retaining every other tape and finite state. -/
theorem reversePhaseTrace :
    (advance (TM2.step target))^[(base (ports .queryReverse)).length + 1]
      (some ⟨some (labels (reversePhaseLabel second)), (ambient, register), base⟩) =
      some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))), (ambient, none),
        Reduction.MachineTransfer.tapesAt (ports .queryReverse) (ports .queryIndex) base []
          ((base (ports .queryReverse)).reverse ++ base (ports .queryIndex))⟩ := by
  have h := Reduction.MachineTransfer.transferAt_fromTapes
    (ports .queryReverse) (ports .queryIndex)
    (fun h => (by decide : Tape.queryReverse ≠ .queryIndex) (distinct h))
    id false (labels (reversePhaseLabel second))
    (some (labels (lookupPhaseLabel second (.run .copyFirst)))) target
    (by cases second <;> exact code _) base ambient register
  unfold Reduction.MachineTransfer.nextAt at h
  unfold advance
  simpa only [List.map_id] using h

/-- Reversing an actual emitted unary field takes exactly `index + 2` steps.
This includes consuming the field's delimiter and leaving the reversal loop. -/
theorem reversePhaseTrace_unary (index : Nat) (suffix : List Bool)
    (queryWord : base (ports .queryReverse) = (encodeWord index).reverse)
    (indexWord : base (ports .queryIndex) = suffix) :
    (advance (TM2.step target))^[index + 2]
      (some ⟨some (labels (reversePhaseLabel second)), (ambient, register), base⟩) =
      some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))), (ambient, none),
        Reduction.MachineTransfer.tapesAt (ports .queryReverse) (ports .queryIndex) base []
          (encodeWord index ++ suffix)⟩ := by
  have h := reversePhaseTrace second positive H ports distinct labels exit target code
    base ambient register
  simpa only [queryWord, indexWord, List.length_reverse, encodeWord_length,
    List.reverse_reverse, Nat.add_assoc] using h

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderRowFrames
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Concrete data and tape frames for an actual expander-row computation

Only the five actual row inputs are stored. Every address, table return and
finite control value below is computed from those inputs. The thirteen tape
frames use the existing phase-output functions. These are data identities and
size bounds, not assumed machine executions. Kernel-checked with Lean 4.33.1.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

structure RowData (v d : Nat) where
  oldTable : Table v (degree d)
  smallTable : Table (cloudSize d) d
  inputVertex : Fin v
  inputCloud : Fin (cloudSize d)
  inputPort : Fin (degree d)

def rowData {v d : Nat} (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (cloud : Fin (cloudSize d)) (port : Fin (degree d)) : RowData v d :=
  ⟨G, H, vertex, cloud, port⟩

namespace RowData

variable {v d : Nat} (r : RowData v d)

def control0 : Control d := start r.smallTable r.inputCloud r.inputPort
def firstRow : Fin (v * degree d) := rowIndex v (degree d) (r.inputVertex, firstOffset r.control0)
def firstValue : Nat := (reverseIndex r.oldTable r.firstRow).val
def firstPair : Fin v × Fin (degree d) := lookup r.oldTable (r.inputVertex, firstOffset r.control0)
def firstVertex : Fin v := r.firstPair.1
def firstReturn : Fin (degree d) := r.firstPair.2
def control1 : Control d := receiveFirst r.control0 r.firstReturn
def secondRow : Fin (v * degree d) := rowIndex v (degree d) (r.firstVertex, secondOffset r.control1)
def secondValue : Nat := (reverseIndex r.oldTable r.secondRow).val
def secondPair : Fin v × Fin (degree d) := lookup r.oldTable (r.firstVertex, secondOffset r.control1)
def secondVertex : Fin v := r.secondPair.1
def secondReturn : Fin (degree d) := r.secondPair.2
def control2 : Control d := receiveSecond r.smallTable r.control1 r.secondReturn
def query1 : Nat := firstAddress r.inputVertex.val r.control0
def query2 : Nat := secondAddress r.firstVertex.val r.control1
def finalValue : Nat := outputAddress r.secondVertex.val r.control2
def tableLength : Nat := (encodeWords (rotationWords r.oldTable)).length

theorem query1_eq_firstRow : r.query1 = r.firstRow.val :=
  firstAddress_eq_rowIndex r.inputVertex r.control0

theorem query2_eq_secondRow : r.query2 = r.secondRow.val :=
  secondAddress_eq_rowIndex r.firstVertex r.control1

@[simp] theorem firstValue_div_degree : r.firstValue / degree d = r.firstVertex.val := rfl
@[simp] theorem firstValue_mod_degree : r.firstValue % degree d = r.firstReturn.val := rfl
@[simp] theorem secondValue_div_degree : r.secondValue / degree d = r.secondVertex.val := rfl
@[simp] theorem secondValue_mod_degree : r.secondValue % degree d = r.secondReturn.val := rfl

theorem firstReturn_eq_residue (positive : 0 < d) :
    r.firstReturn = MachineFixedDivMod.residue (degree d) (Nat.mul_pos positive positive)
      r.firstValue := Fin.ext rfl

theorem secondReturn_eq_residue (positive : 0 < d) :
    r.secondReturn = MachineFixedDivMod.residue (degree d) (Nat.mul_pos positive positive)
      r.secondValue := Fin.ext rfl

theorem rows_le_tableLength : v * degree d ≤ r.tableLength := by
  simp only [tableLength, encodeWords_length, rotationWords_length]
  omega

theorem query1_le_tableLength : r.query1 ≤ r.tableLength := by
  rw [query1_eq_firstRow]
  exact r.firstRow.isLt.le.trans r.rows_le_tableLength

theorem query2_le_tableLength : r.query2 ≤ r.tableLength := by
  rw [query2_eq_secondRow]
  exact r.secondRow.isLt.le.trans r.rows_le_tableLength

theorem firstValue_le_tableLength : r.firstValue ≤ r.tableLength :=
  (reverseIndex r.oldTable r.firstRow).isLt.le.trans r.rows_le_tableLength

theorem secondValue_le_tableLength : r.secondValue ≤ r.tableLength :=
  (reverseIndex r.oldTable r.secondRow).isLt.le.trans r.rows_le_tableLength

theorem inputVertex_le_tableLength : r.inputVertex.val ≤ r.tableLength := by
  have hq : 1 ≤ degree d := Nat.zero_lt_of_lt r.inputPort.isLt
  have hv : v ≤ v * degree d := by simpa using Nat.mul_le_mul_left v hq
  exact r.inputVertex.isLt.le.trans (hv.trans r.rows_le_tableLength)

theorem firstVertex_le_tableLength : r.firstVertex.val ≤ r.tableLength := by
  rw [← firstValue_div_degree]
  exact (Nat.div_le_self r.firstValue (degree d)).trans r.firstValue_le_tableLength

theorem secondVertex_le_tableLength : r.secondVertex.val ≤ r.tableLength := by
  rw [← secondValue_div_degree]
  exact (Nat.div_le_self r.secondValue (degree d)).trans r.secondValue_le_tableLength

theorem firstReturn_le_tableLength : r.firstReturn.val ≤ r.tableLength := by
  rw [← firstValue_mod_degree]
  exact (Nat.mod_le r.firstValue (degree d)).trans r.firstValue_le_tableLength

theorem secondReturn_le_tableLength : r.secondReturn.val ≤ r.tableLength := by
  rw [← secondValue_mod_degree]
  exact (Nat.mod_le r.secondValue (degree d)).trans r.secondValue_le_tableLength

end RowData

variable {v d : Nat}

/-- Complete explicit tape contents; all three scratch roles omitted here are empty. -/
def frameContents (r : RowData v d) (output : List Bool)
    (qr qi lo q1 q2 r1 r2 : List Bool) : Tape → List Bool
  | .inputVertex => encodeWord r.inputVertex.val
  | .table => encodeWords (rotationWords r.oldTable)
  | .output => output
  | .queryReverse => qr
  | .queryIndex => qi
  | .lookupOutput => lo
  | .quotientFirst => q1
  | .quotientSecond => q2
  | .remainderFirst => r1
  | .remainderSecond => r2
  | _ => []

def frame0 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  frameContents r output [] [] [] [] [] [] []
def frame1 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  initializedTapes id (frame0 r output)
def frame2 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  emittedWord .queryReverse (frame1 r output) r.query1
def frame3 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  Reduction.MachineTransfer.tapesAt .queryReverse .queryIndex (frame2 r output) []
    (encodeWord r.query1)
def frame4 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  lookupResultTapes id (frame3 r output) r.firstValue []
def frame5 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  divisionOutput d id .quotientFirst .remainderFirst (frame4 r output) r.firstValue [] [] []
def frame6 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  clearedQueryTapes id (frame5 r output)
def frame7 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  emittedWord .queryReverse (frame6 r output) r.query2
def frame8 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  Reduction.MachineTransfer.tapesAt .queryReverse .queryIndex (frame7 r output) []
    (encodeWord r.query2)
def frame9 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  lookupResultTapes id (frame8 r output) r.secondValue []
def frame10 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  divisionOutput d id .quotientSecond .remainderSecond (frame9 r output) r.secondValue [] [] []
def frame11 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  emittedWord .output (frame10 r output) r.finalValue
def frame12 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  cleanupTapes id (frame11 r output)

theorem lookupResultTapes_id_eq (base : Tape → List Bool)
    (value : Nat) (suffix : List Bool) :
    lookupResultTapes id base value suffix =
      Function.update
        (Function.update (Function.update base .queryIndex (encodeWord 0 ++ suffix))
          .lookupWork [])
        .lookupOutput (encodeWord value ++ base .lookupOutput) := rfl

@[simp] theorem frame1_eq (r : RowData v d) (output : List Bool) :
    frame1 r output = frameContents r output [] [] []
      (encodeWord 0) (encodeWord 0) (encodeWord 0) (encodeWord 0) := by
  funext tape
  cases tape <;> simp [frame1, frame0, frameContents, initializedTapes, encodeWord]

@[simp] theorem frame2_eq (r : RowData v d) (output : List Bool) :
    frame2 r output = frameContents r output (encodeWord r.query1).reverse [] []
      (encodeWord 0) (encodeWord 0) (encodeWord 0) (encodeWord 0) := by
  funext tape
  cases tape <;> simp [frame2, frameContents, emittedWord]

@[simp] theorem frame3_eq (r : RowData v d) (output : List Bool) :
    frame3 r output = frameContents r output [] (encodeWord r.query1) []
      (encodeWord 0) (encodeWord 0) (encodeWord 0) (encodeWord 0) := by
  funext tape
  cases tape <;> simp [frame3, frameContents, Reduction.MachineTransfer.tapesAt]

@[simp] theorem frame4_eq (r : RowData v d) (output : List Bool) :
    frame4 r output = frameContents r output [] (encodeWord 0) (encodeWord r.firstValue)
      (encodeWord 0) (encodeWord 0) (encodeWord 0) (encodeWord 0) := by
  funext tape
  cases tape <;> simp [frame4, lookupResultTapes_id_eq, frameContents]

@[simp] theorem frame5_eq (r : RowData v d) (output : List Bool) :
    frame5 r output = frameContents r output [] (encodeWord 0) (encodeWord 0)
      (encodeWord r.firstVertex.val) (encodeWord 0)
      (encodeWord r.firstReturn.val) (encodeWord 0) := by
  funext tape
  cases tape <;> simp [frame5, divisionOutput, MachineFixedDivMod.unaryTapes,
    MachineFixedDivMod.tapes, MachineCopy.forkTapes, frameContents]

@[simp] theorem frame6_eq (r : RowData v d) (output : List Bool) :
    frame6 r output = frameContents r output [] [] [] (encodeWord r.firstVertex.val)
      (encodeWord 0) (encodeWord r.firstReturn.val) (encodeWord 0) := by
  funext tape
  cases tape <;> simp [frame6, clearedQueryTapes, frameContents, encodeWord]

@[simp] theorem frame7_eq (r : RowData v d) (output : List Bool) :
    frame7 r output = frameContents r output (encodeWord r.query2).reverse [] []
      (encodeWord r.firstVertex.val) (encodeWord 0)
      (encodeWord r.firstReturn.val) (encodeWord 0) := by
  funext tape
  cases tape <;> simp [frame7, emittedWord, frameContents]

@[simp] theorem frame8_eq (r : RowData v d) (output : List Bool) :
    frame8 r output = frameContents r output [] (encodeWord r.query2) []
      (encodeWord r.firstVertex.val) (encodeWord 0)
      (encodeWord r.firstReturn.val) (encodeWord 0) := by
  funext tape
  cases tape <;> simp [frame8, Reduction.MachineTransfer.tapesAt, frameContents]

@[simp] theorem frame9_eq (r : RowData v d) (output : List Bool) :
    frame9 r output = frameContents r output [] (encodeWord 0) (encodeWord r.secondValue)
      (encodeWord r.firstVertex.val) (encodeWord 0)
      (encodeWord r.firstReturn.val) (encodeWord 0) := by
  funext tape
  cases tape <;> simp [frame9, lookupResultTapes_id_eq, frameContents]

@[simp] theorem frame10_eq (r : RowData v d) (output : List Bool) :
    frame10 r output = frameContents r output [] (encodeWord 0) (encodeWord 0)
      (encodeWord r.firstVertex.val) (encodeWord r.secondVertex.val)
      (encodeWord r.firstReturn.val) (encodeWord r.secondReturn.val) := by
  funext tape
  cases tape <;> simp [frame10, divisionOutput, MachineFixedDivMod.unaryTapes,
    MachineFixedDivMod.tapes, MachineCopy.forkTapes, frameContents]

@[simp] theorem frame11_eq (r : RowData v d) (output : List Bool) :
    frame11 r output = frameContents r ((encodeWord r.finalValue).reverse ++ output)
      [] (encodeWord 0) (encodeWord 0)
      (encodeWord r.firstVertex.val) (encodeWord r.secondVertex.val)
      (encodeWord r.firstReturn.val) (encodeWord r.secondReturn.val) := by
  funext tape
  cases tape <;> simp [frame11, emittedWord, frameContents]

@[simp] theorem frame12_eq (r : RowData v d) (output : List Bool) :
    frame12 r output = frameContents r ((encodeWord r.finalValue).reverse ++ output)
      [] [] [] [] [] [] [] := by
  funext tape
  cases tape <;> simp [frame12, cleanupTapes, frameContents]

theorem final_frame_eq (r : RowData v d) (output : List Bool) :
    frame12 r output = emittedWord .output (frame0 r output) r.finalValue := by
  funext tape
  cases tape <;> simp [frame0, emittedWord, frameContents]

/-! Direct input facts for the individual checked phase traces. -/

@[simp] theorem frame0_inputVertex (r : RowData v d) (output : List Bool) :
    frame0 r output .inputVertex = encodeWord r.inputVertex.val := rfl

@[simp] theorem frame0_table (r : RowData v d) (output : List Bool) :
    frame0 r output .table = encodeWords (rotationWords r.oldTable) := rfl

@[simp] theorem frame0_output (r : RowData v d) (output : List Bool) :
    frame0 r output .output = output := rfl

@[simp] theorem frame1_inputVertex (r : RowData v d) (output : List Bool) :
    frame1 r output .inputVertex = encodeWord r.inputVertex.val := by simp [frameContents]

@[simp] theorem frame1_emitScratch (r : RowData v d) (output : List Bool) :
    frame1 r output .emitScratch = [] := by simp [frameContents]

@[simp] theorem frame2_queryReverse (r : RowData v d) (output : List Bool) :
    frame2 r output .queryReverse = (encodeWord r.query1).reverse := by simp [frameContents]

@[simp] theorem frame2_queryIndex (r : RowData v d) (output : List Bool) :
    frame2 r output .queryIndex = [] := by simp [frameContents]

@[simp] theorem frame3_table (r : RowData v d) (output : List Bool) :
    frame3 r output .table = encodeWords (rotationWords r.oldTable) := by simp [frameContents]

@[simp] theorem frame3_lookupRestore (r : RowData v d) (output : List Bool) :
    frame3 r output .lookupRestore = [] := by simp [frameContents]

@[simp] theorem frame3_lookupWork (r : RowData v d) (output : List Bool) :
    frame3 r output .lookupWork = [] := by simp [frameContents]

@[simp] theorem frame3_lookupOutput (r : RowData v d) (output : List Bool) :
    frame3 r output .lookupOutput = [] := by simp [frameContents]

@[simp] theorem frame3_queryIndex (r : RowData v d) (output : List Bool) :
    frame3 r output .queryIndex = encodeWord r.query1 := by simp [frameContents]

@[simp] theorem frame4_lookupOutput (r : RowData v d) (output : List Bool) :
    frame4 r output .lookupOutput = encodeWord r.firstValue := by simp [frameContents]

@[simp] theorem frame4_quotientFirst (r : RowData v d) (output : List Bool) :
    frame4 r output .quotientFirst = encodeWord 0 := by simp [frameContents]

@[simp] theorem frame4_remainderFirst (r : RowData v d) (output : List Bool) :
    frame4 r output .remainderFirst = encodeWord 0 := by simp [frameContents]

@[simp] theorem frame6_quotientFirst (r : RowData v d) (output : List Bool) :
    frame6 r output .quotientFirst = encodeWord r.firstVertex.val := by simp [frameContents]

@[simp] theorem frame6_emitScratch (r : RowData v d) (output : List Bool) :
    frame6 r output .emitScratch = [] := by simp [frameContents]

@[simp] theorem frame7_queryReverse (r : RowData v d) (output : List Bool) :
    frame7 r output .queryReverse = (encodeWord r.query2).reverse := by simp [frameContents]

@[simp] theorem frame7_queryIndex (r : RowData v d) (output : List Bool) :
    frame7 r output .queryIndex = [] := by simp [frameContents]

@[simp] theorem frame8_table (r : RowData v d) (output : List Bool) :
    frame8 r output .table = encodeWords (rotationWords r.oldTable) := by simp [frameContents]

@[simp] theorem frame8_lookupRestore (r : RowData v d) (output : List Bool) :
    frame8 r output .lookupRestore = [] := by simp [frameContents]

@[simp] theorem frame8_lookupWork (r : RowData v d) (output : List Bool) :
    frame8 r output .lookupWork = [] := by simp [frameContents]

@[simp] theorem frame8_lookupOutput (r : RowData v d) (output : List Bool) :
    frame8 r output .lookupOutput = [] := by simp [frameContents]

@[simp] theorem frame8_queryIndex (r : RowData v d) (output : List Bool) :
    frame8 r output .queryIndex = encodeWord r.query2 := by simp [frameContents]

@[simp] theorem frame9_lookupOutput (r : RowData v d) (output : List Bool) :
    frame9 r output .lookupOutput = encodeWord r.secondValue := by simp [frameContents]

@[simp] theorem frame9_quotientSecond (r : RowData v d) (output : List Bool) :
    frame9 r output .quotientSecond = encodeWord 0 := by simp [frameContents]

@[simp] theorem frame9_remainderSecond (r : RowData v d) (output : List Bool) :
    frame9 r output .remainderSecond = encodeWord 0 := by simp [frameContents]

@[simp] theorem frame10_quotientSecond (r : RowData v d) (output : List Bool) :
    frame10 r output .quotientSecond = encodeWord r.secondVertex.val := by simp [frameContents]

@[simp] theorem frame10_emitScratch (r : RowData v d) (output : List Bool) :
    frame10 r output .emitScratch = [] := by simp [frameContents]

@[simp] theorem frame10_output (r : RowData v d) (output : List Bool) :
    frame10 r output .output = output := by simp [frameContents]

theorem cleanupSteps_le_tableLength (r : RowData v d) (output : List Bool) :
    cleanupSteps id (frame11 r output) ≤ 6 * (r.tableLength + 1) + 6 := by
  have h1 := r.firstVertex_le_tableLength
  have h2 := r.secondVertex_le_tableLength
  have h3 := r.firstReturn_le_tableLength
  have h4 := r.secondReturn_le_tableLength
  simp only [cleanupSteps, frame11_eq, id_eq, frameContents, encodeWord_length]
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderRow
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complete execution of one expander-table row

The actual finite program performs both stored-table lookups, splits their
results by its fixed degree, emits the resulting square/zigzag reverse index,
and clears its work tapes. Its transition bound is linear in the unary input
table length. The output accumulator and finite caller state are arbitrary.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords PCP.AlphabetTable

/-- The actual number of transitions, retaining both concrete lookup costs. -/
def rowSteps {v d : Nat} (r : RowData v d) (output : List Bool) : Nat :=
  1 + emitSteps r.inputVertex.val + (r.query1 + 2) +
    MachinePreservingLookupClean.steps (rotationWords r.oldTable) r.firstRow.val +
    (r.firstValue + 2) + 1 + emitSteps r.firstVertex.val + (r.query2 + 2) +
    MachinePreservingLookupClean.steps (rotationWords r.oldTable) r.secondRow.val +
    (r.secondValue + 2) + emitSteps r.secondVertex.val +
    (cleanupSteps id (frame11 r output) + 1)

section Execution

variable {v d : Nat} {ρ Λ : Type} [Fintype ρ]
    (positive : 0 < d) (r : RowData v d) (output : List Bool) (ambient : ρ)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : Tape => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive r.smallTable id labels exit l)

include code

/-- The complete execution follows the concrete program. The only code premise
places its instructions in a caller; every lookup is derived from `oldTable`. -/
theorem rowTraceAt :
    (advance (TM2.step target))^[rowSteps r output]
      (some ⟨some (labels .initialize_), divisionState positive ambient r.control0 none,
        frame0 r output⟩) =
      some ⟨exit, divisionState positive ambient r.control2 none,
        emittedWord .output (frame0 r output) r.finalValue⟩ := by
  let zero := MachineFixedDivMod.residue (degree d) (Nat.mul_pos positive positive) 0
  have h0 : (advance (TM2.step target))^[1]
      (some ⟨some (labels .initialize_), divisionState positive ambient r.control0 none,
        frame0 r output⟩) =
      some ⟨some (labels (.firstEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control0 none, frame1 r output⟩ := by
    simpa only [Function.iterate_one, advance_some, divisionState, frame1] using
      initializeStepAt positive r.smallTable id Function.injective_id labels exit target code
        (frame0 r output) (divisionState positive ambient r.control0 none)
  have h1 := firstEmitTraceAt positive r.smallTable id Function.injective_id
    labels exit target code r.inputVertex.val (frame1 r output)
    (by simp) (by simp) ((ambient,r.control0),zero)
  change (advance (TM2.step target))^[emitSteps r.inputVertex.val]
      (some ⟨some (labels (.firstEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control0 none, frame1 r output⟩) =
      some ⟨some (labels .firstReverse), divisionState positive ambient r.control0 none,
        frame2 r output⟩ at h1
  have h2 := reversePhaseTrace_unary false positive r.smallTable id Function.injective_id
    labels exit target code (frame2 r output) (((ambient,r.control0),zero),()) none
    r.query1 [] (by simp) (by simp)
  simp only [List.append_nil] at h2
  change (advance (TM2.step target))^[r.query1 + 2]
      (some ⟨some (labels .firstReverse), divisionState positive ambient r.control0 none,
        frame2 r output⟩) =
      some ⟨some (labels (.firstLookup (.run .copyFirst))),
        divisionState positive ambient r.control0 none, frame3 r output⟩ at h2
  have h3 := lookupPhaseTrace false positive r.smallTable id Function.injective_id
    labels exit target code (frame3 r output) r.oldTable
    (by simp) (by simp)
    (r.inputVertex, firstOffset r.control0) []
    (by simpa [frameContents, RowData.firstRow] using
      congrArg encodeWord r.query1_eq_firstRow)
    (by simp) (((ambient,r.control0),zero),()) none
  change (advance (TM2.step target))^[MachinePreservingLookupClean.steps
      (rotationWords r.oldTable) r.firstRow.val]
      (some ⟨some (labels (.firstLookup (.run .copyFirst))),
        divisionState positive ambient r.control0 none, frame3 r output⟩) =
      some ⟨some (labels .firstScan), divisionState positive ambient r.control0 none,
        frame4 r output⟩ at h3
  have h4 := firstDivisionTrace positive r.smallTable id Function.injective_id labels exit
    target code (frame4 r output) r.firstValue [] [] []
    (by simp) (by simp) (by simp)
    ambient r.control0 none
  rw [← r.firstReturn_eq_residue positive] at h4
  change (advance (TM2.step target))^[r.firstValue + 2]
      (some ⟨some (labels .firstScan), divisionState positive ambient r.control0 none,
        frame4 r output⟩) =
      some ⟨some (labels .clearQuery), divisionState positive ambient r.control1 none,
        frame5 r output⟩ at h4
  have h5 : (advance (TM2.step target))^[1]
      (some ⟨some (labels .clearQuery), divisionState positive ambient r.control1 none,
        frame5 r output⟩) =
      some ⟨some (labels (.secondEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control1 none, frame6 r output⟩ := by
    simpa only [Function.iterate_one, advance_some, frame6] using
      clearQueryStepAt positive r.smallTable id Function.injective_id labels exit target code
        (frame5 r output) (divisionState positive ambient r.control1 none)
  have h6 := secondEmitTraceAt positive r.smallTable id Function.injective_id
    labels exit target code r.firstVertex.val (frame6 r output)
    (by simp) (by simp) ((ambient,r.control1),zero)
  change (advance (TM2.step target))^[emitSteps r.firstVertex.val]
      (some ⟨some (labels (.secondEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control1 none, frame6 r output⟩) =
      some ⟨some (labels .secondReverse), divisionState positive ambient r.control1 none,
        frame7 r output⟩ at h6
  have h7 := reversePhaseTrace_unary true positive r.smallTable id Function.injective_id
    labels exit target code (frame7 r output) (((ambient,r.control1),zero),()) none
    r.query2 [] (by simp) (by simp)
  simp only [List.append_nil] at h7
  change (advance (TM2.step target))^[r.query2 + 2]
      (some ⟨some (labels .secondReverse), divisionState positive ambient r.control1 none,
        frame7 r output⟩) =
      some ⟨some (labels (.secondLookup (.run .copyFirst))),
        divisionState positive ambient r.control1 none, frame8 r output⟩ at h7
  have h8 := lookupPhaseTrace true positive r.smallTable id Function.injective_id
    labels exit target code (frame8 r output) r.oldTable
    (by simp) (by simp)
    (r.firstVertex, secondOffset r.control1) []
    (by simpa [frameContents, RowData.secondRow] using
      congrArg encodeWord r.query2_eq_secondRow)
    (by simp) (((ambient,r.control1),zero),()) none
  change (advance (TM2.step target))^[MachinePreservingLookupClean.steps
      (rotationWords r.oldTable) r.secondRow.val]
      (some ⟨some (labels (.secondLookup (.run .copyFirst))),
        divisionState positive ambient r.control1 none, frame8 r output⟩) =
      some ⟨some (labels .secondScan), divisionState positive ambient r.control1 none,
        frame9 r output⟩ at h8
  have h9 := secondDivisionTrace positive r.smallTable id Function.injective_id labels exit
    target code (frame9 r output) r.secondValue [] [] []
    (by simp) (by simp) (by simp)
    ambient r.control1 none
  rw [← r.secondReturn_eq_residue positive] at h9
  change (advance (TM2.step target))^[r.secondValue + 2]
      (some ⟨some (labels .secondScan), divisionState positive ambient r.control1 none,
        frame9 r output⟩) =
      some ⟨some (labels (.outputEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control2 none, frame10 r output⟩ at h9
  have h10 := outputEmitTraceAt positive r.smallTable id Function.injective_id
    labels exit target code r.secondVertex.val (frame10 r output)
    (by simp) (by simp) ((ambient,r.control2),zero)
  change (advance (TM2.step target))^[emitSteps r.secondVertex.val]
      (some ⟨some (labels (.outputEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control2 none, frame10 r output⟩) =
      some ⟨some (labels (.cleanup 0)), divisionState positive ambient r.control2 none,
        frame11 r output⟩ at h10
  have h11 := cleanupExitTraceAt positive r.smallTable id Function.injective_id
    labels exit target code (frame11 r output) (divisionState positive ambient r.control2 none)
  change (advance (TM2.step target))^[cleanupSteps id (frame11 r output) + 1]
      (some ⟨some (labels (.cleanup 0)), divisionState positive ambient r.control2 none,
        frame11 r output⟩) =
      some ⟨exit, divisionState positive ambient r.control2 none, frame12 r output⟩ at h11
  rw [final_frame_eq] at h11
  exact concatenate (concatenate (concatenate (concatenate (concatenate
    (concatenate (concatenate (concatenate (concatenate (concatenate
      (concatenate h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11

end Execution

theorem rowSteps_le {v d : Nat} (r : RowData v d) (output : List Bool) :
    rowSteps r output ≤ 80 * (r.tableLength + 1) := by
  have lookup1 := MachinePreservingLookupClean.steps_le (rotationWords r.oldTable)
    r.firstRow.val r.firstValue (rotationWords_getElem? r.oldTable r.firstRow)
  have lookup2 := MachinePreservingLookupClean.steps_le (rotationWords r.oldTable)
    r.secondRow.val r.secondValue (rotationWords_getElem? r.oldTable r.secondRow)
  have h0 := r.inputVertex_le_tableLength
  have h1 := r.query1_le_tableLength
  have h2 := r.firstValue_le_tableLength
  have h3 := r.firstVertex_le_tableLength
  have h4 := r.query2_le_tableLength
  have h5 := r.secondValue_le_tableLength
  have h6 := r.secondVertex_le_tableLength
  have clean := cleanupSteps_le_tableLength r output
  change _ ≤ 6 * r.tableLength + 4 at lookup1 lookup2
  simp only [rowSteps, emitSteps]
  omega

/-- The actual row program has a linear transition bound, with all temporary
tapes empty at return. The bound holds for every valid finite input table. -/
def rowInTimeAt {v d : Nat} {ρ Λ : Type} [Fintype ρ]
    (positive : 0 < d) (r : RowData v d) (output : List Bool) (ambient : ρ)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : Tape => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive r.smallTable id labels exit l) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels .initialize_), divisionState positive ambient r.control0 none,
        frame0 r output⟩
      (some ⟨exit, divisionState positive ambient r.control2 none,
        emittedWord .output (frame0 r output) r.finalValue⟩)
      (80 * (r.tableLength + 1)) where
  steps := rowSteps r output
  evals_in_steps := rowTraceAt positive r output ambient labels exit target code
  steps_le_m := rowSteps_le r output

/-- Specialization to the standalone finite row program. -/
def rowInTime {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (r : RowData v d) (output : List Bool) (ambient : ρ) :
    StateTransition.EvalsToInTime (TM2.step (program positive r.smallTable))
      ⟨some .initialize_, divisionState positive ambient r.control0 none, frame0 r output⟩
      (some ⟨none, divisionState positive ambient r.control2 none,
        emittedWord .output (frame0 r output) r.finalValue⟩)
      (80 * (r.tableLength + 1)) :=
  rowInTimeAt positive r output ambient id none (program positive r.smallTable) (fun _ => rfl)

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderTableRows
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual execution of all expander-table positions for one vertex

The inner loop calls the complete row machine once per fixed cloud/port position.
The returned state and the successful machine execution are constructed together.
Neither a row execution nor an inner-loop execution is a caller premise.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

def tableRowData {v d : Nat} (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (position : Position d) : MachineExpanderRow.RowData v d :=
  MachineExpanderRow.rowData G H vertex (positionPair position).1 (positionPair position).2

theorem tableRowData_finalValue {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (position : Position d) :
    (tableRowData G H vertex position).finalValue = rowValue G H vertex position := rfl

theorem tableRowData_frame0 {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (position : Position d) (output : List Bool) :
    MachineExpanderRow.frame0 (tableRowData G H vertex position) output =
      rowTapes vertex.val (encodeWords (rotationWords G)) output := by
  funext tape
  cases tape <;> rfl

theorem tableRowData_finalFrame {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (position : Position d) (output : List Bool) :
    MachineExpanderRow.emittedWord .output
      (MachineExpanderRow.frame0 (tableRowData G H vertex position) output)
      (tableRowData G H vertex position).finalValue =
      rowTapes vertex.val (encodeWords (rotationWords G))
        ((encodeWord (rowValue G H vertex position)).reverse ++ output) := by
  rw [tableRowData_frame0, tableRowData_finalValue]
  funext tape
  cases tape <;> simp [MachineExpanderRow.emittedWord, rowTapes]

variable {ρ : Type} [Fintype ρ] {v d : Nat}

def rowAfterState (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d) : State ρ d :=
  (MachineExpanderRow.divisionState positive (caller state)
    (tableRowData G H vertex state.2).control2 none, state.2)

omit [Fintype ρ] in
@[simp] theorem rowAfterState_position (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d) :
    (rowAfterState positive G H vertex state).2 = state.2 := rfl

omit [Fintype ρ] in
@[simp] theorem caller_rowAfterState (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d) :
    caller (rowAfterState positive G H vertex state) = caller state := rfl

/-- Preparation and one actual embedded row call, with the two extra tapes
retained. The row value is computed from the actual old and small tables. -/
def preparedRowInTime (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (remaining : Nat) (output countSuffix result : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inr .prepareRow), state,
        boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result⟩
      (some ⟨some (.inr .afterRow), rowAfterState positive G H vertex state,
        boundaryTapes vertex.val remaining (encodeWords (rotationWords G))
          ((encodeWord (rowValue G H vertex state.2)).reverse ++ output) countSuffix result⟩)
      (1 + 80 * ((encodeWords (rotationWords G)).length + 1)) := by
  have raw := rowExecution positive H state.2 (extraTapes remaining countSuffix result)
    (MachineExpanderRow.rowInTime positive (tableRowData G H vertex state.2) output (caller state))
  have run : StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inl .initialize_), prepareState positive H state,
        boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result⟩
      (some ⟨some (.inr .afterRow), rowAfterState positive G H vertex state,
        boundaryTapes vertex.val remaining (encodeWords (rotationWords G))
          ((encodeWord (rowValue G H vertex state.2)).reverse ++ output) countSuffix result⟩)
      (80 * ((encodeWords (rotationWords G)).length + 1)) := by
    rw [tableRowData_finalFrame, tableRowData_frame0] at raw
    simpa only [MachineEmbedding.configuration, MachineEmbedding.label, rowReturn,
      prepareState, boundaryState, rowAfterState, boundaryTapes,
      MachineExpanderRow.RowData.tableLength, MachineExpanderRow.RowData.control0,
      tableRowData, MachineExpanderRow.rowData] using raw
  exact sequence
    (singleStep _ _ _ (prepareRowStep positive H
      (boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result)
      state)) run

/-- A successful suffix of the finite position loop, returning actual finite
state together with the execution certificate and its preserved caller. -/
structure VertexSuffixRun (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (remaining : Nat) (output countSuffix result : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .prepareRow), state,
      boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result⟩
    (some ⟨some (.inr .vertexGuard), finalState,
      boundaryTapes (vertex.val + 1) remaining (encodeWords (rotationWords G))
        (accumulate ((vertexWords G H vertex).drop state.2.val) output) countSuffix result⟩)
    ((rowFactor d - state.2.val) * (80 * ((encodeWords (rotationWords G)).length + 1) + 2))

def suffixRun_aux (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (remaining : Nat)
    (countSuffix result : List Bool) (n : Nat) :
    (state : State ρ d) → state.2.val + n = rowFactor d → (output : List Bool) →
      VertexSuffixRun positive G H vertex state remaining output countSuffix result := by
  induction n with
  | zero =>
      intro state count output
      have hp := state.2.isLt
      exact False.elim (by omega)
  | succ n ih =>
      intro state count output
      let after := rowAfterState positive G H vertex state
      let nextOutput := (encodeWord (rowValue G H vertex state.2)).reverse ++ output
      have row := preparedRowInTime positive G H vertex state remaining output countSuffix result
      by_cases last : n = 0
      · have hp : state.2.val + 1 = rowFactor d := by omega
        have finish := singleStep _ _ _ (afterRow_last_boundaryStep positive H vertex.val remaining
          (encodeWords (rotationWords G)) nextOutput countSuffix result after (by
            change ¬ state.2.val + 1 < rowFactor d
            omega))
        refine ⟨resetPositionState positive after, ?_, rfl, ?_⟩
        · rfl
        · have all := sequence row finish
          have words : accumulate ((vertexWords G H vertex).drop state.2.val) output =
              nextOutput := by
            rw [vertexWords_drop_last G H vertex state.2 hp]
            rfl
          have budget : rowFactor d - state.2.val = 1 := by omega
          rw [words, budget, Nat.one_mul]
          exact widen all (by omega)
      · have more : state.2.val + 1 < rowFactor d := by omega
        let next := advancePositionState positive after
        have nextPositionValue : next.2.val = state.2.val + 1 :=
          nextPosition_val_of_lt positive state.2 more
        have nextCount : next.2.val + n = rowFactor d := by omega
        let tail := ih next nextCount nextOutput
        have advance := singleStep _ _ _ (afterRow_moreStep positive H
          (boundaryTapes vertex.val remaining (encodeWords (rotationWords G))
            nextOutput countSuffix result) after more)
        have all := sequence (sequence row advance) tail.execution
        refine ⟨tail.finalState, ?_, tail.position_zero, ?_⟩
        · exact tail.caller_preserved
        · have words : accumulate ((vertexWords G H vertex).drop state.2.val) output =
              accumulate ((vertexWords G H vertex).drop next.2.val) nextOutput := by
            rw [vertexWords_drop_succ G H vertex state.2, nextPositionValue]
            rfl
          rw [words]
          apply widen all
          have hcount : rowFactor d - state.2.val = n + 1 := by omega
          have hnext : rowFactor d - next.2.val = n := by omega
          rw [hcount, hnext, Nat.add_mul, Nat.one_mul]
          omega

def suffixInTime (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (remaining : Nat) (output countSuffix result : List Bool) :
    VertexSuffixRun positive G H vertex state remaining output countSuffix result :=
  suffixRun_aux positive G H vertex remaining countSuffix result
    (rowFactor d - state.2.val) state (by have h := state.2.isLt; omega) output

/-- The complete inner loop for one vertex, starting at position zero. -/
structure VertexRun (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (remaining : Nat) (output countSuffix result : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .prepareRow), state,
      boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result⟩
    (some ⟨some (.inr .vertexGuard), finalState,
      boundaryTapes (vertex.val + 1) remaining (encodeWords (rotationWords G))
        (accumulate (vertexWords G H vertex) output) countSuffix result⟩)
    (rowFactor d * (80 * ((encodeWords (rotationWords G)).length + 1) + 2))

def vertexInTime (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (position : state.2 = zeroPosition positive)
    (remaining : Nat) (output countSuffix result : List Bool) :
    VertexRun positive G H vertex state remaining output countSuffix result := by
  let run := suffixInTime positive G H vertex state remaining output countSuffix result
  refine ⟨run.finalState, run.caller_preserved, run.position_zero, ?_⟩
  have zero : state.2.val = 0 := congrArg Fin.val position
  simpa only [zero, List.drop_zero, Nat.sub_zero] using run.execution

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderTableLoop
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual outer vertex iteration for expander tables

The invariant is the reversed unary encoding of all completed vertices. Each
positive unary guard invokes the proved complete fixed-position row loop;
the zero guard enters the actual output-reversal phase. No execution premise
is supplied by the caller.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

def oldTableWord {v d : Nat} (G : Table v (degree d)) : List Bool :=
  encodeWords (rotationWords G)

def accumulatedVertices {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (current : Nat) : List Bool :=
  accumulate (priorVertices G H current) []

@[simp] theorem accumulatedVertices_zero {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) : accumulatedVertices G H 0 = [] := by
  simp [accumulatedVertices, accumulate]

theorem accumulatedVertices_succ {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (current : Nat) (valid : current < v) :
    accumulatedVertices G H (current + 1) =
      accumulate (vertexWords G H ⟨current, valid⟩) (accumulatedVertices G H current) := by
  simp only [accumulatedVertices, priorVertices_succ G H current valid, accumulate_append]

theorem accumulatedVertices_full {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) : accumulatedVertices G H v =
      (encodeWords (rotationWords (step G H))).reverse := by
  simp [accumulatedVertices, accumulate_generatedWords]

def vertexBodyBudget {v d : Nat} (G : Table v (degree d)) : Nat :=
  rowFactor d * (80 * ((oldTableWord G).length + 1) + 2)

def vertexLoopBudget {v d : Nat} (G : Table v (degree d)) (remaining : Nat) : Nat :=
  remaining * (vertexBodyBudget G + 1) + 1

def vertexLoopTapes {v d : Nat} (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (current remaining : Nat) (suffix : List Bool) : ∀ tape, List (Alphabet tape) :=
  boundaryTapes current remaining (oldTableWord G) (accumulatedVertices G H current) suffix []

structure VertexLoopRun {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (current remaining : Nat) (state : State ρ d) (suffix : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .vertexGuard), state, vertexLoopTapes G H current remaining suffix⟩
    (some ⟨some (.inr .reverseOutput), finalState, vertexLoopTapes G H v 0 suffix⟩)
    (vertexLoopBudget G remaining)

/-- Execute every remaining vertex in the common finite table program. -/
def vertexLoopInTime {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (current remaining : Nat) (state : State ρ d) (suffix : List Bool)
    (count : current + remaining = v) (position : state.2 = zeroPosition positive) :
    VertexLoopRun positive G H current remaining state suffix := by
  induction remaining generalizing current state with
  | zero =>
      have hc : current = v := by omega
      subst current
      refine ⟨clearRegister state, caller_clearRegister state, ?_, ?_⟩
      · simpa only [clearRegister] using position
      · simpa only [vertexLoopBudget, Nat.zero_mul, Nat.zero_add, vertexLoopTapes] using
          boundarySingleStep _ _ _ (vertexGuard_boundary_zeroStep positive H v (oldTableWord G)
            (accumulatedVertices G H v) suffix [] state)
  | succ remaining ih =>
      have valid : current < v := by omega
      let vertex : Fin v := ⟨current, valid⟩
      let body := vertexInTime positive G H vertex (clearRegister state)
        (by simpa only [clearRegister] using position) remaining
        (accumulatedVertices G H current) suffix []
      have nextCount : current + 1 + remaining = v := by omega
      let rest := ih (current + 1) body.finalState nextCount body.position_zero
      have output_eq : accumulate (vertexWords G H vertex)
          (accumulatedVertices G H current) = accumulatedVertices G H (current + 1) :=
        (accumulatedVertices_succ G H current valid).symm
      let guard := boundarySingleStep _ _ _
        (vertexGuard_boundary_succStep positive H current remaining (oldTableWord G)
          (accumulatedVertices G H current) suffix [] state)
      have bodyRun : StateTransition.EvalsToInTime (TM2.step (program positive H))
          ⟨some (.inr .prepareRow), clearRegister state,
            boundaryTapes current remaining (oldTableWord G)
              (accumulatedVertices G H current) suffix []⟩
          (some ⟨some (.inr .vertexGuard), body.finalState,
            vertexLoopTapes G H (current + 1) remaining suffix⟩)
          (vertexBodyBudget G) := by
        simpa only [vertexLoopTapes, vertexBodyBudget, oldTableWord, output_eq] using body.execution
      let first := StateTransition.EvalsToInTime.trans (TM2.step (program positive H))
        _ _ _ _ _ guard bodyRun
      let all := StateTransition.EvalsToInTime.trans (TM2.step (program positive H))
        _ _ _ _ _ first rest.execution
      refine ⟨rest.finalState, ?_, rest.position_zero, ?_⟩
      · exact rest.caller_preserved.trans
          (body.caller_preserved.trans (caller_clearRegister state))
      · refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
        have bound := all.steps_le_m
        simp only [vertexLoopBudget, Nat.succ_mul] at bound ⊢
        omega

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderTableReverse
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

open Turing
open MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

@[simp] theorem clearRegister_position (state : State ρ d) :
    (clearRegister state).2 = state.2 := rfl

@[simp] theorem clearRegister_register (state : State ρ d) :
    (clearRegister state).1.2 = none := rfl

@[simp] theorem clearRegister_idempotent (state : State ρ d) :
    clearRegister (clearRegister state) = clearRegister state := rfl

theorem boundaryTapes_reverse_update (vertex remaining : Nat)
    (oldTable output countSuffix result nextOutput nextResult : List Bool) :
    Function.update
      (Function.update (boundaryTapes vertex remaining oldTable output countSuffix result)
        (.inl .output) nextOutput)
      (.inr .result) nextResult =
      boundaryTapes vertex remaining oldTable nextOutput countSuffix nextResult := by
  funext tape
  rcases tape with row | extra
  · cases row <;>
      simp [boundaryTapes, rowTapes, MachineEmbedding.tapes, Function.update]
  · cases extra <;>
      simp [boundaryTapes, extraTapes, MachineEmbedding.tapes, Function.update]

variable [Fintype ρ]

/-- Exact execution of the entire final reverse loop, including its empty
test. No reversal-execution hypothesis is assumed. -/
theorem reverseOutputTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    (advance (TM2.step (program positive H)))^[output.length + 1]
      (some ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩) =
      some ⟨some (.inr .done), clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩ := by
  induction output generalizing result state with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, advance_some,
        List.reverse_nil, List.nil_append] using
        reverseOutput_nilStep positive H
          (boundaryTapes vertex remaining oldTable [] countSuffix result) state rfl
  | cons symbol output ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [reverseOutput_consStep positive H
        (boundaryTapes vertex remaining oldTable (symbol :: output) countSuffix result)
        state symbol output rfl]
      change (advance (TM2.step (program positive H)))^[output.length + 1]
        (some ⟨some (.inr .reverseOutput), ((state.1.1, some symbol), state.2),
          Function.update
            (Function.update
              (boundaryTapes vertex remaining oldTable (symbol :: output) countSuffix result)
              (.inl .output) output)
            (.inr .result) (symbol :: result)⟩) = _
      rw [boundaryTapes_reverse_update]
      simpa only [clearRegister, List.reverse_cons, List.append_assoc,
        List.singleton_append] using
        ih (symbol :: result) ((state.1.1, some symbol), state.2)

/-- The actual `done` statement halts one transition after reversal completes. -/
theorem reverseOutputHaltTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    (advance (TM2.step (program positive H)))^[output.length + 2]
      (some ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩) =
      some ⟨none, clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩ := by
  rw [show output.length + 2 = (output.length + 1) + 1 by omega,
    Function.iterate_succ_apply',
    reverseOutputTrace positive H vertex remaining oldTable output countSuffix result state]
  exact doneStep positive H
    (boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result))
    (clearRegister state)

def reverseOutputHaltInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩
      (some ⟨none, clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩)
      (output.length + 2) where
  steps := output.length + 2
  evals_in_steps := reverseOutputHaltTrace positive H vertex remaining oldTable output countSuffix result state
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderTable
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complete finite machine execution for the next expander table

The initialized old table and unary vertex count are consumed by one actual
finite program. The machine writes precisely the complete square/zigzag
rotation table, preserving its old table and all promised framing. The bound
is quadratic in the unary old-table length for each fixed small graph.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

def completeBudget {v d : Nat} (G : Table v (degree d)) (H : Table (cloudSize d) d) : Nat :=
  1 + vertexLoopBudget G v + ((encodeWords (rotationWords (step G H))).length + 2)

def timeCoefficient (d : Nat) : Nat :=
  rowFactor d * (rowFactor d + 1) + 82 * rowFactor d + 5

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.C (timeCoefficient d) * (Polynomial.X + 1) ^ 2

theorem vertices_le_word_length {v d : Nat} (positive : 0 < d)
    (G : Table v (degree d)) : v ≤ (oldTableWord G).length := by
  have hq : 1 ≤ degree d := Nat.mul_pos positive positive
  have hv : v ≤ v * degree d := by simpa using Nat.mul_le_mul_left v hq
  have hr : v * degree d ≤ (oldTableWord G).length := by
    simp only [oldTableWord, encodeWords_length, rotationWords_length]
    omega
  exact hv.trans hr

/-- All actual loop, row, and final reversal costs are bounded quadratically. -/
theorem completeBudget_le {v d : Nat} (positive : 0 < d)
    (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    completeBudget G H ≤ (timePolynomial d).eval (oldTableWord G).length := by
  let L := (oldTableWord G).length
  let M := rowFactor d
  have vBound : v ≤ L + 1 := (vertices_le_word_length positive G).trans (Nat.le_succ L)
  have emitBound : 80 * (L + 1) + 2 ≤ 82 * (L + 1) := by omega
  have bodyBound : vertexBodyBudget G + 1 ≤ (82 * M + 1) * (L + 1) := by
    have mulBound := Nat.mul_le_mul_left M emitBound
    change M * (80 * (L + 1) + 2) + 1 ≤ _
    nlinarith
  have iterations := Nat.mul_le_mul vBound bodyBound
  have loopBound : v * (vertexBodyBudget G + 1) ≤ (82 * M + 1) * (L + 1)^2 := by
    calc
      _ ≤ (L + 1) * ((82 * M + 1) * (L + 1)) := iterations
      _ = _ := by ring
  have rowBound : v * M ≤ M * (L + 1) := by
    simpa only [Nat.mul_comm v M] using Nat.mul_le_mul_left M vBound
  have rowSuccBound : v * M + 1 ≤ (M + 1) * (L + 1) := by nlinarith
  have productBound := Nat.mul_le_mul rowBound rowSuccBound
  have lengthBound : (encodeWords (rotationWords (step G H))).length ≤
      M * (M + 1) * (L + 1)^2 := by
    calc
      _ ≤ (v * M) * (v * M + 1) := by
        simpa only [generatedWords_eq_rotationWords] using encode_generatedWords_length_le G H
      _ ≤ (M * (L + 1)) * ((M + 1) * (L + 1)) := productBound
      _ = _ := by ring
  have oneBound : 1 ≤ (L + 1)^2 := by nlinarith
  have combined := Nat.add_le_add loopBound lengthBound
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  change completeBudget G H ≤ (M * (M + 1) + 82 * M + 5) * (L + 1)^2
  unfold completeBudget vertexLoopBudget
  nlinarith

structure TableRun {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (state : State ρ d) (suffix : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .initialize_), state, initialTapes v (oldTableWord G) suffix⟩
    (some ⟨none, finalState,
      finalTapes v (oldTableWord G) (encodeWords (rotationWords (step G H))) suffix⟩)
    ((timePolynomial d).eval (oldTableWord G).length)

def initializeInTime {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (state : State ρ d) (suffix : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inr .initialize_), state, initialTapes v (oldTableWord G) suffix⟩
      (some ⟨some (.inr .vertexGuard), initialState positive H (caller state),
        vertexLoopTapes G H 0 v suffix⟩) 1 where
  steps := 1
  evals_in_steps := by
    change TM2.step (program (ρ := ρ) positive H)
      ⟨some (.inr .initialize_), state, initialTapes v (oldTableWord G) suffix⟩ =
      some ⟨some (.inr .vertexGuard), initialState positive H (caller state),
        vertexLoopTapes G H 0 v suffix⟩
    simpa only [vertexLoopTapes, accumulatedVertices_zero] using
      initialize_boundaryStep positive H v (oldTableWord G) suffix state
  steps_le_m := Nat.le_refl _

/-- Construct the entire table execution from its actual initialized inputs.
No row trace, loop trace, or abstract computational witness is a hypothesis. -/
def tableInTime {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (state : State ρ d) (suffix : List Bool) : TableRun positive G H state suffix := by
  let loop := vertexLoopInTime positive G H 0 v
    (initialState positive H (caller state)) suffix (by omega) rfl
  let initialRun := initializeInTime positive G H state suffix
  have finish : StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inr .reverseOutput), loop.finalState, vertexLoopTapes G H v 0 suffix⟩
      (some ⟨none, clearRegister loop.finalState,
        finalTapes v (oldTableWord G) (encodeWords (rotationWords (step G H))) suffix⟩)
      ((encodeWords (rotationWords (step G H))).length + 2) := by
    simpa only [vertexLoopTapes, finalTapes, accumulatedVertices_full, List.reverse_reverse,
      List.append_nil, List.length_reverse] using
      reverseOutputHaltInTime positive H v 0 (oldTableWord G)
        (accumulatedVertices G H v) suffix [] loop.finalState
  let first := StateTransition.EvalsToInTime.trans (TM2.step (program positive H))
    _ _ _ _ _ initialRun loop.execution
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program positive H))
    _ _ _ _ _ first finish
  refine ⟨clearRegister loop.finalState, ?_, ?_, ?_⟩
  · exact (caller_clearRegister loop.finalState).trans loop.caller_preserved
  · simpa only [clearRegister] using loop.position_zero
  · refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
    have bound := all.steps_le_m
    have polynomialBound := completeBudget_le positive G H
    unfold completeBudget at polynomialBound
    omega

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderFamilyBoundsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounds for materializing the actual expander family

The costs use the encoded old and new rotation tables, and the already checked
table-machine polynomial. The finite sum follows the actual recursive table
family. These arithmetic lemmas introduce no execution assumptions and make no
claim that the output is polynomial in an isolated binary level parameter.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

noncomputable def resizeCost {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) : Nat :=
  (MachineExpanderTable.timePolynomial d).eval (MachineExpanderTable.oldTableWord G).length +
    6 * v + (MachineExpanderTable.oldTableWord G).length +
    2 * (encodeWords (rotationWords (step G H))).length + 15

def resizeCoefficient (d : Nat) : Nat :=
  MachineExpanderTable.timeCoefficient d * (degree d + 1) ^ 4 +
    3 * (degree d + 1) ^ 2 + 21

/-- The complete unary encoding, including every word delimiter, is counted. -/
theorem wordLength_add_one_le {v q N : Nat} (G : Table v q) (hv : v ≤ N) :
    (encodeWords (rotationWords G)).length + 1 ≤ (q + 1)^2 * (N + 1)^2 := by
  have hlength := encode_rotationWords_length_le G
  have hrow : v * q + 1 ≤ (q + 1) * (N + 1) := by
    have h := Nat.mul_le_mul_right q hv
    nlinarith
  calc
    _ ≤ (v * q + 1)^2 := by nlinarith
    _ ≤ ((q + 1) * (N + 1))^2 := Nat.pow_le_pow_left hrow 2
    _ = _ := by ring

theorem resizeCost_le {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (N : Nat) (hv : v ≤ N)
    (hnext : v * cloudSize d ≤ N) :
    resizeCost G H ≤ resizeCoefficient d * (N + 1)^4 := by
  let oldL := (MachineExpanderTable.oldTableWord G).length
  let newL := (encodeWords (rotationWords (step G H))).length
  have oldBound : oldL + 1 ≤ (degree d + 1)^2 * (N + 1)^2 :=
    wordLength_add_one_le G hv
  have newBound : newL + 1 ≤ (degree d + 1)^2 * (N + 1)^2 :=
    wordLength_add_one_le (step G H) hnext
  have timeBound : (MachineExpanderTable.timePolynomial d).eval oldL ≤
      MachineExpanderTable.timeCoefficient d * (degree d + 1)^4 * (N + 1)^4 := by
    simp only [MachineExpanderTable.timePolynomial, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one]
    calc
      _ ≤ MachineExpanderTable.timeCoefficient d *
          ((degree d + 1)^2 * (N + 1)^2)^2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left oldBound 2)
      _ = _ := by ring
  have pow24 : (N + 1)^2 ≤ (N + 1)^4 :=
    Nat.pow_le_pow_right (Nat.succ_pos N) (by decide)
  have overheadBound : oldL + 2 * newL ≤
      3 * (degree d + 1)^2 * (N + 1)^4 := by
    have h := Nat.mul_le_mul_left ((degree d + 1)^2) pow24
    calc
      _ ≤ 3 * ((degree d + 1)^2 * (N + 1)^2) := by omega
      _ ≤ 3 * ((degree d + 1)^2 * (N + 1)^4) := Nat.mul_le_mul_left 3 h
      _ = _ := by ring
  have npow : N + 1 ≤ (N + 1)^4 := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right (Nat.succ_pos N) (show 1 ≤ 4 by decide)
  have linearBound : 6 * v + 15 ≤ 21 * (N + 1)^4 := by omega
  change (MachineExpanderTable.timePolynomial d).eval oldL + 6 * v + oldL +
    2 * newL + 15 ≤ _
  unfold resizeCoefficient
  nlinarith only [timeBound, overheadBound, linearBound]

noncomputable def resizeSum {d : Nat} (H : Table (cloudSize d) d) (level : Nat) : Nat :=
  ∑ i ∈ Finset.range level, resizeCost (family H i) H

@[simp] theorem resizeSum_zero {d : Nat} (H : Table (cloudSize d) d) :
    resizeSum H 0 = 0 := by simp [resizeSum]

theorem resizeSum_succ {d : Nat} (H : Table (cloudSize d) d) (level : Nat) :
    resizeSum H (level + 1) = resizeSum H level + resizeCost (family H level) H := by
  simp only [resizeSum, Finset.sum_range_succ]

noncomputable def familyBudget {d : Nat} (H : Table (cloudSize d) d) (level : Nat) : Nat :=
  resizeSum H level + level + 3

@[simp] theorem familyBudget_zero {d : Nat} (H : Table (cloudSize d) d) :
    familyBudget H 0 = 3 := by simp [familyBudget]

theorem resizeSum_le {d : Nat} (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (level : Nat) :
    resizeSum H level ≤ resizeCoefficient d * (vertexCount (degree d) level + 1)^5 := by
  let N := vertexCount (degree d) level
  have positive : 0 < degree d := by
    have h : 1 < degree d * degree d := growth
    nlinarith
  have hmono := vertexCount_monotone positive
  have hlevel : level ≤ N := level_le_vertexCount growth level
  have eachBound : ∀ i ∈ Finset.range level,
      resizeCost (family H i) H ≤ resizeCoefficient d * (N + 1)^4 := by
    intro i hi
    have hi' : i < level := Finset.mem_range.mp hi
    apply resizeCost_le (family H i) H N
    · exact hmono (by omega)
    · exact hmono (show i + 1 ≤ level by omega)
  have sumBound : resizeSum H level ≤ level * (resizeCoefficient d * (N + 1)^4) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range level, resizeCoefficient d * (N + 1)^4 :=
        Finset.sum_le_sum eachBound
      _ = _ := by simp
  calc
    _ ≤ level * (resizeCoefficient d * (N + 1)^4) := sumBound
    _ ≤ (N + 1) * (resizeCoefficient d * (N + 1)^4) :=
      Nat.mul_le_mul_right _ (hlevel.trans (Nat.le_succ N))
    _ = _ := by ring

/-- All actual resize costs plus the counted-loop overhead. -/
theorem familyBudget_le {d : Nat} (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (level : Nat) :
    familyBudget H level ≤
      (resizeCoefficient d + 4) * (vertexCount (degree d) level + 1)^5 := by
  have hsum := resizeSum_le H growth level
  have hlevel := level_le_vertexCount growth level
  have hpow : vertexCount (degree d) level + 1 ≤
      (vertexCount (degree d) level + 1)^5 := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (Nat.succ_pos (vertexCount (degree d) level)) (show 1 ≤ 5 by decide)
  have overhead : level + 3 ≤ 4 * (vertexCount (degree d) level + 1)^5 := by omega
  unfold familyBudget
  nlinarith only [hsum, overhead]

def inputCoefficient : Nat :=
  (resizeCoefficient PCP.Expanders.baseDegree + 4) * (PCP.ExpanderFamily.growth + 1)^5

/-- For the fixed base graph, the bounded padding level has a polynomial cost
in the requested unary size, including size zero. -/
theorem familyBudget_at_boundedLevel_le
    (H : Table (cloudSize PCP.Expanders.baseDegree) PCP.Expanders.baseDegree) (k : Nat) :
    familyBudget H (PCP.PreprocessingLevels.boundedLevel k) ≤ inputCoefficient * (k + 1)^5 := by
  have hg : cloudSize PCP.Expanders.baseDegree = PCP.ExpanderFamily.growth := by
    unfold cloudSize degree PCP.ExpanderFamily.growth
    ring
  have growth : 1 < cloudSize PCP.Expanders.baseDegree := by
    rw [hg]
    exact PCP.ExpanderFamily.growth_gt_one
  have bound := familyBudget_le H growth (PCP.PreprocessingLevels.boundedLevel k)
  rw [PCP.PreprocessingLevels.table_vertexCount_eq_paddedSize] at bound
  have sizeBound : PCP.PreprocessingLevels.paddedSize k + 1 ≤
      (PCP.ExpanderFamily.growth + 1) * (k + 1) := by
    have h := paddedSize_le_succ_input k
    nlinarith
  calc
    _ ≤ (resizeCoefficient PCP.Expanders.baseDegree + 4) *
        (PCP.PreprocessingLevels.paddedSize k + 1)^5 := bound
    _ ≤ (resizeCoefficient PCP.Expanders.baseDegree + 4) *
        ((PCP.ExpanderFamily.growth + 1) * (k + 1))^5 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left sizeBound 5)
    _ = _ := by unfold inputCoefficient; ring

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamilyBounds

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

section

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

/-- The six nonempty tape roles that may occur between expansion phases. -/
def cycleWords (remaining : Nat) (word current vertex count result suffix : List Bool) :
    Tape → List Bool
  | .inl (.inl .table) => word
  | .inl (.inl .inputVertex) => vertex
  | .inl (.inr .vertexCount) => count
  | .inl (.inr .result) => result
  | .inr .remainingLevel => encodeWord remaining ++ suffix
  | .inr .currentSize => current
  | _ => []

def cycleTapes (remaining : Nat) (word current vertex count result suffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  fromBoolTapes (cycleWords remaining word current vertex count result suffix)

@[simp] theorem toBool_cycleTapes (remaining : Nat)
    (word current vertex count result suffix : List Bool) :
    toBoolTapes (cycleTapes remaining word current vertex count result suffix) =
      cycleWords remaining word current vertex count result suffix := toBool_fromBool _

theorem boundaryTapes_eq_cycleTapes (remaining current : Nat) (word suffix : List Bool) :
    boundaryTapes remaining current word suffix =
      cycleTapes remaining word (encodeWord current) [] [] [] suffix := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

def copyFrame (remaining current : Nat) (word suffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes (MachineExpanderTable.initialTapes current word [])
    (extraFrame remaining current suffix)

def returnFrame (remaining current : Nat) (oldWord newWord suffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes (MachineExpanderTable.finalTapes current oldWord newWord [])
    (extraFrame remaining current suffix)

def installedFrame (remaining current : Nat) (newWord suffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  cycleTapes remaining newWord [] (encodeWord current) (encodeWord 0) [] suffix

def multipliedFrame (d remaining current : Nat) (newWord suffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  cycleTapes remaining newWord (encodeWord (cloudSize d * current))
    (encodeWord current) (encodeWord 0) [] suffix

theorem copyFrame_eq_cycleTapes (remaining current : Nat) (word suffix : List Bool) :
    copyFrame remaining current word suffix =
      cycleTapes remaining word (encodeWord current) [] (encodeWord current) [] suffix := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> simp [copyFrame, MachineEmbedding.tapes,
        MachineExpanderTable.initialTapes, MachineExpanderTable.extraTapes,
        cycleTapes, fromBoolTapes, boolWord, cycleWords]
  · cases tape <;> rfl

theorem returnFrame_eq_cycleTapes (remaining current : Nat)
    (oldWord newWord suffix : List Bool) :
    returnFrame remaining current oldWord newWord suffix =
      cycleTapes remaining oldWord (encodeWord current) (encodeWord current)
        (encodeWord 0) newWord suffix := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> simp [returnFrame, MachineEmbedding.tapes,
        MachineExpanderTable.finalTapes, MachineExpanderTable.boundaryTapes,
        MachineExpanderTable.extraTapes, cycleTapes, fromBoolTapes, boolWord, cycleWords]
  · cases tape <;> rfl

theorem copyFrame_eq_update (remaining current : Nat) (word suffix : List Bool) :
    Function.update (boundaryTapes remaining current word suffix)
      vertexCountTape (encodeWord current) = copyFrame remaining current word suffix := by
  rw [boundaryTapes_eq_cycleTapes, copyFrame_eq_cycleTapes]
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

theorem multipliedFrame_eq_update (d remaining current : Nat) (word suffix : List Bool) :
    Function.update (installedFrame remaining current word suffix)
      (.inr .currentSize) (encodeWord (cloudSize d * current)) =
      multipliedFrame d remaining current word suffix := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

end

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

theorem installed_returnFrame (remaining current : Nat) (oldWord newWord suffix : List Bool) :
    fromBoolTapes (installedTapes (toBoolTapes (returnFrame remaining current oldWord newWord suffix))
      newWord) = installedFrame remaining current newWord suffix := by
  rw [returnFrame_eq_cycleTapes, toBool_cycleTapes]
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

theorem cleaned_multipliedFrame (d remaining current : Nat) (newWord suffix : List Bool) :
    fromBoolTapes (cleanedCounterTapes
      (toBoolTapes (multipliedFrame d remaining current newWord suffix))) =
      boundaryTapes remaining (current * cloudSize d) newWord suffix := by
  rw [boundaryTapes_eq_cycleTapes]
  unfold multipliedFrame
  rw [toBool_cycleTapes]
  have multiply : cloudSize d * current = current * cloudSize d := Nat.mul_comm _ _
  rw [multiply]
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

structure ResizeRun {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (G : Table v (degree d)) (remaining : Nat) (state : State ρ d) (suffix : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
    ⟨some (.inr (.affine .copyCount .seed)), state,
      boundaryTapes remaining v (MachineExpanderTable.oldTableWord G) suffix⟩
    (some ⟨some (.inr .levelGuard), finalState,
      boundaryTapes remaining (v * cloudSize d)
        (encodeWords (rotationWords (step G H))) suffix⟩)
    (resizeCost G H)

/-- The resize certificate is built from actual primitive and table executions;
its caller supplies no phase trace or computational hypothesis. -/
noncomputable def resizeInTime {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (G : Table v (degree d)) (remaining : Nat) (state : State ρ d) (suffix : List Bool) :
    ResizeRun positive H growth G remaining state suffix := by
  let oldWord := MachineExpanderTable.oldTableWord G
  let newWord := encodeWords (rotationWords (step G H))
  have copy := copyCountInTime positive H growth
    (boundaryTapes remaining v oldWord suffix) v rfl rfl rfl state
  rw [copyFrame_eq_update] at copy
  let called := MachineExpanderTable.tableInTime positive G H (clearRegister state).1 []
  let returned : State ρ d := (called.finalState, ())
  have eta : ((clearRegister state).1, ()) = clearRegister state := by
    rcases state with ⟨state, extra⟩
    cases extra
    rfl
  have call : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inl (.inr .initialize_)), clearRegister state,
        copyFrame remaining v oldWord suffix⟩
      (some ⟨some (.inr .clearOldTable), returned,
        returnFrame remaining v oldWord newWord suffix⟩)
      ((MachineExpanderTable.timePolynomial d).eval oldWord.length) := by
    simpa only [MachineEmbedding.configuration, MachineEmbedding.label, tableReturn, eta,
      copyFrame, returnFrame, oldWord, newWord, returned] using
      tableExecution positive H growth (extraFrame remaining v suffix) called.execution
  have install := installTableInTime positive H growth
    (returnFrame remaining v oldWord newWord suffix) newWord
    (by rw [returnFrame_eq_cycleTapes, toBool_cycleTapes]; rfl)
    (by rw [returnFrame_eq_cycleTapes, toBool_cycleTapes]; rfl) returned
  rw [installed_returnFrame] at install
  have installRun : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .clearOldTable), returned, returnFrame remaining v oldWord newWord suffix⟩
      (some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister returned,
        installedFrame remaining v newWord suffix⟩)
      (oldWord.length + 2 * newWord.length + (v + 1) + 4) := by
    simpa only [returnFrame_eq_cycleTapes, toBool_cycleTapes, cycleWords, tableTape,
      encodeWord_length] using install
  have multiply := multiplySizeInTime positive H growth
    (installedFrame remaining v newWord suffix) v rfl rfl rfl (clearRegister returned)
  rw [clearRegister_idempotent, multipliedFrame_eq_update] at multiply
  have clean := cleanupCountersInTime positive H growth
    (multipliedFrame d remaining v newWord suffix) (clearRegister returned)
  rw [clearRegister_idempotent, cleaned_multipliedFrame] at clean
  have cleanRun : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .drainInputVertex), clearRegister returned,
        multipliedFrame d remaining v newWord suffix⟩
      (some ⟨some (.inr .levelGuard), clearRegister returned,
        boundaryTapes remaining (v * cloudSize d) newWord suffix⟩) (v + 4) := by
    simpa only [multipliedFrame, toBool_cycleTapes, cycleWords, inputVertexTape,
      vertexCountTape, encodeWord_length, Nat.zero_add, Nat.add_assoc] using clean
  let a := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ copy call
  let b := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ a installRun
  let c := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ b multiply
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ c cleanRun
  refine ⟨clearRegister returned, ?_, ?_⟩
  · exact (caller_clearRegister returned).trans
      (called.caller_preserved.trans (caller_clearRegister state))
  · refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
    have bound := all.steps_le_m
    unfold resizeCost
    change _ ≤ (MachineExpanderTable.timePolynomial d).eval oldWord.length +
      6 * v + oldWord.length + 2 * newWord.length + 15
    omega

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderFamilyLoop
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual counted repetition of complete table-expansion cycles. The input
counter is physically decremented, and the invariant carries the exact table
at the completed family level. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

noncomputable def levelLoopCost {d : Nat} (H : Table (cloudSize d) d) : Nat → Nat → Nat
  | _, 0 => 1
  | start, remaining + 1 => 1 + resizeCost (family H start) H +
      levelLoopCost H (start + 1) remaining

theorem levelLoopCost_prefix {d : Nat} (H : Table (cloudSize d) d) (start remaining : Nat) :
    levelLoopCost H start remaining + resizeSum H start =
      resizeSum H (start + remaining) + remaining + 1 := by
  induction remaining generalizing start with
  | zero => simp [levelLoopCost, Nat.add_comm]
  | succ remaining ih =>
      have h := ih (start + 1)
      rw [resizeSum_succ] at h
      have index : start + 1 + remaining = start + (remaining + 1) := by omega
      rw [index] at h
      simp only [levelLoopCost]
      omega

theorem levelLoopCost_zero_start {d : Nat} (H : Table (cloudSize d) d) (remaining : Nat) :
    levelLoopCost H 0 remaining = resizeSum H remaining + remaining + 1 := by
  simpa only [resizeSum_zero, Nat.add_zero, Nat.zero_add] using
    levelLoopCost_prefix H 0 remaining

def levelLoopTapes {d : Nat} (H : Table (cloudSize d) d)
    (completed remaining : Nat) (suffix : List Bool) : ∀ tape, List (Alphabet tape) :=
  boundaryTapes remaining (vertexCount (degree d) completed)
    (encodeWords (rotationWords (family H completed))) suffix

structure LevelLoopRun {d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (completed remaining : Nat) (state : State ρ d) (suffix : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
    ⟨some (.inr .levelGuard), state, levelLoopTapes H completed remaining suffix⟩
    (some ⟨some (.inr .done), finalState, familyTapes H (completed + remaining) suffix⟩)
    (levelLoopCost H completed remaining)

/-- Every body is the already constructed actual resize run. There is no
whole-loop, body-trace, or computational-correctness premise. -/
noncomputable def levelLoopInTime {d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (completed remaining : Nat) (state : State ρ d) (suffix : List Bool) :
    LevelLoopRun positive H growth completed remaining state suffix := by
  induction remaining generalizing completed state with
  | zero =>
      refine ⟨clearRegister state, caller_clearRegister state, ?_⟩
      simpa only [levelLoopCost, levelLoopTapes, familyTapes, Nat.add_zero] using
        familySingleStep _ _ _ (levelGuard_boundary_zeroStep positive H growth
          (vertexCount (degree d) completed) (encodeWords (rotationWords (family H completed)))
          suffix state)
  | succ remaining ih =>
      let cycle := resizeInTime positive H growth (family H completed) remaining
        (clearRegister state) suffix
      let rest := ih (completed + 1) cycle.finalState
      let guard := familySingleStep _ _ _ (levelGuard_boundary_succStep positive H growth
        remaining (vertexCount (degree d) completed)
        (encodeWords (rotationWords (family H completed))) suffix state)
      have cycleRun : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
          ⟨some (.inr (.affine .copyCount .seed)), clearRegister state,
            levelLoopTapes H completed remaining suffix⟩
          (some ⟨some (.inr .levelGuard), cycle.finalState,
            levelLoopTapes H (completed + 1) remaining suffix⟩)
          (resizeCost (family H completed) H) := cycle.execution
      let first := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
        _ _ _ _ _ guard cycleRun
      let all := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
        _ _ _ _ _ first rest.execution
      have index : completed + 1 + remaining = completed + (remaining + 1) := by omega
      refine ⟨rest.finalState, ?_, ?_⟩
      · exact rest.caller_preserved.trans
          (cycle.caller_preserved.trans (caller_clearRegister state))
      · rw [index] at all
        refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
        have bound := all.steps_le_m
        simp only [levelLoopCost]
        omega

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineExpanderFamily
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

/-- Complete initialization, actual counted loop, and normalized halt. -/
noncomputable def familyInTime {d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (level : Nat) (state : State ρ d) (suffix : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .initialize_), state, initialTapes level suffix⟩
      (some ⟨none, initialState positive H (caller state), familyTapes H level suffix⟩)
      (familyBudget H level) := by
  let loop := levelLoopInTime positive H growth 0 level
    (initialState positive H (caller state)) suffix
  have initialRun : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .initialize_), state, initialTapes level suffix⟩
      (some ⟨some (.inr .levelGuard), initialState positive H (caller state),
        levelLoopTapes H 0 level suffix⟩) 1 :=
    singleFamilyStep _ _ _ (initialize_boundaryStep positive H growth level suffix state)
  have finalCaller : caller loop.finalState = caller state := loop.caller_preserved
  have done : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .done), loop.finalState, familyTapes H level suffix⟩
      (some ⟨none, initialState positive H (caller state), familyTapes H level suffix⟩) 1 := by
    simpa only [normalizeState, finalCaller] using
      singleFamilyStep _ _ _ (doneStep positive H growth (familyTapes H level suffix)
        loop.finalState)
  have loopRun : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .levelGuard), initialState positive H (caller state),
        levelLoopTapes H 0 level suffix⟩
      (some ⟨some (.inr .done), loop.finalState, familyTapes H level suffix⟩)
      (levelLoopCost H 0 level) := by simpa only [Nat.zero_add] using loop.execution
  let first := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ initialRun loopRun
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ first done
  refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
  have bound := all.steps_le_m
  have costEquality := levelLoopCost_zero_start H level
  unfold familyBudget
  omega

theorem baseDegree_cloud_growth :
    cloudSize PCP.Expanders.baseDegree = PCP.ExpanderFamily.growth := by
  unfold cloudSize degree PCP.ExpanderFamily.growth
  ring

theorem baseDegree_cloud_gt_one : 1 < cloudSize PCP.Expanders.baseDegree := by
  rw [baseDegree_cloud_growth]
  exact PCP.ExpanderFamily.growth_gt_one

theorem baseDegree_positive : 0 < PCP.Expanders.baseDegree := by
  have h := baseDegree_cloud_gt_one
  unfold cloudSize degree at h
  by_contra hn
  have hz : PCP.Expanders.baseDegree = 0 := by omega
  rw [hz] at h
  norm_num at h

/-- At the physically computable padding level, the actual family run has a
fixed polynomial bound in requested unary size. The separate ceiling-power
machine supplies this exact level and preserves the requested size. -/
noncomputable def paddedFamilyInTime {ρ : Type} [Fintype ρ]
    (H : Table (cloudSize PCP.Expanders.baseDegree) PCP.Expanders.baseDegree)
    (requested : Nat) (state : State ρ PCP.Expanders.baseDegree) (suffix : List Bool) :
    StateTransition.EvalsToInTime
      (TM2.step (program baseDegree_positive H baseDegree_cloud_gt_one))
      ⟨some (.inr .initialize_), state,
        initialTapes (PCP.PreprocessingLevels.boundedLevel requested) suffix⟩
      (some ⟨none, initialState baseDegree_positive H (caller state),
        familyTapes H (PCP.PreprocessingLevels.boundedLevel requested) suffix⟩)
      (inputCoefficient * (requested + 1)^5) where
  toEvalsTo := (familyInTime baseDegree_positive H baseDegree_cloud_gt_one
    (PCP.PreprocessingLevels.boundedLevel requested) state suffix).toEvalsTo
  steps_le_m := (familyInTime baseDegree_positive H baseDegree_cloud_gt_one
    (PCP.PreprocessingLevels.boundedLevel requested) state suffix).steps_le_m.trans
      (familyBudget_at_boundedLevel_le H requested)

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineLazyCodec
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact dummy-block codec used by the complete lazy-table machine. -/
namespace UniqueGamesTheorem.Foundations.Complexity.MachineLazyCodec
open PCP.GraphTables PCP.PreprocessingLazyWords

theorem rowBits_stay {n d : Nat} (v : Fin n) (p : Fin d) :
    MachineDummyRows.rowBits v.val (2 * d * v.val + p.val) =
      encodeWords (rowWords (stayRow d v p)) := by
  have h := MachineDummyRows.rowBits_eq_graph_row v (stayRow d v p).reverseIndex
  rw [stayRow_reverse_val] at h
  exact h

theorem rowsBits_stay {n d : Nat} (v : Fin n) :
    MachineDummyRows.rowsBits v.val (2 * d * v.val) d =
      encodeWords ((List.ofFn (stayRow d v)).flatMap rowWords) := by
  rw [rowsBits_ofFn, encodeWords_flatMap]
  simp only [List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  congr 1
  funext p
  exact rowBits_stay v p

end UniqueGamesTheorem.Foundations.Complexity.MachineLazyCodec

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachinePortReindex
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePortReindex

open Turing MachineComposition
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ A : Type} [DecidableEq K]

def instruction (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 5 → K) (labels : Label d → Λ) (exit : Option Λ) :
    Label d → TM2.Stmt (Alphabet (K := K)) Λ (State A d)
  | .copySeed => MachineUnaryAffineAt.seed (tape 2) 0 (labels .copyScan)
  | .copyScan => MachineUnaryAffineAt.scan (tape 0) (tape 1) (tape 2) 1
      (labels .copyScan) (labels .copyRestore)
  | .copyRestore => Reduction.MachineTransfer.loopAt (tape 1) (tape 0) id false
      (labels .copyRestore) (some (labels .initialize_))
  | .initialize_ => .push (tape 3) (fun _ => false)
      (.push (tape 4) (fun _ => false) (.goto fun _ => labels .divide))
  | .divide => MachineFixedDivMod.scanLoop d positive (tape 2) (tape 3)
      (labels .divide) (fun r => labels (.emit r))
  | .emit r => emit d positive (tape 4) b r (labels .affineScan)
  | .affineScan => MachineUnaryAffineAt.scan (tape 3) (tape 1) (tape 4) c
      (labels .affineScan) (labels .affineRestore)
  | .affineRestore => Reduction.MachineTransfer.loopAt (tape 1) (tape 3) id false
      (labels .affineRestore) (some (labels .drainQuotient))
  | .drainQuotient => MachineDrain.drain (tape 3) (labels .drainQuotient)
      (some (labels .finish))
  | .finish => .pop (tape 2) (fun s _ => clean d positive s.1.1) (exitAt exit)

/-- Exact execution in any caller containing these finite instructions. The
only changed caller tape is the output; the input field and all three initially
empty work tapes are preserved exactly. -/
theorem reindexTrace (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A d))
    (atLabels : ∀ l, program (labels l) = instruction d positive c b tape labels exit l)
    (base : K → List Bool) (j : Nat) (suffix : List Bool)
    (sourceWord : base (tape 0) = encodeWord j ++ suffix)
    (scratchEmpty : base (tape 1) = []) (workEmpty : base (tape 2) = [])
    (quotientEmpty : base (tape 3) = []) (ambient : A) :
    (advance (TM2.step program))^[steps d j]
      (some ⟨some (labels .copySeed), clean d positive ambient, base⟩) =
      some ⟨exit, clean d positive ambient,
        Function.update base (tape 4) (encodeWord (value d c b j) ++ base (tape 4))⟩ := by
  have hd (i k : Fin 5) (h : i ≠ k) : tape i ≠ tape k := fun e => h (distinct e)
  let q := j / d
  let r := MachineFixedDivMod.residue d positive j
  let copied := Function.update base (tape 2) (encodeWord j)
  let initialized := frame tape base (encodeWord j) (encodeWord 0)
    (encodeWord 0 ++ base (tape 4))
  let divided := frame tape base (encodeWord 0) (encodeWord q)
    (encodeWord 0 ++ base (tape 4))
  let emitted := frame tape base (encodeWord 0) (encodeWord q)
    (encodeWord (r.val + b) ++ base (tape 4))
  let computed := frame tape base (encodeWord 0) (encodeWord q)
    (encodeWord (c * q + (r.val + b)) ++ base (tape 4))
  let drained := frame tape base (encodeWord 0) []
    (encodeWord (c * q + (r.val + b)) ++ base (tape 4))
  have copyRun : (advance (TM2.step program))^[2 * (j + 1) + 1]
      (some ⟨some (labels .copySeed), clean d positive ambient, base⟩) =
      some ⟨some (labels .initialize_), clean d positive ambient, copied⟩ := by
    simpa only [clean, copied, Nat.one_mul, Nat.add_zero, workEmpty, List.append_nil] using
      MachineUnaryAffineAt.seededAffineTrace (tape 0) (tape 1) (tape 2)
        (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 1 2 (by decide)) 1 0
        (labels .copySeed) (labels .copyScan) (labels .copyRestore)
        (some (labels .initialize_)) program (atLabels .copySeed) (atLabels .copyScan)
        (atLabels .copyRestore) base j suffix sourceWord scratchEmpty
        (ambient, MachineFixedDivMod.residue d positive 0) none
  have initRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .initialize_), clean d positive ambient, copied⟩) =
      some ⟨some (labels .divide), clean d positive ambient, initialized⟩ := by
    change some (TM2.stepAux (program (labels .initialize_)) _ _) = _
    rw [atLabels]
    simp [instruction, TM2.stepAux, copied, initialized, frame, MachineCopy.forkTapes,
      hd 3 2 (by decide), hd 4 2 (by decide), hd 4 3 (by decide), quotientEmpty, encodeWord]
  have divisionInput : MachineFixedDivMod.unaryTapes (tape 2) (tape 3) (tape 4)
      base j 0 0 [] [] (base (tape 4)) = initialized := by
    simp only [MachineFixedDivMod.unaryTapes, MachineFixedDivMod.tapes,
      List.append_nil, initialized, frame]
  have divisionOutput : MachineFixedDivMod.unaryTapes (tape 2) (tape 3) (tape 4)
      base 0 q 0 [] [] (base (tape 4)) = divided := by
    simp only [MachineFixedDivMod.unaryTapes, MachineFixedDivMod.tapes,
      List.append_nil, divided, frame]
  have divideRun : (advance (TM2.step program))^[j + 1]
      (some ⟨some (labels .divide), clean d positive ambient, initialized⟩) =
      some ⟨some (labels (.emit r)), ((ambient, r), some false), divided⟩ := by
    have h := MachineFixedDivMod.scanTrace_fromCount d positive (tape 2) (tape 3) (tape 4)
      (hd 2 3 (by decide)) (hd 2 4 (by decide)) (hd 3 4 (by decide))
      (labels .divide) (fun a => labels (.emit a)) program (atLabels .divide)
      base j 0 [] [] (base (tape 4)) ambient none
    simpa only [Nat.zero_div, Nat.zero_add, divisionInput, divisionOutput, clean, r, q] using h
  have emitRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels (.emit r)), ((ambient, r), some false), divided⟩) =
      some ⟨some (labels .affineScan), clean d positive ambient, emitted⟩ := by
    change some (TM2.stepAux (program (labels (.emit r))) _ _) = _
    rw [atLabels]
    simp [instruction, emit, stepAux_pushWord, TM2.stepAux, divided, emitted, frame,
      MachineCopy.forkTapes, List.reverse_replicate, encodeWord, List.append_assoc]
  have affineInput : MachineUnaryAffineAt.tapes (tape 3) (tape 1) (tape 4)
      emitted (encodeWord q ++ []) [] (encodeWord (r.val + b) ++ base (tape 4)) = emitted := by
    have heq : emitted (tape 3) = encodeWord q := by
      simp [emitted, frame, MachineCopy.forkTapes, hd 3 4 (by decide)]
    have hempty : emitted (tape 1) = [] := by
      simp [emitted, frame, MachineCopy.forkTapes, hd 1 2 (by decide),
        hd 1 3 (by decide), hd 1 4 (by decide), scratchEmpty]
    have hout : emitted (tape 4) = encodeWord (r.val + b) ++ base (tape 4) := by
      simp [emitted, frame, MachineCopy.forkTapes]
    rw [List.append_nil, ← heq, ← hempty, ← hout]
    exact MachineCopy.forkTapes_self _ _ _ _
  have affineOutput : MachineUnaryAffineAt.tapes (tape 3) (tape 1) (tape 4)
      emitted (encodeWord q ++ []) [] (encodeWord (c * q + (r.val + b)) ++ base (tape 4)) =
      computed := by
    funext k
    by_cases h1 : k = tape 1
    · subst k
      simp [MachineUnaryAffineAt.tapes, emitted, computed, frame, MachineCopy.forkTapes,
        hd 1 2 (by decide), hd 1 3 (by decide), hd 1 4 (by decide), scratchEmpty]
    · by_cases h3 : k = tape 3
      · subst k
        simp [MachineUnaryAffineAt.tapes, emitted, computed, frame, MachineCopy.forkTapes,
          hd 3 1 (by decide), hd 3 4 (by decide)]
      · by_cases h4 : k = tape 4
        · subst k; simp [MachineUnaryAffineAt.tapes, computed, frame, MachineCopy.forkTapes]
        · simp [MachineUnaryAffineAt.tapes, emitted, computed, frame, MachineCopy.forkTapes,
            h1, h3, h4]
  have affineRun : (advance (TM2.step program))^[2 * (q + 1)]
      (some ⟨some (labels .affineScan), clean d positive ambient, emitted⟩) =
      some ⟨some (labels .drainQuotient), clean d positive ambient, computed⟩ := by
    have h := MachineUnaryAffineAt.affineTrace (tape 3) (tape 1) (tape 4)
      (hd 3 1 (by decide)) (hd 3 4 (by decide)) (hd 1 4 (by decide)) c
      (labels .affineScan) (labels .affineRestore) (some (labels .drainQuotient))
      program (atLabels .affineScan) (atLabels .affineRestore) emitted q (r.val + b)
      [] (base (tape 4)) (ambient, MachineFixedDivMod.residue d positive 0) none
    simpa only [affineInput, affineOutput, clean] using h
  have quotientWord : computed (tape 3) = encodeWord q := by
    simp [computed, frame, MachineCopy.forkTapes, hd 3 4 (by decide)]
  have drainOutput : Function.update computed (tape 3) [] = drained := by
    funext k
    by_cases h3 : k = tape 3
    · subst k
      simp [drained, frame, MachineCopy.forkTapes, hd 3 4 (by decide)]
    · by_cases h4 : k = tape 4
      · subst k
        simp [computed, drained, frame, MachineCopy.forkTapes, hd 4 3 (by decide)]
      · simp [computed, drained, frame, MachineCopy.forkTapes, h3, h4]
  have drainRun : (advance (TM2.step program))^[q + 2]
      (some ⟨some (labels .drainQuotient), clean d positive ambient, computed⟩) =
      some ⟨some (labels .finish), clean d positive ambient, drained⟩ := by
    have h := MachineDrain.drainTrace (tape 3) (labels .drainQuotient)
      (some (labels .finish)) program (atLabels .drainQuotient)
      computed (computed (tape 3)) (ambient, MachineFixedDivMod.residue d positive 0) none
    rw [Function.update_eq_self, drainOutput, quotientWord, encodeWord_length] at h
    exact h
  have finishOutput : Function.update drained (tape 2) [] =
      Function.update base (tape 4) (encodeWord (value d c b j) ++ base (tape 4)) := by
    have hv : c * q + (r.val + b) = value d c b j := by
      simp [value, q, r, MachineFixedDivMod.residue, Nat.add_assoc]
    funext k
    by_cases h2 : k = tape 2
    · subst k
      simp [hd 2 4 (by decide), workEmpty]
    · by_cases h3 : k = tape 3
      · subst k
        simp [drained, frame, MachineCopy.forkTapes, hd 3 2 (by decide),
          hd 3 4 (by decide), quotientEmpty]
      · by_cases h4 : k = tape 4
        · subst k
          simp [drained, frame, MachineCopy.forkTapes, hd 4 2 (by decide), hv]
        · simp [drained, frame, MachineCopy.forkTapes, h2, h3, h4]
  have finishRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .finish), clean d positive ambient, drained⟩) =
      some ⟨exit, clean d positive ambient,
        Function.update base (tape 4) (encodeWord (value d c b j) ++ base (tape 4))⟩ := by
    have hw : drained (tape 2) = encodeWord 0 := by
      simp [drained, frame, MachineCopy.forkTapes, hd 2 3 (by decide), hd 2 4 (by decide)]
    change some (TM2.stepAux (program (labels .finish)) _ _) = _
    rw [atLabels]
    cases exit <;> simp [instruction, TM2.stepAux, exitAt, hw, encodeWord, finishOutput, clean]
  have total := joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
    (joinTrace copyRun initRun) divideRun) emitRun) affineRun) drainRun) finishRun
  have hsteps : steps d j =
      (((((2 * (j + 1) + 1) + 1) + (j + 1)) + 1) + 2 * (q + 1)) + (q + 2) + 1 := by
    dsimp [steps, q]
    omega
  rw [hsteps]
  exact total

end UniqueGamesTheorem.Foundations.Complexity.MachinePortReindex

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineLazyRows
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLazyRows

open Turing MachineComposition PCP.GraphTables
open PCP.PreprocessingLazyWords (reverseMap moveRow moveRow_words)

variable {K Λ A : Type} [DecidableEq K]

/-- The program depends on the fixed degree and tape placement, never on
input-dependent vertices, reverse indices, or predicate values. -/
def reindexInstruction (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 9 → K)
    (labels : Label d → Λ) (exit : Option Λ) :
    Label d → TM2.Stmt (fun _ : K => Bool) Λ (State A d)
  | .inl stage => MachinePortReindex.instruction d positive c b
      (tape ∘ addressIndex) (fun stage => labels (.inl stage))
      (some (labels (.inr .relationRead))) stage
  | .inr stage => MachineTableRows.routine (fields tape) (tape 8) (tape 7) (tape 3)
      (fun stage => labels (.inr stage)) exit stage

theorem reindexRowTrace (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 9 → K)
    (distinct : Function.Injective tape) (labels : Label d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A d))
    (atLabels : ∀ l, program (labels l) = reindexInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (v j : Nat) (relation : RelationTable)
    (tailWord : base (tape 0) = encodeWord v)
    (reverseWord : base (tape 1) = encodeWord j)
    (relationWord : base (tape 2) = encodeWords (relationWords relation))
    (scratchEmpty : base (tape 3) = []) (workEmpty : base (tape 4) = [])
    (quotientEmpty : base (tape 5) = []) (newReverseEmpty : base (tape 6) = [])
    (rowEmpty : base (tape 8) = []) (ambient : A) :
    (advance (TM2.step program))^[reindexSteps d c b v j relation (base (tape 7))]
      (some ⟨some (labels (.inl .copySeed)), MachinePortReindex.clean d positive ambient, base⟩) =
      some ⟨exit, MachinePortReindex.clean d positive ambient,
        reindexResultTapes d c b v j relation tape base⟩ := by
  have hd (i k : Fin 9) (h : i ≠ k) : tape i ≠ tape k := fun e => h (distinct e)
  have ha0 : addressIndex 0 = 1 := rfl
  have ha4 : addressIndex 4 = 6 := rfl
  have mapRun := MachinePortReindex.reindexTrace d positive c b
    (tape ∘ addressIndex) (distinct.comp addressIndex_injective)
    (fun stage => labels (.inl stage)) (some (labels (.inr .relationRead)))
    program (fun stage => atLabels (.inl stage)) base j []
    (by simpa only [Function.comp_apply, ha0, List.append_nil] using reverseWord)
    scratchEmpty workEmpty quotientEmpty ambient
  simp only [Function.comp_apply, ha4, newReverseEmpty,
    List.append_nil] at mapRun
  change (advance (TM2.step program))^[MachinePortReindex.steps d j]
    (some ⟨some (labels (.inl .copySeed)), MachinePortReindex.clean d positive ambient, base⟩) =
    some ⟨some (labels (.inr .relationRead)), MachinePortReindex.clean d positive ambient,
      reindexMappedTapes d c b j tape base⟩ at mapRun
  have hfields (i : Fin 3) : fields tape i ≠ tape 8 ∧ fields tape i ≠ tape 3 := by
    fin_cases i
    · exact ⟨hd 0 8 (by decide), hd 0 3 (by decide)⟩
    · exact ⟨hd 6 8 (by decide), hd 6 3 (by decide)⟩
    · exact ⟨hd 2 8 (by decide), hd 2 3 (by decide)⟩
  have hbits : MachineTableRows.fieldBits (fields tape) (reindexMappedTapes d c b j tape base) =
      reindexRowBits d c b v j relation := by
    simp [MachineTableRows.fieldBits, fields, reindexMappedTapes, hd 0 6 (by decide),
      hd 2 6 (by decide), tailWord, relationWord, reindexRowBits]
  have hsize : MachineTableRows.fieldSize (fields tape) (reindexMappedTapes d c b j tape base) =
      (reindexRowBits d c b v j relation).length := by
    rw [← MachineTableRows.fieldBits_length, hbits]
  have hout : reindexMappedTapes d c b j tape base (tape 7) = base (tape 7) := by
    simp [reindexMappedTapes, hd 7 6 (by decide)]
  have appendRun := MachineTableRows.appendTrace (fields tape) (tape 8) (tape 7) (tape 3)
    hfields (hd 8 7 (by decide)) (hd 8 3 (by decide)) (hd 7 3 (by decide))
    (fun stage => labels (.inr stage)) exit program
    (fun stage => atLabels (.inr stage)) (reindexMappedTapes d c b j tape base)
    (by simp [reindexMappedTapes, hd 8 6 (by decide), rowEmpty])
    (by simp [reindexMappedTapes, hd 3 6 (by decide), scratchEmpty])
    (ambient, MachineFixedDivMod.residue d positive 0) none
  rw [hsize, hout, hbits] at appendRun
  change (advance (TM2.step program))^[4 * (reindexRowBits d c b v j relation).length +
      2 * (base (tape 7)).length + 9]
    (some ⟨some (labels (.inr .relationRead)), MachinePortReindex.clean d positive ambient,
      reindexMappedTapes d c b j tape base⟩) =
    some ⟨exit, MachinePortReindex.clean d positive ambient,
      reindexResultTapes d c b v j relation tape base⟩ at appendRun
  rw [show reindexSteps d c b v j relation (base (tape 7)) =
      (4 * (reindexRowBits d c b v j relation).length + 2 * (base (tape 7)).length + 9) +
        MachinePortReindex.steps d j by unfold reindexSteps; omega,
    Function.iterate_add_apply, mapRun, appendRun]

def streamInstruction (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 10 → K)
    (labels : StreamLabel d → Λ) (exit : Option Λ) :
    StreamLabel d → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d)
  | .tailStart => Hastad.SourceMachine.fieldStart (tape 0) (labels .tailRead)
  | .tailRead => Hastad.SourceMachine.fieldLoop (tape 9) (tape 0) (labels .tailRead)
      (some (labels .reverseStart))
  | .reverseStart => Hastad.SourceMachine.fieldStart (tape 1) (labels .reverseRead)
  | .reverseRead => Hastad.SourceMachine.fieldLoop (tape 9) (tape 1) (labels .reverseRead)
      (some (labels .copyRelation))
  | .copyRelation => streamRelationCopy d (tape 9) (tape 2)
      (some (labels (.row (.inl .copySeed))))
  | .row stage => reindexInstruction d positive c b (tape ∘ bodyIndex)
      (fun stage => labels (.row stage)) (some (labels .clearTail)) stage
  | .clearTail => MachineDrain.drain (tape 0) (labels .clearTail) (some (labels .clearOld))
  | .clearOld => MachineDrain.drain (tape 1) (labels .clearOld) (some (labels .clearRelation))
  | .clearRelation => MachineDrain.drain (tape 2) (labels .clearRelation) (some (labels .clearNew))
  | .clearNew => MachineDrain.drain (tape 6) (labels .clearNew) exit

theorem streamRowTrace (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (labels : StreamLabel d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (atLabels : ∀ l, program (labels l) = streamInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (v j : Nat) (relation : RelationTable) (suffix : List Bool)
    (input : base (tape 9) = inputRowBits v j relation ++ suffix)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (tape i) = []) (ambient : A) :
    (advance (TM2.step program))^[streamRowSteps d c b v j relation (base (tape 7))]
      (some ⟨some (labels .tailStart), streamClean d positive ambient, base⟩) =
      some ⟨exit, streamClean d positive ambient,
        streamResultTapes d c b v j relation tape base suffix⟩ := by
  have hd (i k : Fin 10) (h : i ≠ k) : tape i ≠ tape k := fun x => h (distinct x)
  have hb6 : bodyIndex 6 = 6 := rfl
  have hb7 : bodyIndex 7 = 7 := rfl
  have h₀ := empty 0 (by decide) (by decide)
  have h₁ := empty 1 (by decide) (by decide)
  have h₂ := empty 2 (by decide) (by decide)
  have h₃ := empty 3 (by decide) (by decide)
  have h₄ := empty 4 (by decide) (by decide)
  have h₅ := empty 5 (by decide) (by decide)
  have h₆ := empty 6 (by decide) (by decide)
  have h₈ := empty 8 (by decide) (by decide)
  let relationBits := encodeWords (relationWords relation)
  let tailLoaded := Function.update (Function.update base (tape 9)
    (encodeWord j ++ (relationBits ++ suffix))) (tape 0) (encodeWord v)
  let reverseLoaded := Function.update (Function.update tailLoaded (tape 9)
    (relationBits ++ suffix)) (tape 1) (encodeWord j)
  let loaded := Function.update (Function.update reverseLoaded (tape 9) suffix) (tape 2) relationBits
  let rowed := reindexResultTapes d c b v j relation (tape ∘ bodyIndex) loaded
  let tailCleared := Function.update rowed (tape 0) []
  let oldCleared := Function.update tailCleared (tape 1) []
  let relationCleared := Function.update oldCleared (tape 2) []
  have tailRun : (advance (TM2.step program))^[v + 2]
      (some ⟨some (labels .tailStart), streamClean d positive ambient, base⟩) =
      some ⟨some (labels .reverseStart), streamClean d positive ambient, tailLoaded⟩ := by
    have h := (Hastad.SourceMachine.fieldInTime (tape 9) (tape 0) (hd 9 0 (by decide))
      (labels .tailStart) (labels .tailRead) (some (labels .reverseStart)) program
      (atLabels .tailStart) (atLabels .tailRead) base v
      (encodeWord j ++ (relationBits ++ suffix))
      (by simpa only [inputRowBits, List.append_assoc] using input)
      ((ambient, MachineRegularOriginalRow.zeroBuffer),
        MachineFixedDivMod.residue d positive 0) none).evals_in_steps
    simp only [Hastad.SourceMachine.fieldInTime, Hastad.SourceMachine.fieldTapes,
      h₀, List.append_nil] at h
    convert h using 1 <;> rfl
  have reverseRun : (advance (TM2.step program))^[j + 2]
      (some ⟨some (labels .reverseStart), streamClean d positive ambient, tailLoaded⟩) =
      some ⟨some (labels .copyRelation), streamClean d positive ambient, reverseLoaded⟩ := by
    have hstart : tailLoaded (tape 1) = [] := by
      simp [tailLoaded, hd 1 0 (by decide), hd 1 9 (by decide), h₁]
    have h := (Hastad.SourceMachine.fieldInTime (tape 9) (tape 1) (hd 9 1 (by decide))
      (labels .reverseStart) (labels .reverseRead) (some (labels .copyRelation)) program
      (atLabels .reverseStart) (atLabels .reverseRead) tailLoaded j (relationBits ++ suffix)
      (by simp [tailLoaded, hd 9 0 (by decide)])
      ((ambient, MachineRegularOriginalRow.zeroBuffer),
        MachineFixedDivMod.residue d positive 0) none).evals_in_steps
    simp only [Hastad.SourceMachine.fieldInTime, Hastad.SourceMachine.fieldTapes,
      hstart, List.append_nil] at h
    convert h using 1 <;> rfl
  have copyRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .copyRelation), streamClean d positive ambient, reverseLoaded⟩) =
      some ⟨some (labels (.row (.inl .copySeed))), streamClean d positive ambient, loaded⟩ := by
    have hempty : reverseLoaded (tape 2) = [] := by
      simp [reverseLoaded, tailLoaded, hd 2 1 (by decide), hd 2 9 (by decide),
        hd 2 0 (by decide), h₂]
    have h := streamRelationCopy_step d positive (tape 9) (tape 2) (hd 9 2 (by decide))
      (labels .copyRelation) (some (labels (.row (.inl .copySeed)))) program
      (atLabels .copyRelation) relation suffix reverseLoaded
      (by simp [reverseLoaded, relationBits, hd 9 1 (by decide)]) ambient
    simpa only [Function.iterate_one, advance_some, hempty, List.append_nil, loaded] using h
  have hs (i : Fin 10) (hi : i ≠ 0) (hi' : i ≠ 1) (hi'' : i ≠ 2) (hi''' : i ≠ 9) :
      loaded (tape i) = base (tape i) := by
    simp [loaded, reverseLoaded, tailLoaded, hd i 0 hi, hd i 1 hi',
      hd i 2 hi'', hd i 9 hi''']
  have loadedTail : loaded (tape 0) = encodeWord v := by
    simp [loaded, reverseLoaded, tailLoaded, hd 0 2 (by decide), hd 0 9 (by decide),
      hd 0 1 (by decide)]
  have loadedReverse : loaded (tape 1) = encodeWord j := by
    simp [loaded, reverseLoaded, hd 1 2 (by decide), hd 1 9 (by decide)]
  have loadedRelation : loaded (tape 2) = relationBits := by simp [loaded]
  have bodyRun := reindexRowTrace d positive c b (tape ∘ bodyIndex)
    (distinct.comp bodyIndex_injective) (fun stage => labels (.row stage))
    (some (labels .clearTail)) program (fun stage => atLabels (.row stage)) loaded v j relation
    loadedTail loadedReverse loadedRelation
    ((hs 3 (by decide) (by decide) (by decide) (by decide)).trans h₃)
    ((hs 4 (by decide) (by decide) (by decide) (by decide)).trans h₄)
    ((hs 5 (by decide) (by decide) (by decide) (by decide)).trans h₅)
    ((hs 6 (by decide) (by decide) (by decide) (by decide)).trans h₆)
    ((hs 8 (by decide) (by decide) (by decide) (by decide)).trans h₈)
    (ambient, MachineRegularOriginalRow.zeroBuffer)
  have hout : loaded ((tape ∘ bodyIndex) 7) = base (tape 7) :=
    hs 7 (by decide) (by decide) (by decide) (by decide)
  rw [hout] at bodyRun
  change (advance (TM2.step program))^[reindexSteps d c b v j relation (base (tape 7))]
    (some ⟨some (labels (.row (.inl .copySeed))), streamClean d positive ambient, loaded⟩) =
    some ⟨some (labels .clearTail), streamClean d positive ambient, rowed⟩ at bodyRun
  have rowedTail : rowed (tape 0) = encodeWord v := by
    simp only [rowed, reindexResultTapes, reindexMappedTapes, Function.comp_apply, hb6, hb7]
    simpa only [Function.update_of_ne (hd 0 7 (by decide)),
      Function.update_of_ne (hd 0 6 (by decide))] using loadedTail
  have rowedOld : tailCleared (tape 1) = encodeWord j := by
    simp only [tailCleared, rowed, reindexResultTapes, reindexMappedTapes,
      Function.comp_apply, hb6, hb7]
    simpa only [Function.update_of_ne (hd 1 0 (by decide)),
      Function.update_of_ne (hd 1 7 (by decide)), Function.update_of_ne (hd 1 6 (by decide))]
      using loadedReverse
  have rowedRelation : oldCleared (tape 2) = relationBits := by
    simp only [oldCleared, tailCleared, rowed, reindexResultTapes, reindexMappedTapes,
      Function.comp_apply, hb6, hb7]
    simpa only [Function.update_of_ne (hd 2 1 (by decide)),
      Function.update_of_ne (hd 2 0 (by decide)), Function.update_of_ne (hd 2 7 (by decide)),
      Function.update_of_ne (hd 2 6 (by decide))] using loadedRelation
  have rowedNew : relationCleared (tape 6) = encodeWord (MachinePortReindex.value d c b j) := by
    simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
      reindexMappedTapes, Function.comp_apply, bodyIndex, hd 6 2 (by decide),
      hd 6 1 (by decide), hd 6 0 (by decide), hd 6 7 (by decide)]
  have clearTail := (MachineDrain.drainInTime (tape 0) (labels .clearTail)
    (some (labels .clearOld)) program (atLabels .clearTail) rowed
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(rowed (tape 0)).length + 1]
    (some ⟨some (labels .clearTail), streamClean d positive ambient, rowed⟩) =
    some ⟨some (labels .clearOld), streamClean d positive ambient, tailCleared⟩ at clearTail
  rw [rowedTail, encodeWord_length] at clearTail
  have clearOld := (MachineDrain.drainInTime (tape 1) (labels .clearOld)
    (some (labels .clearRelation)) program (atLabels .clearOld) tailCleared
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(tailCleared (tape 1)).length + 1]
    (some ⟨some (labels .clearOld), streamClean d positive ambient, tailCleared⟩) =
    some ⟨some (labels .clearRelation), streamClean d positive ambient, oldCleared⟩ at clearOld
  rw [rowedOld, encodeWord_length] at clearOld
  have clearRelation := (MachineDrain.drainInTime (tape 2) (labels .clearRelation)
    (some (labels .clearNew)) program (atLabels .clearRelation) oldCleared
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(oldCleared (tape 2)).length + 1]
    (some ⟨some (labels .clearRelation), streamClean d positive ambient, oldCleared⟩) =
    some ⟨some (labels .clearNew), streamClean d positive ambient, relationCleared⟩ at clearRelation
  rw [rowedRelation] at clearRelation
  have clearNew := (MachineDrain.drainInTime (tape 6) (labels .clearNew)
    exit program (atLabels .clearNew) relationCleared
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(relationCleared (tape 6)).length + 1]
    (some ⟨some (labels .clearNew), streamClean d positive ambient, relationCleared⟩) =
    some ⟨exit, streamClean d positive ambient,
      Function.update relationCleared (tape 6) []⟩ at clearNew
  rw [rowedNew, encodeWord_length] at clearNew
  have finalFrame : Function.update relationCleared (tape 6) [] =
      streamResultTapes d c b v j relation tape base suffix := by
    funext k
    by_cases h6 : k = tape 6
    · subst k
      simp [streamResultTapes, hd 6 7 (by decide), hd 6 9 (by decide), h₆]
    · by_cases h2 : k = tape 2
      · subst k
        simp [relationCleared, streamResultTapes, hd 2 6 (by decide),
          hd 2 7 (by decide), hd 2 9 (by decide), h₂]
      · by_cases h1 : k = tape 1
        · subst k
          simp [relationCleared, oldCleared, streamResultTapes,
            hd 1 6 (by decide), hd 1 2 (by decide), hd 1 7 (by decide),
            hd 1 9 (by decide), h₁]
        · by_cases h0 : k = tape 0
          · subst k
            simp [relationCleared, oldCleared, tailCleared, streamResultTapes,
              hd 0 6 (by decide), hd 0 2 (by decide), hd 0 1 (by decide),
              hd 0 7 (by decide), hd 0 9 (by decide), h₀]
          · by_cases h7 : k = tape 7
            · subst k
              simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
                reindexMappedTapes, Function.comp_apply, bodyIndex, streamResultTapes,
                loaded, reverseLoaded, tailLoaded, hd 7 6 (by decide), hd 7 2 (by decide),
                hd 7 1 (by decide), hd 7 0 (by decide), hd 7 9 (by decide)]
            · by_cases h9 : k = tape 9
              · subst k
                simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
                  reindexMappedTapes, Function.comp_apply, bodyIndex, loaded, reverseLoaded,
                  tailLoaded, streamResultTapes, hd 9 6 (by decide), hd 9 2 (by decide),
                  hd 9 1 (by decide), hd 9 0 (by decide), hd 9 7 (by decide)]
              · simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
                  reindexMappedTapes, Function.comp_apply, bodyIndex, loaded, reverseLoaded,
                  tailLoaded, streamResultTapes, h6, h2, h1, h0, h7, h9]
  rw [finalFrame] at clearNew
  exact joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
    (joinTrace tailRun reverseRun) copyRun) bodyRun) clearTail) clearOld) clearRelation) clearNew

def vertexInstruction (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 10 → K)
    (labels : VertexLabel d → Λ) (exit : Option Λ) :
    VertexLabel d → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d)
  | (i, none) => if i.val < d then .goto fun _ => labels (i, some .tailStart)
      else MachinePortReindex.exitAt exit
  | (i, some stage) => if h : i.val < d then
      streamInstruction d positive c b tape (fun stage => labels (i, some stage))
        (some (labels (⟨i.val + 1, by omega⟩, none))) stage
      else MachinePortReindex.exitAt exit

theorem recordsInput_eq_codec {n m : Nat} (rows : List (DartRow n m)) :
    recordsInput rows = encodeWords (rows.flatMap rowWords) := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
      simp only [recordsInput, List.flatMap_cons, encodeWords_append,
        MachineTableRows.rowBits_eq, inputRowBits] at ih ⊢
      rw [ih]

/-- Every port executes its actual loader, mapper, emitter, and cleanup.
The trace is proved from the concrete program, with no per-row run premise. -/
theorem vertexSuffixTrace {n m : Nat} (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 10 → K) (distinct : Function.Injective tape)
    (labels : VertexLabel d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (rows : Fin d → DartRow n m)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (tape i) = []) (ambient : A)
    (remaining : Nat) (i : Fin (d + 1)) (count : i.val + remaining = d) (output : List Bool) :
    (advance (TM2.step program))^[vertexSteps d c b ((List.ofFn rows).drop i.val) output]
      (some ⟨some (labels (i, none)), streamClean d positive ambient,
        streamFrame tape base ((List.ofFn rows).drop i.val) output⟩) =
      some ⟨exit, streamClean d positive ambient,
        streamFrame (n := n) (m := m) tape base []
          (output ++ recordsOutput d c b ((List.ofFn rows).drop i.val))⟩ := by
  have hd (a k : Fin 10) (h : a ≠ k) : tape a ≠ tape k := fun x => h (distinct x)
  induction remaining generalizing i output with
  | zero =>
      have hi : i.val = d := by omega
      have hdrop : (List.ofFn rows).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [List.length_ofFn, hi, le_refl]
      rw [hdrop]
      simp only [vertexSteps, recordsOutput, List.flatMap_nil, List.append_nil]
      change some (TM2.stepAux (program (labels (i, none))) _ _) = _
      rw [atLabels]
      cases exit <;> simp [vertexInstruction, hi, MachinePortReindex.exitAt, TM2.stepAux]
  | succ remaining ih =>
      have hi : i.val < d := by omega
      let port : Fin d := ⟨i.val, hi⟩
      let next : Fin (d + 1) := ⟨i.val + 1, by omega⟩
      let rest := (List.ofFn rows).drop (i.val + 1)
      have split : (List.ofFn rows).drop i.val = rows port :: rest := by
        have h := List.getElem_cons_drop (as := List.ofFn rows)
          (i := i.val) (by simpa only [List.length_ofFn] using hi)
        simpa only [List.getElem_ofFn, port, rest] using h.symm
      let initial := streamFrame tape base (rows port :: rest) output
      have boundary : (advance (TM2.step program))^[1]
          (some ⟨some (labels (i, none)), streamClean d positive ambient, initial⟩) =
          some ⟨some (labels (i, some .tailStart)), streamClean d positive ambient, initial⟩ := by
        change some (TM2.stepAux (program (labels (i, none))) _ _) = _
        rw [atLabels]
        simp [vertexInstruction, hi, TM2.stepAux]
      have body := streamRowTrace d positive c b tape distinct
        (fun stage => labels (i, some stage)) (some (labels (next, none))) program
        (by
          intro stage
          simpa only [vertexInstruction, hi, dite_true, next] using (atLabels (i, some stage)))
        initial (rows port).tail.val (rows port).reverseIndex.val (rows port).relation
        (recordsInput rest ++ base (tape 9))
        (by simp [initial, streamFrame, hd 9 7 (by decide), recordsInput, List.append_assoc])
        (by
          intro k hk7 hk9
          simp [initial, streamFrame, hd k 7 hk7, hd k 9 hk9, empty k hk7 hk9]) ambient
      have initialOutput : initial (tape 7) = output := by simp [initial, streamFrame]
      rw [initialOutput] at body
      change (advance (TM2.step program))^[streamRowSteps d c b
        (rows port).tail.val (rows port).reverseIndex.val (rows port).relation output]
        (some ⟨some (labels (i, some .tailStart)), streamClean d positive ambient, initial⟩) =
        some ⟨some (labels (next, none)), streamClean d positive ambient,
          streamResultTapes d c b (rows port).tail.val (rows port).reverseIndex.val
            (rows port).relation tape initial (recordsInput rest ++ base (tape 9))⟩ at body
      rw [show streamResultTapes d c b (rows port).tail.val (rows port).reverseIndex.val
        (rows port).relation tape initial (recordsInput rest ++ base (tape 9)) =
        streamFrame tape base rest
          (output ++ reindexRowBits d c b (rows port).tail.val
            (rows port).reverseIndex.val (rows port).relation) from
          streamFrame_afterRow d c b (rows port) tape distinct base rest output] at body
      have nextCount : next.val + remaining = d := by dsimp [next]; omega
      have tail := ih next nextCount
        (output ++ reindexRowBits d c b (rows port).tail.val
          (rows port).reverseIndex.val (rows port).relation)
      change (advance (TM2.step program))^[vertexSteps d c b rest
        (output ++ reindexRowBits d c b (rows port).tail.val
          (rows port).reverseIndex.val (rows port).relation)]
        (some ⟨some (labels (next, none)), streamClean d positive ambient,
          streamFrame tape base rest (output ++ reindexRowBits d c b (rows port).tail.val
            (rows port).reverseIndex.val (rows port).relation)⟩) =
        some ⟨exit, streamClean d positive ambient,
          streamFrame (n := n) (m := m) tape base [] ((output ++ reindexRowBits d c b (rows port).tail.val
            (rows port).reverseIndex.val (rows port).relation) ++ recordsOutput d c b rest)⟩ at tail
      rw [split]
      have all := joinTrace (joinTrace boundary body) tail
      simpa only [vertexSteps, initial, recordsOutput, List.flatMap_cons, List.append_assoc] using all

theorem vertexTrace {n m : Nat} (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 10 → K) (distinct : Function.Injective tape)
    (labels : VertexLabel d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (rows : Fin d → DartRow n m)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (tape i) = [])
    (ambient : A) (output : List Bool) :
    (advance (TM2.step program))^[vertexSteps d c b (List.ofFn rows) output]
      (some ⟨some (labels (0, none)), streamClean d positive ambient,
        streamFrame tape base (List.ofFn rows) output⟩) =
      some ⟨exit, streamClean d positive ambient,
        streamFrame (n := n) (m := m) tape base [] (output ++ recordsOutput d c b (List.ofFn rows))⟩ := by
  simpa only [Fin.val_zero, List.drop_zero] using vertexSuffixTrace d positive c b tape distinct
    labels exit program atLabels base rows empty ambient d 0 (by simp) output

end UniqueGamesTheorem.Foundations.Complexity.MachineLazyRows

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineTableSplit
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A fixed five-tape machine physically copies a graph table, preserves the
original input, and splits its two unary header fields from the copied rows.
The exact trace is ambient-state polymorphic for static machine placement.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit

open Turing MachineComposition

/-- Six finite control labels, independent of all input sizes and contents. -/
def program {σ : Type} : Label → TM2.Stmt (fun _ : Tape => Bool) Label (State σ)
  | .copyFirst => Reduction.MachineTransfer.loopAt 0 2 id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop 2 0 1 false .copySecond (some .startVertices)
  | .startVertices => Hastad.SourceMachine.fieldStart 3 .readVertices
  | .readVertices => Hastad.SourceMachine.fieldLoop 1 3 .readVertices (some .startDarts)
  | .startDarts => Hastad.SourceMachine.fieldStart 4 .readDarts
  | .readDarts => Hastad.SourceMachine.fieldLoop 1 4 .readDarts none

theorem splitTrace {σ : Type} (n m : Nat) (rowsBits : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[exactSteps n m rowsBits]
      (some ⟨some .copyFirst, (ambient, register),
        initialTapes (encodeWords [n, m] ++ rowsBits)⟩) =
      some ⟨none, (ambient, none), resultTapes n m rowsBits⟩ := by
  let word := encodeWords [n, m] ++ rowsBits
  let b₀ := initialTapes word
  let b₁ := tapes word word [] []
  let b₂ := tapes word (encodeWord m ++ rowsBits) (encodeWord n) []
  let b₃ := resultTapes n m rowsBits
  have h₀ : Function.update b₀ (1 : Tape) (b₀ 0 ++ b₀ 1) = b₁ := by
    funext k; fin_cases k <;> simp [b₀, b₁, initialTapes, tapes]
  have h₁ : Hastad.SourceMachine.fieldTapes (1 : Tape) 3 b₁
      (encodeWord m ++ rowsBits) (encodeWord n ++ b₁ 3) = b₂ := by
    funext k; fin_cases k <;> simp [b₁, b₂, tapes, Hastad.SourceMachine.fieldTapes]
  have h₂ : Hastad.SourceMachine.fieldTapes (1 : Tape) 4 b₂
      rowsBits (encodeWord m ++ b₂ 4) = b₃ := by
    funext k; fin_cases k <;>
      simp [b₂, b₃, resultTapes, tapes, word, Hastad.SourceMachine.fieldTapes]
  have copy := MachineCopy.copyTrace (0 : Tape) 1 2
    (by decide) (by decide) (by decide) false .copyFirst .copySecond (some .startVertices)
    (program (σ := σ)) rfl rfl b₀ (by simp [b₀, initialTapes, tapes]) ambient register
  rw [h₀] at copy
  have c₀ : (advance (TM2.step (program (σ := σ))))^[2 * (word.length + 1)]
      (some ⟨some .copyFirst, (ambient, register), b₀⟩) =
        some ⟨some .startVertices, (ambient, none), b₁⟩ := by
    simpa only [show b₀ 0 = word by simp [b₀, initialTapes, tapes]] using copy
  have scan₁ := (Hastad.SourceMachine.fieldInTime (1 : Tape) 3 (by decide)
    .startVertices .readVertices (some .startDarts) (program (σ := σ)) rfl rfl
    b₁ n (encodeWord m ++ rowsBits)
    (by simp [b₁, tapes, word, encodeWords, List.append_assoc]) ambient none).evals_in_steps
  have c₁ : (advance (TM2.step (program (σ := σ))))^[n + 2]
      (some ⟨some .startVertices, (ambient, none), b₁⟩) =
        some ⟨some .startDarts, (ambient, none), b₂⟩ := by
    dsimp only [Hastad.SourceMachine.fieldInTime] at scan₁
    change (advance (TM2.step (program (σ := σ))))^[n + 2]
      (some ⟨some .startVertices, (ambient, none), b₁⟩) =
      some ⟨some .startDarts, (ambient, none),
        Hastad.SourceMachine.fieldTapes (1 : Tape) 3 b₁ (encodeWord m ++ rowsBits)
          (encodeWord n ++ b₁ 3)⟩ at scan₁
    simpa only [h₁] using scan₁
  have scan₂ := (Hastad.SourceMachine.fieldInTime (1 : Tape) 4 (by decide)
    .startDarts .readDarts none (program (σ := σ)) rfl rfl
    b₂ m rowsBits (by simp [b₂, tapes]) ambient none).evals_in_steps
  have c₂ : (advance (TM2.step (program (σ := σ))))^[m + 2]
      (some ⟨some .startDarts, (ambient, none), b₂⟩) =
        some ⟨none, (ambient, none), b₃⟩ := by
    dsimp only [Hastad.SourceMachine.fieldInTime] at scan₂
    change (advance (TM2.step (program (σ := σ))))^[m + 2]
      (some ⟨some .startDarts, (ambient, none), b₂⟩) =
      some ⟨none, (ambient, none),
        Hastad.SourceMachine.fieldTapes (1 : Tape) 4 b₂ rowsBits
          (encodeWord m ++ b₂ 4)⟩ at scan₂
    simpa only [h₂] using scan₂
  have c₀₁ : (advance (TM2.step (program (σ := σ))))^[(n + 2) + 2 * (word.length + 1)]
      (some ⟨some .copyFirst, (ambient, register), b₀⟩) =
        some ⟨some .startDarts, (ambient, none), b₂⟩ := by
    rw [Function.iterate_add_apply, c₀, c₁]
  have c₀₁₂ : (advance (TM2.step (program (σ := σ))))^[(m + 2) +
      ((n + 2) + 2 * (word.length + 1))]
      (some ⟨some .copyFirst, (ambient, register), b₀⟩) =
        some ⟨none, (ambient, none), b₃⟩ := by
    rw [Function.iterate_add_apply, c₀₁, c₂]
  have count : exactSteps n m rowsBits = (m + 2) + ((n + 2) + 2 * (word.length + 1)) := by
    dsimp [exactSteps, word]
    omega
  rw [count]
  exact c₀₁₂

theorem tableTrace {σ : Type} (table : PCP.GraphTables.Table) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[exactSteps table.vertices table.darts (rowsBits table)]
      (some ⟨some .copyFirst, (ambient, register), initialTapes (PCP.GraphTables.tableBits table)⟩) =
      some ⟨none, (ambient, none), resultTapes table.vertices table.darts (rowsBits table)⟩ := by
  rw [tableBits_header_rows]
  exact splitTrace table.vertices table.darts (rowsBits table) ambient register

end UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineLazyTable
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual whole-table lazy-graph machine, with fixed positive old degree.
All unbounded counts and addresses reside on unary tapes. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLazyTable

open Turing MachineComposition PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

def program (d : Nat) (positive : 0 < d) :
    Label d → TM2.Stmt (fun _ : Tape => Bool) (Label d) (State d)
  | .split label => MachineCloudPadding.Placement.statement splitRoles Label.split
      (some .dartSeed) (MachineTableSplit.program label)
  | .dartSeed => MachineUnaryAffineAt.seed .output 0 .dartScan
  | .dartScan => MachineUnaryAffineAt.scan .darts .scratch .output 2 .dartScan .dartRestore
  | .dartRestore => Reduction.MachineTransfer.loopAt .scratch .darts id false
      .dartRestore (some .vertexSeed)
  | .vertexSeed => MachineUnaryAffineAt.seed .output 0 .vertexScan
  | .vertexScan => MachineUnaryAffineAt.scan .vertices .scratch .output 1 .vertexScan .vertexRestore
  | .vertexRestore => Reduction.MachineTransfer.loopAt .scratch .vertices id false
      .vertexRestore (some .fuelFirst)
  | .fuelFirst => Reduction.MachineTransfer.loopAt .vertices .scratch id false
      .fuelFirst (some .fuelSecond)
  | .fuelSecond => MachineCopy.forkLoop .scratch .vertices .fuel false
      .fuelSecond (some .seedCounters)
  | .seedCounters => .push .vertex (fun _ => false)
      (.push .reverse (fun _ => false) (.goto fun _ => .guard))
  | .guard => MachineUnaryCounter.guard .fuel .copyVertexFirst .clearVertices
  | .copyVertexFirst => Reduction.MachineTransfer.loopAt .vertex .scratch id false
      .copyVertexFirst (some .copyVertexSecond)
  | .copyVertexSecond => MachineCopy.forkLoop .scratch .vertex .tail false
      .copyVertexSecond (some (.dummy (MachineDummyRows.start d)))
  | .dummy label => MachineCloudPadding.Placement.statement dummyRoles Label.dummy
      (some .clearDummyTail) (MachineDummyRows.program d label)
  | .clearDummyTail => MachineDrain.drain .tail .clearDummyTail (some .clearDummyRelation)
  | .clearDummyRelation => MachineDrain.drain .relation .clearDummyRelation (some (.oldRows (0, none)))
  | .oldRows label => MachineLazyRows.vertexInstruction d positive (2 * d) d oldRoles
      Label.oldRows (some .nextVertex) label
  | .nextVertex => pushWord .reverse (List.replicate d true)
      (.push .vertex (fun _ => true) (.goto fun _ => .guard))
  | .clearVertices => MachineDrain.drain .vertices .clearVertices (some .clearDarts)
  | .clearDarts => MachineDrain.drain .darts .clearDarts (some .clearFuel)
  | .clearFuel => MachineDrain.drain .fuel .clearFuel (some .clearVertex)
  | .clearVertex => MachineDrain.drain .vertex .clearVertex (some .clearReverse)
  | .clearReverse => MachineDrain.drain .reverse .clearReverse none

/-- Lift the actual dummy-block routine into the full program and account for
the exact preserved frame. The tail and relation are cleared in the next phase. -/
theorem dummyTrace (d : Nat) (positive : 0 < d) (base : Tape → List Bool) (v e : Nat)
    (ht : base .tail = encodeWord v) (he : base .reverse = encodeWord e)
    (hr : base .relation = []) (hb : base .rowBuffer = []) (hs : base .scratch = []) :
    (advance (TM2.step (program d positive)))^[MachineDummyRows.steps v e (base .output) d + 1]
      (some ⟨some (.dummy (MachineDummyRows.start d)), clean d positive, base⟩) =
      some ⟨some .clearDummyTail, clean d positive,
        Function.update (Function.update (Function.update base .reverse (encodeWord (e + d)))
          .relation MachineDummyRows.trueBits)
          .output (base .output ++ MachineDummyRows.rowsBits v e d)⟩ := by
  have initial : MachineCloudPadding.Placement.tapes dummyView
      (MachineDummyRows.initialTapes v e (base .output)) base = base := by
    funext t
    cases t <;> simp [MachineCloudPadding.Placement.tapes, dummyView,
      MachineDummyRows.initialTapes, MachineDummyRows.fieldTapes, ht, he, hr, hb, hs]
  have final : MachineCloudPadding.Placement.tapes dummyView
      (MachineDummyRows.fieldTapes v (e + d) (base .output ++ MachineDummyRows.rowsBits v e d))
      base = Function.update (Function.update (Function.update base .reverse (encodeWord (e + d)))
        .relation MachineDummyRows.trueBits)
        .output (base .output ++ MachineDummyRows.rowsBits v e d) := by
    funext t
    cases t <;> simp [MachineCloudPadding.Placement.tapes, dummyView,
      MachineDummyRows.fieldTapes, ht, hb, hs]
  have run := MachineCloudPadding.Placement.trace dummyRoles dummyView
    dummyRoles_left dummyRoles_right Label.dummy (some .clearDummyTail) base
    (MachineDummyRows.program d) (program d positive) (fun _ => rfl) _ _ _
    (MachineDummyRows.allTrace d v e (base .output) (clean d positive).1 none)
  simpa only [clean_pair, MachineCloudPadding.Placement.configuration,
    MachineCloudPadding.Placement.label, initial, final] using run

theorem oldTrace {n m : Nat} (d : Nat) (positive : 0 < d)
    (base : Tape → List Bool) (rows : Fin d → GraphTables.DartRow n m) (rest : List Bool)
    (hi : base .source = MachineLazyRows.recordsInput (List.ofFn rows) ++ rest)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (oldRoles i) = []) :
    (advance (TM2.step (program d positive)))^[MachineLazyRows.vertexSteps d (2 * d) d
      (List.ofFn rows) (base .output)]
      (some ⟨some (.oldRows (0, none)), clean d positive, base⟩) =
      some ⟨some .nextVertex, clean d positive,
        Function.update (Function.update base .source rest) .output
          (base .output ++ MachineLazyRows.recordsOutput d (2 * d) d (List.ofFn rows))⟩ := by
  let tailBase := Function.update base Tape.source rest
  have cleanBase : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → tailBase (oldRoles i) = [] := by
    intro i h7 h9
    have hn : oldRoles i ≠ Tape.source := by
      intro h
      have h' : oldRoles i = oldRoles 9 := h
      exact h9 (oldRoles_injective h')
    simpa only [tailBase, Function.update_of_ne hn] using empty i h7 h9
  have initial : MachineLazyRows.streamFrame oldRoles tailBase (List.ofFn rows) (base .output) = base := by
    funext t
    cases t <;> simp [MachineLazyRows.streamFrame, tailBase, oldRoles, hi]
  have final : MachineLazyRows.streamFrame (n := n) (m := m) oldRoles tailBase []
      (base .output ++ MachineLazyRows.recordsOutput d (2 * d) d (List.ofFn rows)) =
      Function.update (Function.update base .source rest) .output
        (base .output ++ MachineLazyRows.recordsOutput d (2 * d) d (List.ofFn rows)) := by
    funext t
    cases t <;> simp [MachineLazyRows.streamFrame, MachineLazyRows.recordsInput, tailBase, oldRoles]
  have run := MachineLazyRows.vertexTrace d positive (2 * d) d oldRoles oldRoles_injective
    Label.oldRows (some .nextVertex) (program d positive) (fun _ => rfl)
    tailBase rows cleanBase () (base .output)
  simpa only [initial, final, clean] using run

theorem prefixTrace (d : Nat) (positive : 0 < d) (n m : Nat) (rows : List Bool) :
    (advance (TM2.step (program d positive)))^[prefixSteps n m rows]
      (some ⟨some (.split .copyFirst), clean d positive,
        initialTapes (encodeWords [n, m] ++ rows)⟩) =
      some ⟨some .guard, clean d positive,
        loopTapes d (encodeWords [n, m] ++ rows) n m n 0 rows (encodeWords [n, 2 * m])⟩ := by
  let word := encodeWords [n, m] ++ rows
  let header := encodeWords [n, 2 * m]
  let b₁ := frame word rows [] (encodeWord n) (encodeWord m) [] [] []
  let b₂ := frame word rows (encodeWord (2 * m)) (encodeWord n) (encodeWord m) [] [] []
  let b₃ := frame word rows header (encodeWord n) (encodeWord m) [] [] []
  let b₄ := frame word rows header (encodeWord n) (encodeWord m) (encodeWord n) [] []
  have hstart : MachineCloudPadding.Placement.tapes splitView
      (MachineTableSplit.initialTapes word) (fun _ => []) = initialTapes word := by
    funext t
    cases t <;> simp [MachineCloudPadding.Placement.tapes, splitView,
      MachineTableSplit.initialTapes, MachineTableSplit.tapes, initialTapes, frame]
  have hend : MachineCloudPadding.Placement.tapes splitView
      (MachineTableSplit.resultTapes n m rows) (fun _ => []) = b₁ := by
    funext t
    cases t <;> simp [MachineCloudPadding.Placement.tapes, splitView,
      MachineTableSplit.resultTapes, MachineTableSplit.tapes, b₁, frame, word]
  have split := MachineCloudPadding.Placement.trace splitRoles splitView
    splitRoles_left splitRoles_right Label.split (some .dartSeed) (fun _ => [])
    MachineTableSplit.program (program d positive) (fun _ => rfl) _ _ _
    (MachineTableSplit.splitTrace n m rows (clean d positive).1 none)
  have c₀ : (advance (TM2.step (program d positive)))^[MachineTableSplit.exactSteps n m rows]
      (some ⟨some (.split .copyFirst), clean d positive, initialTapes word⟩) =
      some ⟨some .dartSeed, clean d positive, b₁⟩ := by
    simp only [MachineCloudPadding.Placement.configuration,
      MachineCloudPadding.Placement.label] at split
    rw [hstart, hend] at split
    simpa only [clean_pair] using split
  have hdart : Function.update b₁ Tape.output (encodeWord (2 * m + 0) ++ b₁ .output) = b₂ := by
    funext t; cases t <;> simp [b₁, b₂, frame]
  have dart := MachineUnaryAffineAt.seededAffineTrace Tape.darts .scratch .output
    (by decide) (by decide) (by decide) 2 0 .dartSeed .dartScan .dartRestore
    (some .vertexSeed) (program d positive) rfl rfl rfl b₁ m []
    (by simp [b₁, frame]) rfl (clean d positive).1 none
  have c₁ : (advance (TM2.step (program d positive)))^[2 * (m + 1) + 1]
      (some ⟨some .dartSeed, clean d positive, b₁⟩) =
      some ⟨some .vertexSeed, clean d positive, b₂⟩ := by
    simpa only [hdart, clean_pair] using dart
  have hv : Function.update b₂ Tape.output (encodeWord (1 * n + 0) ++ b₂ .output) = b₃ := by
    funext t; cases t <;> simp [b₂, b₃, frame, header, encodeWords]
  have vertex := MachineUnaryAffineAt.seededAffineTrace Tape.vertices .scratch .output
    (by decide) (by decide) (by decide) 1 0 .vertexSeed .vertexScan .vertexRestore
    (some .fuelFirst) (program d positive) rfl rfl rfl b₂ n []
    (by simp [b₂, frame]) rfl (clean d positive).1 none
  have c₂ : (advance (TM2.step (program d positive)))^[2 * (n + 1) + 1]
      (some ⟨some .vertexSeed, clean d positive, b₂⟩) =
      some ⟨some .fuelFirst, clean d positive, b₃⟩ := by
    simpa only [hv, clean_pair] using vertex
  have hf : Function.update b₃ Tape.fuel (b₃ .vertices ++ b₃ .fuel) = b₄ := by
    funext t; cases t <;> simp [b₃, b₄, frame]
  have fuel := MachineCopy.copyTrace Tape.vertices .fuel .scratch
    (by decide) (by decide) (by decide) false .fuelFirst .fuelSecond
    (some .seedCounters) (program d positive) rfl rfl b₃ rfl (clean d positive).1 none
  rw [hf] at fuel
  have c₃ : (advance (TM2.step (program d positive)))^[2 * (n + 2)]
      (some ⟨some .fuelFirst, clean d positive, b₃⟩) =
      some ⟨some .seedCounters, clean d positive, b₄⟩ := by
    simpa only [clean_pair, show b₃ .vertices = encodeWord n from rfl, encodeWord_length,
      Nat.add_assoc] using fuel
  have c₄ : (advance (TM2.step (program d positive)))^[1]
      (some ⟨some .seedCounters, clean d positive, b₄⟩) =
      some ⟨some .guard, clean d positive,
        loopTapes d word n m n 0 rows header⟩ := by
    have ht : Function.update (Function.update b₄ Tape.vertex [false]) Tape.reverse [false] =
        loopTapes d word n m n 0 rows header := by
      funext t; cases t <;> simp [b₄, loopTapes, frame, encodeWord]
    simp only [Function.iterate_one, advance_some, TM2.step, program, TM2.stepAux]
    apply congrArg some
    exact congrArg (TM2.Cfg.mk _ _) ht
  have all := joinTrace (joinTrace (joinTrace (joinTrace c₀ c₁) c₂) c₃) c₄
  have hc : MachineTableSplit.exactSteps n m rows + (2 * (m + 1) + 1) +
      (2 * (n + 1) + 1) + 2 * (n + 2) + 1 = prefixSteps n m rows := by
    dsimp [MachineTableSplit.exactSteps, prefixSteps]
    omega
  rw [hc] at all
  exact all

/-- One entire vertex body: preserve-copy its tail, append the real dummy block,
clear its temporary fields, transform all old rows, and increment both counters
by actual pushes. The caller supplies no execution premise. -/
theorem bodyTrace {n m : Nat} (d : Nat) (positive : 0 < d) (input : List Bool)
    (left v : Nat) (rows : Fin d → GraphTables.DartRow n m) (rest output : List Bool) :
    (advance (TM2.step (program d positive)))^[bodySteps d v rows output]
      (some ⟨some .copyVertexFirst, clean d positive,
        loopTapes d input n m left v (MachineLazyRows.recordsInput (List.ofFn rows) ++ rest) output⟩) =
      some ⟨some .guard, clean d positive,
        loopTapes d input n m left (v + 1) rest (output ++ vertexBlock d v rows)⟩ := by
  let source := MachineLazyRows.recordsInput (List.ofFn rows) ++ rest
  let dummy := MachineDummyRows.rowsBits v (2 * d * v) d
  let moving := MachineLazyRows.recordsOutput d (2 * d) d (List.ofFn rows)
  let b₀ := loopTapes d input n m left v source output
  let b₁ := Function.update b₀ Tape.tail (encodeWord v)
  let b₄ := frame input source (output ++ dummy) (encodeWord n) (encodeWord m)
    (encodeWord left) (encodeWord v) (encodeWord (2 * d * v + d))
  let b₂ := Function.update (Function.update b₄ Tape.tail (encodeWord v))
    Tape.relation MachineDummyRows.trueBits
  let b₃ := Function.update b₄ Tape.relation MachineDummyRows.trueBits
  let b₅ := frame input rest ((output ++ dummy) ++ moving) (encodeWord n) (encodeWord m)
    (encodeWord left) (encodeWord v) (encodeWord (2 * d * v + d))
  have hcopy : Function.update b₀ Tape.tail (b₀ .vertex ++ b₀ .tail) = b₁ := by
    simp [b₀, b₁, loopTapes, frame]
  have copy := MachineCopy.copyTrace Tape.vertex .tail .scratch
    (by decide) (by decide) (by decide) false .copyVertexFirst .copyVertexSecond
    (some (.dummy (MachineDummyRows.start d))) (program d positive) rfl rfl b₀ rfl
    (clean d positive).1 none
  rw [hcopy] at copy
  have c₀ : (advance (TM2.step (program d positive)))^[2 * (v + 2)]
      (some ⟨some .copyVertexFirst, clean d positive, b₀⟩) =
      some ⟨some (.dummy (MachineDummyRows.start d)), clean d positive, b₁⟩ := by
    simpa only [clean_pair, show b₀ .vertex = encodeWord v from rfl, encodeWord_length,
      Nat.add_assoc] using copy
  have hdummy : Function.update (Function.update (Function.update b₁ Tape.reverse
      (encodeWord (2 * d * v + d))) Tape.relation MachineDummyRows.trueBits)
      Tape.output (b₁ .output ++ dummy) = b₂ := by
    funext t; cases t <;> simp [b₀, b₁, b₂, b₄, loopTapes, frame]
  have dummies := dummyTrace d positive b₁ v (2 * d * v)
    (by simp [b₁]) (by simp [b₁, b₀, loopTapes, frame])
    (by simp [b₁, b₀, loopTapes, frame]) (by simp [b₁, b₀, loopTapes, frame])
    (by simp [b₁, b₀, loopTapes, frame])
  have c₁ : (advance (TM2.step (program d positive)))^[MachineDummyRows.steps v
      (2 * d * v) output d + 1]
      (some ⟨some (.dummy (MachineDummyRows.start d)), clean d positive, b₁⟩) =
      some ⟨some .clearDummyTail, clean d positive, b₂⟩ := by
    change (advance (TM2.step (program d positive)))^[_] _ =
      some ⟨some .clearDummyTail, clean d positive,
        Function.update (Function.update (Function.update b₁ Tape.reverse
          (encodeWord (2 * d * v + d))) Tape.relation MachineDummyRows.trueBits)
          Tape.output (b₁ .output ++ dummy)⟩ at dummies
    rw [hdummy] at dummies
    simpa only [show b₁ .output = output by simp [b₁, b₀, loopTapes, frame]] using dummies
  have ht : Function.update b₂ Tape.tail [] = b₃ := by
    funext t; cases t <;> simp [b₂, b₃, b₄, frame]
  have drainTail := MachineDrain.drainTrace Tape.tail .clearDummyTail (some .clearDummyRelation)
    (program d positive) rfl b₂ (b₂ .tail) (clean d positive).1 none
  simp only [Function.update_eq_self, ht] at drainTail
  have c₂ : (advance (TM2.step (program d positive)))^[v + 2]
      (some ⟨some .clearDummyTail, clean d positive, b₂⟩) =
      some ⟨some .clearDummyRelation, clean d positive, b₃⟩ := by
    simpa only [clean_pair, show b₂ .tail = encodeWord v by simp [b₂], encodeWord_length,
      Nat.add_assoc] using drainTail
  have hr : Function.update b₃ Tape.relation [] = b₄ := by
    funext t; cases t <;> simp [b₃, b₄, frame]
  have drainRelation := MachineDrain.drainTrace Tape.relation .clearDummyRelation
    (some (.oldRows (0, none))) (program d positive) rfl b₃ (b₃ .relation)
    (clean d positive).1 none
  simp only [Function.update_eq_self, hr] at drainRelation
  have c₃ : (advance (TM2.step (program d positive)))^[8193]
      (some ⟨some .clearDummyRelation, clean d positive, b₃⟩) =
      some ⟨some (.oldRows (0, none)), clean d positive, b₄⟩ := by
    simpa only [clean_pair, show b₃ .relation = MachineDummyRows.trueBits by simp [b₃],
      MachineDummyRows.trueBits_length] using drainRelation
  have hmoving : Function.update (Function.update b₄ Tape.source rest) Tape.output
      (b₄ .output ++ moving) = b₅ := by
    funext t; cases t <;> simp [b₄, b₅, frame]
  have old := oldTrace d positive b₄ rows rest rfl
    (fun i h7 h9 => frame_old_empty _ _ _ _ _ _ _ _ i h7 h9)
  have c₄ : (advance (TM2.step (program d positive)))^[MachineLazyRows.vertexSteps d (2 * d) d
      (List.ofFn rows) (output ++ dummy)]
      (some ⟨some (.oldRows (0, none)), clean d positive, b₄⟩) =
      some ⟨some .nextVertex, clean d positive, b₅⟩ := by
    change (advance (TM2.step (program d positive)))^[_] _ =
      some ⟨some .nextVertex, clean d positive,
        Function.update (Function.update b₄ Tape.source rest) Tape.output
          (b₄ .output ++ moving)⟩ at old
    rw [hmoving] at old
    exact old
  have c₅ : (advance (TM2.step (program d positive)))^[1]
      (some ⟨some .nextVertex, clean d positive, b₅⟩) =
      some ⟨some .guard, clean d positive,
        loopTapes d input n m left (v + 1) rest (output ++ vertexBlock d v rows)⟩ := by
    have hrev : List.replicate d true ++ encodeWord (2 * d * v + d) =
        encodeWord (2 * d * (v + 1)) := by
      have hw := MachineUnaryAffineAt.prepend_replicate_word d (2 * d * v + d) []
      simp only [List.append_nil] at hw
      rw [hw]
      exact congrArg encodeWord (show d + (2 * d * v + d) = 2 * d * (v + 1) by
        simp only [Nat.mul_add, Nat.mul_one]
        omega)
    have ht : Function.update (Function.update b₅ Tape.reverse
        ((List.replicate d true).reverse ++ b₅ .reverse)) Tape.vertex (true :: b₅ .vertex) =
        loopTapes d input n m left (v + 1) rest (output ++ vertexBlock d v rows) := by
      funext t
      cases t <;> simp [b₅, frame, loopTapes, vertexBlock, dummy, moving,
        hrev, List.append_assoc]
      simp [encodeWord, List.replicate_succ]
    simp only [Function.iterate_one, advance_some, TM2.step, program,
      stepAux_pushWord, TM2.stepAux]
    apply congrArg some
    exact congrArg (TM2.Cfg.mk _ _) ht
  have all := joinTrace (joinTrace (joinTrace (joinTrace (joinTrace c₀ c₁) c₂) c₃) c₄) c₅
  exact all

theorem drainPhase (d : Nat) (positive : 0 < d) (tape : Tape) (label : Label d)
    (exit : Option (Label d))
    (atLabel : program d positive label = MachineDrain.drain tape label exit)
    (base : Tape → List Bool) :
    (advance (TM2.step (program d positive)))^[(base tape).length + 1]
      (some ⟨some label, clean d positive, base⟩) =
      some ⟨exit, clean d positive, Function.update base tape []⟩ := by
  simpa only [Function.update_eq_self, clean_pair] using
    MachineDrain.drainTrace tape label exit (program d positive) atLabel base
      (base tape) (clean d positive).1 none

theorem finishTrace (d : Nat) (positive : 0 < d) (input output : List Bool) (n m v : Nat) :
    (advance (TM2.step (program d positive)))^[finishSteps d n m v]
      (some ⟨some .guard, clean d positive, loopTapes d input n m 0 v [] output⟩) =
      some ⟨none, clean d positive, finalTapes input output⟩ := by
  let b₀ := loopTapes d input n m 0 v [] output
  let b₁ := Function.update b₀ Tape.vertices []
  let b₂ := Function.update b₁ Tape.darts []
  let b₃ := Function.update b₂ Tape.fuel []
  let b₄ := Function.update b₃ Tape.vertex []
  have hframe : MachineUnaryCounter.counterTapes Tape.fuel b₀ 0 [] = b₀ := by
    funext t; cases t <;> simp [MachineUnaryCounter.counterTapes, b₀, loopTapes, frame]
  have guard := MachineUnaryCounter.guardTrace_zero Tape.fuel .guard .copyVertexFirst
    .clearVertices (program d positive) rfl b₀ [] (clean d positive).1 none
  have c₀ : (advance (TM2.step (program d positive)))^[1]
      (some ⟨some .guard, clean d positive, b₀⟩) =
      some ⟨some .clearVertices, clean d positive, b₀⟩ := by
    simpa only [hframe, clean_pair] using guard
  have c₁ : (advance (TM2.step (program d positive)))^[n + 2]
      (some ⟨some .clearVertices, clean d positive, b₀⟩) =
      some ⟨some .clearDarts, clean d positive, b₁⟩ := by
    simpa only [show b₀ .vertices = encodeWord n from rfl, encodeWord_length, Nat.add_assoc] using
      drainPhase d positive .vertices .clearVertices (some .clearDarts) rfl b₀
  have c₂ : (advance (TM2.step (program d positive)))^[m + 2]
      (some ⟨some .clearDarts, clean d positive, b₁⟩) =
      some ⟨some .clearFuel, clean d positive, b₂⟩ := by
    have hv : b₁ .darts = encodeWord m := by simp [b₁, b₀, loopTapes, frame]
    simpa only [hv, encodeWord_length, Nat.add_assoc] using
      drainPhase d positive .darts .clearDarts (some .clearFuel) rfl b₁
  have c₃ : (advance (TM2.step (program d positive)))^[2]
      (some ⟨some .clearFuel, clean d positive, b₂⟩) =
      some ⟨some .clearVertex, clean d positive, b₃⟩ := by
    have hv : b₂ .fuel = encodeWord 0 := by simp [b₂, b₁, b₀, loopTapes, frame]
    simpa only [hv, encodeWord_length] using
      drainPhase d positive .fuel .clearFuel (some .clearVertex) rfl b₂
  have c₄ : (advance (TM2.step (program d positive)))^[v + 2]
      (some ⟨some .clearVertex, clean d positive, b₃⟩) =
      some ⟨some .clearReverse, clean d positive, b₄⟩ := by
    have hv : b₃ .vertex = encodeWord v := by simp [b₃, b₂, b₁, b₀, loopTapes, frame]
    simpa only [hv, encodeWord_length, Nat.add_assoc] using
      drainPhase d positive .vertex .clearVertex (some .clearReverse) rfl b₃
  have hend : Function.update b₄ Tape.reverse [] = finalTapes input output := by
    funext t; cases t <;> simp [b₄, b₃, b₂, b₁, b₀, loopTapes, finalTapes, frame]
  have c₅ : (advance (TM2.step (program d positive)))^[2 * d * v + 2]
      (some ⟨some .clearReverse, clean d positive, b₄⟩) =
      some ⟨none, clean d positive, finalTapes input output⟩ := by
    have hv : b₄ .reverse = encodeWord (2 * d * v) := by
      simp [b₄, b₃, b₂, b₁, b₀, loopTapes, frame]
    simpa only [hv, encodeWord_length, Nat.add_assoc, hend] using
      drainPhase d positive .reverse .clearReverse none rfl b₄
  have all := joinTrace (joinTrace (joinTrace (joinTrace (joinTrace c₀ c₁) c₂) c₃) c₄) c₅
  have hc : 1 + (n + 2) + (m + 2) + 2 + (v + 2) + (2 * d * v + 2) =
      finishSteps d n m v := by dsimp [finishSteps]; omega
  rw [hc] at all
  exact all

theorem vertexBlock_codec {n d : Nat} (table : PortTables.Table n d) (v : Fin n) :
    vertexBlock d v.val (PreprocessingLazyWords.row table v) =
      encodeWords ((PreprocessingLazyWords.vertexRows table v).flatMap GraphTables.rowWords) := by
  rw [vertexBlock, MachineLazyCodec.rowsBits_stay, MachineLazyRows.recordsOutput_lazy,
    PreprocessingLazyWords.vertexRows, List.flatMap_append, encodeWords_append]

theorem inputBlocks_codec {n d : Nat} (table : PortTables.Table n d) (events : List (Fin n)) :
    inputBlocks table events = encodeWords
      ((events.flatMap (fun v => List.ofFn (PreprocessingLazyWords.row table v))).flatMap
        GraphTables.rowWords) := by
  rw [List.flatMap_assoc, encodeWords_flatMap]
  simp only [inputBlocks, MachineLazyRows.recordsInput_eq_codec]

theorem outputBlocks_codec {n d : Nat} (table : PortTables.Table n d) (events : List (Fin n)) :
    outputBlocks table events = encodeWords
      ((events.flatMap (PreprocessingLazyWords.vertexRows table)).flatMap GraphTables.rowWords) := by
  rw [List.flatMap_assoc, encodeWords_flatMap]
  simp only [outputBlocks, vertexBlock_codec]

theorem input_table_codec {n d : Nat} (table : PortTables.Table n d) :
    PortTables.tableBits table = encodeWords [n, n * d] ++ inputBlocks table (List.finRange n) := by
  rw [inputBlocks_codec]
  change encodeWords (PortTables.tableWords table) = _
  rw [PortTables.tableWords_eq, PreprocessingLazyWords.flatRows_list, encodeWords_append]
  have hrows : (List.ofFn (fun v => List.ofFn (PreprocessingLazyWords.row table v))).flatten =
      (List.finRange n).flatMap (fun v => List.ofFn (PreprocessingLazyWords.row table v)) := by
    rw [List.ofFn_eq_map]
    rfl
  rw [hrows]

theorem output_table_codec {n d : Nat} (table : PortTables.Table n d) :
    PortTables.tableBits (PreprocessingOverlayTables.lazy table) =
      encodeWords [n, 2 * (n * d)] ++ outputBlocks table (List.finRange n) := by
  rw [outputBlocks_codec, PreprocessingLazyWords.tableBits_lazy, encodeWords_append]
  have hm : n * (2 * d) = 2 * (n * d) := by ac_rfl
  have hrows : (List.ofFn (PreprocessingLazyWords.vertexRows table)).flatten =
      (List.finRange n).flatMap (PreprocessingLazyWords.vertexRows table) := by
    rw [List.ofFn_eq_map]
    rfl
  exact congrArg₂ List.append (congrArg (fun k => encodeWords [n, k]) hm)
    (congrArg (fun rows => encodeWords (rows.flatMap GraphTables.rowWords)) hrows)

/-- Induction over the actual unary fuel and the actual stored vertex order. -/
theorem loopTrace {n d : Nat} (table : PortTables.Table n d) (positive : 0 < d)
    (input : List Bool) (count r : Nat) (hsum : r + count = n) (output : List Bool) :
    (advance (TM2.step (program d positive)))^[loopSteps table r count output]
      (some ⟨some .guard, clean d positive,
        loopTapes d input n (n * d) count r (inputBlocks table (remaining n r)) output⟩) =
      some ⟨none, clean d positive,
        finalTapes input (output ++ outputBlocks table (remaining n r))⟩ := by
  induction count generalizing r output with
  | zero =>
    have hr : r = n := by omega
    subst r
    simpa only [loopSteps, remaining_done, inputBlocks, outputBlocks, List.flatMap_nil,
      List.append_nil] using finishTrace d positive input output n (n * d) n
  | succ count ih =>
    have hr : r < n := by omega
    let rows := PreprocessingLazyWords.row table (⟨r, hr⟩ : Fin n)
    let rest := inputBlocks table (remaining n (r + 1))
    let source := MachineLazyRows.recordsInput (List.ofFn rows) ++ rest
    let b₀ := loopTapes d input n (n * d) (count + 1) r source output
    let b₁ := loopTapes d input n (n * d) count r source output
    have hguard (k : Nat) : MachineUnaryCounter.counterTapes Tape.fuel b₀ k [] =
        loopTapes d input n (n * d) k r source output := by
      funext t; cases t <;> simp [MachineUnaryCounter.counterTapes, b₀, loopTapes, frame]
    have guard := MachineUnaryCounter.guardTrace_succ Tape.fuel .guard .copyVertexFirst
      .clearVertices (program d positive) rfl b₀ count [] (clean d positive).1 none
    have c₀ : (advance (TM2.step (program d positive)))^[1]
        (some ⟨some .guard, clean d positive, b₀⟩) =
        some ⟨some .copyVertexFirst, clean d positive, b₁⟩ := by
      simpa only [hguard, clean_pair] using guard
    have c₁ := bodyTrace d positive input count r rows rest output
    have c₂ := ih (r + 1) (by omega) (output ++ vertexBlock d r rows)
    have all := joinTrace (joinTrace c₀ c₁) c₂
    have hi : inputBlocks table (remaining n r) = source := by
      rw [remaining_cons n r hr]
      rfl
    have ho : outputBlocks table (remaining n r) =
        vertexBlock d r rows ++ outputBlocks table (remaining n (r + 1)) := by
      rw [remaining_cons n r hr]
      rfl
    simpa only [loopSteps, dite_eq_left hr, hi, ho, List.append_assoc] using all

/-- The full table execution, including all headers, all dummy and moving
rows, and complete work-tape cleanup, in the existing exact Boolean codec. -/
theorem tableTrace {n d : Nat} (table : PortTables.Table n d) (positive : 0 < d) :
    (advance (TM2.step (program d positive)))^[totalSteps table]
      (some ⟨some (.split .copyFirst), clean d positive, initialTapes (PortTables.tableBits table)⟩) =
      some ⟨none, clean d positive,
        finalTapes (PortTables.tableBits table)
          (PortTables.tableBits (PreprocessingOverlayTables.lazy table))⟩ := by
  have prefixRun := prefixTrace d positive n (n * d) (inputBlocks table (List.finRange n))
  rw [← input_table_codec table] at prefixRun
  have loop := loopTrace table positive (PortTables.tableBits table) n 0 (by omega)
    (encodeWords [n, 2 * (n * d)])
  simp only [remaining_zero] at loop
  have all := joinTrace prefixRun loop
  rw [← output_table_codec table] at all
  exact all

theorem dummyRows_length_le (v e count : Nat) :
    (MachineDummyRows.rowsBits v e count).length ≤ count * (v + e + count + 8194) := by
  induction count generalizing e with
  | zero => simp [MachineDummyRows.rowsBits]
  | succ count ih =>
    simp only [MachineDummyRows.rowsBits, List.length_append, MachineDummyRows.rowBits_length]
    have h := ih (e + 1)
    have he : v + (e + 1) + count + 8194 = v + e + (count + 1) + 8194 := by omega
    rw [he] at h
    nlinarith only [h]

/-- A uniform bound for the actual vertex body, using the complete output size
as a cap on its existing prefix. Degree is a fixed program parameter. -/
theorem bodySteps_le {n d : Nat} (rows : Fin d → GraphTables.DartRow n (n * d))
    (v L : Nat) (output : List Bool) (hv : v ≤ n) (hn : n ≤ L) (hm : n * d ≤ L)
    (ho : output.length ≤ 20000 * (L + 1) ^ 2) :
    bodySteps d v rows output ≤ 1000000 * (d + 1) ^ 3 * (L + 1) ^ 2 := by
  let D := d + 1
  let N := L + 1
  let P := D * N
  let Q := P * P
  let S := v + 2 * d * v + d + 8194
  let V := (2 * d) * (n * d) + n * d + d
  let R := n + V + 8194
  let C := 2 * n + 8 * (n * d) + V + 4 * R + 8224
  let dummy := MachineDummyRows.rowsBits v (2 * d * v) d
  let after := output ++ dummy
  have hD : 1 ≤ D := by dsimp [D]; omega
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hdD : d ≤ D := by dsimp [D]; omega
  have hLN : L ≤ N := by dsimp [N]; omega
  have hDP : D ≤ P := by
    have h := Nat.mul_le_mul_left D hN
    simpa [P] using h
  have hNP : N ≤ P := by
    have h := Nat.mul_le_mul_right N hD
    simpa [P] using h
  have hP : 1 ≤ P := hN.trans hNP
  have hPQ : P ≤ Q := by
    have h := Nat.mul_le_mul_right P hP
    simpa [Q] using h
  have hQ : 1 ≤ Q := hP.trans hPQ
  have hdP : d ≤ P := hdD.trans hDP
  have hvN : v ≤ N := hv.trans (hn.trans hLN)
  have hvP : v ≤ P := hvN.trans hNP
  have hnP : n ≤ P := hn.trans (hLN.trans hNP)
  have hmN : n * d ≤ N := hm.trans hLN
  have hmP : n * d ≤ P := hmN.trans hNP
  have hdv : d * v ≤ P := by simpa [P] using Nat.mul_le_mul hdD hvN
  have hdm : d * (n * d) ≤ P := by simpa [P] using Nat.mul_le_mul hdD hmN
  have hdPQ : d * P ≤ Q := by simpa [Q] using Nat.mul_le_mul_right P hdP
  have hNQ : N ^ 2 ≤ Q := by simpa [pow_two, Q] using Nat.mul_le_mul hNP hNP
  have hS : S ≤ 10000 * P := by
    have hconst := Nat.mul_le_mul_left 8194 hP
    dsimp [S]
    nlinarith only [hvP, hdP, hdv, hconst, hP]
  have hV : V ≤ 4 * P := by
    dsimp [V]
    nlinarith only [hdm, hmP, hdP]
  have hR : R ≤ 10000 * P := by
    have hconst := Nat.mul_le_mul_left 8194 hP
    dsimp [R]
    nlinarith only [hnP, hV, hconst, hP]
  have hC : C ≤ 50000 * P := by
    have hconst := Nat.mul_le_mul_left 8224 hP
    dsimp [C]
    nlinarith only [hnP, hmP, hV, hR, hconst, hP]
  have hSQ : S ≤ 10000 * Q := hS.trans (Nat.mul_le_mul_left 10000 hPQ)
  have hCQ : C ≤ 50000 * Q := hC.trans (Nat.mul_le_mul_left 50000 hPQ)
  have hdSQ : d * S ≤ 10000 * Q := by
    calc
      d * S ≤ d * (10000 * P) := Nat.mul_le_mul_left d hS
      _ = 10000 * (d * P) := by ring
      _ ≤ 10000 * Q := Nat.mul_le_mul_left 10000 hdPQ
  have hdRQ : d * R ≤ 10000 * Q := by
    calc
      d * R ≤ d * (10000 * P) := Nat.mul_le_mul_left d hR
      _ = 10000 * (d * P) := by ring
      _ ≤ 10000 * Q := Nat.mul_le_mul_left 10000 hdPQ
  have hOut : output.length ≤ 20000 * Q := by
    change output.length ≤ 20000 * N ^ 2 at ho
    exact ho.trans (Nat.mul_le_mul_left 20000 hNQ)
  have hDummyLength : dummy.length ≤ 10000 * Q := by
    have h := dummyRows_length_le v (2 * d * v) d
    change dummy.length ≤ d * S at h
    exact h.trans hdSQ
  have hAfter : after.length ≤ 30000 * Q := by
    dsimp [after]
    rw [List.length_append]
    omega
  have hDummyInside : 4 * S + 2 * (output.length + d * S) + 10 ≤ 100010 * Q := by
    have hconst := Nat.mul_le_mul_left 10 hQ
    nlinarith only [hSQ, hOut, hdSQ, hconst]
  have hDummySteps : MachineDummyRows.steps v (2 * d * v) output d ≤ 100010 * d * Q := by
    calc
      MachineDummyRows.steps v (2 * d * v) output d ≤
          d * (4 * S + 2 * (output.length + d * S) + 10) := by
        simpa only [S] using MachineDummyRows.steps_le_bound v (2 * d * v) output d
      _ ≤ d * (100010 * Q) := Nat.mul_le_mul_left d hDummyInside
      _ = 100010 * d * Q := by ring
  have hOldInside : C + 2 * (after.length + d * R) + 1 ≤ 130001 * Q := by
    nlinarith only [hCQ, hAfter, hdRQ, hQ]
  have hOldSteps : MachineLazyRows.vertexSteps d (2 * d) d (List.ofFn rows) after ≤
      130001 * d * Q + 1 := by
    have h := MachineLazyRows.vertexSteps_le d (2 * d) d (List.ofFn rows) after
    simp only [List.length_ofFn] at h
    change MachineLazyRows.vertexSteps d (2 * d) d (List.ofFn rows) after ≤
      d * (C + 2 * (after.length + d * R) + 1) + 1 at h
    calc
      MachineLazyRows.vertexSteps d (2 * d) d (List.ofFn rows) after ≤
          d * (C + 2 * (after.length + d * R) + 1) + 1 := h
      _ ≤ d * (130001 * Q) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left d hOldInside) 1
      _ = 130001 * d * Q + 1 := by ring
  have hvQ : v ≤ Q := hvP.trans hPQ
  have hOverhead : 3 * v + 8201 ≤ 10000 * Q := by
    have hconst := Nat.mul_le_mul_left 8201 hQ
    nlinarith only [hvQ, hconst, hQ]
  have hBody : bodySteps d v rows output ≤ 230011 * d * Q + 10000 * Q + 1 := by
    change 2 * (v + 2) + (MachineDummyRows.steps v (2 * d * v) output d + 1) +
      (v + 2) + 8193 + MachineLazyRows.vertexSteps d (2 * d) d (List.ofFn rows) after + 1 ≤ _
    nlinarith only [hDummySteps, hOldSteps, hOverhead]
  have hdQQ : d * Q ≤ D * Q := Nat.mul_le_mul_right Q hdD
  have hQQ : Q ≤ D * Q := by simpa using Nat.mul_le_mul_right Q hD
  have hDQ : 1 ≤ D * Q := hQ.trans hQQ
  have hCoarse : bodySteps d v rows output ≤ 300000 * D * Q := by
    nlinarith only [hBody, hdQQ, hQQ, hDQ]
  calc
    bodySteps d v rows output ≤ 300000 * D * Q := hCoarse
    _ ≤ 1000000 * D * Q := by
      have h := Nat.mul_le_mul_right (D * Q) (by norm_num : (300000 : Nat) ≤ 1000000)
      simpa only [Nat.mul_assoc] using h
    _ = 1000000 * (d + 1) ^ 3 * (L + 1) ^ 2 := by dsimp [D, N, P, Q]; ring

theorem loopSteps_le {n d : Nat} (table : PortTables.Table n d) (L count r : Nat)
    (hsum : r + count = n) (hn : n ≤ L) (hm : n * d ≤ L) (output : List Bool)
    (hout : (output ++ outputBlocks table (remaining n r)).length ≤ 20000 * (L + 1) ^ 2) :
    loopSteps table r count output ≤
      count * (1 + 1000000 * (d + 1) ^ 3 * (L + 1) ^ 2) + 5 * L + 11 := by
  induction count generalizing r output with
  | zero =>
    have hr : r = n := by omega
    subst r
    have hdouble : 2 * d * n = 2 * (n * d) := by ac_rfl
    simp only [loopSteps, finishSteps, Nat.zero_mul, Nat.zero_add, hdouble]
    omega
  | succ count ih =>
    have hr : r < n := by omega
    let rows := PreprocessingLazyWords.row table (⟨r, hr⟩ : Fin n)
    have ho : output.length ≤ 20000 * (L + 1) ^ 2 := by
      rw [List.length_append] at hout
      omega
    have hb := bodySteps_le rows r L output hr.le hn hm ho
    have hs : outputBlocks table (remaining n r) =
        vertexBlock d r rows ++ outputBlocks table (remaining n (r + 1)) := by
      rw [remaining_cons n r hr]
      rfl
    have hout' : ((output ++ vertexBlock d r rows) ++
        outputBlocks table (remaining n (r + 1))).length ≤ 20000 * (L + 1) ^ 2 := by
      simpa only [hs, List.append_assoc] using hout
    have ht := ih (r + 1) (by omega) (output ++ vertexBlock d r rows) hout'
    simp only [loopSteps, dite_eq_left hr]
    change (1 + bodySteps d r rows output) +
      loopSteps table (r + 1) count (output ++ vertexBlock d r rows) ≤ _
    nlinarith only [hb, ht]

theorem totalSteps_le {n d : Nat} (table : PortTables.Table n d) :
    totalSteps table ≤ (timePolynomial d).eval (PortTables.tableBits table).length := by
  let L := (PortTables.tableBits table).length
  let N := L + 1
  let C := 1000000 * (d + 1) ^ 3
  have hn : n ≤ L := PortTables.vertices_le_tableBits_length table
  have hm : n * d ≤ L := GraphTables.darts_le_tableBits_length (PortTables.graphTable table)
  have hout : (encodeWords [n, 2 * (n * d)] ++
      outputBlocks table (remaining n 0)).length ≤ 20000 * (L + 1) ^ 2 := by
    rw [remaining_zero, ← output_table_codec]
    exact output_length_le table
  have hl := loopSteps_le table L n 0 (by omega) hn hm _ hout
  have hp : prefixSteps n (n * d) (inputBlocks table (List.finRange n)) ≤ 10 * L + 17 := by
    unfold prefixSteps
    rw [← input_table_codec table]
    change 2 * L + 5 * n + 3 * (n * d) + 17 ≤ _
    omega
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hnN : n ≤ N := by dsimp [N]; omega
  have hN2 : 1 ≤ N ^ 2 := by nlinarith only [hN]
  have hN3 : N ≤ N ^ 3 := by
    have h := Nat.mul_le_mul_left N hN2
    nlinarith only [h]
  have hc := Nat.mul_le_mul_right (1 + C * N ^ 2) hnN
  change loopSteps table 0 n (encodeWords [n, 2 * (n * d)]) ≤ n * (1 + C * N ^ 2) + 5 * L + 11 at hl
  rw [timePolynomial_eval]
  change totalSteps table ≤ (C + 100) * N ^ 3
  unfold totalSteps
  have hLN : L + 1 = N := rfl
  nlinarith only [hp, hl, hc, hN, hN3, hLN]

def machine (d : Nat) (positive : 0 < d) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label d
  main := .split .copyFirst
  σ := State d
  initialState := clean d positive
  m := program d positive

theorem initial_configuration (d : Nat) (positive : 0 < d) (input : List Bool) :
    initList (machine d positive) input =
      ⟨some (.split .copyFirst), clean d positive, initialTapes input⟩ := by
  have ht : (initList (machine d positive) input).stk = initialTapes input := by
    funext t
    cases t <;> simp [initList, machine, initialTapes, frame]
    rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

/-- A full actual finite-machine execution with a fixed-degree polynomial
budget, the exact lazy-table output, preserved original input, and clean work. -/
def machineInTime {n d : Nat} (table : PortTables.Table n d) (positive : 0 < d) :
    StateTransition.EvalsToInTime (machine d positive).step
      (initList (machine d positive) (PortTables.tableBits table))
      (some ⟨none, clean d positive, finalTapes (PortTables.tableBits table)
        (PortTables.tableBits (PreprocessingOverlayTables.lazy table))⟩)
      ((timePolynomial d).eval (PortTables.tableBits table).length) where
  steps := totalSteps table
  evals_in_steps := by
    rw [initial_configuration]
    exact tableTrace table positive
  steps_le_m := totalSteps_le table

end UniqueGamesTheorem.Foundations.Complexity.MachineLazyTable

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineLazyTableRuntime
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical polynomial-time computation of the executable lazy preprocessing map.
The raw machine's retained original input is physically drained by the checked
canonical-output wrapper before it reaches the standard `haltList` endpoint.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLazyTableRuntime

open Turing PCP
open MachineLazyTable (Tape Label State)

def rawProgram (d : Nat) (positive : 0 < d) :
    MachineCanonicalOutput.Program Tape (Label d) (State d) where
  input := .input
  output := .output
  main := .split .copyFirst
  initial := MachineLazyTable.clean d positive
  code := MachineLazyTable.program d positive

theorem cleanup_complete (d : Nat) (positive : 0 < d) (k : Tape) :
    k ∈ cleanupTapes ↔ k ≠ (rawProgram d positive).output := by
  cases k <;> simp [cleanupTapes, rawProgram]

/-- The terminal witness is the checked full lazy-table execution. The wrapper
then drains the retained original input rather than assuming it disappeared. -/
def terminalRun (d : Nat) (positive : 0 < d) (a : PortTables.Input d) :
    MachineCanonicalOutput.TerminalRun (rawProgram d positive) (PortTables.inputBits a)
      (PortTables.inputBits (PreprocessingStageMaps.lazy d a))
      ((MachineLazyTable.timePolynomial d).eval (PortTables.inputBits a).length) where
  state := MachineLazyTable.clean d positive
  tapes := MachineLazyTable.finalTapes (PortTables.inputBits a)
    (PortTables.inputBits (PreprocessingStageMaps.lazy d a))
  execution := MachineLazyTable.machineInTime a.2 positive
  output_eq := rfl

/-- The actual canonical-output finite machine computes precisely the shared
degree-d to degree-2d stage map in polynomial time. -/
noncomputable def computableInPolyTime (d : Nat) (positive : 0 < d) :
    TM2ComputableInPolyTime (PortTables.inputBits (ports := d))
      (PortTables.inputBits (ports := 2 * d)) (PreprocessingStageMaps.lazy d) :=
  MachineCanonicalOutput.computableInPolyTime (rawProgram d positive) cleanupTapes
    (cleanup_complete d positive) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.lazy d) (MachineLazyTable.timePolynomial d) (terminalRun d positive)

/-- Every tape alphabet of this exact completed computation certificate is finite. -/
theorem finite_alphabet (d : Nat) (positive : 0 < d) :
    ∀ k, Finite ((computableInPolyTime d positive).tm.Γ k) :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet (rawProgram d positive) cleanupTapes
    (cleanup_complete d positive) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.lazy d) (MachineLazyTable.timePolynomial d) (terminalRun d positive)

end UniqueGamesTheorem.Foundations.Complexity.MachineLazyTableRuntime

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineOverlayRows
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineOverlayRows

open Turing MachineComposition
open PCP.GraphTables PCP.PreprocessingOverlayWords
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ A : Type} [DecidableEq K]

def instruction (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (labels : Label e → Λ) (exit : Option Λ) :
    Label e → TM2.Stmt (fun _ : K => Bool) Λ (State A e)
  | .loadStart => Hastad.SourceMachine.fieldStart (tape 1) (labels .loadLoop)
  | .loadLoop => Hastad.SourceMachine.fieldLoop (tape 9) (tape 1)
      (labels .loadLoop) (some (labels .seedRelation))
  | .seedRelation => pushWord (tape 2) trueBits.reverse
      (.goto fun _ => labels (.row (.inl .copySeed)))
  | .row stage => MachineLazyRows.reindexInstruction e positive (d + e) d
      (tape ∘ bodyIndex) (fun stage => labels (.row stage))
      (some (labels .drainOld)) stage
  | .drainOld => MachineDrain.drain (tape 1) (labels .drainOld) (some (labels .drainNew))
  | .drainNew => MachineDrain.drain (tape 6) (labels .drainNew) (some (labels .drainRelation))
  | .drainRelation => MachineDrain.drain (tape 2) (labels .drainRelation) exit

/-- Load the actual next expander index, execute the arithmetic and complete
4096-bit row emitter, then clear the three isolated temporary fields. -/
theorem rowTrace (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (labels : Label e → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A e))
    (atLabels : ∀ l, program (labels l) = instruction d e positive tape labels exit l)
    (base : K → List Bool) (v j : Nat) (suffix : List Bool)
    (tailWord : base (tape 0) = encodeWord v)
    (inputWord : base (tape 9) = encodeWord j ++ suffix)
    (empty : ∀ i : Fin 10, i ≠ 0 → i ≠ 7 → i ≠ 9 → base (tape i) = [])
    (ambient : A) :
    (advance (TM2.step program))^[rowSteps d e v j (base (tape 7))]
      (some ⟨some (labels .loadStart), MachinePortReindex.clean e positive ambient, base⟩) =
      some ⟨exit, MachinePortReindex.clean e positive ambient,
        resultTapes d e v j tape base suffix⟩ := by
  have hd (i k : Fin 10) (h : i ≠ k) : tape i ≠ tape k := fun x => h (distinct x)
  have h₁ := empty 1 (by decide) (by decide) (by decide)
  have h₂ := empty 2 (by decide) (by decide) (by decide)
  have h₃ := empty 3 (by decide) (by decide) (by decide)
  have h₄ := empty 4 (by decide) (by decide) (by decide)
  have h₅ := empty 5 (by decide) (by decide) (by decide)
  have h₆ := empty 6 (by decide) (by decide) (by decide)
  have h₈ := empty 8 (by decide) (by decide) (by decide)
  have hi0 : bodyIndex 0 = 0 := rfl
  have hi3 : bodyIndex 3 = 3 := rfl
  have hi4 : bodyIndex 4 = 4 := rfl
  have hi5 : bodyIndex 5 = 5 := rfl
  have hi6 : bodyIndex 6 = 6 := rfl
  have hi8 : bodyIndex 8 = 8 := rfl
  let loaded := Function.update (Function.update base (tape 9) suffix) (tape 1) (encodeWord j)
  let seeded := Function.update loaded (tape 2) trueBits
  let rowed := MachineLazyRows.reindexResultTapes e (d + e) d v j trueRelation
    (tape ∘ bodyIndex) seeded
  let oldCleared := Function.update rowed (tape 1) []
  let newCleared := Function.update oldCleared (tape 6) []
  have loadRun : (advance (TM2.step program))^[j + 2]
      (some ⟨some (labels .loadStart), MachinePortReindex.clean e positive ambient, base⟩) =
      some ⟨some (labels .seedRelation), MachinePortReindex.clean e positive ambient, loaded⟩ := by
    have h := (Hastad.SourceMachine.fieldInTime (tape 9) (tape 1) (hd 9 1 (by decide))
      (labels .loadStart) (labels .loadLoop) (some (labels .seedRelation)) program
      (atLabels .loadStart) (atLabels .loadLoop) base j suffix inputWord
      (ambient, MachineFixedDivMod.residue e positive 0) none).evals_in_steps
    change (advance (TM2.step program))^[j + 2]
      (some ⟨some (labels .loadStart), MachinePortReindex.clean e positive ambient, base⟩) =
      some ⟨some (labels .seedRelation), MachinePortReindex.clean e positive ambient,
        Hastad.SourceMachine.fieldTapes (tape 9) (tape 1) base suffix
          (encodeWord j ++ base (tape 1))⟩ at h
    simpa only [Hastad.SourceMachine.fieldTapes,
      h₁, List.append_nil, MachinePortReindex.clean, loaded] using h
  have seedRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .seedRelation), MachinePortReindex.clean e positive ambient, loaded⟩) =
      some ⟨some (labels (.row (.inl .copySeed))),
        MachinePortReindex.clean e positive ambient, seeded⟩ := by
    change some (TM2.stepAux (program (labels .seedRelation)) _ _) = _
    rw [atLabels]
    simp [instruction, stepAux_pushWord, TM2.stepAux, seeded, loaded,
      hd 2 1 (by decide), hd 2 9 (by decide), h₂]
  have hs (i : Fin 10) (hi : i ≠ 1) (hi' : i ≠ 2) (hi'' : i ≠ 9) :
      seeded (tape i) = base (tape i) := by
    simp [seeded, loaded, hd i 1 hi, hd i 2 hi', hd i 9 hi'']
  have bodyRun := MachineLazyRows.reindexRowTrace e positive (d + e) d
    (tape ∘ bodyIndex) (distinct.comp bodyIndex_injective) (fun s => labels (.row s))
    (some (labels .drainOld)) program (fun s => atLabels (.row s)) seeded v j trueRelation
    (by simpa only [Function.comp_apply, hi0] using
      (hs 0 (by decide) (by decide) (by decide)).trans tailWord)
    (by simp [seeded, loaded, Function.comp_apply, bodyIndex, hd 1 2 (by decide)])
    (by simp [seeded, Function.comp_apply, bodyIndex, trueBits])
    (by simpa only [Function.comp_apply, hi3] using
      (hs 3 (by decide) (by decide) (by decide)).trans h₃)
    (by simpa only [Function.comp_apply, hi4] using
      (hs 4 (by decide) (by decide) (by decide)).trans h₄)
    (by simpa only [Function.comp_apply, hi5] using
      (hs 5 (by decide) (by decide) (by decide)).trans h₅)
    (by simpa only [Function.comp_apply, hi6] using
      (hs 6 (by decide) (by decide) (by decide)).trans h₆)
    (by simpa only [Function.comp_apply, hi8] using
      (hs 8 (by decide) (by decide) (by decide)).trans h₈) ambient
  have hout : seeded ((tape ∘ bodyIndex) 7) = base (tape 7) :=
    hs 7 (by decide) (by decide) (by decide)
  rw [hout] at bodyRun
  change (advance (TM2.step program))^[MachineLazyRows.reindexSteps e (d + e) d v j
      trueRelation (base (tape 7))]
    (some ⟨some (labels (.row (.inl .copySeed))), MachinePortReindex.clean e positive ambient, seeded⟩) =
    some ⟨some (labels .drainOld), MachinePortReindex.clean e positive ambient, rowed⟩ at bodyRun
  have rowedOld : rowed (tape 1) = encodeWord j := by
    simp [rowed, MachineLazyRows.reindexResultTapes, MachineLazyRows.reindexMappedTapes,
      Function.comp_apply, bodyIndex, seeded, loaded, hd 1 7 (by decide),
      hd 1 6 (by decide), hd 1 2 (by decide)]
  have rowedNew : oldCleared (tape 6) = encodeWord (MachinePortReindex.value e (d + e) d j) := by
    simp [oldCleared, rowed, MachineLazyRows.reindexResultTapes,
      MachineLazyRows.reindexMappedTapes, Function.comp_apply, bodyIndex,
      hd 6 1 (by decide), hd 6 7 (by decide)]
  have rowedRelation : newCleared (tape 2) = trueBits := by
    simp [newCleared, oldCleared, rowed, MachineLazyRows.reindexResultTapes,
      MachineLazyRows.reindexMappedTapes, Function.comp_apply, bodyIndex, seeded,
      hd 2 6 (by decide), hd 2 1 (by decide), hd 2 7 (by decide)]
  have drainOld := (MachineDrain.drainInTime (tape 1) (labels .drainOld)
    (some (labels .drainNew)) program (atLabels .drainOld) rowed
    (ambient, MachineFixedDivMod.residue e positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(rowed (tape 1)).length + 1]
    (some ⟨some (labels .drainOld), MachinePortReindex.clean e positive ambient, rowed⟩) =
    some ⟨some (labels .drainNew), MachinePortReindex.clean e positive ambient, oldCleared⟩ at drainOld
  rw [rowedOld, encodeWord_length] at drainOld
  have drainNew := (MachineDrain.drainInTime (tape 6) (labels .drainNew)
    (some (labels .drainRelation)) program (atLabels .drainNew) oldCleared
    (ambient, MachineFixedDivMod.residue e positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(oldCleared (tape 6)).length + 1]
    (some ⟨some (labels .drainNew), MachinePortReindex.clean e positive ambient, oldCleared⟩) =
    some ⟨some (labels .drainRelation), MachinePortReindex.clean e positive ambient, newCleared⟩ at drainNew
  rw [rowedNew, encodeWord_length] at drainNew
  have drainRelation := (MachineDrain.drainInTime (tape 2) (labels .drainRelation)
    exit program (atLabels .drainRelation) newCleared
    (ambient, MachineFixedDivMod.residue e positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(newCleared (tape 2)).length + 1]
    (some ⟨some (labels .drainRelation), MachinePortReindex.clean e positive ambient, newCleared⟩) =
    some ⟨exit, MachinePortReindex.clean e positive ambient,
      Function.update newCleared (tape 2) []⟩ at drainRelation
  rw [rowedRelation] at drainRelation
  have finalFrame : Function.update newCleared (tape 2) [] = resultTapes d e v j tape base suffix := by
    funext k
    by_cases h2 : k = tape 2
    · subst k
      simp [resultTapes, hd 2 7 (by decide), hd 2 9 (by decide), h₂]
    · by_cases h6 : k = tape 6
      · subst k
        simp [newCleared, resultTapes, hd 6 2 (by decide), hd 6 7 (by decide),
          hd 6 9 (by decide), h₆]
      · by_cases h1 : k = tape 1
        · subst k
          simp [newCleared, oldCleared, resultTapes, hd 1 2 (by decide),
            hd 1 6 (by decide), hd 1 7 (by decide), hd 1 9 (by decide), h₁]
        · by_cases h7 : k = tape 7
          · subst k
            simp [newCleared, oldCleared, rowed, MachineLazyRows.reindexResultTapes,
              MachineLazyRows.reindexMappedTapes, Function.comp_apply, bodyIndex,
              resultTapes, rowBits, seeded, loaded, hd 7 2 (by decide),
              hd 7 6 (by decide), hd 7 1 (by decide), hd 7 9 (by decide)]
          · simp [newCleared, oldCleared, rowed, MachineLazyRows.reindexResultTapes,
              MachineLazyRows.reindexMappedTapes, Function.comp_apply, bodyIndex,
              seeded, loaded, resultTapes, h2, h6, h1, h7]
  rw [finalFrame] at drainRelation
  exact joinTrace (joinTrace (joinTrace (joinTrace (joinTrace loadRun seedRun) bodyRun)
    drainOld) drainNew) drainRelation

/-! The fixed-degree vertex loop has one finite label block per port, plus
one terminal boundary. The stored row values do not occur in its program. -/

def vertexInstruction (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (labels : VertexLabel e → Λ) (exit : Option Λ) :
    VertexLabel e → TM2.Stmt (fun _ : K => Bool) Λ (State A e)
  | (i, none) => if i.val < e then .goto fun _ => labels (i, some .loadStart)
      else MachinePortReindex.exitAt exit
  | (i, some stage) => if h : i.val < e then
      instruction d e positive tape (fun stage => labels (i, some stage))
        (some (labels (⟨i.val + 1, by omega⟩, none))) stage
      else MachinePortReindex.exitAt exit

/-- A suffix of the actual fixed-degree port loop. Each row execution is
derived from `rowTrace`; no row-execution premise is accepted. -/
theorem vertexSuffixTrace (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (labels : VertexLabel e → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A e))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d e positive tape labels exit l)
    (base : K → List Bool) (v : Nat) (values : Fin e → Nat)
    (tailWord : base (tape 0) = encodeWord v)
    (empty : ∀ i : Fin 10, i ≠ 0 → i ≠ 7 → i ≠ 9 → base (tape i) = [])
    (ambient : A) (remaining : Nat) (i : Fin (e + 1)) (count : i.val + remaining = e)
    (output : List Bool) :
    (advance (TM2.step program))^[vertexSteps d e v ((List.ofFn values).drop i.val) output]
      (some ⟨some (labels (i, none)), MachinePortReindex.clean e positive ambient,
        streamFrame tape base ((List.ofFn values).drop i.val) output⟩) =
      some ⟨exit, MachinePortReindex.clean e positive ambient,
        streamFrame tape base [] (output ++ streamOutput d e v ((List.ofFn values).drop i.val))⟩ := by
  have hd (a b : Fin 10) (h : a ≠ b) : tape a ≠ tape b := fun x => h (distinct x)
  induction remaining generalizing i output with
  | zero =>
      have hi : i.val = e := by omega
      have hdrop : (List.ofFn values).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [List.length_ofFn, hi, le_refl]
      rw [hdrop]
      simp only [vertexSteps, streamOutput, List.flatMap_nil, List.append_nil]
      change some (TM2.stepAux (program (labels (i, none))) _ _) = _
      rw [atLabels]
      cases exit <;> simp [vertexInstruction, hi, MachinePortReindex.exitAt, TM2.stepAux]
  | succ remaining ih =>
      have hi : i.val < e := by omega
      let port : Fin e := ⟨i.val, hi⟩
      let next : Fin (e + 1) := ⟨i.val + 1, by omega⟩
      let rest := (List.ofFn values).drop (i.val + 1)
      have split : (List.ofFn values).drop i.val = values port :: rest := by
        have h := List.getElem_cons_drop (as := List.ofFn values)
          (i := i.val) (by simpa only [List.length_ofFn] using hi)
        simpa only [List.getElem_ofFn, port, rest] using h.symm
      let initial := streamFrame tape base (values port :: rest) output
      have boundary : (advance (TM2.step program))^[1]
          (some ⟨some (labels (i, none)), MachinePortReindex.clean e positive ambient, initial⟩) =
          some ⟨some (labels (i, some .loadStart)), MachinePortReindex.clean e positive ambient, initial⟩ := by
        change some (TM2.stepAux (program (labels (i, none))) _ _) = _
        rw [atLabels]
        simp [vertexInstruction, hi, TM2.stepAux]
      have body := rowTrace d e positive tape distinct (fun stage => labels (i, some stage))
        (some (labels (next, none))) program
        (by
          intro stage
          simpa only [vertexInstruction, hi, dite_true, next] using
            (atLabels (i, some stage))) initial v (values port)
        (encodeWords rest ++ base (tape 9))
        (by simp [initial, streamFrame, hd 0 7 (by decide), hd 0 9 (by decide), tailWord])
        (by simp [initial, streamFrame, hd 9 7 (by decide), encodeWords, List.append_assoc])
        (by
          intro k hk0 hk7 hk9
          simp [initial, streamFrame, hd k 7 hk7, hd k 9 hk9, empty k hk0 hk7 hk9]) ambient
      have initialOutput : initial (tape 7) = output := by simp [initial, streamFrame]
      rw [initialOutput] at body
      change (advance (TM2.step program))^[rowSteps d e v (values port) output]
        (some ⟨some (labels (i, some .loadStart)), MachinePortReindex.clean e positive ambient, initial⟩) =
        some ⟨some (labels (next, none)), MachinePortReindex.clean e positive ambient,
          resultTapes d e v (values port) tape initial (encodeWords rest ++ base (tape 9))⟩ at body
      rw [show resultTapes d e v (values port) tape initial (encodeWords rest ++ base (tape 9)) =
        streamFrame tape base rest (output ++ rowBits d e v (values port)) from
          streamFrame_afterRow d e v (values port) tape distinct base rest output] at body
      have nextCount : next.val + remaining = e := by dsimp [next]; omega
      have tail := ih next nextCount (output ++ rowBits d e v (values port))
      change (advance (TM2.step program))^[vertexSteps d e v rest (output ++ rowBits d e v (values port))]
        (some ⟨some (labels (next, none)), MachinePortReindex.clean e positive ambient,
          streamFrame tape base rest (output ++ rowBits d e v (values port))⟩) =
        some ⟨exit, MachinePortReindex.clean e positive ambient,
          streamFrame tape base [] ((output ++ rowBits d e v (values port)) ++ streamOutput d e v rest)⟩ at tail
      rw [split]
      have all := joinTrace (joinTrace boundary body) tail
      simpa only [vertexSteps, initial, streamOutput, List.flatMap_cons, List.append_assoc] using all

theorem vertexTrace (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (labels : VertexLabel e → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A e))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d e positive tape labels exit l)
    (base : K → List Bool) (v : Nat) (values : Fin e → Nat)
    (tailWord : base (tape 0) = encodeWord v)
    (empty : ∀ i : Fin 10, i ≠ 0 → i ≠ 7 → i ≠ 9 → base (tape i) = [])
    (ambient : A) (output : List Bool) :
    (advance (TM2.step program))^[vertexSteps d e v (List.ofFn values) output]
      (some ⟨some (labels (0, none)), MachinePortReindex.clean e positive ambient,
        streamFrame tape base (List.ofFn values) output⟩) =
      some ⟨exit, MachinePortReindex.clean e positive ambient,
        streamFrame tape base [] (output ++ streamOutput d e v (List.ofFn values))⟩ := by
  simpa only [Fin.val_zero, List.drop_zero] using vertexSuffixTrace d e positive tape distinct
    labels exit program atLabels base v values tailWord empty ambient e 0 (by simp) output

end UniqueGamesTheorem.Foundations.Complexity.MachineOverlayRows

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineOverlayTable
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineOverlayTable

variable {AmbientState : Type}

open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingOverlayWords
open MachineCloudPadding

/-- Fixed degree control, including two actual independent working streams. -/
def mainInstruction (d e : Nat) (hd : 0 < d) (he : 0 < e) :
    MainLabel d e → TM2.Stmt (fun _ : Tape => Bool) (Label d e) (State AmbientState d e)
  | .copyHFirst => Reduction.MachineTransfer.loopAt expanderArchive scratch id false
      (.inr .copyHFirst) (next .copyHSecond)
  | .copyHSecond => MachineCopy.forkLoop scratch expanderArchive expanderStream false
      (.inr .copyHSecond) (next .countSeed)
  | .countSeed => MachineUnaryAffineAt.seed output 0 (.inr .countScan)
  | .countScan => MachineUnaryAffineAt.scan vertexCount scratch output (d + e)
      (.inr .countScan) (.inr .countRestore)
  | .countRestore => Reduction.MachineTransfer.loopAt scratch vertexCount id false
      (.inr .countRestore) (next .headerSeed)
  | .headerSeed => MachineUnaryAffineAt.seed output 0 (.inr .headerScan)
  | .headerScan => MachineUnaryAffineAt.scan vertexCount scratch output 1
      (.inr .headerScan) (.inr .headerRestore)
  | .headerRestore => Reduction.MachineTransfer.loopAt scratch vertexCount id false
      (.inr .headerRestore) (next .fuelSeed)
  | .fuelSeed => MachineUnaryAffineAt.seed fuel 0 (.inr .fuelScan)
  | .fuelScan => MachineUnaryAffineAt.scan vertexCount scratch fuel 1
      (.inr .fuelScan) (.inr .fuelRestore)
  | .fuelRestore => Reduction.MachineTransfer.loopAt scratch vertexCount id false
      (.inr .fuelRestore) (next .vertexSeed)
  | .vertexSeed => .push vertex (fun _ => false) (.goto fun _ => .inr .guard)
  | .guard => MachineUnaryCounter.guard fuel (.inr (.old (0, none))) (.inr .drainFuel)
  | .old stage => MachineLazyRows.vertexInstruction d hd (d + e) 0 oldTapes
      (fun stage => .inr (.old stage)) (next .tailSeed) stage
  | .tailSeed => MachineUnaryAffineAt.seed tail 0 (.inr .tailScan)
  | .tailScan => MachineUnaryAffineAt.scan vertex scratch tail 1
      (.inr .tailScan) (.inr .tailRestore)
  | .tailRestore => Reduction.MachineTransfer.loopAt scratch vertex id false
      (.inr .tailRestore) (next (.expander (0, none)))
  | .expander stage => MachineStateEquiv.statement (expanderState AmbientState d e)
      (MachineOverlayRows.vertexInstruction d e he expanderTapes
        (fun stage => .inr (.expander stage)) (next .drainTail) stage)
  | .drainTail => MachineDrain.drain tail (.inr .drainTail) (next .increment)
  | .increment => .push vertex (fun _ => true) (.goto fun _ => .inr .guard)
  | .drainFuel => MachineDrain.drain fuel (.inr .drainFuel) (next .drainVertex)
  | .drainVertex => MachineDrain.drain vertex (.inr .drainVertex) (next .drainVertexCount)
  | .drainVertexCount => MachineDrain.drain vertexCount (.inr .drainVertexCount) (next .drainDartCount)
  | .drainDartCount => MachineDrain.drain dartCount (.inr .drainDartCount) none

/-- The checked splitter is placed directly in five homogeneous Boolean
stacks, with its actual halt replaced by the next preparation label. -/
def program (d e : Nat) (hd : 0 < d) (he : 0 < e) :
    Label d e → TM2.Stmt (fun _ : Tape => Bool) (Label d e) (State AmbientState d e)
  | .inl l => Placement.statement Sum.inl Sum.inl (next .copyHFirst)
      (MachineTableSplit.program l)
  | .inr l => mainInstruction d e hd he l

/-- The complete existing splitter is executed, retaining both archives. -/
theorem splitTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (table : GraphTables.Table) (rawH : List Bool) (a : AmbientState) :
    (advance (TM2.step (program d e hd he)))^[MachineTableSplit.exactSteps
      table.vertices table.darts (MachineTableSplit.rowsBits table)]
      (some ⟨some (.inl .copyFirst), clean d e hd he a,
        initialTapes (GraphTables.tableBits table) rawH⟩) =
      some ⟨next .copyHFirst, clean d e hd he a,
        splitTapes table.vertices table.darts (MachineTableSplit.rowsBits table) rawH⟩ := by
  let ambient := (clean d e hd he a).1
  have source := MachineTableSplit.tableTrace table ambient none
  have placed := Placement.trace (Sum.inl : Fin 5 → Tape) splitView (fun _ => rfl)
    (by intro j k h; cases j <;> simp_all [splitView])
    (Sum.inl : MachineTableSplit.Label → Label d e) (next .copyHFirst)
    (initialTapes [] rawH) MachineTableSplit.program (program d e hd he) (fun _ => rfl)
    _ _ _ source
  simp only [Placement.configuration, Placement.label] at placed
  rw [placedTapes, placedTapes] at placed
  simpa only [initialTapes,
    splitTapes, ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using placed

/-- Preserve and copy raw H, emit both output headers from the parsed unary
vertex count, copy the actual fuel field, and initialize_ the physical counter. -/
theorem preparationTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (g h gs : List Bool) (n m : Nat) (a : AmbientState) :
    (advance (TM2.step (program d e hd he)))^[preparationSteps n h]
      (some ⟨next .copyHFirst, clean d e hd he a,
        memory g h gs [] (encodeWord n) (encodeWord m) [] [] [] []⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs h (encodeWord n) (encodeWord m) (encodeWord n) (encodeWord 0) []
          (encodeWords [n, n * (d + e)])⟩ := by
  let b0 := memory g h gs [] (encodeWord n) (encodeWord m) [] [] [] []
  let b1 := memory g h gs h (encodeWord n) (encodeWord m) [] [] [] []
  let b2 := memory g h gs h (encodeWord n) (encodeWord m) [] [] [] (encodeWord ((d + e) * n))
  let b3 := memory g h gs h (encodeWord n) (encodeWord m) [] [] []
    (encodeWords [n, n * (d + e)])
  let b4 := memory g h gs h (encodeWord n) (encodeWord m) (encodeWord n) [] []
    (encodeWords [n, n * (d + e)])
  let ambient := (clean d e hd he a).1
  have hcopy := MachineCopy.copyTrace expanderArchive expanderStream scratch
    (by decide) (by decide) (by decide) false (.inr .copyHFirst) (.inr .copyHSecond)
    (next .countSeed) (program d e hd he) rfl rfl b0 rfl ambient none
  have copyRun : (advance (TM2.step (program d e hd he)))^[2 * (h.length + 1)]
      (some ⟨next .copyHFirst, clean d e hd he a, b0⟩) =
      some ⟨next .countSeed, clean d e hd he a, b1⟩ := by
    simpa only [b0, b1, memory_expanderArchive, memory_expanderStream, next, List.append_nil,
      update_expanderStream, ambient, clean, MachineLazyRows.streamClean,
      MachinePortReindex.clean] using hcopy
  have hcount := MachineUnaryAffineAt.seededAffineTrace vertexCount scratch output
    (by decide) (by decide) (by decide) (d + e) 0
    (.inr .countSeed) (.inr .countScan) (.inr .countRestore) (next .headerSeed)
    (program d e hd he) rfl rfl rfl b1 n [] (by simp [b1, memory, vertexCount]) rfl ambient none
  have countRun : (advance (TM2.step (program d e hd he)))^[2 * (n + 1) + 1]
      (some ⟨next .countSeed, clean d e hd he a, b1⟩) =
      some ⟨next .headerSeed, clean d e hd he a, b2⟩ := by
    simpa only [b1, b2, memory_output, next, List.append_nil, Nat.add_zero, update_output,
      ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using hcount
  have hheader := MachineUnaryAffineAt.seededAffineTrace vertexCount scratch output
    (by decide) (by decide) (by decide) 1 0
    (.inr .headerSeed) (.inr .headerScan) (.inr .headerRestore) (next .fuelSeed)
    (program d e hd he) rfl rfl rfl b2 n [] (by simp [b2, memory, vertexCount]) rfl ambient none
  have headerRun : (advance (TM2.step (program d e hd he)))^[2 * (n + 1) + 1]
      (some ⟨next .headerSeed, clean d e hd he a, b2⟩) =
      some ⟨next .fuelSeed, clean d e hd he a, b3⟩ := by
    simpa only [b2, b3, memory_output, next, Nat.one_mul, Nat.add_zero, update_output,
      Nat.mul_comm (d + e) n, encodeWords, List.append_nil,
      ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using hheader
  have hfuel := MachineUnaryAffineAt.seededAffineTrace vertexCount scratch fuel
    (by decide) (by decide) (by decide) 1 0
    (.inr .fuelSeed) (.inr .fuelScan) (.inr .fuelRestore) (next .vertexSeed)
    (program d e hd he) rfl rfl rfl b3 n [] (by simp [b3, memory, vertexCount]) rfl ambient none
  have fuelRun : (advance (TM2.step (program d e hd he)))^[2 * (n + 1) + 1]
      (some ⟨next .fuelSeed, clean d e hd he a, b3⟩) =
      some ⟨next .vertexSeed, clean d e hd he a, b4⟩ := by
    simpa only [b3, b4, memory_fuel, next, List.append_nil, Nat.one_mul, Nat.add_zero,
      update_fuel, ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using hfuel
  have seedRun : (advance (TM2.step (program d e hd he)))^[1]
      (some ⟨next .vertexSeed, clean d e hd he a, b4⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs h (encodeWord n) (encodeWord m) (encodeWord n) (encodeWord 0) []
          (encodeWords [n, n * (d + e)])⟩ := by
    change some (TM2.stepAux (program d e hd he (.inr .vertexSeed)) _ _) = _
    simp only [program, mainInstruction, TM2.stepAux, b4, memory_vertex,
      update_vertex, next, encodeWord, List.replicate_zero, List.nil_append]
  have all := joinTrace (joinTrace (joinTrace (joinTrace copyRun countRun) headerRun) fuelRun) seedRun
  have count : preparationSteps n h =
      (((2 * (h.length + 1) + (2 * (n + 1) + 1)) + (2 * (n + 1) + 1)) +
        (2 * (n + 1) + 1)) + 1 := by unfold preparationSteps; omega
  rw [count]
  exact all

theorem graphRows_blocks {n d : Nat} (G : PortTables.Table n d) :
    MachineTableSplit.rowsBits (PortTables.graphTable G) = (List.ofFn (oldBlock G)).flatten := by
  change encodeWords ((PortTables.flatRows G).toList.flatMap rowWords) = _
  rw [PreprocessingLazyWords.flatRows_list, encodeWords_flatten_flatMap, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext v
  exact (MachineLazyRows.recordsInput_eq_codec (oldRows G v)).symm

theorem oldVertexTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (v : Fin n) (g h gs hs nv mv f current out : List Bool)
    (a : AmbientState) :
    (advance (TM2.step (program d e hd he)))^[MachineLazyRows.vertexSteps d (d + e) 0 (oldRows G v) out]
      (some ⟨next (.old (0, none)), clean d e hd he a,
        memory g h (oldBlock G v ++ gs) hs nv mv f current [] out⟩) =
      some ⟨next .tailSeed, clean d e hd he a,
        memory g h gs hs nv mv f current [] (out ++ oldOutput G e v)⟩ := by
  have hrun := MachineLazyRows.vertexTrace d hd (d + e) 0 oldTapes oldTapes_injective
    (fun stage => .inr (.old stage)) (next .tailSeed) (program d e hd he) (fun _ => rfl)
    (memory g h gs hs nv mv f current [] []) (row G v)
    (by
      intro i hi7 hi9
      fin_cases i <;> simp_all [oldTapes, memory, tail, oldReverse, relation, scratch,
        dividedCopy, quotient, newReverse, output, rowBuffer, graphStream])
    (a, MachineFixedDivMod.residue e he 0) out
  simpa only [next, oldFrame, MachineLazyRows.recordsInput, List.flatMap_nil, List.nil_append,
    clean, oldBlock, oldRows, oldOutput] using hrun

theorem expanderVertexTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (H : ExpanderTables.Table n e) (v : Fin n) (g h gs hs nv mv f current out : List Bool)
    (a : AmbientState) :
    (advance (TM2.step (program d e hd he)))^[MachineOverlayRows.vertexSteps d e v.val
      (List.ofFn (expanderValues H v)) out]
      (some ⟨next (.expander (0, none)), clean d e hd he a,
        memory g h gs (expanderBlock H v ++ hs) nv mv f current (encodeWord v.val) out⟩) =
      some ⟨next .drainTail, clean d e hd he a,
        memory g h gs hs nv mv f current (encodeWord v.val) (out ++ expanderOutput d H v)⟩ := by
  let source := MachineStateEquiv.program (expanderState AmbientState d e).symm (program d e hd he)
  have code (stage : MachineOverlayRows.VertexLabel e) : source (.inr (.expander stage)) =
      MachineOverlayRows.vertexInstruction d e he expanderTapes
        (fun stage => .inr (.expander stage)) (next .drainTail) stage := by
    change MachineStateEquiv.statement (expanderState AmbientState d e).symm
      (MachineStateEquiv.statement (expanderState AmbientState d e) _) = _
    exact MachineStateEquiv.statement_symm_statement _ _
  have native := MachineOverlayRows.vertexTrace d e he expanderTapes expanderTapes_injective
    (fun stage => .inr (.expander stage)) (next .drainTail) source code
    (memory g h gs hs nv mv f current (encodeWord v.val) []) v.val (expanderValues H v)
    rfl
    (by
      intro i hi0 hi7 hi9
      fin_cases i <;> simp_all [expanderTapes, memory, tail, oldReverse, relation, scratch,
        dividedCopy, quotient, newReverse, output, rowBuffer, expanderStream])
    ((a, MachineRegularOriginalRow.zeroBuffer), MachineFixedDivMod.residue d hd 0) out
  have transported := MachineStateEquiv.trace (expanderState AmbientState d e) source _ _ _ native
  have back : MachineStateEquiv.program (expanderState AmbientState d e) source = program d e hd he :=
    MachineStateEquiv.program_symm_program (expanderState AmbientState d e).symm _
  rw [back] at transported
  simpa only [next, MachineStateEquiv.configuration, expanderState_clean, expanderFrame,
    encodeWords, List.nil_append, expanderBlock, expanderOutput] using transported

theorem tailCopyTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (g h gs hs nv mv f out : List Bool) (k : Nat) (a : AmbientState) :
    (advance (TM2.step (program d e hd he)))^[2 * (k + 1) + 1]
      (some ⟨next .tailSeed, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) [] out⟩) =
      some ⟨next (.expander (0, none)), clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) (encodeWord k) out⟩ := by
  let ambient := (clean d e hd he a).1
  have hrun := MachineUnaryAffineAt.seededAffineTrace vertex scratch tail
    (by decide) (by decide) (by decide) 1 0
    (.inr .tailSeed) (.inr .tailScan) (.inr .tailRestore) (next (.expander (0, none)))
    (program d e hd he) rfl rfl rfl
    (memory g h gs hs nv mv f (encodeWord k) [] out) k []
    (by simp [memory, vertex]) rfl ambient none
  simpa only [memory_tail, next, List.append_nil, Nat.one_mul, Nat.add_zero, update_tail,
    ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using hrun

theorem tailFinishTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (g h gs hs nv mv f out : List Bool) (k : Nat) (a : AmbientState) :
    (advance (TM2.step (program d e hd he)))^[k + 3]
      (some ⟨next .drainTail, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) (encodeWord k) out⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord (k + 1)) [] out⟩ := by
  let ambient := (clean d e hd he a).1
  have hd₀ := MachineDrain.drainTrace tail (.inr .drainTail) (next .increment)
    (program d e hd he) rfl (memory g h gs hs nv mv f (encodeWord k) [] out)
    (encodeWord k) ambient none
  have drain : (advance (TM2.step (program d e hd he)))^[k + 2]
      (some ⟨next .drainTail, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) (encodeWord k) out⟩) =
      some ⟨next .increment, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) [] out⟩ := by
    simpa only [next, encodeWord_length, Nat.add_assoc, update_tail, ambient, clean,
      MachineLazyRows.streamClean, MachinePortReindex.clean] using hd₀
  have increment : (advance (TM2.step (program d e hd he)))^[1]
      (some ⟨next .increment, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) [] out⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord (k + 1)) [] out⟩ := by
    change some (TM2.stepAux (program d e hd he (.inr .increment)) _ _) = _
    simp only [program, mainInstruction, TM2.stepAux, memory_vertex, next,
      update_vertex, encodeWord, List.replicate_succ, List.cons_append]
  have all := joinTrace drain increment
  simpa only [Nat.add_assoc] using all

/-- The complete old/expander pair for one actual vertex, with both physical
stream suffixes and the unchanged unary fuel accounted for. -/
theorem pairTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (v : Fin n)
    (g h gs hs nv mv f out : List Bool) (a : AmbientState) :
    (advance (TM2.step (program d e hd he)))^[pairSteps G H v out]
      (some ⟨next (.old (0, none)), clean d e hd he a,
        memory g h (oldBlock G v ++ gs) (expanderBlock H v ++ hs)
          nv mv f (encodeWord v.val) [] out⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord (v.val + 1)) [] (out ++ outputBlock G H v)⟩ := by
  have h₁ := oldVertexTrace d e hd he G v g h gs (expanderBlock H v ++ hs)
    nv mv f (encodeWord v.val) out a
  have h₂ := tailCopyTrace d e hd he g h gs (expanderBlock H v ++ hs)
    nv mv f (out ++ oldOutput G e v) v.val a
  have h₃ := expanderVertexTrace d e hd he H v g h gs hs nv mv f
    (encodeWord v.val) (out ++ oldOutput G e v) a
  have h₄ := tailFinishTrace d e hd he g h gs hs nv mv f
    ((out ++ oldOutput G e v) ++ expanderOutput d H v) v.val a
  simpa only [pairSteps, outputBlock, List.append_assoc] using
    joinTrace (joinTrace (joinTrace h₁ h₂) h₃) h₄

theorem cleanupTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (g h out : List Bool) (n m : Nat) (a : AmbientState) :
    (advance (TM2.step (program d e hd he)))^[cleanupSteps n m]
      (some ⟨next .drainFuel, clean d e hd he a,
        memory g h [] [] (encodeWord n) (encodeWord m) (encodeWord 0) (encodeWord n) [] out⟩) =
      some ⟨none, clean d e hd he a, memory g h [] [] [] [] [] [] [] out⟩ := by
  let ambient := (clean d e hd he a).1
  have h₁ := MachineDrain.drainTrace fuel (.inr .drainFuel) (next .drainVertex)
    (program d e hd he) rfl
    (memory g h [] [] (encodeWord n) (encodeWord m) [] (encodeWord n) [] out)
    (encodeWord 0) ambient none
  have h₂ := MachineDrain.drainTrace vertex (.inr .drainVertex) (next .drainVertexCount)
    (program d e hd he) rfl
    (memory g h [] [] (encodeWord n) (encodeWord m) [] [] [] out)
    (encodeWord n) ambient none
  have h₃ := MachineDrain.drainTrace vertexCount (.inr .drainVertexCount) (next .drainDartCount)
    (program d e hd he) rfl (memory g h [] [] [] (encodeWord m) [] [] [] out)
    (encodeWord n) ambient none
  have h₄ := MachineDrain.drainTrace dartCount (.inr .drainDartCount) none
    (program d e hd he) rfl (memory g h [] [] [] [] [] [] [] out)
    (encodeWord m) ambient none
  simp only [encodeWord_length, update_fuel, update_vertex, update_vertexCount, update_dartCount] at h₁ h₂ h₃ h₄
  have all := joinTrace (joinTrace (joinTrace h₁ h₂) h₃) h₄
  have hsteps : cleanupSteps n m = ((0 + 1 + 1 + (n + 1 + 1)) + (n + 1 + 1)) + (m + 1 + 1) := by
    unfold cleanupSteps
    omega
  rw [hsteps]
  exact all

/-- Each body premise needed by the generic unary counted-loop theorem is
constructed from the actual old/expander pair execution. -/
theorem loopBodyTraces {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (a : AmbientState) :
    MachineCountedLoop.BodyTraces fuel (.inr .guard) (.inr (.old (0, none)))
      (program d e hd he) [] (fun _ => (clean d e hd he a).1) (fun _ => none)
      (loopBase G H) (loopCost G H) n := by
  intro r hr
  let v : Fin n := ⟨n - (r + 1), by omega⟩
  have hv : v.val + 1 = n - r := by dsimp [v]; omega
  have hinput : MachineUnaryCounter.counterTapes fuel (loopBase G H (r + 1)) r [] =
      memory (PortTables.tableBits G) (rawExpander H)
        (oldBlock G v ++ remaining (oldBlock G) (v.val + 1))
        (expanderBlock H v ++ remaining (expanderBlock H) (v.val + 1))
        (encodeWord n) (encodeWord (n * d)) (encodeWord r) (encodeWord v.val) []
        (outputPrefix G H v.val) := by
    simp only [MachineUnaryCounter.counterTapes, loopBase, List.append_nil, update_fuel]
    change memory _ _ (remaining (oldBlock G) v.val) (remaining (expanderBlock H) v.val)
      _ _ _ _ _ _ = _
    rw [remaining_step (oldBlock G) v, remaining_step (expanderBlock H) v]
  have houtput : MachineUnaryCounter.counterTapes fuel (loopBase G H r) r [] =
      memory (PortTables.tableBits G) (rawExpander H)
        (remaining (oldBlock G) (v.val + 1)) (remaining (expanderBlock H) (v.val + 1))
        (encodeWord n) (encodeWord (n * d)) (encodeWord r) (encodeWord (v.val + 1)) []
        (outputPrefix G H v.val ++ outputBlock G H v) := by
    simp only [MachineUnaryCounter.counterTapes, loopBase, List.append_nil, update_fuel]
    rw [← hv, outputPrefix_step]
  have run := pairTrace d e hd he G H v (PortTables.tableBits G) (rawExpander H)
    (remaining (oldBlock G) (v.val + 1)) (remaining (expanderBlock H) (v.val + 1))
    (encodeWord n) (encodeWord (n * d)) (encodeWord r) (outputPrefix G H v.val) a
  change (advance (TM2.step (program d e hd he)))^[loopCost G H r]
    (some ⟨next (.old (0, none)), clean d e hd he a,
      MachineUnaryCounter.counterTapes fuel (loopBase G H (r + 1)) r []⟩) =
    some ⟨next .guard, clean d e hd he a,
      MachineUnaryCounter.counterTapes fuel (loopBase G H r) r []⟩
  rw [hinput, houtput]
  simpa only [loopCost, dite_eq_left hr, v] using run

theorem loopTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (a : AmbientState) :
    (advance (TM2.step (program d e hd he)))^[MachineCountedLoop.totalSteps (loopCost G H) n]
      (some ⟨next .guard, clean d e hd he a,
        memory (PortTables.tableBits G) (rawExpander H)
          (MachineTableSplit.rowsBits (PortTables.graphTable G)) (rawExpander H)
          (encodeWord n) (encodeWord (n * d)) (encodeWord n) (encodeWord 0) []
          (encodeWords [n, n * (d + e)])⟩) =
      some ⟨next .drainFuel, clean d e hd he a,
        memory (PortTables.tableBits G) (rawExpander H) [] []
          (encodeWord n) (encodeWord (n * d)) (encodeWord 0) (encodeWord n) []
          (PortTables.tableBits (PreprocessingOverlayTables.overlay G H))⟩ := by
  have run := MachineCountedLoop.loopTrace fuel (.inr .guard) (.inr (.old (0, none)))
    (.inr .drainFuel) (program d e hd he) rfl []
    (fun _ => (clean d e hd he a).1) (fun _ => none) (loopBase G H) (loopCost G H) n
    (loopBodyTraces d e hd he G H a)
  have startFrame : MachineUnaryCounter.counterTapes fuel (loopBase G H n) n [] =
      memory (PortTables.tableBits G) (rawExpander H)
        (MachineTableSplit.rowsBits (PortTables.graphTable G)) (rawExpander H)
        (encodeWord n) (encodeWord (n * d)) (encodeWord n) (encodeWord 0) []
        (encodeWords [n, n * (d + e)]) := by
    simp only [MachineUnaryCounter.counterTapes, loopBase, List.append_nil, update_fuel,
      Nat.sub_self, remaining_zero, outputPrefix, prefix_zero]
    simp only [graphRows_blocks, rawExpander, expanderRows_blocks]
  have endFrame : MachineUnaryCounter.counterTapes fuel (loopBase G H 0) 0 [] =
      memory (PortTables.tableBits G) (rawExpander H) [] []
        (encodeWord n) (encodeWord (n * d)) (encodeWord 0) (encodeWord n) []
        (PortTables.tableBits (PreprocessingOverlayTables.overlay G H)) := by
    simp only [MachineUnaryCounter.counterTapes, loopBase, List.append_nil, update_fuel,
      Nat.sub_zero, remaining_end, outputPrefix, prefix_end, tableBits_blocks]
  simp only [MachineCountedLoop.guardConfiguration, MachineCountedLoop.exitConfiguration] at run
  rw [startFrame, endFrame] at run
  simpa only [next, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using run

theorem tableTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (a : AmbientState) :
    (advance (TM2.step (program d e hd he)))^[tableSteps G H]
      (some ⟨some (.inl .copyFirst), clean d e hd he a,
        initialTapes (PortTables.tableBits G) (rawExpander H)⟩) =
      some ⟨none, clean d e hd he a,
        memory (PortTables.tableBits G) (rawExpander H) [] [] [] [] [] [] []
          (PortTables.tableBits (PreprocessingOverlayTables.overlay G H))⟩ := by
  have h₁ := splitTrace d e hd he (PortTables.graphTable G) (rawExpander H) a
  rw [splitTapes_memory] at h₁
  have header : encodeWords [n, n * d] ++ MachineTableSplit.rowsBits (PortTables.graphTable G) =
      PortTables.tableBits G := (MachineTableSplit.tableBits_header_rows (PortTables.graphTable G)).symm
  change (advance (TM2.step (program d e hd he)))^[MachineTableSplit.exactSteps n (n * d)
      (MachineTableSplit.rowsBits (PortTables.graphTable G))]
    (some ⟨some (.inl .copyFirst), clean d e hd he a,
      initialTapes (PortTables.tableBits G) (rawExpander H)⟩) =
    some ⟨next .copyHFirst, clean d e hd he a,
      memory (encodeWords [n, n * d] ++ MachineTableSplit.rowsBits (PortTables.graphTable G))
        (rawExpander H) (MachineTableSplit.rowsBits (PortTables.graphTable G)) []
        (encodeWord n) (encodeWord (n * d)) [] [] [] []⟩ at h₁
  rw [header] at h₁
  have h₂ := preparationTrace d e hd he (PortTables.tableBits G) (rawExpander H)
    (MachineTableSplit.rowsBits (PortTables.graphTable G)) n (n * d) a
  have h₃ := loopTrace d e hd he G H a
  have h₄ := cleanupTrace d e hd he (PortTables.tableBits G) (rawExpander H)
    (PortTables.tableBits (PreprocessingOverlayTables.overlay G H)) n (n * d) a
  exact joinTrace (joinTrace (joinTrace h₁ h₂) h₃) h₄

def tableInTime {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (a : AmbientState) :
    StateTransition.EvalsToInTime (TM2.step (program d e hd he))
      ⟨some (.inl .copyFirst), clean d e hd he a,
        initialTapes (PortTables.tableBits G) (rawExpander H)⟩
      (some ⟨none, clean d e hd he a,
        memory (PortTables.tableBits G) (rawExpander H) [] [] [] [] [] [] []
          (PortTables.tableBits (PreprocessingOverlayTables.overlay G H))⟩)
      ((timePolynomial d e).eval ((PortTables.tableBits G).length + (rawExpander H).length)) where
  steps := tableSteps G H
  evals_in_steps := tableTrace d e hd he G H a
  steps_le_m := tableSteps_le G H

end UniqueGamesTheorem.Foundations.Complexity.MachineOverlayTable

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachinePaddedExpanderFamilyBoundsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamilyBounds

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

def timeCoefficient : Nat :=
  MachineExpanderFamilyBounds.inputCoefficient + PCP.ExpanderFamily.growth + 29

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C timeCoefficient * Polynomial.X^5

theorem timePolynomial_encoding (k : Nat) :
    timePolynomial.eval (encodeWord k).length = timeCoefficient * (k + 1)^5 := by
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, encodeWord_length]

theorem ceilingCost_le (g k : Nat) :
    (MachineCeilingPower.timePolynomial g).eval (encodeWord k).length ≤
      (g + 29) * (k + 1)^5 := by
  rw [MachineCeilingPower.timePolynomial_encoding]
  have squareBound : (k + 1)^2 ≤ (k + 1)^5 :=
    Nat.pow_le_pow_right (Nat.succ_pos k) (by decide)
  have linearBound : k + 1 ≤ (k + 1)^5 := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (Nat.succ_pos k) (show 1 ≤ 5 by decide)
  have constantBound : 1 ≤ (k + 1)^5 := by omega
  have squareCost := Nat.mul_le_mul_left (g + 8) squareBound
  have linearCost := Nat.mul_le_mul_left 18 linearBound
  have constantCost := Nat.mul_le_mul_left 3 constantBound
  unfold MachineCeilingPower.timeBound
  nlinarith only [squareCost, linearCost, constantCost]

theorem combinedCost_le (k : Nat) :
    (MachineCeilingPower.timePolynomial PCP.ExpanderFamily.growth).eval
        (encodeWord k).length +
      MachineExpanderFamilyBounds.inputCoefficient * (k + 1)^5 ≤
        timePolynomial.eval (encodeWord k).length := by
  rw [timePolynomial_encoding]
  have h := ceilingCost_le PCP.ExpanderFamily.growth k
  unfold timeCoefficient
  nlinarith only [h]

def outputWord
    (H : Table (cloudSize PCP.Expanders.baseDegree) PCP.Expanders.baseDegree) (k : Nat) :
    List Bool :=
  encodeWords (rotationWords (family H (PCP.PreprocessingLevels.boundedLevel k)))

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamilyBounds


namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily

open Turing

section TableCoordinates

open PCP.ExpanderTables PCP.ExpanderRowControl

abbrev SmallTable := Table (cloudSize fixedDegree) fixedDegree
abbrev Tape := MachineExpanderFamily.Tape ⊕ MachineCeilingPower.Tape
abbrev Alphabet (_ : Tape) := Bool
abbrev Label := MachineExpanderFamily.Label fixedDegree ⊕ MachineCeilingPower.Label
abbrev State (ρ : Type) := MachineExpanderFamily.State ρ fixedDegree × (Bool × Option Bool)

def familyTape (tape : MachineExpanderFamily.Tape) : Tape := .inl tape

def familyView : Tape → Option MachineExpanderFamily.Tape
  | .inl tape => some tape
  | .inr _ => none

@[simp] theorem familyView_left (tape : MachineExpanderFamily.Tape) :
    familyView (familyTape tape) = some tape := rfl

theorem familyView_right (j : Tape) (tape : MachineExpanderFamily.Tape)
    (h : familyView j = some tape) : familyTape tape = j := by
  cases j with
  | inl j =>
    have hj : j = tape := Option.some.inj h
    subst tape
    rfl
  | inr j => simp [familyView] at h

/-- The only shared tape is the level: the first phase writes the exact word
that the second phase's unary guard consumes. -/
def ceilingTape : MachineCeilingPower.Tape → Tape
  | .level => .inl (.inr .remainingLevel)
  | tape => .inr tape

def ceilingView : Tape → Option MachineCeilingPower.Tape
  | .inl (.inr .remainingLevel) => some .level
  | .inl _ => none
  | .inr .level => none
  | .inr tape => some tape

@[simp] theorem ceilingView_left (tape : MachineCeilingPower.Tape) :
    ceilingView (ceilingTape tape) = some tape := by
  cases tape <;> rfl

theorem ceilingView_right (j : Tape) (tape : MachineCeilingPower.Tape)
    (h : ceilingView j = some tape) : ceilingTape tape = j := by
  cases j with
  | inl j =>
    cases j with
    | inl j => simp [ceilingView] at h
    | inr j =>
      cases j <;> simp_all [ceilingView, ceilingTape]
      cases h
      rfl
  | inr j => cases j <;> simp_all [ceilingView, ceilingTape] <;> cases h <;> rfl

def familyLabel (label : MachineExpanderFamily.Label fixedDegree) : Label := .inl label
def ceilingLabel (label : MachineCeilingPower.Label) : Label := .inr label
def main : Label := .inr .init
def familyEntry : Label := .inl (.inr .initialize_)

def ceilingStates (ρ : Type) :
    MachineCeilingPower.State (MachineExpanderFamily.State ρ fixedDegree) ≃ State ρ :=
  Equiv.prodAssoc _ _ _

@[simp] theorem ceilingStates_apply (ρ : Type)
    (state : MachineCeilingPower.State (MachineExpanderFamily.State ρ fixedDegree)) :
    ceilingStates ρ state = (state.1.1, (state.1.2, state.2)) := rfl

section Placement

variable {ρ : Type} [Fintype ρ]

/-- The family retains the completed ceiling machine's two finite registers. -/
def familySource (H : SmallTable) : MachineExpanderFamily.Label fixedDegree →
    TM2.Stmt MachineExpanderFamily.BoolAlphabet
      (MachineExpanderFamily.Label fixedDegree) (State ρ) :=
  MachineStateFrame.frameProgram (τ := Bool × Option Bool)
    (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one)

/-- The ceiling program preserves the family state as its ambient component. -/
def ceilingSource : MachineCeilingPower.Label →
    TM2.Stmt MachineCeilingPower.Alphabet MachineCeilingPower.Label (State ρ) :=
  MachineStateEquiv.program (ceilingStates ρ)
    (MachineCeilingPower.program PCP.ExpanderFamily.growth)

/-- Actual composition on shared Boolean tapes. No runtime bridge operation
is required, because both programs use the same physical level tape. -/
def program (H : SmallTable) : Label → TM2.Stmt Alphabet Label (State ρ)
  | .inl label =>
    MachineCloudPadding.Placement.statement familyTape familyLabel none (familySource H label)
  | .inr label =>
    MachineCloudPadding.Placement.statement ceilingTape ceilingLabel (some familyEntry)
      (ceilingSource (ρ := ρ) label)

@[simp] theorem program_family (H : SmallTable)
    (label : MachineExpanderFamily.Label fixedDegree) :
    program (ρ := ρ) H (familyLabel label) =
      MachineCloudPadding.Placement.statement familyTape familyLabel none
        (familySource H label) := rfl

@[simp] theorem program_ceiling (H : SmallTable) (label : MachineCeilingPower.Label) :
    program (ρ := ρ) H (ceilingLabel label) =
      MachineCloudPadding.Placement.statement ceilingTape ceilingLabel (some familyEntry)
        (ceilingSource (ρ := ρ) label) := rfl

/-- Initial state for an arbitrary preserved family-state component. -/
def initialState (state : MachineExpanderFamily.State ρ fixedDegree)
    (register : Option Bool) : State ρ := (state, (false, register))

def finalState (H : SmallTable) (state : MachineExpanderFamily.State ρ fixedDegree) : State ρ :=
  (MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H
    (MachineExpanderFamily.caller state), (false, none))

/-- Only the unary request is initially present. -/
def initialTapes (requested : Nat) : Tape → List Bool
  | .inr .input => encodeWord requested
  | _ => []

def retainedCeilingTapes (requested : Nat) : MachineCeilingPower.Tape → List Bool :=
  MachineCeilingPower.memory (encodeWord requested) []
    (encodeWord (PCP.PreprocessingLevels.paddedSize requested)) [] [] [] [] []

def handoffTapes (requested : Nat) : Tape → List Bool
  | .inl tape => MachineExpanderFamily.toBoolTapes
      (MachineExpanderFamily.initialTapes (PCP.PreprocessingLevels.boundedLevel requested) []) tape
  | .inr tape => retainedCeilingTapes requested tape

def finalTapes (H : SmallTable) (requested : Nat) : Tape → List Bool
  | .inl tape => MachineExpanderFamily.toBoolTapes
      (MachineExpanderFamily.familyTapes H (PCP.PreprocessingLevels.boundedLevel requested) []) tape
  | .inr tape => retainedCeilingTapes requested tape

@[simp] theorem initialTapes_input (requested : Nat) :
    initialTapes requested (.inr .input) = encodeWord requested := rfl

@[simp] theorem finalTapes_input (H : SmallTable) (requested : Nat) :
    finalTapes H requested (.inr .input) = encodeWord requested := rfl

@[simp] theorem finalTapes_power (H : SmallTable) (requested : Nat) :
    finalTapes H requested (.inr .power) =
      encodeWord (PCP.PreprocessingLevels.paddedSize requested) := rfl

end Placement

open MachineCloudPadding PCP.ExpanderTableWords

def ceilingInput (requested : Nat) : MachineCeilingPower.Tape → List Bool :=
  MachineCeilingPower.memory (encodeWord requested) [] [] [] [] [] [] []

def ceilingOutput (requested : Nat) : MachineCeilingPower.Tape → List Bool :=
  MachineCeilingPower.memory (encodeWord requested) []
    (encodeWord (PCP.PreprocessingLevels.paddedSize requested)) []
    (encodeWord (PCP.PreprocessingLevels.boundedLevel requested)) [] [] []

def retainedFrame (requested : Nat) : Tape → List Bool
  | .inl _ => []
  | .inr tape => retainedCeilingTapes requested tape

theorem ceiling_initial_tapes (requested : Nat) :
    Placement.tapes ceilingView (ceilingInput requested) (fun _ => []) =
      initialTapes requested := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with tape | tape
    · rfl
    · cases tape <;> rfl
  · cases tape <;> rfl

/-- The produced unary level is already on the exact family input tape. -/
theorem ceiling_handoff_tapes (requested : Nat) :
    Placement.tapes ceilingView (ceilingOutput requested) (fun _ => []) =
      handoffTapes requested := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with tape | tape
    · rcases tape with tape | tape
      · cases tape <;> rfl
      · cases tape <;> rfl
    · cases tape <;>
        simp [Placement.tapes, ceilingView, ceilingOutput, handoffTapes,
          MachineExpanderFamily.toBoolTapes, MachineExpanderFamily.toBoolWord,
          MachineExpanderFamily.initialTapes, MachineEmbedding.tapes,
          MachineCeilingPower.memory]
  · cases tape <;> rfl

theorem family_initial_tapes (requested : Nat) :
    Placement.tapes familyView
      (MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.initialTapes (PCP.PreprocessingLevels.boundedLevel requested) []))
      (retainedFrame requested) = handoffTapes requested := by
  funext tape
  cases tape <;> rfl

theorem family_final_tapes (H : SmallTable) (requested : Nat) :
    Placement.tapes familyView
      (MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.familyTapes H (PCP.PreprocessingLevels.boundedLevel requested) []))
      (retainedFrame requested) = finalTapes H requested := by
  funext tape
  cases tape <;> rfl

theorem ceiling_initial_configuration {ρ : Type} (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) (register : Option Bool) :
    Placement.configuration ceilingView ceilingLabel (some familyEntry) (fun _ => [])
      (MachineStateEquiv.configuration (ceilingStates ρ)
        ⟨some .init, ((state, false), register), ceilingInput requested⟩) =
      ⟨some main, initialState state register, initialTapes requested⟩ := by
  simp only [Placement.configuration, Placement.label, MachineStateEquiv.configuration,
    ceilingStates_apply, ceiling_initial_tapes, ceilingLabel, main, initialState]

/-- Ceiling halt enters the family initializer with no intervening transition. -/
theorem ceiling_handoff_configuration {ρ : Type} (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) :
    Placement.configuration ceilingView ceilingLabel (some familyEntry) (fun _ => [])
      (MachineStateEquiv.configuration (ceilingStates ρ)
        ⟨none, ((state, false), none), ceilingOutput requested⟩) =
      ⟨some familyEntry, (state, (false, none)), handoffTapes requested⟩ := by
  simp only [Placement.configuration, Placement.label, MachineStateEquiv.configuration,
    ceilingStates_apply, ceiling_handoff_tapes]

/-- Static alphabet and state framing of the actual family initial endpoint. -/
theorem family_initial_configuration {ρ : Type} (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) (metadata : Bool × Option Bool) :
    Placement.configuration familyView familyLabel none (retainedFrame requested)
      (MachineStateFrame.frameConfiguration metadata
        (MachineAlphabetTransport.configuration MachineExpanderFamily.alphabet_eq
          ⟨some (.inr .initialize_), state,
            MachineExpanderFamily.initialTapes (PCP.PreprocessingLevels.boundedLevel requested) []⟩)) =
      ⟨some familyEntry, (state, metadata), handoffTapes requested⟩ := by
  rw [MachineExpanderFamily.configuration_toBool]
  simp only [MachineStateFrame.frameConfiguration, Placement.configuration, Placement.label,
    family_initial_tapes, familyEntry, familyLabel]

/-- The family endpoint retains both external ceiling words and its original
normalized state; its remaining-level word is the consumed zero word. -/
theorem family_final_configuration {ρ : Type} (H : SmallTable) (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) :
    Placement.configuration familyView familyLabel none (retainedFrame requested)
      (MachineStateFrame.frameConfiguration (false, none)
        (MachineAlphabetTransport.configuration MachineExpanderFamily.alphabet_eq
          ⟨none,
            MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H
              (MachineExpanderFamily.caller state),
            MachineExpanderFamily.familyTapes H (PCP.PreprocessingLevels.boundedLevel requested) []⟩)) =
      ⟨none, finalState H state, finalTapes H requested⟩ := by
  rw [MachineExpanderFamily.configuration_toBool]
  simp only [MachineStateFrame.frameConfiguration, Placement.configuration, Placement.label,
    family_final_tapes, finalState]

@[simp] theorem handoffTapes_level (requested : Nat) :
    handoffTapes requested (ceilingTape .level) =
      encodeWord (PCP.PreprocessingLevels.boundedLevel requested) := by
  simp [handoffTapes, ceilingTape, MachineExpanderFamily.toBoolTapes,
    MachineExpanderFamily.toBoolWord, MachineExpanderFamily.initialTapes,
    MachineEmbedding.tapes]

@[simp] theorem handoffTapes_level_shadow (requested : Nat) :
    handoffTapes requested (.inr .level) = [] := rfl

@[simp] theorem finalTapes_level_shadow (H : SmallTable) (requested : Nat) :
    finalTapes H requested (.inr .level) = [] := rfl

@[simp] theorem finalTapes_remainingLevel (H : SmallTable) (requested : Nat) :
    finalTapes H requested (ceilingTape .level) = encodeWord 0 := by
  simp [finalTapes, ceilingTape, MachineExpanderFamily.toBoolTapes,
    MachineExpanderFamily.toBoolWord, MachineExpanderFamily.familyTapes,
    MachineExpanderFamily.boundaryTapes, MachineExpanderFamily.extraFrame,
    MachineEmbedding.tapes]

theorem finalTapes_currentSize (H : SmallTable) (requested : Nat) :
    finalTapes H requested (familyTape (.inr .currentSize)) =
      encodeWord (PCP.PreprocessingLevels.paddedSize requested) := by
  change encodeWord (vertexCount (degree fixedDegree)
    (PCP.PreprocessingLevels.boundedLevel requested)) = _
  exact congrArg encodeWord (PCP.PreprocessingLevels.table_vertexCount_eq_paddedSize requested)

theorem finalTapes_table (H : SmallTable) (requested : Nat) :
    finalTapes H requested (familyTape MachineExpanderFamily.tableTape) =
      encodeWords (rotationWords (family H (PCP.PreprocessingLevels.boundedLevel requested))) := rfl

end TableCoordinates


/-!
# Actual requested-size to expander-table computation

One finite program physically computes the padding level and then constructs
the complete corresponding rotation table. The level output of the first
phase is the input tape of the second phase. The actual execution preserves
the request, retains the padded size, and has a fixed polynomial time bound
in the unary request length.
-/

open MachineCloudPadding MachineComposition

variable {ρ : Type} [Fintype ρ]

/-- Actual geometric search, placed onto the eventual family-level tape. -/
noncomputable def ceilingInTime (H : SmallTable) (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some main, initialState state register, initialTapes requested⟩
      (some ⟨some familyEntry, (state, (false, none)), handoffTapes requested⟩)
      ((MachineCeilingPower.timePolynomial PCP.ExpanderFamily.growth).eval
        (encodeWord requested).length) := by
  let original := MachineCeilingPower.paddingInTime requested state register
  let renamed := MachineStateEquiv.execution (ceilingStates ρ)
    (MachineCeilingPower.program PCP.ExpanderFamily.growth) original
  let placed := liftExecutionInTime (TM2.step (ceilingSource (ρ := ρ)))
    (TM2.step (program H))
    (Placement.configuration ceilingView ceilingLabel (some familyEntry) (fun _ => []))
    (Placement.step_simulation ceilingTape ceilingView ceilingView_left ceilingView_right
      ceilingLabel (some familyEntry) (fun _ => []) (ceilingSource (ρ := ρ))
      (program H) (program_ceiling H)) renamed
  have initialEq := ceiling_initial_configuration requested state register
  have finalEq := ceiling_handoff_configuration requested state
  unfold ceilingInput at initialEq
  unfold ceilingOutput at finalEq
  simpa only [initialEq, finalEq] using placed

/-- Actual table materialization consumes the level produced by the preceding
phase while retaining the original request and its computed padded size. -/
noncomputable def materializeInTime (H : SmallTable) (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some familyEntry, (state, (false, none)), handoffTapes requested⟩
      (some ⟨none, finalState H state, finalTapes H requested⟩)
      (MachineExpanderFamilyBounds.inputCoefficient * (requested + 1)^5) := by
  let original := MachineExpanderFamily.paddedFamilyInTime H requested state []
  let boolean := MachineAlphabetTransport.executionInTime MachineExpanderFamily.alphabet_eq
    (MachineExpanderFamily.program MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one) original
  let framed := MachineStateFrame.frameExecution
    (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one) (false, (none : Option Bool)) boolean
  let placed := liftExecutionInTime (TM2.step (familySource H)) (TM2.step (program H))
    (Placement.configuration familyView familyLabel none (retainedFrame requested))
    (Placement.step_simulation familyTape familyView familyView_left familyView_right
      familyLabel none (retainedFrame requested) (familySource H) (program H)
      (program_family H)) framed
  simpa only [family_initial_configuration, family_final_configuration] using placed

/-- A single concrete finite program takes the original unary request all the
way to the exact forward family table. Both phase executions are supplied by
proved machines; there is no construction or runtime hypothesis. -/
noncomputable def paddedInTime (H : SmallTable) (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some main, initialState state register, initialTapes requested⟩
      (some ⟨none, finalState H state, finalTapes H requested⟩)
      (MachinePaddedExpanderFamilyBounds.timePolynomial.eval (encodeWord requested).length) := by
  let first := ceilingInTime H requested state register
  let second := materializeInTime H requested state
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program H))
    _ _ _ _ _ first second
  exact
    { toEvalsTo := all.toEvalsTo
      steps_le_m := all.steps_le_m.trans
        (by simpa only [Nat.add_comm] using
          MachinePaddedExpanderFamilyBounds.combinedCost_le requested) }

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineVertexPadding
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Vertex padding from the original serialized port graph

Header counters, the geometric padding count, and the initial row buffer
are generated by physical tape operations before the checked row emitter.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineVertexPadding

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.PCP
open MachineCloudPadding

def program {σ : Type} (d : Nat) (hd : 0 < d) : Label d → TM2.Stmt Alphabet (Label d) (State σ)
  | .splitCode l => Placement.statement splitTape Label.splitCode (some (.powerCode .init))
      (MachineTableSplit.program l)
  | .powerCode l => Placement.statement powerTape Label.powerCode (some .dartSeed)
      (MachineCeilingPower.program ExpanderFamily.growth l)
  | .dartSeed => MachineUnaryAffineAt.seed .output 0 .dartScan
  | .dartScan => MachineUnaryAffineAt.scan .power .scratch .output d .dartScan .dartRestore
  | .dartRestore => Reduction.MachineTransfer.loopAt
      .scratch .power id false .dartRestore (some .vertexSeed)
  | .vertexSeed => MachineUnaryAffineAt.seed .output 0 .vertexScan
  | .vertexScan => MachineUnaryAffineAt.scan .power .scratch .output 1 .vertexScan .vertexRestore
  | .vertexRestore => Reduction.MachineTransfer.loopAt
      .scratch .power id false .vertexRestore (some .copyFirst)
  | .copyFirst => Reduction.MachineTransfer.loopAt
      .power .scratch id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop
      .scratch .power .fuel false .copySecond (some (.subtractCode .subtract))
  | .subtractCode l => Placement.statement subtractTape Label.subtractCode
      (some (.rowsCode (.inr .initialize_))) (MachineCloudPadding.program l)
  | .rowsCode l => Placement.statement rowTape Label.rowsCode (some .cleanVertex) (rowProgram d hd l)
  | .cleanVertex => MachineDrain.drain .vertex .cleanVertex (some .cleanEdge)
  | .cleanEdge => MachineDrain.drain .edge .cleanEdge (some .cleanPower)
  | .cleanPower => MachineDrain.drain .power .cleanPower (some .cleanRelation)
  | .cleanRelation => MachineDrain.drain .relation .cleanRelation (some .cleanFuel)
  | .cleanFuel => MachineDrain.drain .fuel .cleanFuel none

end UniqueGamesTheorem.Foundations.Complexity.MachineVertexPadding

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachinePaddedOverlay
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Physical composition of vertex padding, expander generation, and overlay

The level produced by vertex padding is the family machine's actual input
stack. The two resulting archives are the overlay machine's actual archive
stacks. Static tape placement and finite-state framing preserve the original
input; no copying or recomputation is hidden in a phase boundary.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlay

open Turing MachineComposition MachineCloudPadding
open PCP

abbrev Tape := MachineVertexPadding.Tape ⊕ (MachineExpanderFamily.Tape ⊕ MachineOverlayTable.Tape)
abbrev Alphabet (_ : Tape) := Bool
abbrev Label (d : Nat) := MachineVertexPadding.Label d ⊕ (MachineExpanderFamily.Label baseDegree ⊕ MachineOverlayTable.Label d overlayDegree)
abbrev State (d : Nat) := MachineVertexPadding.State (MachineExpanderFamily.State Unit baseDegree × MachineOverlayTable.State Unit d overlayDegree)

theorem overlayDegree_positive : 0 < overlayDegree :=
  Nat.mul_pos MachineExpanderFamily.baseDegree_positive MachineExpanderFamily.baseDegree_positive

def paddingTape (k : MachineVertexPadding.Tape) : Tape := .inl k

def paddingView : Tape → Option MachineVertexPadding.Tape
  | .inl k => some k
  | .inr _ => none

@[simp] theorem paddingView_left (k : MachineVertexPadding.Tape) : paddingView (paddingTape k) = some k := rfl

theorem paddingView_right (j : Tape) (k : MachineVertexPadding.Tape)
    (h : paddingView j = some k) : paddingTape k = j := by
  cases j with
  | inl j => cases Option.some.inj h; rfl
  | inr j => simp [paddingView] at h

/-- The family unary guard consumes the padding machine's existing level. -/
def familyTape (k : MachineExpanderFamily.Tape) : Tape :=
  if k = .inr .remainingLevel then .inl .level else .inr (.inl k)

def familyView : Tape → Option MachineExpanderFamily.Tape
  | .inl .level => some (.inr .remainingLevel)
  | .inr (.inl k) => if k = .inr .remainingLevel then none else some k
  | _ => none

@[simp] theorem familyView_left (k : MachineExpanderFamily.Tape) : familyView (familyTape k) = some k := by
  by_cases h : k = .inr .remainingLevel
  · subst k; rfl
  · simp [familyTape, familyView, h]

theorem familyView_right (j : Tape) (k : MachineExpanderFamily.Tape)
    (h : familyView j = some k) : familyTape k = j := by
  rcases j with j | j
  · cases j <;> simp_all [familyView, familyTape]
  · rcases j with j | j
    · by_cases hj : j = .inr .remainingLevel <;> simp_all [familyView, familyTape]
    · simp [familyView] at h

/-- Overlay reads exactly the two archives written by the previous phases. -/
def overlayTape (k : MachineOverlayTable.Tape) : Tape :=
  if k = MachineOverlayTable.graphArchive then .inl .output
  else if k = MachineOverlayTable.expanderArchive then .inr (.inl MachineExpanderFamily.tableTape)
  else .inr (.inr k)

def overlayView : Tape → Option MachineOverlayTable.Tape
  | .inl .output => some MachineOverlayTable.graphArchive
  | .inr (.inl k) => if k = MachineExpanderFamily.tableTape then some MachineOverlayTable.expanderArchive else none
  | .inr (.inr k) =>
      if k = MachineOverlayTable.graphArchive ∨ k = MachineOverlayTable.expanderArchive then none else some k
  | _ => none

@[simp] theorem overlayView_left (k : MachineOverlayTable.Tape) : overlayView (overlayTape k) = some k := by
  by_cases hg : k = MachineOverlayTable.graphArchive
  · subst k; rfl
  · by_cases he : k = MachineOverlayTable.expanderArchive
    · subst k; rfl
    · simp [overlayTape, overlayView, hg, he]

theorem overlayView_right (j : Tape) (k : MachineOverlayTable.Tape)
    (h : overlayView j = some k) : overlayTape k = j := by
  rcases j with j | j
  · cases j <;> simp_all [overlayView, overlayTape, MachineOverlayTable.graphArchive]
  · rcases j with j | j
    · by_cases hj : j = MachineExpanderFamily.tableTape
      · subst j
        have hk : MachineOverlayTable.expanderArchive = k := by
          simpa [overlayView] using h
        subst k
        rfl
      · simp [overlayView, hj] at h
    · by_cases hg : j = MachineOverlayTable.graphArchive
      · simp [overlayView, hg] at h
      · by_cases he : j = MachineOverlayTable.expanderArchive
        · simp [overlayView, he] at h
        · simp_all [overlayView, overlayTape]

variable {d : Nat}

def paddingLabel (l : MachineVertexPadding.Label d) : Label d := .inl l
def familyLabel (l : MachineExpanderFamily.Label baseDegree) : Label d := .inr (.inl l)
def overlayLabel (l : MachineOverlayTable.Label d overlayDegree) : Label d := .inr (.inr l)
def main : Label d := paddingLabel (.splitCode .copyFirst)
def familyEntry : Label d := familyLabel (.inr .initialize_)
def overlayEntry : Label d := overlayLabel (.inl .copyFirst)

def familyStates (d : Nat) :
    (MachineExpanderFamily.State Unit baseDegree × ((MachineOverlayTable.State Unit d overlayDegree × Bool) × Option Bool)) ≃
      State d where
  toFun s := (((s.1, s.2.1.1), s.2.1.2), s.2.2)
  invFun s := (s.1.1.1, ((s.1.1.2, s.1.2), s.2))
  left_inv := by rintro ⟨f, ⟨⟨o, b⟩, r⟩⟩; rfl
  right_inv := by rintro ⟨⟨⟨f, o⟩, b⟩, r⟩; rfl

def overlayStates (d : Nat) :
    (MachineOverlayTable.State Unit d overlayDegree × ((MachineExpanderFamily.State Unit baseDegree × Bool) × Option Bool)) ≃
      State d where
  toFun s := (((s.2.1.1, s.1), s.2.1.2), s.2.2)
  invFun s := (s.1.1.2, ((s.1.1.1, s.1.2), s.2))
  left_inv := by rintro ⟨o, ⟨⟨f, b⟩, r⟩⟩; rfl
  right_inv := by rintro ⟨⟨⟨f, o⟩, b⟩, r⟩; rfl

def familySource (H : BaseTable) (d : Nat) : MachineExpanderFamily.Label baseDegree →
    TM2.Stmt MachineExpanderFamily.BoolAlphabet (MachineExpanderFamily.Label baseDegree) (State d) :=
  MachineStateEquiv.program (familyStates d) (MachineStateFrame.frameProgram
    (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H MachineExpanderFamily.baseDegree_cloud_gt_one))

def overlaySource (d : Nat) (hd : 0 < d) : MachineOverlayTable.Label d overlayDegree →
    TM2.Stmt (fun _ : MachineOverlayTable.Tape => Bool) (MachineOverlayTable.Label d overlayDegree) (State d) :=
  MachineStateEquiv.program (overlayStates d) (MachineStateFrame.frameProgram
    (MachineOverlayTable.program d overlayDegree hd overlayDegree_positive))

def program (H : BaseTable) (d : Nat) (hd : 0 < d) :
    Label d → TM2.Stmt Alphabet (Label d) (State d)
  | .inl l => Placement.statement paddingTape paddingLabel (some familyEntry) (MachineVertexPadding.program d hd l)
  | .inr (.inl l) => Placement.statement familyTape familyLabel (some overlayEntry)
      (familySource H d l)
  | .inr (.inr l) => Placement.statement overlayTape overlayLabel none (overlaySource d hd l)

def clean (H : BaseTable) (d : Nat) (hd : 0 < d) : State d :=
  (((MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H (),
    MachineOverlayTable.clean d overlayDegree hd overlayDegree_positive ()), false), none)

/-- The archives, family count, and level residue are the only retained
non-output stacks. Work stacks, including unused duplicate slots, are empty. -/
def memory (input padded level rotor count output : List Bool) : Tape → List Bool
  | .inl k => MachineVertexPadding.memory input padded [] [] [] level [] [] k
  | .inr (.inl (.inl (.inl .table))) => rotor
  | .inr (.inl (.inr .currentSize)) => count
  | .inr (.inl _) => []
  | .inr (.inr k) => if k = MachineOverlayTable.output then output else []

def rotor (H : BaseTable) (n : Nat) : List Bool :=
  encodeWords (ExpanderTableWords.rotationWords
    (ExpanderTables.family H (PreprocessingLevels.boundedLevel n)))

def initialTapes {n d : Nat} (t : PortTables.Table n d) : Tape → List Bool :=
  memory (PortTables.tableBits t) [] [] [] [] []

def paddedTapes {n d : Nat} (t : PortTables.Table n d) : Tape → List Bool :=
  memory (PortTables.tableBits t) (PortTables.tableBits (padded t))
    (encodeWord (PreprocessingLevels.boundedLevel n)) [] [] []

def familyTapes (H : BaseTable) {n d : Nat} (t : PortTables.Table n d) : Tape → List Bool :=
  memory (PortTables.tableBits t) (PortTables.tableBits (padded t))
    (encodeWord 0) (rotor H n) (encodeWord (PreprocessingLevels.paddedSize n)) []

def finalTapes (H : BaseTable) {n d : Nat} (t : PortTables.Table n d) : Tape → List Bool :=
  memory (PortTables.tableBits t) (PortTables.tableBits (padded t))
    (encodeWord 0) (rotor H n) (encodeWord (PreprocessingLevels.paddedSize n))
    (PortTables.tableBits (PreprocessingStageMaps.paddedOverlay H d ⟨n, t⟩).2)

def placeExecution {K Λ S : Type} [DecidableEq K]
    (tape : K → Tape) (view : Tape → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Label d) (exit : Option (Label d)) (extra : Tape → List Bool)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ S)
    (target : Label d → TM2.Stmt Alphabet (Label d) S)
    (atLabels : ∀ l, target (labels l) = Placement.statement tape labels exit (source l))
    {a b : TM2.Cfg (fun _ : K => Bool) Λ S} {budget : Nat}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step target)
      (Placement.configuration view labels exit extra a)
      (some (Placement.configuration view labels exit extra b)) budget :=
  liftExecutionInTime _ _ _
    (Placement.step_simulation tape view left right labels exit extra source target atLabels) run

theorem padding_initial_memory (input : List Bool) :
    Placement.tapes paddingView (MachineVertexPadding.memory input [] [] [] [] [] [] []) (fun _ => []) =
      memory input [] [] [] [] [] := by
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · rcases k with k | k
      · rcases k with k | k <;> cases k <;> rfl
      · cases k <;> rfl
    · simp [Placement.tapes, paddingView, memory]

theorem padding_final_memory (input output level : List Bool) :
    Placement.tapes paddingView (MachineVertexPadding.memory input output [] [] [] level [] []) (fun _ => []) =
      memory input output level [] [] [] := by
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · rcases k with k | k
      · rcases k with k | k <;> cases k <;> rfl
      · cases k <;> rfl
    · simp [Placement.tapes, paddingView, memory]

theorem family_initial_memory (input output : List Bool) (level : Nat) :
    Placement.tapes familyView
      (MachineExpanderFamily.toBoolTapes (MachineExpanderFamily.initialTapes level []))
      (memory input output (encodeWord level) [] [] []) =
      memory input output (encodeWord level) [] [] [] := by
  funext k
  rcases k with k | k
  · cases k <;> simp [Placement.tapes, familyView, memory,
      MachineVertexPadding.memory, MachineExpanderFamily.toBoolTapes,
      MachineExpanderFamily.toBoolWord, MachineExpanderFamily.initialTapes,
      MachineEmbedding.tapes]
  · rcases k with k | k
    · rcases k with k | k
      · rcases k with k | k <;> cases k <;>
          simp [Placement.tapes, familyView, memory, MachineExpanderFamily.toBoolTapes,
            MachineExpanderFamily.toBoolWord, MachineExpanderFamily.initialTapes,
            MachineExpanderFamily.tableFrame, MachineEmbedding.tapes]
      · cases k <;>
          simp [Placement.tapes, familyView, memory, MachineExpanderFamily.toBoolTapes,
            MachineExpanderFamily.toBoolWord, MachineExpanderFamily.initialTapes,
            MachineEmbedding.tapes]
    · rfl

theorem family_final_memory (H : BaseTable) (input output : List Bool) (level : Nat) :
    Placement.tapes familyView
      (MachineExpanderFamily.toBoolTapes (MachineExpanderFamily.familyTapes H level []))
      (memory input output (encodeWord level) [] [] []) =
      memory input output (encodeWord 0)
        (encodeWords (ExpanderTableWords.rotationWords (ExpanderTables.family H level)))
        (encodeWord (ExpanderTables.vertexCount overlayDegree level)) [] := by
  funext k
  rcases k with k | k
  · cases k <;> simp [Placement.tapes, familyView, memory,
      MachineVertexPadding.memory, MachineExpanderFamily.toBoolTapes,
      MachineExpanderFamily.toBoolWord, MachineExpanderFamily.familyTapes,
      MachineExpanderFamily.boundaryTapes, MachineExpanderFamily.extraFrame,
      MachineEmbedding.tapes]
  · rcases k with k | k
    · rcases k with k | k
      · rcases k with k | k <;> cases k <;>
          simp [Placement.tapes, familyView, memory, MachineExpanderFamily.toBoolTapes,
            MachineExpanderFamily.toBoolWord, MachineExpanderFamily.familyTapes,
            MachineExpanderFamily.boundaryTapes, MachineExpanderFamily.tableFrame,
            MachineEmbedding.tapes]
      · cases k <;>
          simp [Placement.tapes, familyView, memory, MachineExpanderFamily.toBoolTapes,
            MachineExpanderFamily.toBoolWord, MachineExpanderFamily.familyTapes,
            MachineExpanderFamily.boundaryTapes, MachineExpanderFamily.extraFrame,
            MachineEmbedding.tapes, overlayDegree, PreprocessingRegularTables.internalDegree,
            ExpanderRowControl.degree]
    · simp [Placement.tapes, familyView, memory]

/-- The second phase executes the checked family program from the already
materialized level. Its runtime is polynomial in the original vertex count. -/
noncomputable def familyInTime (H : BaseTable) {n d : Nat} (hd : 0 < d)
    (t : PortTables.Table n d) :
    StateTransition.EvalsToInTime (TM2.step (program H d hd))
      ⟨some familyEntry, clean H d hd, paddedTapes t⟩
      (some ⟨some overlayEntry, clean H d hd, familyTapes H t⟩)
      (MachineExpanderFamilyBounds.inputCoefficient * (n + 1)^5) := by
  let f := MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H ()
  let o := MachineOverlayTable.clean d overlayDegree hd overlayDegree_positive ()
  have caller : MachineExpanderFamily.caller f = () := Subsingleton.elim _ _
  have castRun := MachineAlphabetTransport.successfulExecutionInTime
    MachineExpanderFamily.alphabet_eq
    (MachineExpanderFamily.program MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one)
    (MachineExpanderFamily.paddedFamilyInTime H n f [])
  have boolRun : StateTransition.EvalsToInTime
      (TM2.step (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H
        MachineExpanderFamily.baseDegree_cloud_gt_one))
      ⟨some (.inr .initialize_), f, MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.initialTapes (PreprocessingLevels.boundedLevel n) [])⟩
      (some ⟨none, f, MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.familyTapes H (PreprocessingLevels.boundedLevel n) [])⟩)
      (MachineExpanderFamilyBounds.inputCoefficient * (n + 1)^5) := by
    simpa only [MachineExpanderFamily.boolView, MachineExpanderFamily.configuration_toBool,
      caller] using castRun
  have framed := MachineStateFrame.frameExecution
    (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one) ((o, false), (none : Option Bool)) boolRun
  have transported := MachineStateEquiv.execution (familyStates d)
    (MachineStateFrame.frameProgram
      (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H
        MachineExpanderFamily.baseDegree_cloud_gt_one)) framed
  have sourceRun : StateTransition.EvalsToInTime (TM2.step (familySource H d))
      ⟨some (.inr .initialize_), clean H d hd, MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.initialTapes (PreprocessingLevels.boundedLevel n) [])⟩
      (some ⟨none, clean H d hd, MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.familyTapes H (PreprocessingLevels.boundedLevel n) [])⟩)
      (MachineExpanderFamilyBounds.inputCoefficient * (n + 1)^5) := by
    simpa only [familySource, MachineStateEquiv.configuration,
      MachineStateFrame.frameConfiguration, Option.map_some, familyStates,
      Equiv.coe_fn_mk, clean, f, o]
      using transported
  have run := placeExecution familyTape familyView familyView_left familyView_right
    familyLabel (some overlayEntry) (paddedTapes t) (familySource H d) (program H d hd)
    (fun _ => rfl) sourceRun
  have finishRaw := family_final_memory H (PortTables.tableBits t)
    (PortTables.tableBits (padded t)) (PreprocessingLevels.boundedLevel n)
  have hsize : ExpanderTables.vertexCount overlayDegree (PreprocessingLevels.boundedLevel n) =
      PreprocessingLevels.paddedSize n := PreprocessingLevels.table_vertexCount_eq_paddedSize n
  have count : memory (PortTables.tableBits t) (PortTables.tableBits (padded t))
      (encodeWord 0) (rotor H n)
      (encodeWord (ExpanderTables.vertexCount overlayDegree (PreprocessingLevels.boundedLevel n))) [] =
      familyTapes H t :=
    congrArg (fun size => memory (PortTables.tableBits t) (PortTables.tableBits (padded t))
      (encodeWord 0) (rotor H n) (encodeWord size) []) hsize
  have finish := finishRaw.trans count
  simpa only [Placement.configuration, Placement.label, paddedTapes,
    family_initial_memory, finish, familyEntry] using run

theorem rotationWords_resize {n m q : Nat} (h : n = m) (H : ExpanderTables.Table n q) :
    ExpanderTableWords.rotationWords (PreprocessingRegularTables.resizeTable h H) =
      ExpanderTableWords.rotationWords H := by
  cases h
  rfl

theorem rotor_familyAt (H : BaseTable) (n : Nat) :
    MachineOverlayTable.rawExpander (PreprocessingStageMaps.familyAt H n) = rotor H n := by
  unfold MachineOverlayTable.rawExpander PreprocessingStageMaps.familyAt rotor
  exact congrArg encodeWords (rotationWords_resize
    (PreprocessingLevels.table_vertexCount_eq_paddedSize n)
    (ExpanderTables.family H (PreprocessingLevels.boundedLevel n)))

theorem overlay_memory (input graph raw count output : List Bool) :
    Placement.tapes overlayView
      (MachineOverlayTable.memory graph raw [] [] [] [] [] [] [] output)
      (memory input graph (encodeWord 0) raw count []) =
      memory input graph (encodeWord 0) raw count output := by
  funext k
  rcases k with k | k
  · cases k <;> simp [Placement.tapes, overlayView, memory, MachineVertexPadding.memory,
      MachineOverlayTable.memory, MachineOverlayTable.graphArchive]
  · rcases k with k | k
    · rcases k with k | k
      · rcases k with k | k <;> cases k <;>
          simp [Placement.tapes, overlayView, memory, MachineExpanderFamily.tableTape,
            MachineOverlayTable.memory, MachineOverlayTable.expanderArchive]
      · cases k <;>
          simp [Placement.tapes, overlayView, memory, MachineExpanderFamily.tableTape]
    · rcases k with k | k <;> fin_cases k <;>
        simp [Placement.tapes, overlayView, memory, MachineOverlayTable.memory,
          MachineOverlayTable.graphArchive, MachineOverlayTable.expanderArchive,
          MachineOverlayTable.output]

/-- Overlay executes on the two archives physically produced above; only
its output stack changes in the retained outside frame. -/
noncomputable def overlayInTime (H : BaseTable) {n d : Nat} (hd : 0 < d)
    (t : PortTables.Table n d) :
    StateTransition.EvalsToInTime (TM2.step (program H d hd))
      ⟨some overlayEntry, clean H d hd, familyTapes H t⟩
      (some ⟨none, clean H d hd, finalTapes H t⟩)
      ((MachineOverlayTable.timePolynomial d overlayDegree).eval
        ((PortTables.tableBits (padded t)).length + (rotor H n).length)) := by
  let f := MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H ()
  have original := MachineOverlayTable.tableInTime d overlayDegree hd overlayDegree_positive
    (padded t) (PreprocessingStageMaps.familyAt H n) ()
  have framed := MachineStateFrame.frameExecution
    (MachineOverlayTable.program d overlayDegree hd overlayDegree_positive)
    ((f, false), (none : Option Bool))
    original
  have transported := MachineStateEquiv.execution (overlayStates d)
    (MachineStateFrame.frameProgram
      (MachineOverlayTable.program d overlayDegree hd overlayDegree_positive)) framed
  have sourceRun : StateTransition.EvalsToInTime (TM2.step (overlaySource d hd))
      ⟨some (.inl .copyFirst), clean H d hd,
        MachineOverlayTable.initialTapes (PortTables.tableBits (padded t)) (rotor H n)⟩
      (some ⟨none, clean H d hd,
        MachineOverlayTable.memory (PortTables.tableBits (padded t)) (rotor H n)
          [] [] [] [] [] [] []
          (PortTables.tableBits (PreprocessingStageMaps.paddedOverlay H d ⟨n, t⟩).2)⟩)
      ((MachineOverlayTable.timePolynomial d overlayDegree).eval
        ((PortTables.tableBits (padded t)).length + (rotor H n).length)) := by
    simpa only [overlaySource, MachineStateEquiv.configuration,
      MachineStateFrame.frameConfiguration, Option.map_some, overlayStates, Equiv.coe_fn_mk, clean, f,
      rotor_familyAt, PreprocessingStageMaps.paddedOverlay, PreprocessingStageMaps.padding,
      padded] using transported
  have run := placeExecution overlayTape overlayView overlayView_left overlayView_right
    overlayLabel none (familyTapes H t) (overlaySource d hd) (program H d hd)
    (fun _ => rfl) sourceRun
  simpa only [Placement.configuration, Placement.label, familyTapes, finalTapes,
    MachineOverlayTable.initialTapes_memory, overlay_memory, overlayEntry] using run

theorem archive_length_le (H : BaseTable) {n d : Nat} (t : PortTables.Table n d) :
    (PortTables.tableBits (padded t)).length + (rotor H n).length ≤
      (archivePolynomial d).eval (PortTables.tableBits t).length := by
  let m := PreprocessingLevels.paddedSize n
  let s := ExpanderFamily.growth * ((PortTables.tableBits t).length + 1)
  have hm : m ≤ s := MachineVertexPadding.power_length_bound t
  have hmd : m*d ≤ s*d := Nat.mul_le_mul_right d hm
  have hmq : m*overlayDegree ≤ s*overlayDegree := Nat.mul_le_mul_right overlayDegree hm
  have hg := GraphTables.tableBits_length_le (PortTables.graphTable (padded t))
  change (PortTables.tableBits (padded t)).length ≤
    m + m*d + 2 + m*d*(m + m*d + 8192) at hg
  have hg' := hg.trans (Nat.add_le_add
    (Nat.add_le_add_right (Nat.add_le_add hm hmd) 2)
    (Nat.mul_le_mul hmd (Nat.add_le_add_right (Nat.add_le_add hm hmd) 8192)))
  have hr := ExpanderTableWords.encode_rotationWords_length_le
    (PreprocessingStageMaps.familyAt H n)
  change (MachineOverlayTable.rawExpander (PreprocessingStageMaps.familyAt H n)).length ≤
    (m*overlayDegree)*(m*overlayDegree+1) at hr
  rw [rotor_familyAt] at hr
  have hr' := hr.trans (Nat.mul_le_mul hmq (Nat.add_le_add_right hmq 1))
  have h := Nat.add_le_add hg' hr'
  simpa only [archivePolynomial, sizePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat,
    s] using h

noncomputable def familyPolynomial : Polynomial Nat :=
  Polynomial.C MachineExpanderFamilyBounds.inputCoefficient * (Polynomial.X + 1)^5

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  MachineVertexPadding.timePolynomial d + familyPolynomial +
    (MachineOverlayTable.timePolynomial d overlayDegree).comp (archivePolynomial d)

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlay

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularFamily
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Materializing a cloud rotor inside the regularization machine

Core tape 4 contains the unary cloud size and core tape 7 receives the complete
forward rotor table. The actual family computation runs on private tapes;
three retained unary words are then physically drained. All other core tapes
are preserved and all private tapes are empty on return.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily

open Turing MachineComposition
open MachineCloudPadding

abbrev NativeTape := MachinePaddedExpanderFamily.Tape
abbrev Tape := CoreTape ⊕ NativeTape

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialTablesLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit structural numberings of the raw 3SAT incidence graph. Unused
declared variable names are retained; their unary input header pays for them.
The graph has one dummy vertex and one tautological loop, even for an empty
formula. No input-dependent choice of a finite enumeration is made. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialTables

open Target GraphTables

def slotOrder : Slot ≃ Fin 3 where
  toFun
    | .first => 0
    | .second => 1
    | .third => 2
  invFun i := if i = 0 then .first else if i = 1 then .second else .third
  left_inv s := by cases s <;> rfl
  right_inv i := by fin_cases i <;> rfl

def vertexOrder (F : Formula) :
    InitialGraph.Vertex F ≃ Fin (F.variables + F.clauses.length + 1) :=
  ((finSumFinEquiv.sumCongr unitOrder).trans finSumFinEquiv)

def eventOrder (F : Formula) : RandomEvent F ≃ Fin (F.clauses.length * 3) :=
  ((Equiv.refl (Fin F.clauses.length)).prodCongr slotOrder).trans finProdFinEquiv

def dartOrder (F : Formula) : InitialGraph.Dart F ≃ Fin (6 * F.clauses.length + 1) :=
  (((((eventOrder F).prodCongr finTwoEquiv.symm).trans finProdFinEquiv).sumCongr
    unitOrder).trans finSumFinEquiv).trans (finCongr (by omega))

def raw64 (F : Formula) : ConstraintGraph (InitialGraph.Vertex F)
    (InitialGraph.Dart F) AlphabetRetraction.Label64 :=
  AlphabetRetraction.pullback (InitialGraph.raw F) AlphabetRetraction.decode64

def table (F : Formula) : GraphTables.Table :=
  GraphTables.ofEnumeratedGraph (raw64 F) (vertexOrder F) (dartOrder F) labelOrder

@[simp] theorem table_vertices (F : Formula) :
    (table F).vertices = F.variables + F.clauses.length + 1 := rfl

@[simp] theorem table_darts (F : Formula) : (table F).darts = 6 * F.clauses.length + 1 := rfl

end UniqueGamesTheorem.Foundations.PCP.RawInitialTables

/-! Polynomial arithmetic for the actual initial-machine phase counts. The
separate execution theorem must connect these counts to the concrete program. -/

/-! Explicit finite predicates and numeric row words of the initial incidence table.
Every relation retains all 4096 entries, including repetitions. -/

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

namespace UniqueGamesTheorem.Foundations.PCP.RoundTables

def powered (H : BaseTable) (table : GraphTables.Table) : GenericGraphTables.Table alphabet :=
  PoweringTables.table (PreprocessingTables.preprocess H table) walkParameter

def build (H : BaseTable) (table : GraphTables.Table) : GraphTables.Table :=
  AlphabetTable.Table.build (powered H table)

theorem powered_vertices (H : BaseTable) (table : GraphTables.Table) :
    (powered H table).vertices = PreprocessingTables.vertices table := rfl

theorem powered_darts (H : BaseTable) (table : GraphTables.Table) :
    (powered H table).darts = 2 * PreprocessingTables.vertices table *
      PreprocessingTables.degree ^ (walkParameter + 1) := rfl

theorem build_darts_positive (H : BaseTable) (table : GraphTables.Table) :
    0 < (build H table).darts := by
  change 0 < (AlphabetTable.Table.build (powered H table)).darts
  rw [AlphabetTableBounds.build_darts, powered_darts]
  exact Nat.mul_pos (Nat.mul_pos
    (Nat.mul_pos (by decide) (PreprocessingTables.vertices_positive table))
    (Nat.pow_pos degree_positive)) (dartFactor_positive alphabet)

theorem build_size_le (H : BaseTable) (table : GraphTables.Table)
    (ht : 0 < table.darts) :
    (build H table).vertices + (build H table).darts ≤
      sizeFactor * (table.vertices + table.darts) := by
  have hv := PreprocessingTables.vertices_le_of_positive table ht
  have he : (powered H table).vertices + (powered H table).darts =
      PreprocessingTables.vertices table *
        (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1)) := by
    rw [powered_vertices, powered_darts]
    ring
  have hp := Nat.mul_le_mul_right
    (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1)) hv
  calc
    _ ≤ AlphabetGraphBounds.sizeFactor alphabet *
        ((powered H table).vertices + (powered H table).darts) :=
      AlphabetTableBounds.build_total_le (powered H table)
    _ = AlphabetGraphBounds.sizeFactor alphabet *
        (PreprocessingTables.vertices table *
          (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1))) := by rw [he]
    _ ≤ AlphabetGraphBounds.sizeFactor alphabet *
        ((ExpanderFamily.growth ^ 2 * table.darts) *
          (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1))) :=
      Nat.mul_le_mul_left _ hp
    _ = sizeFactor * table.darts := by unfold sizeFactor; ring
    _ ≤ sizeFactor * (table.vertices + table.darts) :=
      Nat.mul_le_mul_left _ (Nat.le_add_left _ _)

abbrev Input := {table : GraphTables.Table // 0 < table.darts}

def step (H : BaseTable) (input : Input) : Input :=
  ⟨build H input.val, build_darts_positive H input.val⟩

def size (input : Input) : Nat := input.val.vertices + input.val.darts

theorem step_size (H : BaseTable) (input : Input) :
    size (step H input) ≤ sizeFactor * size input := build_size_le H input.val input.property

end UniqueGamesTheorem.Foundations.PCP.RoundTables

/-! Gap amplification for the actual numbered table round. The fixed base
expander is the only supplied construction datum with a spectral certificate. -/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Machines_MachineRegularTable
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual regular-table construction

The header subroutine reads the two original graph headers, computes the
padding total by the actual prefix machine, performs unary addition and
constant multiplication, and appends both resulting header fields. The
outer vertex routines are assembled from actual metadata and row programs.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.PCP

namespace Header

def dartsTape : Tape := .inr .darts

end Header

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialMachineReadClause
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Read exactly one concrete six-field CNF clause in the actual global machine,
then execute its real sign-loading instruction. No extra finish transition
is inserted. Every unrelated tape and the unread input suffix are preserved.
-/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause

open Turing Complexity Hastad RawInitialMachineModel

/-- The six actual serialized fields, in name/sign/name/sign/name/sign order. -/
def fieldValue {n : ℕ} (c : Target.Clause n) (j : Fin 6) : ℕ :=
  (Complexity.clauseWords c)[j.val]'(by
    rw [Complexity.clauseWords_length]
    exact j.isLt)

/-- Full caller frame after the clause fields have been consumed. -/
def recordTapes {n : ℕ} (base : Tape → List Bool) (c : Target.Clause n)
    (suffix : List Bool) : Tape → List Bool
  | .input => suffix
  | .field j => encodeWord (fieldValue c j)
  | k => base k

@[simp] theorem recordTapes_input {n : ℕ} (base : Tape → List Bool)
    (c : Target.Clause n) (suffix : List Bool) :
    recordTapes base c suffix .input = suffix := rfl

@[simp] theorem recordTapes_field {n : ℕ} (base : Tape → List Bool)
    (c : Target.Clause n) (suffix : List Bool) (j : Fin 6) :
    recordTapes base c suffix (.field j) = encodeWord (fieldValue c j) := rfl

@[simp] theorem recordTapes_name {n : ℕ} (base : Tape → List Bool)
    (c : Target.Clause n) (suffix : List Bool) (j : Fin 3) :
    recordTapes base c suffix (.field (nameField j)) =
      encodeWord ((c)[j].variableIndex.val) := by
  fin_cases j <;> rfl

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_TableIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Iteration of the concrete stored-table round, with the original formula's
actual initial graph size controlling the number of rounds. -/

namespace UniqueGamesTheorem.Foundations.PCP.TableIteration

open RoundTables
open Target Complexity

def run (H : BaseTable) : Nat → Input → Input := AmplificationIteration.run (step H)

end UniqueGamesTheorem.Foundations.PCP.TableIteration

end

end OAI
end


