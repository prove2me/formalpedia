-- Prove2me | Definitions.Def_OAIQ252P013
-- name    : OAIQ252P013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T07:47:44.552716+00:00
-- url     : https://prove2.me/theorems/4c6664db-082f-4acd-be34-2f0e5060df36
-- title:
--   Definitions bundle OAIQ252P013 of the split of OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 350 declarations of OpenAI's Lean: 103 definitions, 6 inductive types or structures, 2 instances and 239 theorems. The definitions and types are `OAI.PerfectCompleteness.FilledUniformSampler.Exterior`, `OAI.PerfectCompleteness.FilledUniformSampler.evaluate`, `OAI.PerfectCompleteness.FilledUniformSampler.exteriorEquiv`, `OAI.PerfectCompleteness.FilledUniformSampler.filledSplitEquiv`, `OAI.PerfectCompleteness.FixedRows.cutoff`, `OAI.PerfectCompleteness.FixedRows.sourceLength`, `OAI.PerfectCompleteness.OriginalChildBlocks.observed`, `OAI.PerfectCompleteness.OriginalChildBlocks.sourceLaw`, `OAI.PerfectCompleteness.PreliminaryOutput.value`, `OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.emittedBytes`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput.cleanupExecution`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput.computableInPolyTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput.outputsInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCeilingPower.paddingInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPadding.program`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix.paddingView`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix.program`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLazyRows.StreamState`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLazyRows.relationStateEquiv`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLazyRows.streamClean`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLazyRows.streamInstruction`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLazyRows.streamRelationCopy`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLazyRows.vertexInstruction`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLazyTable.State`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLazyTable.clean`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.ceilingInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.ceilingInput`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.ceilingOutput`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalState`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.initialState`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.materializeInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.paddedInTime`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.retainedFrame`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.Alphabet`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.Label`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.NativeTape`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.SmallTable`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.Tape`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.familyTape`, `OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily.familyView` and 69 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `PerfectCompleteness_Construction_OriginalChildBlocks`, `PerfectCompleteness_Foundations_SourceKeyBoundsLemmas`, `PerfectCompleteness_Foundations_WholeCutCallsLemmas`, `PerfectCompleteness_Machines_ExactTargetOnlineEncoding`, `PerfectCompleteness_Reduction_FixedRows`, `PerfectCompleteness_Reduction_PreliminaryOutputLemmas`, `PerfectCompleteness_Sampling_FilledUniformSampler`, `UniqueGames_Machines_FinalCNFLoopLemmas`, `UniqueGames_Machines_MachineCanonicalOutputLemmas`, `UniqueGames_Machines_MachineCeilingPower`, `UniqueGames_Machines_MachineCloudCount`, `UniqueGames_Machines_MachineCloudPadding`, `UniqueGames_Machines_MachineCloudPrefix`, `UniqueGames_Machines_MachineCloudRankLemmas`, `UniqueGames_Machines_MachineLazyRows`, `UniqueGames_Machines_MachineLazyTable`, `UniqueGames_Machines_MachinePaddedExpanderFamilyBoundsLemmas`, `UniqueGames_Machines_MachinePaddedOverlayRuntimeLemmas`, `UniqueGames_Machines_MachineRegularFamily`, `UniqueGames_Machines_MachineRegularInternalRow`, `UniqueGames_Machines_MachineRegularMetadata`, `UniqueGames_Machines_MachineRegularOriginalBody`, `UniqueGames_Machines_MachineRegularOriginalBodyBounds`, `UniqueGames_Machines_MachineRegularOriginalClean`, `UniqueGames_Machines_MachineRegularOriginalRow`, `UniqueGames_Machines_MachineRegularOwnerBody`, `UniqueGames_Machines_MachineRegularOwnerBodyBounds`, `UniqueGames_Machines_MachineRegularOwnerCleanup`, `UniqueGames_Machines_MachineRegularOwnerProgram`, `UniqueGames_Machines_MachineRegularTable`, `UniqueGames_Machines_MachineRegularVertexBlock`, `UniqueGames_PCP_PreprocessingInternalRows`, `UniqueGames_PCP_PreprocessingPaddingWords`, `UniqueGames_PCP_PreprocessingRegularLoopWordsLemmas`, `UniqueGames_PCP_PreprocessingRegularWords`, `UniqueGames_PCP_PreprocessingTablesLemmas`.
--
--   **Imports.** It imports the published bundle `Def_PerfectCompleteness`; the bundles `OAIQ252P007`, `OAIQ252P008`, `OAIQ252P009` and `OAIQ252P010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ252P016` and `OAIQ252P017`.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Computability.Encoding
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Std
import Definitions.Def_PerfectCompleteness
import Definitions.Def_OAIQ252P007
import Definitions.Def_OAIQ252P008
import Definitions.Def_OAIQ252P009
import Definitions.Def_OAIQ252P010

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCeilingPower
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPadding.powerMemory _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCompare.compareInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.ceilingStates_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.ceilingView_left _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_level_shadow _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_remainingLevel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.handoffTapes_level _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.handoffTapes_level_shadow _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.initialTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.program_ceiling _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferLeft_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferRight_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
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

theorem compareStep_zero (g p : Nat) (input saved level fuel spare product : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .compare, ((ambient, flag), register),
        memory input (encodeWord 0) (encodeWord p) saved level fuel spare product⟩ =
      some ⟨some .restore, ((ambient, flag), none),
        memory input [] (encodeWord p) saved level fuel spare product⟩ := by
  change some (TM2.stepAux compareLoop _ _) = _
  simp [compareLoop, TM2.stepAux, memory, encodeWord]

theorem compareStep_succ_zero (g x : Nat) (input saved level fuel spare product : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .compare, ((ambient, flag), register),
        memory input (encodeWord (x + 1)) (encodeWord 0) saved level fuel spare product⟩ =
      some ⟨some .compare, ((ambient, true), none),
        memory input (encodeWord x) (encodeWord 0) saved level fuel spare product⟩ := by
  change some (TM2.stepAux compareLoop _ _) = _
  simp [compareLoop, TM2.stepAux, memory, encodeWord, List.replicate_succ]

theorem compareStep_succ_succ (g x p : Nat) (input saved level fuel spare product : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .compare, ((ambient, flag), register),
        memory input (encodeWord (x + 1)) (encodeWord (p + 1)) saved level fuel spare product⟩ =
      some ⟨some .compare, ((ambient, flag), none),
        memory input (encodeWord x) (encodeWord p) (true :: saved) level fuel spare product⟩ := by
  change some (TM2.stepAux compareLoop _ _) = _
  simp [compareLoop, TM2.stepAux, memory, encodeWord, List.replicate_succ]

/-- The comparison is performed by actual finite-head transitions. -/
theorem compareTrace (g x p : Nat) (input saved level fuel spare product : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step (program g)))^[x + 1]
      (some ⟨some .compare, ((ambient, flag), register),
        memory input (encodeWord x) (encodeWord p) saved level fuel spare product⟩) =
      some ⟨some .restore, ((ambient, overflow flag x p), none),
        memory input [] (encodeWord (p - x))
          (List.replicate (min x p) true ++ saved) level fuel spare product⟩ := by
  induction x generalizing p saved flag register with
  | zero =>
      simpa [overflow] using compareStep_zero g p input saved level fuel spare product ambient flag register
  | succ x ih =>
      rw [Function.iterate_succ_apply]
      change (advance (TM2.step (program g)))^[x + 1]
        (TM2.step (program g) ⟨some .compare, ((ambient, flag), register),
          memory input (encodeWord (x + 1)) (encodeWord p) saved level fuel spare product⟩) = _
      cases p with
      | zero =>
          rw [compareStep_succ_zero]
          simpa [overflow] using ih 0 saved true none
      | succ p =>
          rw [compareStep_succ_succ]
          simpa [overflow, Nat.succ_min_succ, List.replicate_succ', List.append_assoc] using
            ih p (true :: saved) flag none

theorem compareRestoredTrace (g k p : Nat) (level fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[k + min k p + 2]
      (some ⟨some .compare, ((ambient, false), register),
        memory (encodeWord k) (encodeWord k) (encodeWord p) [] level fuel [] []⟩) =
      some ⟨some .decide, ((ambient, decide (p < k)), none),
        memory (encodeWord k) [] (encodeWord p) [] level fuel [] []⟩ := by
  have hc := compareTrace g k p (encodeWord k) [] level fuel [] [] ambient false register
  simp only [overflow, Bool.false_or, List.append_nil] at hc
  let mid := memory (encodeWord k) [] (encodeWord (p - k))
    (List.replicate (min k p) true) level fuel [] []
  have hr := Reduction.MachineTransfer.transferAt_fromTapes Tape.saved Tape.power (by decide)
    id false Label.restore (some Label.decide) (program g) rfl mid (ambient, decide (p < k)) none
  have hsum : min k p + (p - k) = p := by omega
  simp only [mid, memory, List.length_replicate, List.reverse_replicate, List.map_id,
    Reduction.MachineTransfer.tapesAt, update_saved, update_power] at hr
  rw [replicate_encodeWord, hsum] at hr
  rw [show k + min k p + 2 = (min k p + 1) + (k + 1) by omega,
    Function.iterate_add_apply, hc]
  exact hr

theorem scaleStep_succ (g p b : Nat) (input level fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .scale, ((ambient, false), register),
        memory input [] (encodeWord (p + 1)) [] level fuel [] (List.replicate b true)⟩ =
      some ⟨some .scale, ((ambient, false), some true),
        memory input [] (encodeWord p) [] level fuel [] (List.replicate (g + b) true)⟩ := by
  change some (TM2.stepAux (scaleLoop g) _ _) = _
  simp [scaleLoop, TM2.stepAux, memory, encodeWord, List.replicate_succ,
    Reduction.MachineSubstitution.stepAux_pushWord]

theorem scaleStep_zero (g b : Nat) (input level fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .scale, ((ambient, false), register),
        memory input [] (encodeWord 0) [] level fuel [] (List.replicate b true)⟩ =
      some ⟨some .transfer, ((ambient, false), none),
        memory input [] (encodeWord 0) [] (true :: level) fuel [] (List.replicate b true)⟩ := by
  change some (TM2.stepAux (scaleLoop g) _ _) = _
  simp [scaleLoop, TM2.stepAux, memory, encodeWord]

theorem scaleScanTrace (g p b : Nat) (input level fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[p + 1]
      (some ⟨some .scale, ((ambient, false), register),
        memory input [] (encodeWord p) [] level fuel [] (List.replicate b true)⟩) =
      some ⟨some .transfer, ((ambient, false), none),
        memory input [] (encodeWord 0) [] (true :: level) fuel [] (List.replicate (g * p + b) true)⟩ := by
  induction p generalizing b register with
  | zero => simpa using scaleStep_zero g b input level fuel ambient register
  | succ p ih =>
      rw [Function.iterate_succ_apply]
      change (advance (TM2.step (program g)))^[p + 1]
        (TM2.step (program g) ⟨some .scale, ((ambient, false), register),
          memory input [] (encodeWord (p + 1)) [] level fuel [] (List.replicate b true)⟩) = _
      rw [scaleStep_succ, ih]
      have h : g * p + (g + b) = g * (p + 1) + b := by rw [Nat.mul_succ]; omega
      rw [h]

/-- The fixed-coefficient unary multiplication is an actual scan and transfer;
the level increment is one explicit push in the final scan transition. -/
theorem scaleTrace (g k p e : Nat) (fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[p + g * p + 2]
      (some ⟨some .scale, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) fuel [] []⟩) =
      some ⟨some .guard, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord (p * g)) [] (encodeWord (e + 1)) fuel [] []⟩ := by
  have hs := scaleScanTrace g p 0 (encodeWord k) (encodeWord e) fuel ambient register
  simp only [List.replicate_zero, Nat.add_zero] at hs
  let mid := memory (encodeWord k) [] (encodeWord 0) [] (true :: encodeWord e) fuel []
    (List.replicate (g * p) true)
  have ht := Reduction.MachineTransfer.transferAt_fromTapes Tape.product Tape.power (by decide)
    id false Label.transfer (some Label.guard) (program g) rfl mid (ambient, false) none
  simp only [mid, memory, List.length_replicate, List.reverse_replicate, List.map_id,
    Reduction.MachineTransfer.tapesAt, update_product, update_power,
    replicate_encodeWord, Nat.add_zero] at ht
  have he : true :: encodeWord e = encodeWord (e + 1) := by simp [encodeWord, List.replicate_succ]
  rw [he, Nat.mul_comm g p] at ht
  rw [he, Nat.mul_comm g p] at hs
  have h := appendTrace (advance (TM2.step (program g))) hs ht
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm] using h

theorem cleanupTrace (g k p e f : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[f + 2]
      (some ⟨some .cleanup, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) [] [] []⟩ := by
  have h := MachineDrain.drainTrace Tape.fuel Label.cleanup none (program g) rfl
    (memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) [] [] [])
    (encodeWord f) (ambient, false) register
  simpa only [encodeWord_length, update_fuel, Nat.add_assoc] using h

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

theorem decideStep (g k p e f : Nat) (ambient : σ) :
    TM2.step (program g)
      ⟨some .decide, ((ambient, decide (p < k)), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ =
      some ⟨some (if k ≤ p then Label.cleanup else Label.scale), ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ := by
  by_cases h : k ≤ p
  · have hn : ¬p < k := by omega
    simp [TM2.step, program, TM2.stepAux, h, hn]
  · have hn : p < k := by omega
    simp [TM2.step, program, TM2.stepAux, h, hn]

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
      · simp only [h, ite_false, if_false] at hpref
        have hscale := scaleTrace g k p e (encodeWord f) ambient none
        have hrun := appendTrace _ hpref (appendTrace _ hscale (ih (e + 1) (p * g) none))
        simpa only [coreTime, PreprocessingLevels.levelLoop, h, ite_false, if_false] using hrun

theorem initStep (g k : Nat) (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩ =
      some ⟨some .fuelFirst, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord 1) [] (encodeWord 0) [] [] []⟩ := by
  change some (TM2.stepAux (program g .init) _ _) = _
  simp [program, TM2.stepAux, memory, encodeWord]

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
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCloudCount
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudCount

open Turing
open MachineComposition

variable {Λ σ : Type}

open UniqueGamesTheorem.Foundations.PCP

theorem rowList_cloud_count (t : GraphTables.Table) (v : Fin t.vertices) :
    ((GraphTables.rowList t).filter (fun r => decide (r.tail = v))).length =
      PreprocessingCloudIndex.cloudSize t v := by
  rw [rowList_eq_finRange_map, List.filter_map, List.length_map]
  rfl

theorem tableRows_hits (t : GraphTables.Table) (v : Fin t.vertices) :
    rowsHits v.val (tableRows t) = PreprocessingCloudIndex.cloudSize t v := by
  rw [rowsHits_eq_filter]
  simp only [tableRows, List.filter_map, List.length_map]
  simpa only [Function.comp_def, Fin.val_inj] using rowList_cloud_count t v

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
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCloudPadding
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix.frame_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix.frame_level _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix.frame_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix.frame_query _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix.update_frame_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix.update_frame_level _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix.update_frame_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix.update_frame_query _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_remainingLevel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.handoffTapes_level _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.initialTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.program_ceiling _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
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

def program : Label → TM2.Stmt Alphabet Label (State σ)
  | .init => .push .count (fun _ => false) (.goto fun _ => .countCode .copyFirst)
  | .countCode l => Placement.statement countTape Label.countCode (some .branch)
      (MachineCloudCount.program l)
  | .branch => .peek .count (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.load (fun state => (state.1, none)) (.goto fun _ => .powerCode .init))
        (.push .power (fun _ => false) (.push .level (fun _ => false)
          (.load (fun state => (state.1, none)) .halt))))
  | .powerCode l => Placement.statement powerTape Label.powerCode (some .subtract)
      (MachineCeilingPower.program ExpanderFamily.growth l)
  | .subtract => subtractLoop
  | .restore => Reduction.MachineTransfer.loopAt
      .scratch .count id false .restore none

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

theorem subtractStep_zero (table query level saved : List Bool) (p : Nat)
    (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some .subtract, ((ambient, false), register),
        memory table query (encodeWord 0) [] saved [] (encodeWord p) level [] []⟩ =
      some ⟨some .restore, ((ambient, false), none),
        memory table query (encodeWord 0) [] saved [] (encodeWord p) level [] []⟩ := by
  change some (TM2.stepAux subtractLoop _ _) = _
  simp [subtractLoop, TM2.stepAux, memory, encodeWord]

theorem subtractStep_succ (table query level saved : List Bool) (k p : Nat)
    (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some .subtract, ((ambient, false), register),
        memory table query (encodeWord (k + 1)) [] saved [] (encodeWord (p + 1)) level [] []⟩ =
      some ⟨some .subtract, ((ambient, false), none),
        memory table query (encodeWord k) [] (true :: saved) [] (encodeWord p) level [] []⟩ := by
  change some (TM2.stepAux subtractLoop _ _) = _
  simp [subtractLoop, TM2.stepAux, memory, encodeWord, List.replicate_succ]

theorem subtractScanTrace (table query level : List Bool) (k p : Nat)
    (saved : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[k + 1]
      (some ⟨some .subtract, ((ambient, false), register),
        memory table query (encodeWord k) [] saved [] (encodeWord (k + p)) level [] []⟩) =
      some ⟨some .restore, ((ambient, false), none),
        memory table query (encodeWord 0) [] (List.replicate k true ++ saved) []
          (encodeWord p) level [] []⟩ := by
  induction k generalizing saved register with
  | zero => simpa only [Nat.zero_add, Function.iterate_one, advance_some,
      List.replicate_zero, List.nil_append] using
      subtractStep_zero table query level saved p ambient register
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    simp only [Nat.succ_add]
    change (advance (TM2.step program))^[k + 1]
      (TM2.step program ⟨some .subtract, ((ambient, false), register),
        memory table query (encodeWord (k + 1)) [] saved []
          (encodeWord ((k + p) + 1)) level [] []⟩) = _
    rw [subtractStep_succ]
    simpa only [List.replicate_succ', List.append_assoc, List.singleton_append] using
      ih (true :: saved) none

/-- Physical unary subtraction preserves the complete count word by moving
its consumed tallies to scratch and then transferring them back. -/
theorem subtractTrace (table query level : List Bool) (k p : Nat) (hkp : k ≤ p)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * k + 2]
      (some ⟨some .subtract, ((ambient, false), register),
        memory table query (encodeWord k) [] [] [] (encodeWord p) level [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory table query (encodeWord k) [] [] [] (encodeWord (p - k)) level [] []⟩ := by
  have hs := subtractScanTrace table query level k (p - k) [] ambient register
  rw [show k + (p - k) = p by omega] at hs
  simp only [List.append_nil] at hs
  let mid := memory table query (encodeWord 0) [] (List.replicate k true) []
    (encodeWord (p - k)) level [] []
  have hr := Reduction.MachineTransfer.transferAt_fromTapes Tape.scratch Tape.count (by decide)
    id false Label.restore none program rfl mid (ambient, false) none
  simp only [mid, memory, List.length_replicate, List.reverse_replicate, List.map_id,
    Reduction.MachineTransfer.tapesAt, update_scratch, update_count] at hr
  rw [MachineCeilingPower.replicate_encodeWord, Nat.add_zero] at hr
  have h := appendTrace _ hs hr
  simpa only [show (k + 1) + (k + 1) = 2 * k + 2 by omega, Nat.add_zero] using h

theorem branchStep_zero (table query : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some .branch, ((ambient, false), register),
        memory table query (encodeWord 0) [] [] [] [] [] [] []⟩ =
      some ⟨none, ((ambient, false), none),
        memory table query (encodeWord 0) [] [] [] (encodeWord 0) (encodeWord 0) [] []⟩ := by
  simp [TM2.step, program, TM2.stepAux, memory, encodeWord]

theorem branchStep_succ (table query : List Bool) (k : Nat) (ambient : σ)
    (register : Option Bool) :
    TM2.step program
      ⟨some .branch, ((ambient, false), register),
        memory table query (encodeWord (k + 1)) [] [] [] [] [] [] []⟩ =
      some ⟨some (.powerCode .init), ((ambient, false), none),
        memory table query (encodeWord (k + 1)) [] [] [] [] [] [] []⟩ := by
  simp [TM2.step, program, TM2.stepAux, memory, encodeWord, List.replicate_succ]

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
    simpa only [postTime, Nat.succ_ne_zero, ite_false, if_false, padding,
      PreprocessingLevels.cloudPaddedSize_of_pos (Nat.succ_pos k)] using h

theorem initStep (table query : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some .init, ((ambient, false), register), memory table query [] [] [] [] [] [] [] []⟩ =
      some ⟨some (.countCode .copyFirst), ((ambient, false), register),
        memory table query (encodeWord 0) [] [] [] [] [] [] []⟩ := by
  simp [TM2.step, program, TM2.stepAux, memory, encodeWord]

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

theorem totalTime_le (t : GraphTables.Table) (v : Fin t.vertices) (suffix : List Bool) :
    totalTime t v ≤ timePolynomial.eval (inputLength t v suffix) := by
  have hc := MachineCloudCount.totalSteps_le t.vertices t.darts v.val (MachineCloudCount.tableRows t)
  rw [MachineCloudCount.tableRows_input] at hc
  have hp := postTime_le (PreprocessingCloudIndex.cloudSize t v)
  have hk := count_length_le t v suffix
  have ht := table_length_le t v suffix
  have hsq := Nat.mul_le_mul_left (ExpanderFamily.growth + 8)
    (Nat.pow_le_pow_left hk 2)
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]
  unfold MachineCeilingPower.timeBound at hp
  unfold totalTime
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudPadding

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_FinalCNFLoopLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

/-!
The complete actual output-producing trace of the final CNF machine. Its
terminal configuration still contains private work tapes; FinalCNFCleanup
supplies the subsequent canonical halt required by the machine interface.
-/

open Turing PCP PCP.AlphabetTable FinalCNFTableAdapter

def emittedBytes (plan : Plan) (table : GraphTables.Table) : List Bool :=
  encodeWords [6 * table.vertices + 36864 * table.darts, 40960 * table.darts] ++
    outputStream plan table (List.finRange table.darts)

end UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingTablesLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Bounds on actual metadata, stored rotor words, and emitted prefixes. These
are size estimates used inside separately proved machine executions. -/
namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingMachineBounds
open PreprocessingRegularTables PreprocessingCloudIndex
open UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators

theorem cloudRotorBits_le (t : GraphTables.Table) (v : Fin t.vertices) {q : Nat}
    (table : ExpanderTables.Table (cloudSize t v + padding t v) q) :
    (encodeWords (ExpanderTableWords.rotationWords table)).length ≤
      (rotorPolynomial q).eval (inputLength t) := by
  have hd : (cloudSize t v + padding t v) * q ≤
      (ExpanderFamily.growth * q) * inputLength t := by
    calc
      _ ≤ (ExpanderFamily.growth * inputLength t) * q :=
        Nat.mul_le_mul_right _ (cloudTotal_le_input t v)
      _ = _ := by ac_rfl
  have h := (ExpanderTableWords.encode_rotationWords_length_le table).trans
    (Nat.mul_le_mul hd (Nat.add_le_add_right hd 1))
  simpa only [rotorPolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one] using h

end UniqueGamesTheorem.Foundations.PCP.PreprocessingMachineBounds

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingInternalRows
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows

open DegreeReplacement PreprocessingCloudIndex PreprocessingRegularTables

variable (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)

/-- Decode the returned cloud index into its actual global padded dart. -/
def destination (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    PaddedCloud t padding v :=
  paddedCloudSelect t padding v (localStep t padding tables v x p).1

/-- The reindexed local cloud graph is exactly the stored local lookup. -/
theorem cloud_rotation (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (cloudGraphs t padding tables v).rot (x, p) =
      (destination t padding tables v x p, (localStep t padding tables v x p).2) := by
  have h := GraphTransport.reindex_rot (ExpanderTables.graph (tables v))
    (paddedCloudEquiv t padding v).symm (Equiv.refl _)
    (paddedCloudRank t padding v x) p
  simpa only [cloudGraphs, ExpanderTables.graph_rot, Equiv.refl_apply,
    paddedCloudRank, paddedCloudSelect, Equiv.symm_apply_apply, destination, localStep] using h

/-- The actual global replacement rotation uses that same lookup and select. -/
theorem source_rotation (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (sourcePortGraph t padding tables).rot (x.val, .inl p) =
      ((destination t padding tables v x p).val,
        .inl (localStep t padding tables v x p).2) := by
  rcases x with ⟨x, hx⟩
  subst v
  exact congrArg
    (fun z : PaddedCloud t padding
        ((paddedGraph (GraphTables.semantics t) (fun v => Fin (padding v))).tail x) × Fin q =>
      (z.1.val, (Sum.inl z.2 : Fin q ⊕ Unit)))
    (cloud_rotation t padding tables _ ⟨x, rfl⟩ p)

/-- Full output rotation, retaining the actual return port. -/
theorem rotation_internal (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    PortTables.rotation (ofCloudTables t padding tables)
        (vertexOrder t padding x.val, portOrder q (.inl p)) =
      (vertexOrder t padding (destination t padding tables v x p).val,
        portOrder q (.inl (localStep t padding tables v x p).2)) := by
  rw [rotation_ofCloudTables, source_rotation t padding tables v x p]

/-- The stored global reverse index is the row-major encoding of the destination. -/
theorem reverseIndex_internal (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    ((ofCloudTables t padding tables).reverseIndex[rowIndex t padding v x p]).val =
      (q + 1) * (vertexOrder t padding (destination t padding tables v x p).val).val +
        (localStep t padding tables v x p).2.val := by
  unfold rowIndex
  rw [← PortTables.rowIndex_rotation, rotation_internal t padding tables v x p,
    PortTables.rowIndex_val, portOrder_internal]
  dsimp only
  omega

theorem row_reverse (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (row t padding tables v x p).reverseIndex.val =
      (q + 1) * (vertexOrder t padding (destination t padding tables v x p).val).val +
        (localStep t padding tables v x p).2.val := by
  simpa only [row, PortTables.flatRows, Vector.getElem_ofFn, Fin.getElem_fin] using
    reverseIndex_internal t padding tables v x p

/-- Rank/select destination decoding agrees with the prefix-offset formula. -/
theorem selectedIndex_eq (v : Fin t.vertices) (i : Fin (cloudSize t v + padding v)) :
    (vertexOrder t padding (paddedCloudSelect t padding v i).val).val =
      selectedIndex t padding v i := by
  unfold selectedIndex
  split
  · rename_i hi
    have he : i = Fin.castAdd (padding v) (⟨i.val, hi⟩ : Fin (cloudSize t v)) := Fin.ext rfl
    refine (congrArg (fun j =>
      (vertexOrder t padding (paddedCloudSelect t padding v j).val).val) he).trans ?_
    rw [paddedCloudSelect_castAdd]
    rfl
  · rename_i hi
    have hj : i.val - cloudSize t v < padding v := by have h := i.isLt; omega
    have he : i = Fin.natAdd (cloudSize t v) (⟨i.val - cloudSize t v, hj⟩ : Fin (padding v)) := by
      apply Fin.ext
      dsimp only [Fin.val_natAdd]
      omega
    refine (congrArg (fun j =>
      (vertexOrder t padding (paddedCloudSelect t padding v j).val).val) he).trans ?_
    rw [paddedCloudSelect_natAdd]
    change (vertexOrder t padding
      (Sum.inr ⟨v, (⟨i.val - cloudSize t v, hj⟩ : Fin (padding v))⟩)).val = _
    exact PreprocessingPaddingOffsets.vertexOrder_dummy_val t padding v _

/-- Dummy target indices use the checked prefix offset and local index. -/
theorem selectedIndex_dummy (v : Fin t.vertices) (i : Fin (cloudSize t v + padding v))
    (hi : cloudSize t v ≤ i.val) :
    selectedIndex t padding v i =
      t.darts + PreprocessingPaddingOffsets.offset padding v.val + (i.val - cloudSize t v) := by
  simp only [selectedIndex, dite_eq_right (Nat.not_lt_of_ge hi)]

/-- Closed arithmetic reverse field for the row machine. -/
theorem row_reverse_selectedIndex (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (row t padding tables v x p).reverseIndex.val =
      (q + 1) * selectedIndex t padding v (localStep t padding tables v x p).1 +
        (localStep t padding tables v x p).2.val := by
  rw [row_reverse]
  unfold destination
  rw [selectedIndex_eq]

end UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCanonicalOutputLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_words _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_get _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_row _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_remainingLevel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.handoffTapes_level _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.initialTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.cursorBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.prefixBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rowList_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rows_at _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderTableWords.decode_rotationWords _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_oldCloudIndex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.mem_cloudDarts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.actualRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
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

end UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTableRows

open Turing
open PCP.GraphTables

variable {K Λ σ : Type} [DecidableEq K]

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

theorem rowBits_eq_graph_row {n m : Nat} (v : Fin n) (e : Fin m) :
    rowBits v.val e.val = encodeWords (rowWords (⟨v, e, trueRelation⟩ : DartRow n m)) := by
  rw [MachineTableRows.rowBits_eq]
  rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineDummyRows

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingPaddingWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact serialization of whole-vertex padding

The original dart rows remain in their original order, with every old tail,
reverse index, and relation bit unchanged. The suffix is exactly the bit stream
emitted by the checked dummy-vertex machine, starting at vertex `n` and dart
`n*d`. This is an equality for the actual table codec, with no runtime premise.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingWords

open Complexity PortTables

variable {n m d : Nat}

/-- Recover the original flat row from its exact mixed-radix coordinates. -/
theorem rowBits_flat (table : Table n d) (i : Fin (n * d)) :
    encodeWords (GraphTables.rowWords ((flatRows table)[i])) =
      rowBits table ((rowIndex n d).symm i).1 ((rowIndex n d).symm i).2 := by
  simp only [flatRows, Vector.getElem_ofFn, Fin.getElem_fin,
    MachineTableRows.rowBits_eq, rowBits, Prod.eta, Equiv.apply_symm_apply]

/-- Serializing all rows agrees with grouping their bits by vertex and port. -/
theorem rowsBits_eq_vertices (table : Table n d) :
    rowsBits table = (List.ofFn (fun v : Fin n => vertexBits table v)).flatten := by
  have hflat : (flatRows table).toList =
      List.ofFn (fun i : Fin (n * d) => (flatRows table)[i]) := by
    simp only [flatRows, Vector.toList_ofFn, Vector.getElem_ofFn, Fin.getElem_fin]
  unfold rowsBits
  rw [hflat, encodeWords_flatMap, List.flatMap_def, List.map_ofFn]
  change (List.ofFn (fun i : Fin (n * d) =>
    encodeWords (GraphTables.rowWords ((flatRows table)[i])))).flatten = _
  simp_rw [rowBits_flat]
  simpa only [Equiv.symm_apply_apply, vertexBits] using
    flatten_ofFn_rowIndex (fun i : Fin (n * d) =>
      rowBits table ((rowIndex n d).symm i).1 ((rowIndex n d).symm i).2)

end UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingWords

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingRegularWords
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complete serialization of the actual regularized table

Each global vertex emits its internal ports in increasing order, then its
inherited port. Original darts are the first global vertices. Dummy vertices
follow in increasing owner and local-dummy order. These are identities for the
actual stored rows and existing codec, with arbitrary actual cloud tables.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords

open DegreeReplacement PreprocessingCloudIndex PreprocessingRegularTables Complexity
open scoped BigOperators

variable (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)

/-- The inherited original row keeps the complete input predicate. -/
theorem inherited_original_words (e : Fin t.darts) :
    GraphTables.rowWords (actualRow t padding tables (.inl e) (.inr ())) =
      [e.val, (q + 1) * t.rows[e].reverseIndex.val + q] ++
        GraphTables.relationWords t.rows[e].relation := by
  simp only [GraphTables.rowWords, actualRow_tail, vertexOrder_original,
    inherited_original_reverse, inherited_original_relation]

/-- The inherited dummy row is an always-accepting self-loop. -/
theorem inherited_dummy_words (v : Fin t.vertices) (j : Fin (padding v)) :
    GraphTables.rowWords (actualRow t padding tables (.inr ⟨v, j⟩) (.inr ())) =
      [t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val,
        (q + 1) * (t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val) + q] ++
        GraphTables.relationWords MachineDummyRows.trueRelation := by
  simp only [GraphTables.rowWords, actualRow_tail,
    PreprocessingPaddingOffsets.vertexOrder_dummy_val,
    inherited_dummy_reverse, inherited_dummy_relation]

/-- Per-row serialization agrees with the generic table codec. -/
theorem actualRow_bits (x : Vertex t padding) (p : Fin q ⊕ Unit) :
    encodeWords (GraphTables.rowWords (actualRow t padding tables x p)) =
      PreprocessingPaddingWords.rowBits (ofCloudTables t padding tables)
        (vertexOrder t padding x) (portOrder q p) := by
  simpa only [actualRow, Equiv.symm_apply_apply] using
    PreprocessingPaddingWords.rowBits_flat (ofCloudTables t padding tables)
      (PortTables.rowIndex _ _ (vertexOrder t padding x, portOrder q p))

/-- Each block uses exactly the port order of the actual stored table. -/
theorem vertexBits_eq (x : Vertex t padding) :
    vertexBits t padding tables x =
      PreprocessingPaddingWords.vertexBits (ofCloudTables t padding tables)
        (vertexOrder t padding x) := by
  unfold vertexBits vertexRows
  rw [List.flatMap_append, encodeWords_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [encodeWords_flatMap, List.flatMap_def, List.map_ofFn]
  change (List.ofFn (fun p : Fin q =>
    encodeWords (GraphTables.rowWords (actualRow t padding tables x (.inl p))))).flatten ++
      encodeWords (GraphTables.rowWords (actualRow t padding tables x (.inr ()))) = _
  simp_rw [actualRow_bits]
  unfold PreprocessingPaddingWords.vertexBits
  rw [List.ofFn_succ_last, List.flatten_append]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  rfl

/-- The explicit padding list is the inverse enumeration of its numeric order. -/
theorem paddingOrder_ofFn :
    List.ofFn (paddingOrder padding).symm = paddingList padding := by
  calc
    List.ofFn (paddingOrder padding).symm =
        List.ofFn (fun i : Fin (paddingList padding).length =>
          (paddingOrder padding).symm (Fin.cast (paddingList_length padding) i)) :=
      List.ofFn_congr (paddingList_length padding).symm (paddingOrder padding).symm
    _ = paddingList padding := by
      change List.ofFn (fun i => (paddingList padding).get i) = _
      exact List.ofFn_get _

/-- Any global-vertex payload follows old darts, then the explicit dummy list. -/
theorem vertexOrder_ofFn {α : Type*} (f : Vertex t padding → α) :
    List.ofFn (fun i : Fin (vertexCount t padding) => f ((vertexOrder t padding).symm i)) =
      List.ofFn (fun e : Fin t.darts => f (.inl e)) ++
        (paddingList padding).map (fun z => f (.inr z)) := by
  change List.ofFn (fun i : Fin (t.darts + ∑ v, padding v) =>
    f ((vertexOrder t padding).symm i)) = _
  rw [List.ofFn_add]
  have hold (e : Fin t.darts) :
      (vertexOrder t padding).symm (e.castLE (Nat.le_add_right t.darts (∑ v, padding v))) =
        Sum.inl e := (vertexOrder t padding).symm_apply_apply (Sum.inl e)
  have hnew (i : Fin (∑ v, padding v)) :
      (vertexOrder t padding).symm (i.natAdd t.darts) =
        Sum.inr ((paddingOrder padding).symm i) := by
    apply (vertexOrder t padding).injective
    erw [Equiv.apply_symm_apply]
    change i.natAdd t.darts = Fin.natAdd t.darts
      ((paddingOrder padding) ((paddingOrder padding).symm i))
    rw [Equiv.apply_symm_apply]
  apply congrArg₂ (· ++ ·)
  · exact congrArg List.ofFn (funext (fun i => congrArg f (hold i)))
  · calc
      List.ofFn (fun i : Fin (∑ v, padding v) =>
          f ((vertexOrder t padding).symm (i.natAdd t.darts))) =
          List.ofFn (fun i => f (.inr ((paddingOrder padding).symm i))) :=
        congrArg List.ofFn (funext (fun i => congrArg f (hnew i)))
      _ = (List.ofFn (paddingOrder padding).symm).map (fun z => f (.inr z)) :=
        (List.map_ofFn (f := (paddingOrder padding).symm) (g := fun z => f (.inr z))).symm
      _ = _ := by rw [paddingOrder_ofFn]

/-- The stored dummy list uses exactly the nested owner/local-index loop order. -/
theorem paddingList_flatMap {α : Type*} (f : (Σ v : Fin t.vertices, Fin (padding v)) → List α) :
    (paddingList padding).flatMap f =
      (List.ofFn (fun v : Fin t.vertices =>
        (List.ofFn (fun j : Fin (padding v) => f ⟨v, j⟩)).flatten)).flatten := by
  simp only [paddingList, List.sigma, List.finRange, List.flatMap_def,
    List.map_flatten, List.flatten_flatten, List.map_ofFn, Function.comp_def]

/-- The whole actual row stream, split into the two executable outer loops. -/
theorem rowsBits_ofCloudTables :
    PreprocessingPaddingWords.rowsBits (ofCloudTables t padding tables) =
      (List.ofFn (originalVertexBits t padding tables)).flatten ++
        (List.ofFn (fun v : Fin t.vertices =>
          (List.ofFn (dummyVertexBits t padding tables v)).flatten)).flatten := by
  rw [PreprocessingPaddingWords.rowsBits_eq_vertices]
  have hblocks :
      List.ofFn (fun i : Fin (vertexCount t padding) =>
        PreprocessingPaddingWords.vertexBits (ofCloudTables t padding tables) i) =
      List.ofFn (fun i : Fin (vertexCount t padding) =>
        vertexBits t padding tables ((vertexOrder t padding).symm i)) := by
    apply congrArg List.ofFn
    funext i
    rw [vertexBits_eq, Equiv.apply_symm_apply]
  rw [hblocks, vertexOrder_ofFn, List.flatten_append]
  change (List.ofFn (originalVertexBits t padding tables)).flatten ++
      ((paddingList padding).map (fun z => dummyVertexBits t padding tables z.1 z.2)).flatten = _
  rw [← List.flatMap_def, paddingList_flatMap]

/-- Exact complete codec identity: new headers, original blocks, then dummy blocks. -/
theorem tableBits_ofCloudTables :
    PortTables.tableBits (ofCloudTables t padding tables) =
      encodeWords [vertexCount t padding, vertexCount t padding * (q + 1)] ++
        (List.ofFn (originalVertexBits t padding tables)).flatten ++
        (List.ofFn (fun v : Fin t.vertices =>
          (List.ofFn (dummyVertexBits t padding tables v)).flatten)).flatten := by
  change encodeWords (PortTables.tableWords (ofCloudTables t padding tables)) = _
  rw [PortTables.tableWords_eq, encodeWords_append]
  change encodeWords [vertexCount t padding, vertexCount t padding * (q + 1)] ++
    PreprocessingPaddingWords.rowsBits (ofCloudTables t padding tables) = _
  rw [rowsBits_ofCloudTables, List.append_assoc]

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_PreprocessingRegularLoopWordsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Bounds on the actual output prefixes used by the regularization loops.
The bounds include the stored headers and all earlier original/owner blocks.
They concern actual serialized words; machine executions are proved separately. -/
namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularBounds

open PreprocessingRegularTables PreprocessingRegularWords PreprocessingRegularLoopWords
open UniqueGamesTheorem.Foundations.Complexity
open scoped BigOperators

theorem offset_succ {n : Nat} (p : Fin n → Nat) (k : Nat) (h : k < n) :
    PreprocessingPaddingOffsets.offset p (k + 1) =
      PreprocessingPaddingOffsets.offset p k + p ⟨k, h⟩ := by
  unfold PreprocessingPaddingOffsets.offset
  rw [List.take_succ_eq_append_getElem (show k < (List.finRange n).length by simpa using h)]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, List.finRange, List.getElem_ofFn]

def header (t : GraphTables.Table) (p : Fin t.vertices → Nat) (q : Nat) : List Bool :=
  encodeWords [vertexCount t p, vertexCount t p * (q + 1)]

def ownerBits (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (v : Fin t.vertices) : List Bool :=
  (List.ofFn (dummyVertexBits t p tables v)).flatten

def originalPrefix (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (k : Nat) : List Bool :=
  header t p q ++ blocksPrefix (originalVertexBits t p tables) k

def ownerPrefix (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (k : Nat) : List Bool :=
  header t p q ++ (List.ofFn (originalVertexBits t p tables)).flatten ++
    blocksPrefix (ownerBits t p tables) k

def dummyPrefix (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (v : Fin t.vertices) (k : Nat) : List Bool :=
  ownerPrefix t p tables v.val ++ blocksPrefix (dummyVertexBits t p tables v) k

variable (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)

theorem originalPrefix_length_le (k : Nat) :
    (originalPrefix t p tables k).length ≤
      (PortTables.tableBits (ofCloudTables t p tables)).length := by
  have h := blocksPrefix_length_le (originalVertexBits t p tables) k
  rw [tableBits_ofCloudTables]
  simp only [originalPrefix, header, List.length_append]
  omega

theorem ownerPrefix_length_le (k : Nat) :
    (ownerPrefix t p tables k).length ≤
      (PortTables.tableBits (ofCloudTables t p tables)).length := by
  have h := blocksPrefix_length_le (ownerBits t p tables) k
  have he : ownerBits t p tables =
      (fun v => (List.ofFn (dummyVertexBits t p tables v)).flatten) := rfl
  rw [tableBits_ofCloudTables]
  simp only [ownerPrefix, header, List.length_append] at *
  simp only [he] at *
  omega

theorem dummyPrefix_length_le (v : Fin t.vertices) (k : Nat) :
    (dummyPrefix t p tables v k).length ≤
      (PortTables.tableBits (ofCloudTables t p tables)).length := by
  have hi := blocksPrefix_length_le (dummyVertexBits t p tables v) k
  have ho := blocksPrefix_length_le (ownerBits t p tables) (v.val + 1)
  rw [blocksPrefix_succ _ _ v.isLt] at ho
  have he : ownerBits t p tables =
      (fun v => (List.ofFn (dummyVertexBits t p tables v)).flatten) := rfl
  simp only [Fin.eta] at ho
  rw [tableBits_ofCloudTables]
  simp only [dummyPrefix, ownerPrefix, header, ownerBits, List.length_append] at *
  simp only [he] at *
  omega

theorem regular_originalPrefix_le (H : BaseTable) (k : Nat) :
    (originalPrefix t (padding t) (familyCloudTable H t) k).length ≤
      PreprocessingMachineBounds.regularPolynomial.eval
        (PreprocessingMachineBounds.inputLength t) :=
  (originalPrefix_length_le t (padding t) (familyCloudTable H t) k).trans
    (PreprocessingMachineBounds.regularBits_le H t)

theorem regular_ownerPrefix_le (H : BaseTable) (k : Nat) :
    (ownerPrefix t (padding t) (familyCloudTable H t) k).length ≤
      PreprocessingMachineBounds.regularPolynomial.eval
        (PreprocessingMachineBounds.inputLength t) :=
  (ownerPrefix_length_le t (padding t) (familyCloudTable H t) k).trans
    (PreprocessingMachineBounds.regularBits_le H t)

theorem regular_dummyPrefix_le (H : BaseTable) (v : Fin t.vertices) (k : Nat) :
    (dummyPrefix t (padding t) (familyCloudTable H t) v k).length ≤
      PreprocessingMachineBounds.regularPolynomial.eval
        (PreprocessingMachineBounds.inputLength t) :=
  (dummyPrefix_length_le t (padding t) (familyCloudTable H t) v k).trans
    (PreprocessingMachineBounds.regularBits_le H t)

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularBounds

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOriginalRow
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_append _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_nil _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_append _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_nil _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_done _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_head _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_words _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_acceptsAt _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_get _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_reverseAt _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headValue _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_row _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_head _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tableBits _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tableWords _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.build_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.build_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rowList_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rows_at _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.actualRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Machine execution for an inherited regularization row

The machine reads the original reverse index from the physically stored input
table. The unread working copy then starts at the 4096 original predicate
fields; a fixed finite Boolean block copy retains exactly those fields. Unary
arithmetic computes the new reverse index, and the checked row emitter appends
the three physical fields. No input table or unbounded arithmetic function is
stored in the machine's finite state or instructions.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalRow

open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingRegularTables

/-! ## The actual stored row and its input word boundaries -/

theorem tableWords_at_row (t : Table) (e : Fin t.darts) :
    GraphTables.tableWords t = prefixWords t e ++ (rowWords t.rows[e] ++ suffixWords t e) := by
  have he : e.val < (rowList t).length := by simpa only [rowList_length] using e.isLt
  have hs : (rowList t).take e.val ++ (rowList t)[e.val] ::
      (rowList t).drop (e.val + 1) = rowList t := by
    rw [List.getElem_cons_drop he, List.take_append_drop]
  have hw := congrArg (fun rs : List (DartRow t.vertices t.darts) => rs.flatMap rowWords) hs
  simp only [List.flatMap_append, List.flatMap_cons, rowList, Vector.getElem_toList] at hw
  unfold GraphTables.tableWords prefixWords suffixWords rowList
  rw [← hw]
  simp only [List.append_assoc, Fin.getElem_fin]

theorem tableWords_drop_row (t : Table) (e : Fin t.darts) :
    (GraphTables.tableWords t).drop (2 + 4098 * e.val) = rowWords t.rows[e] ++ suffixWords t e := by
  rw [tableWords_at_row]
  exact List.drop_left' (l₂ := rowWords t.rows[e] ++ suffixWords t e)
    (prefixWords_length t e)

theorem selected_reverse (t : Table) (e : Fin t.darts) :
    (GraphTables.tableWords t)[4098 * e.val + 3]? = some t.rows[e].reverseIndex.val := by
  have h := congrArg (fun words : List Nat => words[1]?) (tableWords_drop_row t e)
  simp only [List.getElem?_drop] at h
  rw [show 2 + 4098 * e.val + 1 = 4098 * e.val + 3 by omega] at h
  simpa [rowWords] using h

theorem remaining_relation (t : Table) (e : Fin t.darts) :
    (GraphTables.tableWords t).drop (4098 * e.val + 3 + 1) =
      relationWords t.rows[e].relation ++ suffixWords t e := by
  rw [show 4098 * e.val + 3 + 1 = (2 + 4098 * e.val) + 2 by omega,
    ← List.drop_drop, tableWords_drop_row]
  simp only [rowWords, List.cons_append, List.drop_succ_cons, List.drop_zero, List.nil_append]

/-! ## One fixed finite program -/

def zeroBuffer : Buffer := MachineFixedBlockMap.emptyBuffer 4096

/-! ## Physical intermediate tape states -/

theorem looked_other (t : Table) (e : Fin t.darts) (base : Tape → List Bool)
    (k : Tape) (h₂ : k ≠ 2) (h₃ : k ≠ 3) (h₄ : k ≠ 4) :
    looked t e base k = base k :=
  MachineAffineLookup.finalTapes_other lookupTape base _ _ _ k h₂ h₃ h₄

theorem looked_reverse (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    looked t e base 4 = encodeWord t.rows[e].reverseIndex.val ++ base 4 :=
  MachineAffineLookup.finalTapes_output lookupTape base _ _ _

theorem looked_relation (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    looked t e base 3 = encodeWords (relationWords t.rows[e].relation) ++
      (encodeWords (suffixWords t e) ++ base 3) := by
  change MachineLookup.tapes (2 : Tape) 3 4 base
    (encodeWord 0 ++ base 2)
    (encodeWords ((GraphTables.tableWords t).drop (4098 * e.val + 3 + 1)) ++ base 3)
    (encodeWord t.rows[e].reverseIndex.val ++ base 4) 3 = _
  rw [MachineLookup.tapes_source _ _ _ (by decide), remaining_relation, encodeWords_append]
  exact List.append_assoc _ _ _

/-- Reusable identity copy of exactly the physically read 4096 unary Boolean
fields. The fixed register is reset; every other state component is retained. -/
theorem relationCopy_step {K Λ σ : Type} [DecidableEq K]
    (src dst : K) (hne : src ≠ dst) (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (code : program label = relationCopyAt src dst exit)
    (relation : RelationTable) (suffix : List Bool) (base : K → List Bool)
    (input : base src = encodeWords (relationWords relation) ++ suffix)
    (ambient : σ) (buffer : Buffer) (register : Option Bool) :
    TM2.step program ⟨some label, ((ambient, buffer), register), base⟩ =
      some ⟨exit, ((ambient, zeroBuffer), register),
        Function.update (Function.update base src suffix) dst
          (encodeWords (relationWords relation) ++ base dst)⟩ := by
  change some (TM2.stepAux (program label) _ base) = _
  rw [code]
  unfold relationCopyAt
  rw [MachineStateEquiv.stepAux_transport_symm]
  change some (MachineStateEquiv.configuration (copyStateEquiv σ)
    (TM2.stepAux (PoweringMachineRow.encodedBlockAt src dst (id : Buffer → Buffer) exit)
      ((ambient, register), buffer) base)) = _
  have hinput : base src = PoweringMachineRow.encodeBits
      (List.ofFn (fun i : Fin 4096 => relation[i])) ++ suffix := by
    rw [relationBits_eq_encodedBlock]
    exact input
  rw [PoweringMachineRow.stepAux_encodedBlockAt src dst (id : Buffer → Buffer)
    exit hne (fun i : Fin 4096 => relation[i]) suffix
    ((ambient, register), buffer) base hinput]
  simp only [id_eq, relationBits_eq_encodedBlock, MachineStateEquiv.configuration,
    copyStateEquiv, zeroBuffer]
  rfl

theorem copied_other (t : Table) (e : Fin t.darts) (base : Tape → List Bool)
    (k : Tape) (h₂ : k ≠ 2) (h₃ : k ≠ 3) (h₄ : k ≠ 4) (h₇ : k ≠ 7) :
    copied t e base k = base k := by
  simp only [copied, Function.update_of_ne h₇, Function.update_of_ne h₃,
    looked_other t e base k h₂ h₃ h₄]

theorem copied_reverse (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    copied t e base 4 = encodeWord t.rows[e].reverseIndex.val ++ base 4 := by
  simp only [copied, Function.update_of_ne (by decide : (4 : Tape) ≠ 7),
    Function.update_of_ne (by decide : (4 : Tape) ≠ 3), looked_reverse]

theorem copied_relation (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    copied t e base 7 = encodeWords (relationWords t.rows[e].relation) ++ base 7 := by
  simp only [copied, Function.update_self]

theorem affined_other (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool)
    (k : Tape) (h₂ : k ≠ 2) (h₃ : k ≠ 3) (h₄ : k ≠ 4) (h₆ : k ≠ 6) (h₇ : k ≠ 7) :
    affined q t e base k = base k := by
  simp only [affined, Function.update_of_ne h₆, copied_other t e base k h₂ h₃ h₄ h₇]

theorem affined_reverse (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    affined q t e base 6 = encodeWord ((q + 1) * t.rows[e].reverseIndex.val + q) ++ base 6 := by
  simp only [affined, Function.update_self]

theorem affined_relation (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    affined q t e base 7 = encodeWords (relationWords t.rows[e].relation) ++ base 7 := by
  simp only [affined, Function.update_of_ne (by decide : (7 : Tape) ≠ 6), copied_relation]

theorem affined_fields (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    MachineTableRows.fieldBits fields (affined q t e base) = encodeWords (emittedWords q t e) := by
  have htail := affined_other q t e base 0 (by decide) (by decide) (by decide)
    (by decide) (by decide)
  simp only [MachineTableRows.fieldBits, fields_zero, fields_one, fields_two,
    htail, input.indexWord, affined_reverse, input.computedEmpty,
    affined_relation, input.relationEmpty, List.append_nil,
    emittedWords, encodeWords, List.append_assoc]

section Execution

variable {Λ σ : Type}

theorem lookupTrace (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (input : Input t e base)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineAffineLookup.steps (GraphTables.tableWords t) e.val 4098 3]
      (some ⟨some (labels (.lookup .seed)), ((ambient, zeroBuffer), register), base⟩) =
      some ⟨some (labels .copyRelation), ((ambient, zeroBuffer), none), looked t e base⟩ := by
  exact MachineAffineLookup.affineLookupTrace 0 lookupTape lookupTape_injective source_outside
    4098 3 (fun l => labels (.lookup l)) (some (labels .copyRelation)) program
    (fun l => code (.lookup l)) base (GraphTables.tableWords t) input.tableWord input.scratchEmpty
    e.val [] (by simpa only [List.append_nil] using input.indexWord)
    t.rows[e].reverseIndex.val (selected_reverse t e) (ambient, zeroBuffer) register

theorem copyTrace (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (ambient : σ) :
    (advance (TM2.step program))^[1]
      (some ⟨some (labels .copyRelation), ((ambient, zeroBuffer), none), looked t e base⟩) =
      some ⟨some (labels .reverseSeed), ((ambient, zeroBuffer), none), copied t e base⟩ := by
  simp only [Function.iterate_one, advance_some]
  have run := relationCopy_step (3 : Tape) 7 (by decide) (labels .copyRelation)
    (some (labels .reverseSeed)) program (code .copyRelation) t.rows[e].relation
    (encodeWords (suffixWords t e) ++ base 3) (looked t e base) (looked_relation t e base)
    ambient zeroBuffer none
  rw [looked_other t e base 7 (by decide) (by decide) (by decide)] at run
  exact run

theorem affineTrace (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (input : Input t e base)
    (ambient : σ) :
    (advance (TM2.step program))^[2 * (t.rows[e].reverseIndex.val + 1) + 1]
      (some ⟨some (labels .reverseSeed), ((ambient, zeroBuffer), none), copied t e base⟩) =
      some ⟨some (labels (.emit .relationRead)), ((ambient, zeroBuffer), none),
        affined q t e base⟩ := by
  have hsource : copied t e base 4 = encodeWord t.rows[e].reverseIndex.val ++ [] := by
    rw [copied_reverse, input.reverseEmpty]
  have hscratch : copied t e base 5 = [] := by
    rw [copied_other t e base 5 (by decide) (by decide) (by decide) (by decide), input.scratchEmpty]
  have run := MachineUnaryAffineAt.seededAffineTrace (4 : Tape) 5 6 (by decide) (by decide)
    (by decide) (q + 1) q (labels .reverseSeed) (labels .reverseScan) (labels .reverseRestore)
    (some (labels (.emit .relationRead))) program (code .reverseSeed) (code .reverseScan)
    (code .reverseRestore) (copied t e base) t.rows[e].reverseIndex.val [] hsource hscratch
    (ambient, zeroBuffer) none
  rw [copied_other t e base 6 (by decide) (by decide) (by decide) (by decide)] at run
  exact run

theorem emitTrace (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (input : Input t e base)
    (ambient : σ) :
    (advance (TM2.step program))^[rowSteps q t e base]
      (some ⟨some (labels (.emit .relationRead)), ((ambient, zeroBuffer), none), affined q t e base⟩) =
      some ⟨exit, ((ambient, zeroBuffer), none), finalTapes q t e base⟩ := by
  have hrow : affined q t e base 8 = [] := by
    rw [affined_other q t e base 8 (by decide) (by decide) (by decide) (by decide)
      (by decide), input.rowEmpty]
  have hscratch : affined q t e base 5 = [] := by
    rw [affined_other q t e base 5 (by decide) (by decide) (by decide) (by decide)
      (by decide), input.scratchEmpty]
  have hout := affined_other q t e base 9 (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hfields := affined_fields q t e base input
  have hsize : MachineTableRows.fieldSize fields (affined q t e base) =
      (encodeWords (emittedWords q t e)).length := by
    rw [← MachineTableRows.fieldBits_length, hfields]
  have run := MachineTableRows.appendTrace fields (8 : Tape) 9 5 fields_separate
    (by decide) (by decide) (by decide) (fun l => labels (.emit l)) exit program
    (fun l => code (.emit l)) (affined q t e base) hrow hscratch (ambient, zeroBuffer) none
  rw [hsize, hout, hfields] at run
  exact run

/-- All four phases are derived from their concrete instructions. -/
theorem traceAt (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (input : Input t e base)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps q t e base]
      (some ⟨some (labels (.lookup .seed)), ((ambient, zeroBuffer), register), base⟩) =
      some ⟨exit, ((ambient, zeroBuffer), none), finalTapes q t e base⟩ := by
  have hlookup := lookupTrace q labels exit program code t e base input ambient register
  have hcopy := copyTrace q labels exit program code t e base ambient
  have haffine := affineTrace q labels exit program code t e base input ambient
  have hemit := emitTrace q labels exit program code t e base input ambient
  exact join_trace (join_trace (join_trace hlookup hcopy) haffine) hemit

end Execution

theorem steps_le (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    steps q t e base ≤ timeBound q (tableBits t).length (base 9).length := by
  have hl := MachineAffineLookup.steps_le (GraphTables.tableWords t) e.val 4098 3
    t.rows[e].reverseIndex.val (selected_reverse t e)
  have htable := tableWords_length_le_bits t
  have he : e.val ≤ (tableBits t).length := by have he := e.isLt; omega
  have hr : t.rows[e].reverseIndex.val ≤ (tableBits t).length := by
    have hrlt := t.rows[e].reverseIndex.isLt
    omega
  have hrel := relationBits_length_le t.rows[e].relation
  have hmul := Nat.mul_le_mul_left (4 * (q + 1) + 2) hr
  change MachineAffineLookup.steps (GraphTables.tableWords t) e.val 4098 3 ≤
    2 * e.val + 5 * (tableBits t).length + 6 at hl
  unfold steps rowSteps timeBound emittedWords
  simp only [encodeWords, List.length_append, encodeWord_length]
  nlinarith

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalRow

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineLazyRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLazyRows

open Turing MachineComposition PCP.GraphTables
open PCP.PreprocessingLazyWords (reverseMap moveRow moveRow_words)

variable {K Λ A : Type} [DecidableEq K]

abbrev StreamState (A : Type) (d : Nat) := State (A × Buffer) d

def streamClean (d : Nat) (positive : 0 < d) (ambient : A) : StreamState A d :=
  MachinePortReindex.clean d positive (ambient, MachineRegularOriginalRow.zeroBuffer)

/-- Only finite register coordinates change; all tapes remain fixed. -/
def relationStateEquiv (A : Type) (d : Nat) :
    MachineRegularOriginalRow.State (A × Fin d) ≃ StreamState A d where
  toFun s := (((s.1.1.1, s.1.2), s.1.1.2), s.2)
  invFun s := (((s.1.1.1, s.1.2), s.1.1.2), s.2)
  left_inv _ := rfl
  right_inv _ := rfl

def streamRelationCopy (d : Nat) (source destination : K) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d) :=
  MachineStateEquiv.statement (relationStateEquiv A d)
    (MachineRegularOriginalRow.relationCopyAt source destination exit)

theorem streamRelationCopy_step (d : Nat) (positive : 0 < d)
    (source destination : K) (different : source ≠ destination)
    (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (code : program label = streamRelationCopy d source destination exit)
    (relation : RelationTable) (suffix : List Bool) (base : K → List Bool)
    (input : base source = encodeWords (relationWords relation) ++ suffix) (ambient : A) :
    TM2.step program ⟨some label, streamClean d positive ambient, base⟩ =
      some ⟨exit, streamClean d positive ambient,
        Function.update (Function.update base source suffix) destination
          (encodeWords (relationWords relation) ++ base destination)⟩ := by
  have hraw := MachineRegularOriginalRow.relationCopy_step source destination different label exit
    (fun _ => MachineRegularOriginalRow.relationCopyAt source destination exit) rfl
    relation suffix base input (ambient, MachineFixedDivMod.residue d positive 0)
    MachineRegularOriginalRow.zeroBuffer none
  have haux := Option.some.inj hraw
  change some (TM2.stepAux (program label) (streamClean d positive ambient) base) = _
  rw [code, streamRelationCopy, MachineStateEquiv.stepAux_transport_symm]
  change some (MachineStateEquiv.configuration (relationStateEquiv A d)
    (TM2.stepAux (MachineRegularOriginalRow.relationCopyAt source destination exit)
      (((ambient, MachineFixedDivMod.residue d positive 0),
        MachineRegularOriginalRow.zeroBuffer), none) base)) = _
  rw [haux]
  rfl

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

end UniqueGamesTheorem.Foundations.Complexity.MachineLazyRows

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineLazyTable
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

abbrev State (d : Nat) := MachineLazyRows.StreamState Unit d

def clean (d : Nat) (positive : 0 < d) : State d :=
  MachineLazyRows.streamClean d positive ()

theorem clean_pair (d : Nat) (positive : 0 < d) :
    ((clean d positive).1, (none : Option Bool)) = clean d positive := rfl

theorem inputBlocks_codec {n d : Nat} (table : PortTables.Table n d) (events : List (Fin n)) :
    inputBlocks table events = encodeWords
      ((events.flatMap (fun v => List.ofFn (PreprocessingLazyWords.row table v))).flatMap
        GraphTables.rowWords) := by
  rw [List.flatMap_assoc, encodeWords_flatMap]
  simp only [inputBlocks, MachineLazyRows.recordsInput_eq_codec]

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

end UniqueGamesTheorem.Foundations.Complexity.MachineLazyTable

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachinePaddedExpanderFamilyBoundsLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlay.familyView_left _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily

open Turing

section TableCoordinates

open PCP.ExpanderTables PCP.ExpanderRowControl

section Placement

variable {ρ : Type} [Fintype ρ]

/-- Initial state for an arbitrary preserved family-state component. -/
def initialState (state : MachineExpanderFamily.State ρ fixedDegree)
    (register : Option Bool) : State ρ := (state, (false, register))

def finalState (H : SmallTable) (state : MachineExpanderFamily.State ρ fixedDegree) : State ρ :=
  (MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H
    (MachineExpanderFamily.caller state), (false, none))

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
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCloudRankLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudRank

open Turing MachineComposition MachineCloudCount

variable {σ : Type}

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

open UniqueGamesTheorem.Foundations.PCP

theorem cloudSelectSteps_le (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v)) (querySuffix : List Bool) :
    cloudSelectSteps t v i querySuffix ≤
      10 * ((GraphTables.tableBits t).length + (queryWord v.val i.val querySuffix).length) + 20 := by
  let e := PreprocessingCloudIndex.cloudSelect t v i
  have h := totalSteps_le t.vertices t.darts v.val i.val (tableRows t)
    ((tableRows t).take e.val.val) (remainder t e.val) querySuffix
    (tableWord_split t v e.val e.property)
  simpa only [cloudSelectSteps, e, MachineCloudCount.tableRows_input] using h

end UniqueGamesTheorem.Foundations.Complexity.MachineCloudSelect

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularInternalRow
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Physical construction of an internal regularization row

The input values belong on unary tapes. The cloud degree and the queried port
are the only arithmetic parameters fixed in finite control. The stored cloud
rotation supplies both the destination's local index and the return port.
The final row contains the full fixed equality predicate.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow

open Turing MachineComposition
open PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} [DecidableEq K]

theorem equalityBits_length_le : equalityBits.length ≤ 8192 :=
  GraphTables.relationBits_length_le _

theorem emittedBits_eq_row (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PreprocessingCloudIndex.PaddedCloud t padding v) (p : Fin q) :
    emittedBits q (PreprocessingRegularTables.vertexOrder t padding x.val).val
      (PreprocessingInternalRows.selectedIndex t padding v
        (PreprocessingInternalRows.localStep t padding tables v x p).1)
      (PreprocessingInternalRows.localStep t padding tables v x p).2.val =
        encodeWords (GraphTables.rowWords
          (PreprocessingInternalRows.row t padding tables v x p)) := by
  rw [MachineTableRows.rowBits_eq, PreprocessingInternalRows.row_tail,
    PreprocessingInternalRows.row_reverse_selectedIndex, PreprocessingInternalRows.row_relation]
  rfl

theorem finishSteps_le (q x z r outputLength : Nat) :
    finishSteps q x z r outputLength ≤
      (5 * q + 7) * z + 7 * r + 4 * x + 2 * outputLength + 40986 := by
  have h := equalityBits_length_le
  unfold finishSteps
  nlinarith

theorem rotorSteps_le {n q : Nat} (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q) :
    rotorSteps table i p ≤ 2 * i.val +
      5 * (encodeWords (ExpanderTableWords.rotationWords table)).length + n * q + 8 := by
  have hl := MachineAffineLookup.steps_le (ExpanderTableWords.rotationWords table)
    i.val q p.val _ (selected_rotation table i p)
  have hb := (ExpanderTables.rowIndex n q (ExpanderTables.lookup table (i, p))).isLt
  rw [ExpanderTables.rowIndex_val] at hb
  unfold rotorSteps
  omega

theorem selectOldTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v)) (o : Nat) (ambient : σ) :
    (advance (TM2.step selectProgram))^[oldSelectSteps t v i]
      (some ⟨some (.inr (.copy .oldLocal .seed)), selectCleanState ambient none,
        selectMemory (GraphTables.tableBits t) i.val v.val
          (PreprocessingCloudIndex.cloudSize t v) o t.darts [] [] [] [] [] []⟩) =
      some ⟨none, selectCleanState ambient none,
        selectMemory (GraphTables.tableBits t) i.val v.val
          (PreprocessingCloudIndex.cloudSize t v) o t.darts []
          (encodeWord (PreprocessingCloudIndex.cloudSelect t v i).val.val) [] [] [] []⟩ := by
  let graph := GraphTables.tableBits t
  let k := PreprocessingCloudIndex.cloudSize t v
  have hi := selectCopyTrace .oldLocal
    (selectMemory graph i.val v.val k o t.darts [] [] [] [] [] [])
    i.val rfl rfl ambient none
  simp only [copyDestination, afterCopy, selectMemory_query, update_selectMemory_query, List.append_nil] at hi
  have hv := selectCopyTrace .oldOwner
    (selectMemory graph i.val v.val k o t.darts (encodeWord i.val) [] [] [] [] [])
    v.val rfl rfl ambient none
  simp only [copyDestination, afterCopy, selectMemory_query, update_selectMemory_query] at hv
  have hc := selectCloudTrace t v i (selectExtraMemory i.val v.val k o t.darts [] [] [] [])
    ambient none
  have hq : MachineCloudSelect.queryWord v.val i.val [] =
      encodeWord v.val ++ encodeWord i.val := by
    simp only [MachineCloudSelect.queryWord, MachineCloudRank.queryWord, List.append_nil]
  change (advance (TM2.step selectProgram))^[MachineCloudSelect.cloudSelectSteps t v i []]
    (some ⟨some (.inl (.inr .initialize_)), selectCleanState ambient none,
      selectMemory graph i.val v.val k o t.darts
        (MachineCloudSelect.queryWord v.val i.val []) [] [] [] [] []⟩) =
    some ⟨some (.inr (.cleanup 0)), selectCleanState ambient none,
      selectMemory graph i.val v.val k o t.darts
        (MachineCloudSelect.queryWord v.val i.val [])
        (encodeWord (PreprocessingCloudIndex.cloudSelect t v i).val.val) [] [] [] []⟩ at hc
  rw [hq] at hc
  have hd := selectCleanupTrace graph i.val v.val k o t.darts
    (encodeWord v.val ++ encodeWord i.val)
    (encodeWord (PreprocessingCloudIndex.cloudSelect t v i).val.val) [] [] [] [] ambient
  have hn : (encodeWord v.val ++ encodeWord i.val).length + ([] : List Bool).length + ([] : List Bool).length +
      ([] : List Bool).length + ([] : List Bool).length + 5 = v.val + i.val + 7 := by
    simp only [List.length_append, encodeWord_length, List.length_nil]
    omega
  rw [hn] at hd
  exact joinTrace (joinTrace (joinTrace hi hv) hc) hd

/-- The entire actual selector program, with both runtime branches and the
same clean final frame. Metadata values are premises about physical tapes. -/
theorem selectionTrace (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (PreprocessingCloudIndex.cloudSize t v + padding v))
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step selectProgram))^[selectionSteps t padding v i]
      (some ⟨some (.inr (.compare .scan)), selectCleanState ambient register,
        selectMemory (GraphTables.tableBits t) i.val v.val
          (PreprocessingCloudIndex.cloudSize t v)
          (PreprocessingPaddingOffsets.offset padding v.val) t.darts [] [] [] [] [] []⟩) =
      some ⟨none, selectCleanState ambient none,
        selectMemory (GraphTables.tableBits t) i.val v.val
          (PreprocessingCloudIndex.cloudSize t v)
          (PreprocessingPaddingOffsets.offset padding v.val) t.darts []
          (encodeWord (PreprocessingInternalRows.selectedIndex t padding v i)) [] [] [] []⟩ := by
  have hc := selectComparisonTrace
    (selectMemory (GraphTables.tableBits t) i.val v.val
      (PreprocessingCloudIndex.cloudSize t v)
      (PreprocessingPaddingOffsets.offset padding v.val) t.darts [] [] [] [] [] [])
    i.val (PreprocessingCloudIndex.cloudSize t v) rfl rfl rfl rfl ambient register
  by_cases hi : i.val < PreprocessingCloudIndex.cloudSize t v
  · simp only [ite_eq_left hi] at hc
    have hb := selectOldTrace t v ⟨i.val, hi⟩
      (PreprocessingPaddingOffsets.offset padding v.val) ambient
    simpa only [selectionSteps, dite_eq_left hi,
      PreprocessingInternalRows.selectedIndex_old t padding v i hi] using joinTrace hc hb
  · simp only [ite_eq_right hi] at hc
    have hb := selectDummyTrace (GraphTables.tableBits t) i.val v.val
      (PreprocessingCloudIndex.cloudSize t v)
      (PreprocessingPaddingOffsets.offset padding v.val) t.darts (Nat.le_of_not_gt hi) ambient
    simpa only [selectionSteps, dite_eq_right hi,
      PreprocessingInternalRows.selectedIndex_dummy t padding v i (Nat.le_of_not_gt hi)]
      using joinTrace hc hb

theorem selectionSteps_le (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (PreprocessingCloudIndex.cloudSize t v + padding v)) :
    selectionSteps t padding v i ≤
      10 * (GraphTables.tableBits t).length + 16 * i.val + 13 * v.val +
      5 * PreprocessingCloudIndex.cloudSize t v +
      2 * PreprocessingPaddingOffsets.offset padding v.val + 2 * t.darts + 57 := by
  unfold selectionSteps
  split
  · rename_i hi
    have hb := MachineCloudSelect.cloudSelectSteps_le t v ⟨i.val, hi⟩ []
    have hmin : min i.val (PreprocessingCloudIndex.cloudSize t v) = i.val := Nat.min_eq_left hi.le
    simp only [oldSelectSteps, MachineUnaryLessAt.steps, hmin]
    simp only [MachineCloudSelect.queryWord, MachineCloudRank.queryWord,
      List.length_append, encodeWord_length, List.length_nil] at hb
    omega
  · rename_i hi
    rw [dummySelectSteps_eq _ _ _ _ (Nat.le_of_not_gt hi)]
    have hmin := Nat.min_le_right i.val (PreprocessingCloudIndex.cloudSize t v)
    unfold MachineUnaryLessAt.steps
    omega

theorem coreSelectionTrace (q : Nat) (positive : 0 < q) (p : Fin q)
    (labels : CoreLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = coreInstruction q positive p labels exit l)
    (t : GraphTables.Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices)
    (j : Fin (PreprocessingCloudIndex.cloudSize t v + padding v))
    (x i : Nat) (rotor output query scan flat returnPort : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[selectionSteps t padding v j]
      (some ⟨some (labels (.select (.inr (.compare .scan)))), coreInitialState q positive ambient,
        coreMemory (GraphTables.tableBits t) x v.val i (PreprocessingCloudIndex.cloudSize t v)
          (PreprocessingPaddingOffsets.offset padding v.val) t.darts rotor output query scan flat
          (encodeWord j.val) returnPort []⟩) =
      some ⟨some (labels (.finish .seedReturn)), coreInitialState q positive ambient,
        coreMemory (GraphTables.tableBits t) x v.val i (PreprocessingCloudIndex.cloudSize t v)
          (PreprocessingPaddingOffsets.offset padding v.val) t.darts rotor output query scan flat
          (encodeWord j.val) returnPort
          (encodeWord (PreprocessingInternalRows.selectedIndex t padding v j))⟩ := by
  let e := coreSelectStateEquiv σ q
  let state := (ambient, (MachineFixedBlockMap.emptyBuffer 4096,
    MachineFixedDivMod.residue q positive 0))
  have sourceRun := selectionTrace t padding v j state none
  have moved := MachineStateEquiv.trace e selectProgram _ _ _ sourceRun
  let base := coreMemory (GraphTables.tableBits t) x v.val i
    (PreprocessingCloudIndex.cloudSize t v)
    (PreprocessingPaddingOffsets.offset padding v.val) t.darts rotor output query scan flat
    (encodeWord j.val) returnPort []
  have placed := MachineCloudPadding.Placement.trace coreSelectTape coreSelectView
    coreSelectView_left coreSelectView_right (fun l => labels (.select l))
    (some (labels (.finish .seedReturn))) base
    (MachineStateEquiv.program e selectProgram) program (fun l => code (.select l))
    _ _ _ moved
  simp only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    MachineStateEquiv.configuration, base, coreSelectFrame] at placed
  convert placed using 1 <;> rfl

/-- One full actual internal row of the serialized regularization, including
the physical rotor lookup, both destination cases, full equality predicate,
row append and complete reusable cleanup frame. -/
theorem coreTrace (q : Nat) (positive : 0 < q) (p : Fin q)
    (labels : CoreLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = coreInstruction q positive p labels exit l)
    (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PreprocessingCloudIndex.PaddedCloud t padding v)
    (output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[coreSteps t padding tables v x p output.length]
      (some ⟨some (labels (coreEntry q)), coreInitialState q positive ambient,
        coreInputTapes t padding tables v x output⟩) =
      some ⟨exit, coreInitialState q positive ambient,
        coreInputTapes t padding tables v x
          (output ++ encodeWords (GraphTables.rowWords
            (PreprocessingInternalRows.row t padding tables v x p)))⟩ := by
  let rank := PreprocessingCloudIndex.paddedCloudRank t padding v x
  let step := ExpanderTables.lookup (tables v) (rank, p)
  let z := PreprocessingInternalRows.selectedIndex t padding v step.1
  let X := (PreprocessingRegularTables.vertexOrder t padding x.val).val
  let o := PreprocessingPaddingOffsets.offset padding v.val
  let bits := encodeWords (ExpanderTableWords.rotationWords (tables v))
  let tailBits := encodeWords ((ExpanderTableWords.rotationWords (tables v)).drop
    (q * rank.val + p.val + 1))
  let graph := GraphTables.tableBits t
  let k := PreprocessingCloudIndex.cloudSize t v
  have hr := coreRotorTrace positive (tables v) rank p labels exit program code
    graph X v.val k o t.darts output ambient
  have hs := coreSelectionTrace q positive p labels exit program code t padding v step.1
    X rank.val bits output (encodeWord 0) tailBits (encodeWord 0) (encodeWord step.2.val) ambient
  have hf := coreFinishTrace q positive p labels exit program code
    graph X v.val rank.val k o t.darts step.1.val step.2.val z bits output
    (encodeWord 0) tailBits (encodeWord 0) ambient
  have hc := coreCleanupTrace q positive p labels exit program code
    (coreMemory graph X v.val rank.val k o t.darts bits
      (output ++ emittedBits q X z step.2.val)
      (encodeWord 0) tailBits (encodeWord 0) (encodeWord step.1.val)
      (encodeWord step.2.val) (encodeWord z))
    (ambient, (MachineFixedBlockMap.emptyBuffer 4096,
      (MachineFixedDivMod.residue q positive 0, (false, MachineCloudSelect.Phase.checking))))
  rw [coreCleanupSteps_memory, coreCleaned_memory] at hc
  have h := joinTrace (joinTrace (joinTrace hr hs) hf) hc
  have hbits : emittedBits q X z step.2.val =
      encodeWords (GraphTables.rowWords (PreprocessingInternalRows.row t padding tables v x p)) :=
    emittedBits_eq_row t padding tables v x p
  rw [hbits] at h
  exact h

/-- A selected original dart is below the original dart count; a dummy
target is the old-dart count plus its physical prefix and local remainder. -/
theorem selectedIndex_le (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (PreprocessingCloudIndex.cloudSize t v + padding v)) :
    PreprocessingInternalRows.selectedIndex t padding v i ≤
      t.darts + PreprocessingPaddingOffsets.offset padding v.val + i.val := by
  unfold PreprocessingInternalRows.selectedIndex
  split
  · rename_i hi
    have h := (PreprocessingCloudIndex.cloudSelect t v ⟨i.val, hi⟩).val.isLt
    omega
  · omega

/-- Every rotor entry occupies at least its delimiter on the physical tape. -/
theorem rotorSize_le_encodedLength {n q : Nat} (positive : 0 < q)
    (table : ExpanderTables.Table n q) :
    n ≤ (encodeWords (ExpanderTableWords.rotationWords table)).length := by
  have h : n * q ≤ (encodeWords (ExpanderTableWords.rotationWords table)).length := by
    rw [encodeWords_length, ExpanderTableWords.rotationWords_length]
    omega
  exact (Nat.le_mul_of_pos_right n positive).trans h

theorem coreSteps_le (q : Nat) (positive : 0 < q) (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PreprocessingCloudIndex.PaddedCloud t padding v)
    (p : Fin q) (outputLength : Nat) :
    coreSteps t padding tables v x p outputLength ≤
      coreTimeBound q (GraphTables.tableBits t).length
        (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
        (PreprocessingRegularTables.vertexOrder t padding x.val).val v.val
        (PreprocessingCloudIndex.paddedCloudRank t padding v x).val
        (PreprocessingCloudIndex.cloudSize t v)
        (PreprocessingPaddingOffsets.offset padding v.val) t.darts outputLength := by
  let rank := PreprocessingCloudIndex.paddedCloudRank t padding v x
  let step := ExpanderTables.lookup (tables v) (rank, p)
  let z := PreprocessingInternalRows.selectedIndex t padding v step.1
  let X := (PreprocessingRegularTables.vertexOrder t padding x.val).val
  let o := PreprocessingPaddingOffsets.offset padding v.val
  let L := (GraphTables.tableBits t).length
  let R := (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
  let k := PreprocessingCloudIndex.cloudSize t v
  let tailBits := encodeWords ((ExpanderTableWords.rotationWords (tables v)).drop
    (q * rank.val + p.val + 1))
  have hN : k + padding v ≤ R := rotorSize_le_encodedLength positive (tables v)
  have hj : step.1.val ≤ R := step.1.isLt.le.trans hN
  have hr : step.2.val ≤ q := step.2.isLt.le
  have hz : z ≤ t.darts + o + R := by
    have h := selectedIndex_le t padding v step.1
    change z ≤ t.darts + o + step.1.val at h
    omega
  have hsize : (k + padding v) * q ≤ R := by
    dsimp only [R, k]
    rw [encodeWords_length, ExpanderTableWords.rotationWords_length]
    omega
  have hrotor : rotorSteps (tables v) rank p ≤ 2 * rank.val + 6 * R + 8 := by
    have h := rotorSteps_le (tables v) rank p
    change rotorSteps (tables v) rank p ≤ 2 * rank.val + 5 * R + (k + padding v) * q + 8 at h
    omega
  have hselect : selectionSteps t padding v step.1 ≤
      10 * L + 16 * R + 13 * v.val + 5 * k + 2 * o + 2 * t.darts + 57 := by
    have h := selectionSteps_le t padding v step.1
    change selectionSteps t padding v step.1 ≤
      10 * L + 16 * step.1.val + 13 * v.val + 5 * k + 2 * o + 2 * t.darts + 57 at h
    omega
  have hfinish : finishSteps q X z step.2.val outputLength ≤
      (5 * q + 7) * (t.darts + o + R) + 7 * q + 4 * X + 2 * outputLength + 40986 := by
    have h := finishSteps_le q X z step.2.val outputLength
    have hm := Nat.mul_le_mul_left (5 * q + 7) hz
    omega
  have htail : tailBits.length ≤ R := encodedDrop_length_le
    (ExpanderTableWords.rotationWords (tables v)) (q * rank.val + p.val + 1)
  have hcleanup : tailBits.length + step.1.val + step.2.val + z + 15 ≤
      R + R + q + (t.darts + o + R) + 15 := by omega
  calc
    coreSteps t padding tables v x p outputLength
        ≤ (2 * rank.val + 6 * R + 8) +
          (10 * L + 16 * R + 13 * v.val + 5 * k + 2 * o + 2 * t.darts + 57) +
          ((5 * q + 7) * (t.darts + o + R) + 7 * q + 4 * X + 2 * outputLength + 40986) +
          (R + R + q + (t.darts + o + R) + 15) :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hrotor hselect) hfinish) hcleanup
    _ = _ := by
      change _ = coreTimeBound q L R X v.val rank.val k o t.darts outputLength
      unfold coreTimeBound
      ring

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCloudPrefix
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_append _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_nil _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_append _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_nil _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_done _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_head _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headValue _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_row _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_head _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tableBits _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tableWords _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCompare.compareInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_remainingLevel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.handoffTapes_level _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.initialTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_emit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_fuel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_m _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_n _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_query _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_scratch _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_sum _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_work _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferLeft_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt.transferRight_tapes _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.atGuard _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Driver.program_guard _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.build_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.build_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rowList_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.actualRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCloudPrefix

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.PCP
open scoped BigOperators

def paddingView : Tape → Option MachineCloudPadding.Tape
  | .inner k => some k
  | _ => none

theorem paddingView_left (k : MachineCloudPadding.Tape) : paddingView (.inner k) = some k := rfl

theorem paddingView_right (j : Tape) (k : MachineCloudPadding.Tape)
    (h : paddingView j = some k) : Tape.inner k = j := by
  cases j <;> simp_all [paddingView]

theorem placedTapes (inner : MachineCloudPadding.Tape → List Bool) (extra : Tape → List Bool) :
    MachineCloudPadding.Placement.tapes paddingView inner extra =
      memory inner (extra .bound) (extra .remaining) (extra .total) := by
  funext j; cases j <;> rfl

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

theorem sumFrom_list (t : GraphTables.Table) (xs : List (Fin t.vertices)) (v : Nat)
    (hseq : ∀ i (hi : i < xs.length), (xs[i]).val = v + i) :
    sumFrom t v xs.length = (xs.map (PreprocessingRegularTables.padding t)).sum := by
  induction xs generalizing v with
  | nil => simp [sumFrom]
  | cons x xs ih =>
      have hx : x.val = v := by simpa using! hseq 0 (by simp)
      have hv : v < t.vertices := by simpa only [hx] using x.isLt
      have he : (⟨v, hv⟩ : Fin t.vertices) = x := Fin.ext hx.symm
      have hnext : ∀ i (hi : i < xs.length), (xs[i]).val = v + 1 + i := by
        intro i hi
        have h := hseq (i + 1) (by simpa using Nat.succ_lt_succ hi)
        simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using h
      simp only [List.length_cons, sumFrom, amount, dite_eq_left hv, he,
        List.map_cons, List.sum_cons]
      rw [ih (v + 1) hnext]
      rfl

theorem sumFrom_eq_offset (t : GraphTables.Table) (b : Nat) (hb : b ≤ t.vertices) :
    sumFrom t 0 b =
      PreprocessingPaddingOffsets.offset (PreprocessingRegularTables.padding t) b := by
  have h := sumFrom_list t ((List.finRange t.vertices).take b) 0
    (by intro i hi; simp only [List.getElem_take, List.getElem_finRange, Fin.val_cast,
      Nat.zero_add])
  simpa only [List.length_take, List.length_finRange, Nat.min_eq_left hb,
    PreprocessingPaddingOffsets.offset] using h

theorem initStep (table bound : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .init, ((ambient, false), register), frame table [] [] [] [] bound [] []⟩ =
      some ⟨some .copyFirst, ((ambient, false), register),
        frame table (encodeWord 0) [] [] [] bound [] (encodeWord 0)⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

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
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularMetadata
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_append _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_nil _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_append _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_nil _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_done _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_head _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_words _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_acceptsAt _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_get _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_reverseAt _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headValue _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_row _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_head _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tableBits _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tableWords _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_remainingLevel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.handoffTapes_level _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.initialTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.update_selectMemory_left _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.update_selectMemory_local _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.update_selectMemory_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.update_selectMemory_query _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.update_selectMemory_right _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularInternalRow.update_selectMemory_size _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_emit _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_fuel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_m _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_n _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_query _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_scratch _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_sum _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Header.update_frame_work _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.honest_vertexBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.cursorBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.prefixBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations.oldPredicate_relationAt _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Relations.relationAt_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.build_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.build_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rowList_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rows_at _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.basePredicate_transposeBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringRowData.basePredicate_walkBits _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringTest.poweredGraph_tail_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.equalityRelation_apply _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.actualRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Regularization.graph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual metadata preparation for an original regularized vertex. The
shared 27-tape row interface is preserved, with two explicit extra outputs
for padding count and geometric level. Family generation is a subsequent
stage and owns the rotor tape. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularMetadata

open Turing MachineComposition
open UniqueGamesTheorem.Foundations.PCP

variable {σ : Type}

/-- Fixed finite code. Original graph/global-index inputs are never replaced
by specification values; owner and rank queries are produced on the tapes. -/
def program : Label → TM2.Stmt Alphabet Label (State σ)
  | .owner l => MachineAffineLookup.instruction (.inl 1) ownerTapes 4098 2
      Label.owner (some .ownerClearQuery) l
  | .ownerClearQuery => MachineDrain.drain (.inl 9) .ownerClearQuery (some .ownerClearWork)
  | .ownerClearWork => MachineDrain.drain (.inl 10) .ownerClearWork (some .copyXFirst)
  | .copyXFirst => Reduction.MachineTransfer.loopAt (.inl 1) (.inl 10) id false
      .copyXFirst (some .copyXSecond)
  | .copyXSecond => MachineCopy.forkLoop (.inl 10) (.inl 1) (.inl 9) false
      .copyXSecond (some .copyOwnerFirst)
  | .copyOwnerFirst => Reduction.MachineTransfer.loopAt (.inl 2) (.inl 10) id false
      .copyOwnerFirst (some .copyOwnerSecond)
  | .copyOwnerSecond => MachineCopy.forkLoop (.inl 10) (.inl 2) (.inl 9) false
      .copyOwnerSecond (some .rankInit)
  | .rankInit => .push (.inl 3) (fun _ => false) (.goto fun _ => .rank .queryFirst)
  | .rank l => MachineCloudPadding.Placement.statement rankTape Label.rank
      (some .rankClearQuery) (MachineCloudRank.rankProgram l)
  | .rankClearQuery => MachineDrain.drain (.inl 9) .rankClearQuery (some .rankClearWork)
  | .rankClearWork => MachineDrain.drain (.inl 10) .rankClearWork (some .rankClearFuel)
  | .rankClearFuel => MachineDrain.drain (.inl 12) .rankClearFuel (some (.prefixCode .init))
  | .prefixCode l => MachineCloudPadding.Placement.statement prefixTape Label.prefixCode
      (some .prefixClearQuery) (MachineCloudPrefix.program l)
  | .prefixClearQuery => MachineDrain.drain (.inl 9) .prefixClearQuery (some .prefixClearFuel)
  | .prefixClearFuel => MachineDrain.drain (.inl 18) .prefixClearFuel (some (.cloud .init))
  | .cloud l => MachineCloudPadding.Placement.statement cloudTape Label.cloud none
      (MachineCloudPadding.program l)

def prefixView : Tape → Option MachineCloudPrefix.Tape
  | .inl i => match i.val with
    | 0 => some (.inner .table)
    | 9 => some (.inner .query)
    | 10 => some (.inner .count)
    | 11 => some (.inner .work)
    | 12 => some (.inner .scratch)
    | 13 => some (.inner .spare)
    | 14 => some (.inner .power)
    | 15 => some (.inner .level)
    | 16 => some (.inner .fuel)
    | 17 => some (.inner .product)
    | 2 => some .bound
    | 18 => some .remaining
    | 5 => some .total
    | _ => none
  | .inr _ => none

theorem prefixView_left (k : MachineCloudPrefix.Tape) : prefixView (prefixTape k) = some k := by
  cases k with
  | inner k => cases k <;> rfl
  | bound => rfl
  | remaining => rfl
  | total => rfl
theorem prefixView_right (j : Tape) (k : MachineCloudPrefix.Tape)
    (h : prefixView j = some k) : prefixTape k = j := by
  cases j with
  | inl j => fin_cases j <;> simp_all [prefixView, prefixTape] <;> subst k <;> rfl
  | inr j => simp_all [prefixView]

theorem cloudView_left (k : MachineCloudPadding.Tape) : cloudView (cloudTape k) = some k := by
  cases k <;> rfl
theorem cloudView_right (j : Tape) (k : MachineCloudPadding.Tape)
    (h : cloudView j = some k) : cloudTape k = j := by
  cases j with
  | inl j => fin_cases j <;> simp_all [cloudView, cloudTape] <;> subst k <;> rfl
  | inr j => cases j <;> simp_all [cloudView, cloudTape] <;> subst k <;> rfl

def cfg (label : Option Label) (data : Data) (ambient : σ) (register : Option Bool) :
    TM2.Cfg Alphabet Label (State σ) :=
  ⟨label, ((ambient, false), register), frame data⟩

/-- Common owner-based stage for original and dummy vertices. The count,
padding, and level are actual outputs of the checked physical cloud scan. -/
theorem cloudTrace (t : GraphTables.Table) (v : Fin t.vertices) (data : Data)
    (htable : data.table = GraphTables.tableBits t) (howner : data.owner = encodeWord v.val)
    (hcount : data.count = []) (hpadding : data.padding = []) (hlevel : data.level = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineCloudPadding.totalTime t v]
      (some (cfg (some (.cloud .init)) data ambient register)) =
      some (cfg none (cloudData t v data) ambient none) := by
  have raw := MachineCloudPadding.cloudPaddingTrace t v [] ambient register
  simp only [List.append_nil] at raw
  have placed := MachineCloudPadding.Placement.trace cloudTape cloudView cloudView_left cloudView_right
    Label.cloud none (frame data) MachineCloudPadding.program program (fun _ => rfl)
    (MachineCloudPadding.totalTime t v) _ _ raw
  have hstart : MachineCloudPadding.Placement.tapes cloudView
      (MachineCloudPadding.memory (GraphTables.tableBits t) (encodeWord v.val)
        [] [] [] [] [] [] [] []) (frame data) = frame data := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp_all [MachineCloudPadding.Placement.tapes, cloudView, frame, MachineCloudPadding.memory]
    | inr j => cases j <;>
        simp_all [MachineCloudPadding.Placement.tapes, cloudView, frame, MachineCloudPadding.memory]
  have hfinish : MachineCloudPadding.Placement.tapes cloudView
      (MachineCloudPadding.memory (GraphTables.tableBits t) (encodeWord v.val)
        (encodeWord (PreprocessingCloudIndex.cloudSize t v)) [] [] []
        (encodeWord (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v)))
        (encodeWord (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v))) [] [])
      (frame data) = frame (cloudData t v data) := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp_all [MachineCloudPadding.Placement.tapes, cloudView, frame, cloudData, MachineCloudPadding.memory]
    | inr j => cases j <;>
        simp_all [MachineCloudPadding.Placement.tapes, cloudView, frame, cloudData, MachineCloudPadding.memory]
  simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    hstart, hfinish, cfg] using placed

theorem drainAt (source : Tape) (again : Label) (exit : Option Label)
    (code : program (σ := σ) again = MachineDrain.drain source again exit)
    (base : Tape → List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[(base source).length + 1]
      (some ⟨some again, ((ambient, false), register), base⟩) =
      some ⟨exit, ((ambient, false), none), Function.update base source []⟩ := by
  simpa only [Function.update_eq_self] using
    MachineDrain.drainTrace source again exit program code base (base source)
      (ambient, false) register

/-- The actual padding-prefix scan, followed by removal of its copied query
and exhausted fuel. Every other core field is preserved. -/
theorem prefixTrace (t : GraphTables.Table) (v : Fin t.vertices) (data : Data)
    (htable : data.table = GraphTables.tableBits t) (howner : data.owner = encodeWord v.val)
    (hoffset : data.offset = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[prefixSteps t v]
      (some (cfg (some (.prefixCode .init)) data ambient register)) =
      some (cfg (some (.cloud .init)) (prefixData t v data) ambient none) := by
  have raw := MachineCloudPrefix.prefixTrace t v.val v.isLt.le [] ambient register
  simp only [List.append_nil] at raw
  let mid := MachineCloudPadding.Placement.tapes prefixView
    (MachineCloudPrefix.frame (GraphTables.tableBits t) (encodeWord v.val) [] [] []
      (encodeWord v.val) (encodeWord 0)
      (encodeWord (PreprocessingPaddingOffsets.offset
        (PreprocessingRegularTables.padding t) v.val))) (frame data)
  have placed := MachineCloudPadding.Placement.trace prefixTape prefixView prefixView_left
    prefixView_right Label.prefixCode (some .prefixClearQuery) (frame data)
    MachineCloudPrefix.program program (fun _ => rfl)
    (MachineCloudPrefix.totalTime t v.val []) _ _ raw
  have hstart : MachineCloudPadding.Placement.tapes prefixView
      (MachineCloudPrefix.frame (GraphTables.tableBits t) [] [] [] [] (encodeWord v.val) [] [])
      (frame data) = frame data := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp [htable, howner, hoffset, MachineCloudPadding.Placement.tapes, prefixView, frame,
          MachineCloudPrefix.frame, MachineCloudPrefix.memory, MachineCloudPadding.memory]
    | inr j => cases j <;> rfl
  have phase : (advance (TM2.step program))^[MachineCloudPrefix.totalTime t v.val []]
      (some (cfg (some (.prefixCode .init)) data ambient register)) =
      some ⟨some .prefixClearQuery, ((ambient, false), none), mid⟩ := by
    simpa only [MachineCloudPadding.Placement.configuration,
      MachineCloudPadding.Placement.label, hstart, cfg, mid] using placed
  have first := drainAt (.inl 9) .prefixClearQuery (some .prefixClearFuel) rfl mid ambient none
  have second := drainAt (.inl 18) .prefixClearFuel (some (.cloud .init)) rfl
    (Function.update mid (.inl 9) []) ambient none
  have hquery : (mid (.inl 9)).length + 1 = v.val + 2 := by
    simp [mid, MachineCloudPadding.Placement.tapes, prefixView, MachineCloudPrefix.frame, MachineCloudPrefix.memory,
      MachineCloudPadding.memory, encodeWord_length]
  have hfuel : ((Function.update mid (.inl 9) []) (.inl 18)).length + 1 = 2 := by
    simp [mid, MachineCloudPadding.Placement.tapes, prefixView, MachineCloudPrefix.frame, MachineCloudPrefix.memory,
      encodeWord_length]
  have hfinish : Function.update (Function.update mid (.inl 9) []) (.inl 18) [] =
      frame (prefixData t v data) := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp [htable, howner, mid, MachineCloudPadding.Placement.tapes, prefixView, frame, prefixData,
          MachineCloudPrefix.frame, MachineCloudPrefix.memory, MachineCloudPadding.memory]
    | inr j => cases j <;> rfl
  rw [hquery] at first
  rw [hfuel, hfinish] at second
  exact join_trace (join_trace phase first) second

theorem selected_owner (t : GraphTables.Table) (e : Fin t.darts) :
    (GraphTables.tableWords t)[4098 * e.val + 2]? = some t.rows[e].tail.val := by
  have h := congrArg (fun words : List Nat => words[0]?)
    (MachineRegularOriginalRow.tableWords_drop_row t e)
  simp only [List.getElem?_drop, Nat.add_zero] at h
  rw [show 2 + 4098 * e.val = 4098 * e.val + 2 by omega] at h
  simpa [GraphTables.rowWords] using h

/-- The owner is read from its actual field at `4098*x+2`; arithmetic, table
copy, lookup, and cleanup all execute in the finite machine. -/
theorem ownerTrace (t : GraphTables.Table) (e : Fin t.darts) (data : Data)
    (htable : data.table = GraphTables.tableBits t)
    (hindex : data.globalIndex = encodeWord e.val) (howner : data.owner = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[ownerSteps t e]
      (some (cfg (some (.owner .seed)) data ambient register)) =
      some (cfg (some .copyXFirst) (ownerData t e data) ambient none) := by
  have distinct : Function.Injective ownerTapes := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [ownerTapes]
  have outside : ∀ i, (.inl 1 : Tape) ≠ ownerTapes i := by
    intro i
    fin_cases i <;> decide
  let mid := MachineAffineLookup.finalTapes ownerTapes (frame data)
    (GraphTables.tableWords t) (4098 * e.val + 2) t.rows[e].tail.val
  have phase : (advance (TM2.step program))^[
      MachineAffineLookup.steps (GraphTables.tableWords t) e.val 4098 2]
      (some (cfg (some (.owner .seed)) data ambient register)) =
      some ⟨some .ownerClearQuery, ((ambient, false), none), mid⟩ := by
    exact MachineAffineLookup.affineLookupTrace (.inl 1) ownerTapes distinct outside 4098 2
      Label.owner (some .ownerClearQuery) program (fun _ => rfl) (frame data)
      (GraphTables.tableWords t) htable rfl e.val []
      (by change data.globalIndex = encodeWord e.val ++ [];
          simpa only [List.append_nil] using hindex)
      t.rows[e].tail.val (selected_owner t e) (ambient, false) register
  have first := drainAt (.inl 9) .ownerClearQuery (some .ownerClearWork) rfl mid ambient none
  have second := drainAt (.inl 10) .ownerClearWork (some .copyXFirst) rfl
    (Function.update mid (.inl 9) []) ambient none
  have hquery : (mid (.inl 9)).length + 1 = 2 := by
    simp [mid, MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes,
      MachineLookup.tapes, ownerTapes, frame, encodeWord_length]
  have hwork : (Function.update mid (.inl 9) []) (.inl 10) = ownerRemainder t e := by
    simp [mid, MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes,
      MachineLookup.tapes, ownerTapes, frame, ownerRemainder]
  have hfinish : Function.update (Function.update mid (.inl 9) []) (.inl 10) [] =
      frame (ownerData t e data) := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp [howner, mid, MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes,
          MachineLookup.tapes, ownerTapes, frame, ownerData]
    | inr j => cases j <;> rfl
  rw [hquery] at first
  rw [hwork, hfinish] at second
  exact join_trace (join_trace phase first) second

/-- Two preserving copy loops physically create `[owner,x]`; a transition
then initializes the unary result counter. -/
theorem queryTrace (data : Data) (v x : Nat)
    (howner : data.owner = encodeWord v) (hindex : data.globalIndex = encodeWord x)
    (hrank : data.localRank = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[querySteps v x]
      (some (cfg (some .copyXFirst) data ambient register)) =
      some ⟨some (.rank .queryFirst), ((ambient, false), none), queryFrame data v x⟩ := by
  let first := Function.update (frame data) (.inl 9) data.globalIndex
  let second := Function.update first (.inl 9) (data.owner ++ data.globalIndex)
  have copyX := MachineCopy.copyTrace (.inl 1 : Tape) (.inl 9) (.inl 10)
    (by decide) (by decide) (by decide) false Label.copyXFirst Label.copyXSecond
    (some .copyOwnerFirst) program rfl rfl (frame data) rfl (ambient, false) register
  have copyOwner := MachineCopy.copyTrace (.inl 2 : Tape) (.inl 9) (.inl 10)
    (by decide) (by decide) (by decide) false Label.copyOwnerFirst Label.copyOwnerSecond
    (some .rankInit) program rfl rfl first (by simp [first, frame]) (ambient, false) none
  have firstRun : (advance (TM2.step program))^[2 * (x + 2)]
      (some (cfg (some .copyXFirst) data ambient register)) =
      some ⟨some .copyOwnerFirst, ((ambient, false), none), first⟩ := by
    simpa only [frame_index, frame_query_empty, hindex, encodeWord_length,
      List.append_nil, cfg, first] using copyX
  have secondRun : (advance (TM2.step program))^[2 * (v + 2)]
      (some ⟨some .copyOwnerFirst, ((ambient, false), none), first⟩) =
      some ⟨some .rankInit, ((ambient, false), none), second⟩ := by
    simpa [first, frame, howner, encodeWord_length, second] using copyOwner
  have init : (advance (TM2.step program))^[1]
      (some ⟨some .rankInit, ((ambient, false), none), second⟩) =
      some ⟨some (.rank .queryFirst), ((ambient, false), none), queryFrame data v x⟩ := by
    have ht : Function.update second (.inl 3) (false :: second (.inl 3)) =
        queryFrame data v x := by
      funext j
      cases j with
      | inl j => fin_cases j <;>
          simp_all [queryFrame, second, first, frame, rankQuery,
            MachineCloudRank.queryWord, encodeWord]
      | inr j => cases j <;> rfl
    simp only [Function.iterate_one, advance_some, TM2.step, program, TM2.stepAux, ht]
  exact join_trace (join_trace firstRun secondRun) init

/-- Rank is computed by physically scanning earlier original rows, with the
fresh query and copied scan/fuel all removed before the next phase. -/
theorem rankTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v) (data : Data)
    (htable : data.table = GraphTables.tableBits t)
    (howner : data.owner = encodeWord v.val) (hindex : data.globalIndex = encodeWord e.val.val)
    (hrank : data.localRank = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[rankSteps t v e]
      (some (cfg (some .copyXFirst) data ambient register)) =
      some (cfg (some (.prefixCode .init)) (rankData t v e data) ambient none) := by
  have query := queryTrace data v.val e.val.val howner hindex hrank ambient register
  have raw := MachineCloudRank.cloudRankTrace t v e [] [] ambient none
  simp only [List.append_nil] at raw
  let mid := MachineCloudPadding.Placement.tapes rankView
    (MachineCloudCount.memory (GraphTables.tableBits t) (rankRemainder t v e)
      (rankQuery v.val e.val.val) []
      (encodeWord (PreprocessingCloudIndex.cloudRank t v e).val) (encodeWord 0)) (frame data)
  have placed := MachineCloudPadding.Placement.trace rankTape rankView rankView_left
    rankView_right Label.rank (some .rankClearQuery) (frame data)
    MachineCloudRank.rankProgram program (fun _ => rfl)
    (MachineCloudRank.rankSteps t.vertices t.darts v.val e.val.val (MachineCloudCount.tableRows t) [])
    _ _ raw
  have hstart : MachineCloudPadding.Placement.tapes rankView
      (MachineCloudCount.memory (GraphTables.tableBits t) []
        (rankQuery v.val e.val.val) [] (encodeWord 0) []) (frame data) =
      queryFrame data v.val e.val.val := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp_all [MachineCloudPadding.Placement.tapes, rankView, frame,
          queryFrame, MachineCloudCount.memory]
    | inr j => cases j <;> rfl
  simp only [rankQuery] at hstart
  have phase : (advance (TM2.step program))^[
      MachineCloudRank.rankSteps t.vertices t.darts v.val e.val.val (MachineCloudCount.tableRows t) []]
      (some ⟨some (.rank .queryFirst), ((ambient, false), none), queryFrame data v.val e.val.val⟩) =
      some ⟨some .rankClearQuery, ((ambient, false), none), mid⟩ := by
    simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
      hstart, mid, rankQuery, rankRemainder] using placed
  have first := drainAt (.inl 9) .rankClearQuery (some .rankClearWork) rfl mid ambient none
  have second := drainAt (.inl 10) .rankClearWork (some .rankClearFuel) rfl
    (Function.update mid (.inl 9) []) ambient none
  have third := drainAt (.inl 12) .rankClearFuel (some (.prefixCode .init)) rfl
    (Function.update (Function.update mid (.inl 9) []) (.inl 10) []) ambient none
  have hquery : mid (.inl 9) = rankQuery v.val e.val.val := rfl
  have hwork : Function.update mid (.inl 9) [] (.inl 10) = rankRemainder t v e := by
    simp [mid, MachineCloudPadding.Placement.tapes, rankView, MachineCloudCount.memory]
  have hfuel : ((Function.update (Function.update mid (.inl 9) []) (.inl 10) [])
      (.inl 12)).length + 1 = 2 := by
    simp [mid, MachineCloudPadding.Placement.tapes, rankView, MachineCloudCount.memory,
      encodeWord_length]
  have hfinish : Function.update
      (Function.update (Function.update mid (.inl 9) []) (.inl 10) []) (.inl 12) [] =
      frame (rankData t v e data) := by
    funext j
    cases j with
    | inl j => fin_cases j <;>
        simp [mid, MachineCloudPadding.Placement.tapes, rankView, frame, rankData,
          MachineCloudCount.memory, htable]
    | inr j => cases j <;> rfl
  rw [hquery] at first
  rw [hwork] at second
  rw [hfuel, hfinish] at third
  exact join_trace (join_trace (join_trace (join_trace query phase) first) second) third

/-- Full original-vertex metadata preparation. Inputs and all row/output
fields are preserved, results occupy their agreed physical tapes, and every
one of the eighteen core work tapes is empty at return. -/
theorem originalTrace (t : GraphTables.Table) (e : Fin t.darts) (data : Data)
    (htable : data.table = GraphTables.tableBits t)
    (hindex : data.globalIndex = encodeWord e.val)
    (howner : data.owner = []) (hrank : data.localRank = []) (hcount : data.count = [])
    (hoffset : data.offset = []) (hpadding : data.padding = []) (hlevel : data.level = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[totalTime t e]
      (some (cfg (some (.owner .seed)) data ambient register)) =
      some (cfg none (originalData t e data) ambient none) := by
  have own := ownerTrace t e data htable hindex howner ambient register
  have rank := rankTrace t t.rows[e].tail (originalMember t e) (ownerData t e data)
    htable rfl hindex hrank ambient none
  have pref := prefixTrace t t.rows[e].tail
    (rankData t t.rows[e].tail (originalMember t e) (ownerData t e data))
    htable rfl hoffset ambient none
  have cloud := cloudTrace t t.rows[e].tail
    (prefixData t t.rows[e].tail
      (rankData t t.rows[e].tail (originalMember t e) (ownerData t e data)))
    htable rfl hcount hpadding hlevel ambient none
  exact join_trace (join_trace (join_trace own rank) pref) cloud

theorem ownerRemainder_length_le (t : GraphTables.Table) (e : Fin t.darts) :
    (ownerRemainder t e).length ≤ (GraphTables.tableBits t).length :=
  encodeWords_drop_length_le _ _

theorem rankRemainder_length_le (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v) :
    (rankRemainder t v e).length ≤ (GraphTables.tableBits t).length := by
  have split := congrArg List.length
    (MachineCloudRank.encoded_rows_split (MachineCloudCount.tableRows t) e.val.val)
  have input := MachineCloudCount.inputWord_length t.vertices t.darts (MachineCloudCount.tableRows t)
  rw [MachineCloudCount.tableRows_input] at input
  simp only [List.length_append] at split
  unfold rankRemainder
  omega

theorem totalTime_le (t : GraphTables.Table) (e : Fin t.darts) :
    totalTime t e ≤ timePolynomial.eval (GraphTables.tableBits t).length := by
  let v := t.rows[e].tail
  let c := originalMember t e
  let N := (GraphTables.tableBits t).length
  have hn := GraphTables.vertices_le_tableBits_length t
  have hm := GraphTables.darts_le_tableBits_length t
  have hv : v.val < N := lt_of_lt_of_le v.isLt hn
  have hx : e.val ≤ N := e.isLt.le.trans hm
  have ownerBound := MachineAffineLookup.steps_le (GraphTables.tableWords t)
    e.val 4098 2 t.rows[e].tail.val (selected_owner t e)
  have ownerRest := ownerRemainder_length_le t e
  have rankBound := MachineCloudRank.rankSteps_le t.vertices t.darts v.val e.val
    (MachineCloudCount.tableRows t) []
  rw [MachineCloudCount.tableRows_input] at rankBound
  have rankRest := rankRemainder_length_le t v c
  have hpIn : MachineCloudPrefix.inputLength t v.val [] ≤ 2*N := by
    simp only [MachineCloudPrefix.inputLength, List.append_nil, encodeWord_length]
    omega
  have hcIn : MachineCloudPadding.inputLength t v [] ≤ 2*N := by
    simp only [MachineCloudPadding.inputLength, List.append_nil, encodeWord_length]
    omega
  have hp := (MachineCloudPrefix.totalTime_le t v.val v.isLt.le []).trans
    (natPolynomial_eval_mono MachineCloudPrefix.timePolynomial hpIn)
  have hc := (MachineCloudPadding.totalTime_le t v []).trans
    (natPolynomial_eval_mono MachineCloudPadding.timePolynomial hcIn)
  have ho := overhead_le N e.val v.val hx hv.le
  have hsmall : ownerSteps t e + rankSteps t v c + (v.val+2) + 2 ≤
      overhead N e.val v.val := by
    simp only [MachineCloudRank.queryWord, List.length_append, encodeWord_length,
      List.length_nil] at rankBound
    simp only [ownerSteps, rankSteps, querySteps, rankQuery, MachineCloudRank.queryWord,
      List.length_append, encodeWord_length, List.length_nil, overhead]
    change _ ≤ _ at ownerBound
    dsimp only [c, originalMember] at rankRest ⊢
    change MachineAffineLookup.steps (GraphTables.tableWords t) e.val 4098 2 ≤
      2*e.val+5*N+6 at ownerBound
    omega
  have htotal : totalTime t e = ownerSteps t e + rankSteps t v c +
      MachineCloudPrefix.totalTime t v.val [] + (v.val+2) + 2 +
        MachineCloudPadding.totalTime t v := by
    simp only [totalTime, prefixSteps, v, c]
    omega
  rw [htotal]
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one]
  change _ ≤ MachineCloudPrefix.timePolynomial.eval (2*N) +
    MachineCloudPadding.timePolynomial.eval (2*N) + 40*(N+1)
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularMetadata

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachinePaddedOverlayRuntimeLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for the actual regularization subcalls. These lemmas
bound the established step counts; they do not assume any machine execution. -/
namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularExecutionBounds

open Turing MachineComposition PCP PCP.PreprocessingRegularTables PCP.PreprocessingCloudIndex
open PCP.PreprocessingMachineBounds MachineRegularInternalRow

/-- The completed reusable family call includes the three actual drains. -/
theorem family_budget_le (t : GraphTables.Table) (v : Fin t.vertices) :
    MachinePaddedExpanderFamilyBounds.timePolynomial.eval (cloudSize t v + 1) +
      2 * ExpanderFamily.growth * (cloudSize t v + 1) + 7 ≤
        familyPolynomial.eval (inputLength t) := by
  have h := Nat.add_le_add_right (cloudSize_le_input t v) 1
  have hp := natPolynomial_eval_mono MachinePaddedExpanderFamilyBounds.timePolynomial h
  have hm := Nat.mul_le_mul_left (2 * ExpanderFamily.growth) h
  simp only [familyPolynomial, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_ofNat]
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularExecutionBounds

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularFamily
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlay.familyView_left _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.cursorBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.prefixBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
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
abbrev Alphabet (_ : Tape) := Bool
abbrev SmallTable := MachinePaddedExpanderFamily.SmallTable

def inputNative : NativeTape := .inr .input
def outputNative : NativeTape := .inl MachineExpanderFamily.tableTape
def powerNative : NativeTape := .inr .power
def sizeNative : NativeTape := .inl (.inr .currentSize)
def levelNative : NativeTape := .inl (.inr .remainingLevel)

def powerTape : Tape := .inr powerNative
def sizeTape : Tape := .inr sizeNative
def levelTape : Tape := .inr levelNative

/-- Unused private shadows of the two public roles remain empty. -/
def familyTape (t : NativeTape) : Tape :=
  if t = inputNative then .inl 4 else if t = outputNative then .inl 7 else .inr t

def familyView : Tape → Option NativeTape
  | .inl i => if i = 4 then some inputNative else if i = 7 then some outputNative else none
  | .inr t => if t = inputNative then none else if t = outputNative then none else some t

theorem familyView_left (t : NativeTape) : familyView (familyTape t) = some t := by
  by_cases hi : t = inputNative
  · subst t; simp [familyTape, familyView]
  · by_cases ho : t = outputNative
    · subst t; simp [familyTape, familyView, hi]
    · simp [familyTape, familyView, hi, ho]

theorem familyView_right (j : Tape) (t : NativeTape)
    (h : familyView j = some t) : familyTape t = j := by
  cases j with
  | inl i =>
    by_cases hi : i = 4
    · subst i
      have ht : inputNative = t := by simpa [familyView] using h
      subst t; simp [familyTape]
    · by_cases ho : i = 7
      · subst i
        have ht : outputNative = t := by simpa [familyView] using h
        subst t; simp [familyTape, inputNative, outputNative]
      · simp [familyView, hi, ho] at h
  | inr j =>
    by_cases hi : j = inputNative
    · simp [familyView, hi] at h
    · by_cases ho : j = outputNative
      · simp [familyView, ho] at h
      · have ht : j = t := by simpa [familyView, hi, ho] using h
        subst t; simp [familyTape, hi, ho]

inductive Label
  | start
  | family (label : MachinePaddedExpanderFamily.Label)
  | drainPower | drainSize | drainLevel
  deriving DecidableEq, Fintype

def frame (core : CoreTape → List Bool) : Tape → List Bool
  | .inl i => core i
  | .inr _ => []

def rotor (H : SmallTable) (k : Nat) : List Bool :=
  MachinePaddedExpanderFamilyBounds.outputWord H k

def resultCore (H : SmallTable) (k : Nat) (core : CoreTape → List Bool) :
    CoreTape → List Bool := Function.update core 7 (rotor H k)

def working (core : CoreTape → List Bool) (power size level : List Bool) : Tape → List Bool
  | .inl i => core i
  | .inr t => if t = powerNative then power
      else if t = sizeNative then size else if t = levelNative then level else []

@[simp] theorem working_power (core : CoreTape → List Bool) (p s l : List Bool) :
    working core p s l powerTape = p := by simp [working, powerTape]

@[simp] theorem working_size (core : CoreTape → List Bool) (p s l : List Bool) :
    working core p s l sizeTape = s := by
  simp [working, sizeTape, powerNative, sizeNative]

@[simp] theorem working_level (core : CoreTape → List Bool) (p s l : List Bool) :
    working core p s l levelTape = l := by
  simp [working, levelTape, powerNative, sizeNative, levelNative]

theorem update_working_power (core : CoreTape → List Bool) (p s l p' : List Bool) :
    Function.update (working core p s l) powerTape p' = working core p' s l := by
  funext t
  cases t with
  | inl i => simp [working, powerTape]
  | inr t => by_cases h : t = powerNative <;> simp [working, powerTape, h]

theorem update_working_size (core : CoreTape → List Bool) (p s l s' : List Bool) :
    Function.update (working core p s l) sizeTape s' = working core p s' l := by
  funext t
  cases t with
  | inl i => simp [working, sizeTape]
  | inr t =>
    by_cases h : t = sizeNative
    · subst t; simp [working, sizeTape, powerNative, sizeNative]
    · simp [working, sizeTape, h]

theorem update_working_level (core : CoreTape → List Bool) (p s l l' : List Bool) :
    Function.update (working core p s l) levelTape l' = working core p s l' := by
  funext t
  cases t with
  | inl i => simp [working, levelTape]
  | inr t =>
    by_cases h : t = levelNative
    · subst t; simp [working, levelTape, powerNative, sizeNative, levelNative]
    · simp [working, levelTape, h]

@[simp] theorem working_empty (core : CoreTape → List Bool) :
    working core [] [] [] = frame core := by
  funext t; cases t <;> simp [working, frame]

theorem initial_other (k : Nat) (t : NativeTape) (h : t ≠ inputNative) :
    MachinePaddedExpanderFamily.initialTapes k t = [] := by
  cases t with
  | inl t => rfl
  | inr t => cases t <;> simp_all [MachinePaddedExpanderFamily.initialTapes, inputNative]

/-- The only retained native work words are the two sizes and the exhausted level. -/
theorem final_other (H : SmallTable) (k : Nat) (t : NativeTape)
    (hi : t ≠ inputNative) (ho : t ≠ outputNative) (hp : t ≠ powerNative)
    (hs : t ≠ sizeNative) (hl : t ≠ levelNative) :
    MachinePaddedExpanderFamily.finalTapes H k t = [] := by
  rcases t with ((row | tableExtra) | familyExtra) | ceiling
  · cases row <;>
      simp_all [inputNative, outputNative, MachineExpanderFamily.tableTape,
        MachinePaddedExpanderFamily.finalTapes, MachineExpanderFamily.toBoolTapes,
        MachineExpanderFamily.toBoolWord, MachineExpanderFamily.familyTapes,
        MachineExpanderFamily.boundaryTapes, MachineExpanderFamily.tableFrame,
        MachineEmbedding.tapes]
  · cases tableExtra <;> rfl
  · cases familyExtra <;>
      simp_all [sizeNative, levelNative, MachinePaddedExpanderFamily.finalTapes,
        MachineExpanderFamily.toBoolTapes, MachineExpanderFamily.toBoolWord,
        MachineExpanderFamily.familyTapes, MachineExpanderFamily.boundaryTapes,
        MachineExpanderFamily.extraFrame, MachineEmbedding.tapes]
  · cases ceiling <;>
      simp_all [inputNative, powerNative, MachinePaddedExpanderFamily.finalTapes,
        MachinePaddedExpanderFamily.retainedCeilingTapes, MachineCeilingPower.memory]

theorem initial_placement (k : Nat) (core : CoreTape → List Bool)
    (hinput : core 4 = encodeWord k) (houtput : core 7 = []) :
    Placement.tapes familyView (MachinePaddedExpanderFamily.initialTapes k) (frame core) =
      frame core := by
  funext t
  cases t with
  | inl i =>
    by_cases hi : i = 4
    · subst i; simp [Placement.tapes, familyView, frame, inputNative, hinput]
    · by_cases ho : i = 7
      · subst i
        simp [Placement.tapes, familyView, frame, outputNative,
          MachinePaddedExpanderFamily.initialTapes, houtput]
      · simp [Placement.tapes, familyView, frame, hi, ho]
  | inr t =>
    by_cases hi : t = inputNative
    · simp [Placement.tapes, familyView, frame, hi]
    · by_cases ho : t = outputNative
      · simp [Placement.tapes, familyView, frame, ho]
      · simp [Placement.tapes, familyView, frame, hi, ho, initial_other k t hi]

theorem final_placement (H : SmallTable) (k : Nat) (core : CoreTape → List Bool)
    (hinput : core 4 = encodeWord k) :
    Placement.tapes familyView (MachinePaddedExpanderFamily.finalTapes H k) (frame core) =
      working (resultCore H k core)
        (encodeWord (PCP.PreprocessingLevels.paddedSize k))
        (encodeWord (PCP.PreprocessingLevels.paddedSize k)) (encodeWord 0) := by
  funext t
  cases t with
  | inl i =>
    by_cases hi : i = 4
    · subst i
      simp [Placement.tapes, familyView, working, resultCore, inputNative, hinput]
    · by_cases ho : i = 7
      · subst i
        simp [Placement.tapes, familyView, working, resultCore, outputNative,
          rotor, MachinePaddedExpanderFamilyBounds.outputWord]
        change MachinePaddedExpanderFamily.finalTapes H k
          (MachinePaddedExpanderFamily.familyTape MachineExpanderFamily.tableTape) = _
        exact MachinePaddedExpanderFamily.finalTapes_table H k
      · simp [Placement.tapes, familyView, working, resultCore, frame, hi, ho]
  | inr t =>
    by_cases hi : t = inputNative
    · subst t
      simp [Placement.tapes, familyView, working, frame,
        inputNative, powerNative, sizeNative, levelNative]
    · by_cases ho : t = outputNative
      · subst t
        simp [Placement.tapes, familyView, working, frame,
          outputNative, MachineExpanderFamily.tableTape, inputNative,
          powerNative, sizeNative, levelNative]
      · by_cases hp : t = powerNative
        · subst t
          simp [Placement.tapes, familyView, working, powerNative, inputNative, outputNative]
        · by_cases hs : t = sizeNative
          · subst t
            simpa [Placement.tapes, familyView, working, sizeNative,
              powerNative, inputNative, outputNative, MachineExpanderFamily.tableTape,
              MachinePaddedExpanderFamily.familyTape] using
              MachinePaddedExpanderFamily.finalTapes_currentSize H k
          · by_cases hl : t = levelNative
            · subst t
              simpa [Placement.tapes, familyView, working, levelNative,
                sizeNative, powerNative, inputNative, outputNative,
                MachineExpanderFamily.tableTape, MachinePaddedExpanderFamily.ceilingTape] using
                MachinePaddedExpanderFamily.finalTapes_remainingLevel H k
            · simp [Placement.tapes, familyView, working, hi, ho, hp, hs, hl,
                final_other H k t hi ho hp hs hl]

theorem totalBudget_le (k : Nat) :
    1 + MachinePaddedExpanderFamilyBounds.timePolynomial.eval (encodeWord k).length +
        (2 * PCP.PreprocessingLevels.paddedSize k + 6) ≤
      timePolynomial.eval (encodeWord k).length := by
  have hs := MachineExpanderFamilyBounds.paddedSize_le_succ_input k
  have hm := Nat.mul_le_mul_left 2 hs
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat, encodeWord_length]
  simp only [Nat.mul_assoc] at hm ⊢
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularFamily

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOriginalClean
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_archive _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes_rowIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_append _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_nil _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_append _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_nil _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_done _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_head _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRow_words _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_acceptsAt _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_get _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericRows_reverseAt _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headValue _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_row _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_head _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tableBits _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tableWords _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.divisionOutput_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.emittedWord_target _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame0_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame10_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame11_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame12_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame1_inputVertex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame2_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame3_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame4_remainderFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame5_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame6_quotientFirst _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame7_queryReverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_queryIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame8_table _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_lookupOutput _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_quotientSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow.frame9_remainderSecond _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_quotient _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_remainder _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineFixedDivMod.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_power _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.finalTapes_remainingLevel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.handoffTapes_level _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedExpanderFamily.initialTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.finalTapes_prefix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.addInTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_destination _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAddAt.unaryTapes_source _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.cursorBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.prefixBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.build_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.build_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rowList_length _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Table.rows_at _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.actualRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reusable inherited-row execution with actual cleanup

Five concrete drain loops remove the query delimiter, unread scan suffix,
raw reverse field, computed reverse field, and copied relation. With initially
empty work tapes, the only final tape change is the appended output row. The
index on tape zero and input table on tape one are both preserved.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalClean

open Turing MachineComposition PCP PCP.GraphTables PCP.PreprocessingRegularTables

theorem cleanupTraceAt {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (base : Tape → List Bool) (state : State σ) :
    (advance (TM2.step program))^[cleanupSteps base]
      (some ⟨some (labels .query), state, base⟩) =
      some ⟨exit, (state.1, none), cleanupTapes base⟩ := by
  let t1 := Function.update base (2 : Tape) []
  let t2 := Function.update t1 (3 : Tape) []
  let t3 := Function.update t2 (4 : Tape) []
  let t4 := Function.update t3 (6 : Tape) []
  have h0 := MachineDrain.drainTrace (2 : Tape) (labels .query) (some (labels .scan))
    program (code .query) base (base 2) state.1 state.2
  have h1 := MachineDrain.drainTrace (3 : Tape) (labels .scan) (some (labels .rawReverse))
    program (code .scan) t1 (t1 3) state.1 none
  have h2 := MachineDrain.drainTrace (4 : Tape) (labels .rawReverse) (some (labels .computedReverse))
    program (code .rawReverse) t2 (t2 4) state.1 none
  have h3 := MachineDrain.drainTrace (6 : Tape) (labels .computedReverse) (some (labels .relation))
    program (code .computedReverse) t3 (t3 6) state.1 none
  have h4 := MachineDrain.drainTrace (7 : Tape) (labels .relation) exit
    program (code .relation) t4 (t4 7) state.1 none
  simp only [Function.update_eq_self] at h0 h1 h2 h3 h4
  simp only [t1, t2, t3, t4, Function.update_of_ne (by decide : (3 : Tape) ≠ 2),
    Function.update_of_ne (by decide : (4 : Tape) ≠ 3),
    Function.update_of_ne (by decide : (4 : Tape) ≠ 2),
    Function.update_of_ne (by decide : (6 : Tape) ≠ 4),
    Function.update_of_ne (by decide : (6 : Tape) ≠ 3),
    Function.update_of_ne (by decide : (6 : Tape) ≠ 2),
    Function.update_of_ne (by decide : (7 : Tape) ≠ 6),
    Function.update_of_ne (by decide : (7 : Tape) ≠ 4),
    Function.update_of_ne (by decide : (7 : Tape) ≠ 3),
    Function.update_of_ne (by decide : (7 : Tape) ≠ 2)] at h1 h2 h3 h4
  exact join_trace (join_trace (join_trace (join_trace h0 h1) h2) h3) h4

theorem cleanup_frame (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    cleanupTapes (MachineRegularOriginalRow.finalTapes q t e base) =
      Function.update base 9
        (base 9 ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e)) := by
  funext k
  fin_cases k <;>
    simp [cleanupTapes, MachineRegularOriginalRow.finalTapes,
      MachineRegularOriginalRow.affined, MachineRegularOriginalRow.copied,
      MachineRegularOriginalRow.looked, MachineAffineLookup.finalTapes,
      MachinePreservingLookup.finalTapes, MachineLookup.tapes,
      MachineRegularOriginalRow.lookupTape, input.queryEmpty, input.scanEmpty,
      input.reverseEmpty, input.computedEmpty, input.relationEmpty]

theorem suffix_length_le (t : Table) (e : Fin t.darts) :
    (encodeWords (MachineRegularOriginalRow.suffixWords t e)).length ≤ (tableBits t).length := by
  have hlength : (tableBits t).length =
      (encodeWords (MachineRegularOriginalRow.prefixWords t e)).length +
        ((encodeWords (rowWords t.rows[e])).length +
          (encodeWords (MachineRegularOriginalRow.suffixWords t e)).length) := by
    rw [tableBits, MachineRegularOriginalRow.tableWords_at_row,
      encodeWords_append, encodeWords_append, List.length_append, List.length_append]
  omega

theorem cleanupSteps_eq (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    cleanupSteps (MachineRegularOriginalRow.finalTapes q t e base) =
      (encodeWords (MachineRegularOriginalRow.suffixWords t e)).length +
        (q + 2) * t.rows[e].reverseIndex.val + q +
          (encodeWords (relationWords t.rows[e].relation)).length + 8 := by
  have hquery : MachineRegularOriginalRow.finalTapes q t e base 2 = encodeWord 0 := by
    simp only [MachineRegularOriginalRow.finalTapes,
      Function.update_of_ne (by decide : (2 : Tape) ≠ 9), MachineRegularOriginalRow.affined,
      Function.update_of_ne (by decide : (2 : Tape) ≠ 6), MachineRegularOriginalRow.copied,
      Function.update_of_ne (by decide : (2 : Tape) ≠ 7),
      Function.update_of_ne (by decide : (2 : Tape) ≠ 3)]
    change MachineLookup.tapes (2 : Tape) 3 4 base
      (encodeWord 0 ++ base 2)
      (encodeWords ((GraphTables.tableWords t).drop (4098 * e.val + 3 + 1)) ++ base 3)
      (encodeWord t.rows[e].reverseIndex.val ++ base 4) 2 = _
    rw [MachineLookup.tapes_index _ _ _ (by decide) (by decide), input.queryEmpty,
      List.append_nil]
  have hscan : MachineRegularOriginalRow.finalTapes q t e base 3 =
      encodeWords (MachineRegularOriginalRow.suffixWords t e) := by
    simp only [MachineRegularOriginalRow.finalTapes,
      Function.update_of_ne (by decide : (3 : Tape) ≠ 9), MachineRegularOriginalRow.affined,
      Function.update_of_ne (by decide : (3 : Tape) ≠ 6), MachineRegularOriginalRow.copied,
      Function.update_of_ne (by decide : (3 : Tape) ≠ 7), Function.update_self,
      input.scanEmpty, List.append_nil]
  have hraw : MachineRegularOriginalRow.finalTapes q t e base 4 =
      encodeWord t.rows[e].reverseIndex.val := by
    simp only [MachineRegularOriginalRow.finalTapes,
      Function.update_of_ne (by decide : (4 : Tape) ≠ 9), MachineRegularOriginalRow.affined,
      Function.update_of_ne (by decide : (4 : Tape) ≠ 6), MachineRegularOriginalRow.copied_reverse,
      input.reverseEmpty, List.append_nil]
  have hcomputed : MachineRegularOriginalRow.finalTapes q t e base 6 =
      encodeWord ((q + 1) * t.rows[e].reverseIndex.val + q) := by
    simp only [MachineRegularOriginalRow.finalTapes,
      Function.update_of_ne (by decide : (6 : Tape) ≠ 9), MachineRegularOriginalRow.affined_reverse,
      input.computedEmpty, List.append_nil]
  have hrelation : MachineRegularOriginalRow.finalTapes q t e base 7 =
      encodeWords (relationWords t.rows[e].relation) := by
    simp only [MachineRegularOriginalRow.finalTapes,
      Function.update_of_ne (by decide : (7 : Tape) ≠ 9), MachineRegularOriginalRow.affined_relation,
      input.relationEmpty, List.append_nil]
  simp only [cleanupSteps, hquery, hscan, hraw, hcomputed, hrelation, encodeWord_length]
  ring

theorem cleanupSteps_le (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    cleanupSteps (MachineRegularOriginalRow.finalTapes q t e base) ≤
      (q + 3) * (tableBits t).length + q + 8200 := by
  rw [cleanupSteps_eq q t e base input]
  have hsuffix := suffix_length_le t e
  have htable := tableWords_length_le_bits t
  have hr : t.rows[e].reverseIndex.val ≤ (tableBits t).length := by
    have hrlt := t.rows[e].reverseIndex.isLt
    omega
  have hmul := Nat.mul_le_mul_left (q + 2) hr
  have hrel := relationBits_length_le t.rows[e].relation
  nlinarith

theorem steps_le (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    steps q t e base ≤ timeBound q (tableBits t).length (base 9).length := by
  have hrow := MachineRegularOriginalRow.steps_le q t e base
  have hclean := cleanupSteps_le q t e base input
  unfold steps timeBound MachineRegularOriginalRow.timeBound at *
  nlinarith

theorem traceAt {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (input : Input t e base)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps q t e base]
      (some ⟨some (labels (.row (.lookup .seed))),
        ((ambient, MachineRegularOriginalRow.zeroBuffer), register), base⟩) =
      some ⟨exit, ((ambient, MachineRegularOriginalRow.zeroBuffer), none),
        Function.update base 9
          (base 9 ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e))⟩ := by
  have row := MachineRegularOriginalRow.traceAt q (fun l => labels (.row l))
    (some (labels .query)) program (fun l => code (.row l)) t e base input.toInput ambient register
  have clean := cleanupTraceAt q labels exit program code
    (MachineRegularOriginalRow.finalTapes q t e base)
    ((ambient, MachineRegularOriginalRow.zeroBuffer), none)
  rw [cleanup_frame q t e base input] at clean
  exact join_trace row clean

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalClean

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularVertexBlock
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual regularized vertex-block execution

The finite internal-port loop invokes the checked row machine for every port in
order. Each invocation restores the shared 27-tape frame. Inherited-row stages
use fixed tape placements and finite state permutations.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularVertexBlock

open Turing MachineComposition PCP MachineRegularInternalRow
open PreprocessingCloudIndex PreprocessingRegularTables

variable {σ Λ : Type}

/-- Every body is an actual invocation of `coreTrace`; the code hypothesis only
states the fixed placement into the caller's program. -/
theorem portPrefixTrace (q : Nat) (positive : 0 < q)
    (labels : PortLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = portInstruction q positive labels exit l)
    (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) (output : List Bool) (ambient : σ)
    (k : Nat) (hk : k ≤ q) :
    (advance (TM2.step program))^[portSteps t padding tables v x output.length k]
      (some ⟨portEntry q labels exit 0, coreInitialState q positive ambient,
        coreInputTapes t padding tables v x output⟩) =
      some ⟨portEntry q labels exit k, coreInitialState q positive ambient,
        coreInputTapes t padding tables v x
          (output ++ portBits (rowBits t padding tables v x) k)⟩ := by
  induction k with
  | zero => simp only [portSteps, portBits, List.append_nil, Function.iterate_zero, id_eq]
  | succ k ih =>
    have h : k < q := by omega
    have first := ih (by omega)
    have second := coreTrace q positive ⟨k, h⟩ (fun s => labels (⟨k, h⟩, s))
      (portEntry q labels exit (k + 1)) program (fun s => code (⟨k, h⟩, s))
      t padding tables v x (output ++ portBits (rowBits t padding tables v x) k) ambient
    have he : portEntry q labels exit k = some (labels (⟨k, h⟩, coreEntry q)) := by
      simp only [portEntry, dite_eq_left h]
    rw [he] at first
    have total := joinTrace first second
    simpa only [portSteps, dite_eq_left h, List.length_append, portBits, rowBits,
      List.append_assoc] using total

theorem portTrace (q : Nat) (positive : 0 < q)
    (labels : PortLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = portInstruction q positive labels exit l)
    (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) (output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[portSteps t padding tables v x output.length q]
      (some ⟨portEntry q labels exit 0, coreInitialState q positive ambient,
        coreInputTapes t padding tables v x output⟩) =
      some ⟨exit, coreInitialState q positive ambient,
        coreInputTapes t padding tables v x
          (output ++ (List.ofFn (rowBits t padding tables v x)).flatten)⟩ := by
  simpa only [portEntry, lt_self_iff_false, dite_false, portBits_all] using
    portPrefixTrace q positive labels exit program code t padding tables v x output ambient q le_rfl

def originalView : CoreTape → Option MachineRegularOriginalClean.Tape :=
  ![some 1, some 0, none, none, none, none, none, none, some 9, some 5,
    some 2, some 3, some 4, none, none, none, none, none, none, none,
    none, none, none, none, some 6, some 7, some 8]

theorem originalView_left (k : MachineRegularOriginalClean.Tape) :
    originalView (originalTapes k) = some k := by fin_cases k <;> rfl

theorem originalView_right (j : CoreTape) (k : MachineRegularOriginalClean.Tape)
    (h : originalView j = some k) : originalTapes k = j := by
  fin_cases j <;> simp [originalView] at h
  all_goals subst k; rfl

theorem originalMemory_input (t : GraphTables.Table) (e : Fin t.darts) (output : List Bool) :
    MachineRegularOriginalClean.Input t e (originalMemory (GraphTables.tableBits t) e.val output) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

theorem originalMemory_update (graph : List Bool) (x : Nat) (output output' : List Bool) :
    Function.update (originalMemory graph x output) (9 : MachineRegularOriginalClean.Tape) output' =
      originalMemory graph x output' := by funext j; fin_cases j <;> rfl

theorem originalFrame (graph : List Bool) (x v i k o m : Nat) (rotor output output' : List Bool) :
    MachineCloudPadding.Placement.tapes originalView (originalMemory graph x output')
      (coreMemory graph x v i k o m rotor output [] [] [] [] [] []) =
      coreMemory graph x v i k o m rotor output' [] [] [] [] [] [] := by
  funext j; fin_cases j <;> rfl

/-- The inherited old relation is physically copied by the checked original-row
machine, with a static tape placement and state permutation. -/
theorem originalCoreTrace (q : Nat) (positive : 0 < q)
    (labels : MachineRegularOriginalClean.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = originalCoreInstruction q labels exit l)
    (t : GraphTables.Table) (e : Fin t.darts) (v i k o m : Nat)
    (rotor output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[MachineRegularOriginalClean.steps q t e
        (originalMemory (GraphTables.tableBits t) e.val output)]
      (some ⟨some (labels (.row (.lookup .seed))), coreInitialState q positive ambient,
        coreMemory (GraphTables.tableBits t) e.val v i k o m rotor output [] [] [] [] [] []⟩) =
      some ⟨exit, coreInitialState q positive ambient,
        coreMemory (GraphTables.tableBits t) e.val v i k o m rotor
          (output ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e))
          [] [] [] [] [] []⟩ := by
  let state := (ambient, (MachineFixedDivMod.residue q positive 0,
    (false, MachineCloudSelect.Phase.checking)))
  have run := MachineRegularOriginalClean.traceAt q id none
    (MachineRegularOriginalClean.instruction q id none) (fun _ => rfl) t e
    (originalMemory (GraphTables.tableBits t) e.val output)
    (originalMemory_input t e output) state none
  rw [originalMemory_update] at run
  have moved := MachineStateEquiv.trace (originalStateEquiv σ q)
    (MachineRegularOriginalClean.instruction q id none) _ _ _ run
  have placed := MachineCloudPadding.Placement.trace originalTapes originalView
    originalView_left originalView_right labels exit
    (coreMemory (GraphTables.tableBits t) e.val v i k o m rotor output [] [] [] [] [] [])
    (MachineStateEquiv.program (originalStateEquiv σ q)
      (MachineRegularOriginalClean.instruction q id none)) program code _ _ _ moved
  simp only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    MachineStateEquiv.configuration, originalFrame] at placed
  convert placed using 1 <;> rfl

theorem originalRowSteps_eq (q : Nat) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    MachineRegularOriginalClean.steps q t e (originalMemory (GraphTables.tableBits t) e.val output) =
      originalRowSteps q t e output.length := by
  unfold originalRowSteps MachineRegularOriginalClean.steps
  rw [MachineRegularOriginalClean.cleanupSteps_eq q t e _ (originalMemory_input t e output),
    MachineRegularOriginalClean.cleanupSteps_eq q t e _
      (originalMemory_input t e (List.replicate output.length false))]
  simp only [MachineRegularOriginalRow.steps, MachineRegularOriginalRow.rowSteps,
    originalMemory, Matrix.cons_val, List.length_replicate]

theorem vertexBits_split (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) :
    PreprocessingRegularWords.vertexBits t padding tables x.val =
      (List.ofFn (rowBits t padding tables v x)).flatten ++
        encodeWords (GraphTables.rowWords
          (PreprocessingRegularWords.actualRow t padding tables x.val (.inr ()))) := by
  unfold PreprocessingRegularWords.vertexBits PreprocessingRegularWords.vertexRows
  rw [List.flatMap_append, encodeWords_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [encodeWords_flatMap, List.flatMap_def, List.map_ofFn]
  rfl

theorem dummyTraceAt (q : Nat) (positive : 0 < q)
    (labels : Label q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = instruction q positive labels exit l)
    (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (j : Fin (padding v)) (output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[dummySteps t padding tables v j output.length]
      (some ⟨some (labels (dummyEntry q positive)), coreInitialState q positive ambient,
        coreInputTapes t padding tables v (paddedNew t padding v j) output⟩) =
      some ⟨exit, coreInitialState q positive ambient,
        coreInputTapes t padding tables v (paddedNew t padding v j)
          (output ++ PreprocessingRegularWords.dummyVertexBits t padding tables v j)⟩ := by
  let x := paddedNew t padding v j
  let bits := (List.ofFn (rowBits t padding tables v x)).flatten
  have ports := portTrace q positive (fun l => labels (.dummyPort l))
    (some (labels (.dummy (.affine .seed)))) program
    (fun l => code (.dummyPort l)) t padding tables v x output ambient
  have inherited := dummyCoreTrace q positive (fun l => labels (.dummy l)) exit program
    (fun l => code (.dummy l)) (GraphTables.tableBits t) (vertexOrder t padding x.val).val v.val
    (paddedCloudRank t padding v x).val (cloudSize t v)
    (PreprocessingPaddingOffsets.offset padding v.val) t.darts
    (encodeWords (ExpanderTableWords.rotationWords (tables v))) (output ++ bits) ambient
  have total := joinTrace ports inherited
  have hbits : PreprocessingRegularWords.dummyVertexBits t padding tables v j =
      bits ++ MachineRegularDummyRow.emittedBits q (vertexOrder t padding x.val).val := by
    have h := vertexBits_split t padding tables v x
    change PreprocessingRegularWords.dummyVertexBits t padding tables v j =
      bits ++ encodeWords (GraphTables.rowWords
        (PreprocessingRegularWords.actualRow t padding tables (.inr ⟨v, j⟩) (.inr ()))) at h
    rw [PreprocessingRegularWords.inherited_dummy_words] at h
    rw [encodeWords_pair] at h
    rw [show (vertexOrder t padding x.val).val =
      t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val from
      PreprocessingPaddingOffsets.vertexOrder_dummy_val t padding v j]
    simpa only [MachineRegularDummyRow.emittedBits, MachineRegularDummyRow.reverseIndex,
      MachineDummyRows.rowBits, MachineDummyRows.trueBits, List.append_assoc] using h
  rw [hbits]
  simp only [dummySteps, portEntry, dite_eq_left positive, dummyEntry,
    List.length_append, List.append_assoc, x, bits] at total ⊢
  convert total using 1 <;> rfl

theorem rowBits_length_le (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (rowBits t padding tables v x p).length ≤ rowSizeBound q (vertexCount t padding) :=
  GraphTables.rowBits_length_le _

theorem allRowBits_length_le (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) :
    (List.ofFn (rowBits t padding tables v x)).flatten.length ≤
      q * rowSizeBound q (vertexCount t padding) := by
  rw [← portBits_all]
  exact portBits_length_le _ _ (rowBits_length_le t padding tables v x) q

theorem portSteps_le (q : Nat) (positive : 0 < q) (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) (outputLength : Nat) (n : Nat) (hn : n ≤ q) :
    portSteps t padding tables v x outputLength n ≤
      n * coreTimeBound q (GraphTables.tableBits t).length
        (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
        (vertexOrder t padding x.val).val v.val (paddedCloudRank t padding v x).val
        (cloudSize t v) (PreprocessingPaddingOffsets.offset padding v.val) t.darts
        (outputLength + q * rowSizeBound q (vertexCount t padding)) := by
  induction n with
  | zero => simp only [portSteps, Nat.zero_mul, le_refl]
  | succ n ih =>
    have h : n < q := by omega
    have first := ih (by omega)
    have second := coreSteps_le q positive t padding tables v x ⟨n, h⟩
      (outputLength + (portBits (rowBits t padding tables v x) n).length)
    have hlen := portBits_length_le (rowBits t padding tables v x)
      (rowSizeBound q (vertexCount t padding)) (rowBits_length_le t padding tables v x) n
    have hmul := Nat.mul_le_mul_right (rowSizeBound q (vertexCount t padding)) (Nat.le_of_lt h)
    have hcost : coreSteps t padding tables v x ⟨n, h⟩
        (outputLength + (portBits (rowBits t padding tables v x) n).length) ≤
        coreTimeBound q (GraphTables.tableBits t).length
          (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
          (vertexOrder t padding x.val).val v.val (paddedCloudRank t padding v x).val
          (cloudSize t v) (PreprocessingPaddingOffsets.offset padding v.val) t.darts
          (outputLength + q * rowSizeBound q (vertexCount t padding)) := by
      unfold coreTimeBound at second ⊢
      omega
    rw [portSteps, dite_eq_left h, Nat.succ_mul]
    exact Nat.add_le_add first hcost

theorem originalSteps_le (q : Nat) (positive : 0 < q) (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (e : Fin t.darts) (outputLength : Nat) :
    originalSteps t padding tables e outputLength ≤
      originalTimeBound q (GraphTables.tableBits t).length
        (encodeWords (ExpanderTableWords.rotationWords (tables t.rows[e].tail))).length
        e.val t.rows[e].tail.val (paddedCloudRank t padding t.rows[e].tail (oldCloud t padding e)).val
        (cloudSize t t.rows[e].tail) (PreprocessingPaddingOffsets.offset padding t.rows[e].tail.val)
        t.darts outputLength (vertexCount t padding) := by
  let v := t.rows[e].tail
  let x := oldCloud t padding e
  let extra := (List.ofFn (rowBits t padding tables v x)).flatten.length
  have hp := portSteps_le q positive t padding tables v x outputLength q le_rfl
  have hi := MachineRegularOriginalClean.steps_le q t e
    (originalMemory (GraphTables.tableBits t) e.val (List.replicate (outputLength + extra) false))
    (originalMemory_input t e (List.replicate (outputLength + extra) false))
  have hl := allRowBits_length_le t padding tables v x
  change originalRowSteps q t e (outputLength + extra) ≤
    MachineRegularOriginalClean.timeBound q (GraphTables.tableBits t).length
      (List.replicate (outputLength + extra) false).length at hi
  rw [List.length_replicate] at hi
  change portSteps t padding tables v x outputLength q +
    originalRowSteps q t e (outputLength + extra) ≤ _
  unfold originalTimeBound portTimeBound MachineRegularOriginalClean.timeBound at *
  have hx : (vertexOrder t padding x.val).val = e.val := rfl
  rw [hx] at hp
  dsimp only [v, x, extra] at *
  omega

theorem dummySteps_le (q : Nat) (positive : 0 < q) (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (j : Fin (padding v)) (outputLength : Nat) :
    dummySteps t padding tables v j outputLength ≤
      dummyTimeBound q (GraphTables.tableBits t).length
        (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
        (vertexOrder t padding (.inr ⟨v, j⟩)).val v.val
        (paddedCloudRank t padding v (paddedNew t padding v j)).val
        (cloudSize t v) (PreprocessingPaddingOffsets.offset padding v.val)
        t.darts outputLength (vertexCount t padding) := by
  have hp := portSteps_le q positive t padding tables v (paddedNew t padding v j) outputLength q le_rfl
  have hl := allRowBits_length_le t padding tables v (paddedNew t padding v j)
  unfold dummySteps dummyTimeBound portTimeBound MachineRegularDummyRow.timeBound
  have hx : (paddedNew t padding v j).val = Sum.inr ⟨v, j⟩ := rfl
  rw [hx] at hp
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularVertexBlock

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOriginalBody
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlay.familyView_left
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One actual original-vertex body of regularization

The finite code composes physical metadata preparation, expander-family
materialization, all vertex rows, and seven metadata drain loops. The outer
loop owns the global vertex counter and keeps it unchanged during this body.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable

abbrev Alphabet (_ : Tape) := Bool

def metadataTape : MachineRegularMetadata.Tape → Tape
  | .inl i => .inl i
  | .inr e => .inr (.inl e)

def metadataView : Tape → Option MachineRegularMetadata.Tape
  | .inl i => some (.inl i)
  | .inr (.inl e) => some (.inr e)
  | .inr (.inr _) => none

def vertexView : Tape → Option (Fin 27)
  | .inl i => some i
  | .inr _ => none

theorem metadataView_left (k : MachineRegularMetadata.Tape) :
    metadataView (metadataTape k) = some k := by cases k <;> rfl

theorem metadataView_right (j : Tape) (k : MachineRegularMetadata.Tape)
    (h : metadataView j = some k) : metadataTape k = j := by
  cases j with
  | inl i => cases h; rfl
  | inr j => cases j with
    | inl e => cases h; rfl
    | inr e => cases h

theorem vertexView_left (k : Fin 27) : vertexView (.inl k) = some k := rfl

theorem vertexView_right (j : Tape) (k : Fin 27)
    (h : vertexView j = some k) : Sum.inl k = j := by
  cases j with
  | inl i => cases h; rfl
  | inr e => cases h

inductive Label
  | metadata (l : MachineRegularMetadata.Label)
  | family (l : MachineRegularFamily.Label)
  | vertex (l : MachineRegularVertexBlock.Label internalDegree)
  | clear (i : Fin 7)
  deriving DecidableEq, Fintype

def entry : Label := .metadata (.owner .seed)

def clearTape : Fin 7 → Tape :=
  ![.inl 2, .inl 3, .inl 4, .inl 5, .inl 7,
    .inr (.inl .padding), .inr (.inl .level)]

def clearEntry (k : Nat) : Option Label :=
  if h : k < 7 then some (.clear ⟨k, h⟩) else none

def clearSource (source : Tape) : Unit → TM2.Stmt Alphabet Unit MetaState :=
  fun _ => MachineDrain.drain source () none

def frame (data : Data) : Tape → List Bool
  | .inl i => MachineRegularMetadata.frame data (.inl i)
  | .inr (.inl e) => MachineRegularMetadata.frame data (.inr e)
  | .inr (.inr _) => []

def initialData (t : GraphTables.Table) (e : Fin t.darts) (output : List Bool) : Data where
  table := GraphTables.tableBits t
  globalIndex := encodeWord e.val
  owner := []
  localRank := []
  count := []
  offset := []
  darts := encodeWord t.darts
  rotor := []
  output := output
  padding := []
  level := []

def metadataData (t : GraphTables.Table) (e : Fin t.darts) (output : List Bool) : Data :=
  MachineRegularMetadata.originalData t e (initialData t e output)

theorem metadataPlacement (data extra : Data) :
    MachineCloudPadding.Placement.tapes metadataView (MachineRegularMetadata.frame data)
      (frame extra) = frame data := by
  funext j
  cases j with
  | inl i => rfl
  | inr j => cases j <;> rfl

/-- Seven real drain loops, including the complete materialized rotor. -/
def clearMemory (base : Tape → List Bool) : Nat → Tape → List Bool
  | 0 => base
  | k + 1 => if h : k < 7 then
      Function.update (clearMemory base k) (clearTape ⟨k, h⟩) [] else clearMemory base k

def clearSteps (base : Tape → List Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => clearSteps base k + if h : k < 7 then
      ((clearMemory base k) (clearTape ⟨k, h⟩)).length + 1 else 0

theorem identityPlacement (base extra : Tape → List Bool) :
    MachineCloudPadding.Placement.tapes some base extra = base := rfl

theorem clearFrame (data : Data) : clearMemory (frame data) 7 =
    frame { data with
      owner := []
      localRank := []
      count := []
      offset := []
      rotor := []
      padding := []
      level := [] } := by
  funext j
  cases j with
  | inl i => fin_cases i <;>
      simp [clearMemory, clearTape, frame, MachineRegularMetadata.frame]
  | inr j => cases j with
    | inl e => cases e <;>
        simp [clearMemory, clearTape, frame, MachineRegularMetadata.frame]
    | inr e => simp [clearMemory, clearTape, frame]

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBody

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOriginalBodyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Polynomial runtime for the actual original-vertex body. The size parameter
includes the already accumulated output, so no output-prefix premise is used. -/
namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBodyBounds

open Turing MachineComposition PCP PreprocessingCloudIndex PreprocessingRegularTables
open PreprocessingMachineBounds MachineRegularOriginalBody

def bodySize (t : GraphTables.Table) (output : List Bool) : Nat :=
  inputLength t + output.length

theorem wide_le (t : GraphTables.Table) (output : List Bool) :
    inputLength t ≤ (ExpanderFamily.growth+1)*bodySize t output ∧
    ExpanderFamily.growth*inputLength t ≤ (ExpanderFamily.growth+1)*bodySize t output ∧
    output.length ≤ (ExpanderFamily.growth+1)*bodySize t output := by
  have hN : inputLength t ≤ bodySize t output := Nat.le_add_right _ _
  have hO : output.length ≤ bodySize t output := Nat.le_add_left _ _
  have hg := Nat.mul_le_mul_left ExpanderFamily.growth hN
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem vertexSteps_le (H : PreprocessingRegularTables.BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    MachineRegularOriginalBody.vertexSteps H t e output ≤
      (blockPolynomial internalDegree).eval (bodySize t output) := by
  let v := t.rows[e].tail
  let W := (ExpanderFamily.growth+1)*bodySize t output
  have bounds := wide_le t output
  have hx := e.isLt.le.trans (GraphTables.darts_le_tableBits_length t)
  have hv := v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  have hk := cloudSize_le_input t v
  have hi := (cloudRank t v (MachineRegularMetadata.originalMember t e)).isLt.le.trans hk
  have hm := GraphTables.darts_le_tableBits_length t
  have ho := prefix_le_input t v.val
  have hV := regularVertices_le_input t
  have hR := (cloudRotorBits_le t v (familyCloudTable H t v)).trans
    (natPolynomial_eval_mono (rotorPolynomial internalDegree)
      (Nat.le_add_right (inputLength t) output.length))
  have raw := MachineRegularVertexBlock.originalSteps_le internalDegree degree_positive
    t (padding t) (familyCloudTable H t) e output.length
  have bound := originalTimeBound_le internalDegree _ _ _ _ _ _ _ _ _ _ W _
    bounds.1 hR (hx.trans bounds.1) (hv.trans bounds.1) (hi.trans bounds.1)
    (hk.trans bounds.1) (ho.trans bounds.2.1) (hm.trans bounds.1) bounds.2.2
    (hV.trans bounds.2.1)
  rw [blockPolynomial_eval]
  exact raw.trans bound

theorem clearSteps_frame (data : Data) :
    clearSteps (frame data) 7 = data.owner.length + data.localRank.length +
      data.count.length + data.offset.length + data.rotor.length + data.padding.length +
      data.level.length + 7 := by
  simp [clearSteps, clearMemory, clearTape, frame, MachineRegularMetadata.frame]
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalBodyBounds

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOwnerCleanup
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup

open Turing MachineComposition

abbrev Alphabet (_ : Tape) := Bool

inductive Label
  | scan
  | restore
  | drain (l : MachineDrainMany.Label cleanupTapes)
  deriving DecidableEq, Fintype

def entry : Label := .scan

variable {Λ : Type}

def cleanupEntry (labels : Label → Λ) (exit : Option Λ) : Option Λ :=
  MachineDrainMany.entry cleanupTapes (fun l => labels (.drain l)) exit

def steps (base : Tape → List Bool) (d : Nat) : Nat :=
  2 * (d + 1) + (cleanupTapes.map (fun k => (base k).length + 1)).sum

theorem drainSteps_eq (base : Tape → List Bool) (d o : Nat) :
    MachineDrainMany.steps cleanupTapes (afterAddition base d o) =
      (cleanupTapes.map (fun k => (base k).length + 1)).sum := by
  simp [MachineDrainMany.steps, cleanupTapes, afterAddition, prefixTape,
    localRank, count, rotor, padding, level, dummyFuel, core]

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOwnerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual dummy-owner body of regularization

The owner is a physically stored unary index. The code computes its cloud
metadata, initializes local index and fuel, skips the family computation when
padding is zero, and otherwise generates one rotor for all dummy vertices of
this owner. Each vertex iteration consumes one fuel bit and increments both
physical vertex indices. The final checked addition and cleanup leave only the
updated global index, prefix, and accumulated output.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable
open PreprocessingRegularLoopWords

abbrev Tape := MachineRegularOriginalBody.Tape ⊕ Fin 2
abbrev Alphabet (_ : Tape) := Bool

instance instDecidableEqTape : DecidableEq Tape := MachineRegularOwnerCleanup.tapeDecidableEq

def core (k : Fin 27) : Tape := .inl (.inl k)
def paddingTape : Tape := .inl (.inr (.inl .padding))
def dummyFuel : Tape := .inr 0
def scratch : Tape := .inr 1

def metadataTape (k : MachineRegularMetadata.Tape) : Tape :=
  .inl (MachineRegularOriginalBody.metadataTape k)

def metadataView : Tape → Option MachineRegularMetadata.Tape
  | .inl k => MachineRegularOriginalBody.metadataView k
  | .inr _ => none

def vertexView : Tape → Option (Fin 27)
  | .inl k => MachineRegularOriginalBody.vertexView k
  | .inr _ => none

theorem metadataView_left (k : MachineRegularMetadata.Tape) :
    metadataView (metadataTape k) = some k := MachineRegularOriginalBody.metadataView_left k

theorem metadataView_right (j : Tape) (k : MachineRegularMetadata.Tape)
    (h : metadataView j = some k) : metadataTape k = j := by
  cases j with
  | inl j => exact congrArg Sum.inl (MachineRegularOriginalBody.metadataView_right j k h)
  | inr j => cases h

theorem vertexView_left (k : Fin 27) : vertexView (core k) = some k := rfl

theorem vertexView_right (j : Tape) (k : Fin 27)
    (h : vertexView j = some k) : core k = j := by
  cases j with
  | inl j => exact congrArg Sum.inl (MachineRegularOriginalBody.vertexView_right j k h)
  | inr j => cases h

inductive Label
  | metadata (l : MachineRegularMetadata.Label)
  | copyCount (l : MachineUnaryAffineAt.Label)
  | copyFuel (l : MachineUnaryAffineAt.Label)
  | guard
  | family (l : MachineRegularFamily.Label)
  | loop
  | vertex (l : MachineRegularVertexBlock.Label internalDegree)
  | bump
  | cleanup (l : MachineRegularOwnerCleanup.Label)
  deriving DecidableEq, Fintype

def entry : Label := .metadata (.cloud .init)

def working (data : Data) (fuel saved : List Bool) : Tape → List Bool
  | .inl k => MachineRegularOriginalBody.frame data k
  | .inr i => if i = 0 then fuel else saved

def frame (data : Data) : Tape → List Bool := working data [] []

def initialData (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) : Data where
  table := GraphTables.tableBits t
  globalIndex := encodeWord (t.darts + PreprocessingPaddingOffsets.offset (padding t) v.val)
  owner := encodeWord v.val
  localRank := []
  count := []
  offset := encodeWord (PreprocessingPaddingOffsets.offset (padding t) v.val)
  darts := encodeWord t.darts
  rotor := []
  output := output
  padding := []
  level := []

def metadataData (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) : Data :=
  MachineRegularMetadata.cloudData t v (initialData t v output)

def seededData (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) : Data :=
  { metadataData t v output with localRank := encodeWord (cloudSize t v) }

def finalData (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) : Data :=
  { initialData t v output with
    globalIndex := encodeWord (t.darts + PreprocessingPaddingOffsets.offset (padding t) v.val + padding t v)
    offset := encodeWord (PreprocessingPaddingOffsets.offset (padding t) v.val + padding t v)
    output := output ++ ownerBits H t v }

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOwnerBody
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual execution and exact runtime of the fixed dummy-owner program. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable PreprocessingRegularLoopWords

theorem metadataPlacement (data extra : Data) :
    MachineCloudPadding.Placement.tapes metadataView (MachineRegularMetadata.frame data)
      (frame extra) = frame data := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => rfl
    | inr j => cases j <;> rfl
  | inr i => rfl

theorem working_update_local (data : Data) (fuel saved word : List Bool) :
    Function.update (working data fuel saved) (core 3) word =
      working { data with localRank := word } fuel saved := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;>
        simp [working, core, MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
    | inr j => cases j with
      | inl e => cases e <;>
          simp [working, core, MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
      | inr e => simp [working, core, MachineRegularOriginalBody.frame]
  | inr i => simp [working, core]

theorem working_update_fuel (data : Data) (fuel saved word : List Bool) :
    Function.update (working data fuel saved) dummyFuel word = working data word saved := by
  funext j
  cases j with
  | inl j => simp [working, dummyFuel]
  | inr i => fin_cases i <;> simp [working, dummyFuel]

theorem working_update_global (data : Data) (fuel saved word : List Bool) :
    Function.update (working data fuel saved) (core 1) word =
      working { data with globalIndex := word } fuel saved := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;>
        simp [working, core, MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
    | inr j => cases j with
      | inl e => cases e <;>
          simp [working, core, MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
      | inr e => simp [working, core, MachineRegularOriginalBody.frame]
  | inr i => simp [working, core]

def preSteps (t : GraphTables.Table) (v : Fin t.vertices) : Nat :=
  MachineCloudPadding.totalTime t v + (2 * (cloudSize t v + 1) + 1) +
    (2 * (padding t v + 1) + 1)

@[simp] theorem working_fuel (data : Data) (fuel saved : List Bool) :
    working data fuel saved dummyFuel = fuel := rfl

@[simp] theorem working_scratch (data : Data) (fuel saved : List Bool) :
    working data fuel saved scratch = saved := rfl

theorem cleanupFrame (data : Data) (fuel : List Bool) (d o : Nat) :
    MachineRegularOwnerCleanup.finalTapes (working data fuel []) d o =
      frame { data with
        localRank := []
        count := []
        rotor := []
        padding := []
        level := []
        offset := encodeWord (d + o) } := by
  funext j
  rw [MachineRegularOwnerCleanup.finalTapes_apply]
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;>
        simp [MachineRegularOwnerCleanup.cleanupTapes, MachineRegularOwnerCleanup.localRank,
          MachineRegularOwnerCleanup.count, MachineRegularOwnerCleanup.rotor,
          MachineRegularOwnerCleanup.padding, MachineRegularOwnerCleanup.level,
          MachineRegularOwnerCleanup.dummyFuel, MachineRegularOwnerCleanup.prefixTape,
          MachineRegularOwnerCleanup.core, frame, working, MachineRegularOriginalBody.frame,
          MachineRegularMetadata.frame]
    | inr j => cases j with
      | inl e => cases e <;>
          simp [MachineRegularOwnerCleanup.cleanupTapes, MachineRegularOwnerCleanup.localRank,
            MachineRegularOwnerCleanup.count, MachineRegularOwnerCleanup.rotor,
            MachineRegularOwnerCleanup.padding, MachineRegularOwnerCleanup.level,
            MachineRegularOwnerCleanup.dummyFuel,
            MachineRegularOwnerCleanup.core, frame, working, MachineRegularOriginalBody.frame,
            MachineRegularMetadata.frame]
      | inr e =>
          simp [MachineRegularOwnerCleanup.cleanupTapes, MachineRegularOwnerCleanup.localRank,
            MachineRegularOwnerCleanup.count, MachineRegularOwnerCleanup.rotor,
            MachineRegularOwnerCleanup.padding, MachineRegularOwnerCleanup.level,
            MachineRegularOwnerCleanup.dummyFuel, MachineRegularOwnerCleanup.prefixTape,
            MachineRegularOwnerCleanup.core, frame, working, MachineRegularOriginalBody.frame]
  | inr i => fin_cases i <;>
      simp [MachineRegularOwnerCleanup.cleanupTapes, MachineRegularOwnerCleanup.localRank,
        MachineRegularOwnerCleanup.count, MachineRegularOwnerCleanup.rotor,
        MachineRegularOwnerCleanup.padding, MachineRegularOwnerCleanup.level,
        MachineRegularOwnerCleanup.dummyFuel, MachineRegularOwnerCleanup.prefixTape,
        MachineRegularOwnerCleanup.core, frame, working]

theorem cleanupZeroFrame (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (hp : padding t v = 0) :
    MachineRegularOwnerCleanup.finalTapes
      (working (seededData t v output) (encodeWord 0) []) (padding t v)
      (PreprocessingPaddingOffsets.offset (padding t) v.val) = frame (finalData H t v output) := by
  rw [cleanupFrame]
  apply congrArg frame
  simp only [seededData, metadataData, MachineRegularMetadata.cloudData, initialData,
    finalData, hp, ownerBits_zero H t v hp, List.append_nil, Nat.add_zero, Nat.zero_add]

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularOwnerBodyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Bounds for actual dummy-owner execution

The size parameter includes the old output length. During the owner loop,
newly emitted dummy blocks are bounded by the actual complete regularized
table codec. No hypothesis about a machine body's execution supplies a bound.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBodyBounds

open Turing MachineComposition PCP PreprocessingCloudIndex PreprocessingRegularTables
open PreprocessingMachineBounds PreprocessingRegularLoopWords

def bodySize (t : GraphTables.Table) (output : List Bool) : Nat :=
  inputLength t + output.length

theorem wide_le (t : GraphTables.Table) (output : List Bool) :
    inputLength t ≤ (ExpanderFamily.growth+1)*bodySize t output ∧
    ExpanderFamily.growth*inputLength t ≤ (ExpanderFamily.growth+1)*bodySize t output ∧
    output.length ≤ (ExpanderFamily.growth+1)*bodySize t output := by
  have hN : inputLength t ≤ bodySize t output := Nat.le_add_right _ _
  have hO : output.length ≤ bodySize t output := Nat.le_add_left _ _
  have hg := Nat.mul_le_mul_left ExpanderFamily.growth hN
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Any finite prefix inside this owner is a part of the actual output table,
including when the supplied prefix length is larger than the number of blocks. -/
theorem ownerPrefix_length_le (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (n : Nat) :
    (blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
      (familyCloudTable H t) v) n).length ≤ regularPolynomial.eval (inputLength t) := by
  have h := PreprocessingRegularBounds.regular_dummyPrefix_le t H v n
  simp only [PreprocessingRegularBounds.dummyPrefix, List.length_append] at h
  omega

theorem growingOutput_length_le (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (n : Nat) (output : List Bool) :
    (output ++ blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
      (familyCloudTable H t) v) n).length ≤
      (ExpanderFamily.growth+1)*bodySize t output + regularPolynomial.eval (bodySize t output) := by
  have h := (ownerPrefix_length_le H t v n).trans
    (natPolynomial_eval_mono regularPolynomial (Nat.le_add_right (inputLength t) output.length))
  have hO := (wide_le t output).2.2
  rw [List.length_append]
  exact Nat.add_le_add hO h

/-- One actual dummy block has a uniform polynomial cost at every prefix of
the owner loop. The only inputs are the real table, indices, and old output. -/
theorem dummySteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (j : Fin (padding t v)) (n : Nat) (output : List Bool) :
    MachineRegularVertexBlock.dummySteps t (padding t) (familyCloudTable H t) v j
      (output ++ blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
        (familyCloudTable H t) v) n).length ≤
      (blockPolynomial internalDegree).eval (bodySize t output) := by
  let x := paddedNew t (padding t) v j
  let W := (ExpanderFamily.growth+1)*bodySize t output
  have bounds := wide_le t output
  have hx := (vertexOrder t (padding t) x.val).isLt.le.trans (regularVertices_le_input t)
  have hv := v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  have hi := (paddedCloudRank t (padding t) v x).isLt.le.trans (cloudTotal_le_input t v)
  have hk := cloudSize_le_input t v
  have hm := GraphTables.darts_le_tableBits_length t
  have ho := prefix_le_input t v.val
  have hV := regularVertices_le_input t
  have hR := (cloudRotorBits_le t v (familyCloudTable H t v)).trans
    (natPolynomial_eval_mono (rotorPolynomial internalDegree)
      (Nat.le_add_right (inputLength t) output.length))
  have hO := growingOutput_length_le H t v n output
  have raw := MachineRegularVertexBlock.dummySteps_le internalDegree
    MachineRegularOriginalBody.degree_positive t (padding t) (familyCloudTable H t) v j
      (output ++ blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
        (familyCloudTable H t) v) n).length
  have bound := dummyTimeBound_le internalDegree _ _ _ _ _ _ _ _ _ _ W _ _
    bounds.1 hR (hx.trans bounds.2.1) (hv.trans bounds.1) (hi.trans bounds.2.1)
    (hk.trans bounds.1) (ho.trans bounds.2.1) (hm.trans bounds.1) hO
    (hV.trans bounds.2.1)
  rw [blockPolynomial_eval]
  exact raw.trans bound

theorem preSteps_le (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) :
    MachineRegularOwnerBody.preSteps t v ≤ prePolynomial.eval (bodySize t output) := by
  have bounds := wide_le t output
  have hk := cloudSize_le_input t v
  have hd := cloudTotal_le_input t v
  have hv := v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  change v.val ≤ inputLength t at hv
  have hN : inputLength t ≤ bodySize t output := Nat.le_add_right _ _
  have hinput : MachineCloudPadding.inputLength t v [] ≤ 2*bodySize t output+1 := by
    simp only [MachineCloudPadding.inputLength, List.append_nil, encodeWord_length]
    change inputLength t + (v.val+1) ≤ _
    omega
  have hm := (MachineCloudPadding.totalTime_le t v []).trans
    (natPolynomial_eval_mono MachineCloudPadding.timePolynomial hinput)
  simp only [MachineRegularOwnerBody.preSteps, prePolynomial, wide, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

theorem loopSteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (n : Nat) (hn : n ≤ padding t v) :
    MachineRegularOwnerBody.loopSteps H t v output n hn ≤
      n * ((blockPolynomial internalDegree).eval (bodySize t output) + 2) := by
  induction n with
  | zero => simp only [MachineRegularOwnerBody.loopSteps, Nat.zero_mul, le_refl]
  | succ n ih =>
    have h : n < padding t v := by omega
    have first := ih (by omega)
    have second := dummySteps_le H t v ⟨n, h⟩ n output
    rw [MachineRegularOwnerBody.loopSteps, Nat.succ_mul]
    change MachineRegularOwnerBody.loopSteps H t v output n _ +
      (1 + MachineRegularVertexBlock.dummySteps t (padding t) (familyCloudTable H t) v ⟨n, h⟩
        (output ++ blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
          (familyCloudTable H t) v) n).length + 1) ≤ _
    omega

theorem allLoopSteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    MachineRegularOwnerBody.loopSteps H t v output (padding t v) le_rfl ≤
      loopPolynomial.eval (bodySize t output) := by
  have hd := (cloudTotal_le_input t v).trans (wide_le t output).2.1
  have hp : padding t v ≤ (ExpanderFamily.growth+1)*bodySize t output := by omega
  have h := (loopSteps_le H t v output (padding t v) le_rfl).trans
    (Nat.mul_le_mul_right _ hp)
  simpa only [loopPolynomial, wide, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using h

/-- Exact cost of the six physical drain loops and the prefix addition,
expressed through the actual entry stack lengths. -/
theorem cleanupSteps_working (data : MachineRegularOwnerBody.Data)
    (fuel saved : List Bool) (d : Nat) :
    MachineRegularOwnerCleanup.steps (MachineRegularOwnerBody.working data fuel saved) d =
      2*(d+1) + data.localRank.length + data.count.length + data.rotor.length +
        data.padding.length + data.level.length + fuel.length + 6 := by
  change 2*(d+1) + ((data.localRank.length+1) + ((data.count.length+1) +
    ((data.rotor.length+1) + ((data.padding.length+1) + ((data.level.length+1) +
      ((fuel.length+1)+0)))))) = _
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBodyBounds

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineRegularTable
attribute [-simp] _root_.OAI.PerfectCompleteness.TargetHeaderMachine.encodeWord_zero _root_.OAI.PerfectCompleteness.TupleEnumerationMachine.outputBlock_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.ForestStage.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationMachine.tapes_current _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure.tokenBits_or _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionArena.tapes_capacity _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_original _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineTableSplit.resultTapes_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_start _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringInitializeFrame.prepared_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineFinish.afterHeaders_output _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_counter _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineInitialize.final_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.inTime_steps _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceHeaderAccumulate.result_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.cursorBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopState.prefixBits_zero _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name
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

inductive Label
  | init | seedM | clearIndex
  | lookup (field : Field) (label : MachinePreservingLookupClean.Label)
  | prefix (label : MachineCloudPrefix.Label)
  | copyFirst (phase : CopyPhase) | copySecond (phase : CopyPhase)
  | add | scaleSeed | scaleScan | scaleRestore
  | appendFirst | appendSecond | appendThird
  | cleanupZeros | clearQuery | done
  deriving DecidableEq, Fintype

def fieldExit : Field → Label
  | .vertices => .seedM
  | .darts => .clearIndex

theorem lookupSlots_injective (field : Field) : Function.Injective (lookupSlots field) := by
  intro i j h
  cases field <;> fin_cases i <;> fin_cases j <;>
    simp_all [lookupSlots, fieldTape, tableTape, indexTape, workTape, nTape, mTape, scratchTape]

def copyExit : CopyPhase → Label
  | .count => .add
  | .rEmit => .copyFirst .nEmit
  | .nEmit => .appendFirst

def prefixView : Tape → Option MachineCloudPrefix.Tape
  | .inl k => some k
  | .inr _ => none

theorem prefixView_left (k : MachineCloudPrefix.Tape) : prefixView (.inl k) = some k := rfl

theorem prefixView_right (j : Tape) (k : MachineCloudPrefix.Tape)
    (h : prefixView j = some k) : Sum.inl k = j := by
  cases j <;> simp_all [prefixView]

theorem prefixTapes (inner : MachineCloudPrefix.Tape → List Bool) (extra : Tape → List Bool) :
    MachineCloudPadding.Placement.tapes prefixView inner extra =
      memory inner (extra mTape) (extra indexTape) (extra workTape) (extra scratchTape)
        (extra verticesTape) (extra dartsTape) (extra emitTape) (extra outputTape) := by
  funext j
  cases j with
  | inl k => rfl
  | inr k => cases k <;> rfl

variable {σ : Type}

def program (q : Nat) : Label → TM2.Stmt Alphabet Label (State σ)
  | .init => .push indexTape (fun _ => false) (.goto fun _ => .lookup .vertices (.run .copyFirst))
  | .seedM => .push indexTape (fun _ => true) (.goto fun _ => .lookup .darts (.run .copyFirst))
  | .clearIndex => .pop indexTape (fun state _ => (state.1, none))
      (.goto fun _ => .prefix .init)
  | .lookup field l => MachinePreservingLookupClean.statement (lookupSlots field)
      (Label.lookup field) (some (fieldExit field)) l
  | .prefix l => MachineCloudPadding.Placement.statement Sum.inl Label.prefix
      (some (.copyFirst .count)) (MachineCloudPrefix.program l)
  | .copyFirst phase => Reduction.MachineTransfer.loopAt (copySource phase) scratchTape
      id false (.copyFirst phase) (some (.copySecond phase))
  | .copySecond phase => MachineCopy.forkLoop scratchTape (copySource phase) (copyDestination phase)
      false (.copySecond phase) (some (copyExit phase))
  | .add => MachineUnaryAddAt.loop sumTape verticesTape .add (some .scaleSeed)
  | .scaleSeed => MachineUnaryAffineAt.seed dartsTape 0 .scaleScan
  | .scaleScan => MachineUnaryAffineAt.scan verticesTape scratchTape dartsTape (q + 1)
      .scaleScan .scaleRestore
  | .scaleRestore => Reduction.MachineTransfer.loopAt scratchTape verticesTape id false
      .scaleRestore (some (.copyFirst .rEmit))
  | .appendFirst => Reduction.MachineTransfer.loopAt outputTape scratchTape id false
      .appendFirst (some .appendSecond)
  | .appendSecond => Reduction.MachineTransfer.loopAt emitTape scratchTape id false
      .appendSecond (some .appendThird)
  | .appendThird => Reduction.MachineTransfer.loopAt scratchTape outputTape id false
      .appendThird (some .cleanupZeros)
  | .cleanupZeros => .pop sumTape (fun state _ => (state.1, none))
      (.pop fuelTape (fun state _ => (state.1, none)) (.goto fun _ => .clearQuery))
  | .clearQuery => MachineLookup.discard queryTape .clearQuery .done
  | .done => .halt

theorem vertexTotal_eq (t : GraphTables.Table) :
    vertexTotal t = t.darts + paddingTotal t := by
  unfold vertexTotal PreprocessingRegularTables.vertexCount paddingTotal
  rw [PreprocessingPaddingOffsets.offset_all]

theorem initStep (q : Nat) (table output : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step (program q)
      ⟨some .init, ((ambient, false), register),
        frame table [] [] [] [] [] [] [] [] [] [] [] output⟩ =
      some ⟨some (.lookup .vertices (.run .copyFirst)), ((ambient, false), register),
        frame table [] [] [] [] [] (encodeWord 0) [] [] [] [] [] output⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

theorem seedMStep (q : Nat) (table n output : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step (program q)
      ⟨some .seedM, ((ambient, false), register),
        frame table n [] [] [] [] (encodeWord 0) [] [] [] [] [] output⟩ =
      some ⟨some (.lookup .darts (.run .copyFirst)), ((ambient, false), register),
        frame table n [] [] [] [] (encodeWord 1) [] [] [] [] [] output⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

theorem clearIndexStep (q : Nat) (table n m output : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step (program q)
      ⟨some .clearIndex, ((ambient, false), register),
        frame table n [] [] [] m (encodeWord 0) [] [] [] [] [] output⟩ =
      some ⟨some (.prefix .init), ((ambient, false), none),
        frame table n [] [] [] m [] [] [] [] [] [] output⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

/-- Both original header numbers are produced by physical preserving lookups. -/
theorem readTrace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[readTime t]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] [] [] [] [] [] [] [] output⟩) =
      some ⟨some (.prefix .init), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] []
          (encodeWord t.darts) [] [] [] [] [] [] output⟩ := by
  have hi : (advance (TM2.step (program q)))^[1]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] [] [] [] [] [] [] [] output⟩) =
      some ⟨some (.lookup .vertices (.run .copyFirst)), ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] [] (encodeWord 0) [] [] [] [] [] output⟩ :=
    initStep q _ _ ambient register
  have hn := MachinePreservingLookupClean.traceAt_fromTapes (lookupSlots .vertices)
    (lookupSlots_injective .vertices) (Label.lookup .vertices) (some Label.seedM)
    (program q) (fun _ => rfl)
    (frame (GraphTables.tableBits t) [] [] [] [] [] (encodeWord 0) [] [] [] [] [] output)
    (GraphTables.tableWords t) rfl rfl 0 t.vertices (by simp [GraphTables.tableWords]) []
    (by simp [lookupSlots]) (by simp [lookupSlots]) (ambient, false) register
  simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, lookupSlots, fieldTape] at hn
  have hs : (advance (TM2.step (program q)))^[1]
      (some ⟨some .seedM, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] []
          (encodeWord 0) [] [] [] [] [] output⟩) =
      some ⟨some (.lookup .darts (.run .copyFirst)), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] []
          (encodeWord 1) [] [] [] [] [] output⟩ :=
    seedMStep q _ _ _ ambient none
  have hm := MachinePreservingLookupClean.traceAt_fromTapes (lookupSlots .darts)
    (lookupSlots_injective .darts) (Label.lookup .darts) (some Label.clearIndex)
    (program q) (fun _ => rfl)
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] []
      (encodeWord 1) [] [] [] [] [] output)
    (GraphTables.tableWords t) rfl rfl 1 t.darts (by simp [GraphTables.tableWords]) []
    (by simp [lookupSlots]) (by simp [lookupSlots]) (ambient, false) none
  simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, lookupSlots, fieldTape] at hm
  have hc : (advance (TM2.step (program q)))^[1]
      (some ⟨some .clearIndex, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] []
          (encodeWord t.darts) (encodeWord 0) [] [] [] [] [] output⟩) =
      some ⟨some (.prefix .init), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] []
          (encodeWord t.darts) [] [] [] [] [] [] output⟩ :=
    clearIndexStep q _ _ _ _ ambient none
  exact appendTrace _ (appendTrace _ (appendTrace _ (appendTrace _ hi hn) hs) hm) hc

/-- The original vertex count is the physical bound supplied to the checked
padding-prefix machine. Its complement tapes preserve the original dart count. -/
theorem prefixTrace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[MachineCloudPrefix.totalTime t t.vertices []]
      (some ⟨some (.prefix .init), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] []
          (encodeWord t.darts) [] [] [] [] [] [] output⟩) =
      some ⟨some (.copyFirst .count), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
          [] [] [] [] [] [] output⟩ := by
  have h := MachineCloudPadding.Placement.trace Sum.inl prefixView prefixView_left prefixView_right
    Label.prefix (some (Label.copyFirst .count))
    (frame [] [] [] [] [] (encodeWord t.darts) [] [] [] [] [] [] output)
    (MachineCloudPrefix.program (σ := σ)) (program q) (fun _ => rfl) _ _ _
    (MachineCloudPrefix.prefixTrace t t.vertices (Nat.le_refl _) [] ambient register)
  simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    prefixTapes, frame_m, frame_index, frame_work, frame_scratch, frame_vertices, frame_darts,
    frame_emit, frame_output, List.append_nil, paddingTotal, frame, memory,
    mTape, indexTape, workTape, scratchTape, verticesTape, dartsTape, emitTape, outputTape] using h

theorem computeTrace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[computeTime t]
      (some ⟨some (.copyFirst .count), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
          [] [] [] [] [] [] output⟩) =
      some ⟨some (.copyFirst .rEmit), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord 0) (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] output⟩ := by
  have hc := MachineCopy.copyTrace mTape verticesTape scratchTape (by decide) (by decide)
    (by decide) false (Label.copyFirst .count) (Label.copySecond .count) (some Label.add)
    (program q) rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
      [] [] [] [] [] [] output) rfl (ambient, false) register
  simp only [frame_m, frame_vertices, encodeWord_length, List.append_nil, update_frame_vertices] at hc
  have ha := MachineUnaryAddAt.addFromTapes sumTape verticesTape (by decide)
    Label.add (some Label.scaleSeed) (program q) rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
      [] [] [] (encodeWord t.darts) [] [] output)
    (paddingTotal t) t.darts [] [] (by simp) (by simp) (ambient, false) none
  simp only [MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt,
    List.append_nil, update_frame_sum, update_frame_vertices] at ha
  rw [show paddingTotal t + t.darts = vertexTotal t by rw [vertexTotal_eq]; omega] at ha
  have hm := MachineUnaryAffineAt.seededAffineTrace verticesTape scratchTape dartsTape
    (by decide) (by decide) (by decide) (q + 1) 0 Label.scaleSeed Label.scaleScan
    Label.scaleRestore (some (Label.copyFirst .rEmit)) (program q) rfl rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts)
      [] [] [] (encodeWord (vertexTotal t)) [] [] output)
    (vertexTotal t) [] (by simp) rfl (ambient, false) none
  simp only [frame_darts, List.append_nil, Nat.add_zero, update_frame_darts] at hm
  rw [show (q + 1) * vertexTotal t = dartTotal q t by unfold dartTotal; ac_rfl] at hm
  exact appendTrace _ (appendTrace _ hc ha) hm

theorem headerBits_eq (q : Nat) (t : GraphTables.Table) :
    headerBits q t = encodeWord (vertexTotal t) ++ encodeWord (dartTotal q t) := by
  simp only [headerBits, encodeWords, List.append_nil]

theorem headerBits_length (q : Nat) (t : GraphTables.Table) :
    (headerBits q t).length = vertexTotal t + dartTotal q t + 2 := by
  rw [headerBits_eq]
  simp only [List.length_append, encodeWord_length]
  omega

theorem cleanupZerosStep (q : Nat) (table n m N R output : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step (program q)
      ⟨some .cleanupZeros, ((ambient, false), register),
        frame table n n (encodeWord 0) (encodeWord 0) m [] [] [] N R [] output⟩ =
      some ⟨some .clearQuery, ((ambient, false), none),
        frame table n n [] [] m [] [] [] N R [] output⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

theorem emitTrace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[emitTime q t output]
      (some ⟨some (.copyFirst .rEmit), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord 0) (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] output⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩ := by
  have hr := MachineCopy.copyTrace dartsTape emitTape scratchTape (by decide) (by decide)
    (by decide) false (Label.copyFirst .rEmit) (Label.copySecond .rEmit)
    (some (Label.copyFirst .nEmit)) (program q) rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
      (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] output)
    rfl (ambient, false) register
  simp only [frame_darts, frame_emit, encodeWord_length, List.append_nil, update_frame_emit] at hr
  have hn := MachineCopy.copyTrace verticesTape emitTape scratchTape (by decide) (by decide)
    (by decide) false (Label.copyFirst .nEmit) (Label.copySecond .nEmit)
    (some Label.appendFirst) (program q) rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
      (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) (encodeWord (dartTotal q t)) output)
    rfl (ambient, false) none
  simp only [frame_vertices, frame_emit, encodeWord_length, update_frame_emit, ← headerBits_eq] at hn
  have ha := MachineAppendAt.appendTrace emitTape outputTape scratchTape
    (by decide) (by decide) (by decide) false Label.appendFirst Label.appendSecond Label.appendThird
    (some Label.cleanupZeros) (program q) rfl rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
      (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) (headerBits q t) output)
    rfl (ambient, false) none
  simp only [frame_emit, frame_output, MachineAppendAt.appendTapes,
    Reduction.MachineTransfer.tapesAt, update_frame_emit, update_frame_output] at ha
  have hz : (advance (TM2.step (program q)))^[1]
      (some ⟨some .cleanupZeros, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
          (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] (output ++ headerBits q t)⟩) =
      some ⟨some .clearQuery, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          [] [] (encodeWord t.darts) [] [] [] (encodeWord (vertexTotal t))
          (encodeWord (dartTotal q t)) [] (output ++ headerBits q t)⟩ :=
    cleanupZerosStep q _ _ _ _ _ _ ambient none
  have hc := MachineLookup.discardTrace queryTape Label.clearQuery Label.done (program q) rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      [] [] (encodeWord t.darts) [] [] [] (encodeWord (vertexTotal t))
      (encodeWord (dartTotal q t)) [] (output ++ headerBits q t))
    t.vertices [] (by simp) (ambient, false) none
  simp only [update_frame_query] at hc
  have hd : (advance (TM2.step (program q)))^[1]
      (some ⟨some .done, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩ := rfl
  exact appendTrace _ (appendTrace _ (appendTrace _ (appendTrace _ (appendTrace _ hr hn) ha) hz) hc) hd

theorem trace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[totalTime q t output]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] [] [] [] [] [] [] [] output⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩ :=
  appendTrace _ (appendTrace _ (appendTrace _ (readTrace q t output ambient register)
    (prefixTrace q t output ambient none)) (computeTrace q t output ambient none))
      (emitTrace q t output ambient none)

theorem totalTime_le (q : Nat) (t : GraphTables.Table) (output : List Bool) :
    totalTime q t output ≤ (timePolynomial q).eval ((GraphTables.tableBits t).length + output.length) := by
  let L := (GraphTables.tableBits t).length + output.length
  have hT : (GraphTables.tableBits t).length ≤ L := by unfold L; omega
  have hO : output.length ≤ L := by unfold L; omega
  have hn := (GraphTables.vertices_le_tableBits_length t).trans hT
  have hm := (GraphTables.darts_le_tableBits_length t).trans hT
  have hN : vertexTotal t ≤ ExpanderFamily.growth * L :=
    (PreprocessingMachineBounds.regularVertices_le_input t).trans
      (Nat.mul_le_mul_left ExpanderFamily.growth hT)
  have hS : paddingTotal t ≤ ExpanderFamily.growth * L :=
    (PreprocessingMachineBounds.prefix_le_input t t.vertices).trans
      (Nat.mul_le_mul_left ExpanderFamily.growth hT)
  have hR : dartTotal q t ≤ (ExpanderFamily.growth * (q + 1)) * L := by
    calc
      _ ≤ (ExpanderFamily.growth * L) * (q + 1) := Nat.mul_le_mul_right (q + 1) hN
      _ = _ := by ac_rfl
  have hr0 := MachinePreservingLookupClean.steps_le (GraphTables.tableWords t) 0 t.vertices
    (by simp [GraphTables.tableWords])
  have hr1 := MachinePreservingLookupClean.steps_le (GraphTables.tableWords t) 1 t.darts
    (by simp [GraphTables.tableWords])
  have hread : readTime t ≤ 12 * L + 11 := by
    change _ ≤ 6 * (GraphTables.tableBits t).length + 4 at hr0 hr1
    unfold readTime
    omega
  have hprefixInput : MachineCloudPrefix.inputLength t t.vertices [] ≤ 2 * L + 1 := by
    simp only [MachineCloudPrefix.inputLength, List.append_nil, encodeWord_length]
    omega
  have hp := (MachineCloudPrefix.totalTime_le t t.vertices (Nat.le_refl _) []).trans
    (natPolynomial_eval_mono MachineCloudPrefix.timePolynomial hprefixInput)
  have harith : readTime t + computeTime t + emitTime q t output ≤
      (arithmeticPolynomial q).eval L := by
    simp only [arithmeticPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
    unfold computeTime emitTime
    rw [headerBits_length]
    omega
  have htotal := Nat.add_le_add hp harith
  simpa only [totalTime, timePolynomial, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one,
    L, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal

end Header

namespace Top

inductive Label
  | header (l : Header.Label)
  | oldSeed
  | copyFirst (phase : CopyPhase)
  | copySecond (phase : CopyPhase)
  | oldGuard
  | oldBody (l : MachineRegularOriginalBody.Label)
  | oldIncrement
  | ownerSeed
  | ownerGuard
  | ownerBody (l : MachineRegularOwnerBody.Label)
  | ownerIncrement
  | clear (i : Fin 7)
  deriving DecidableEq, Fintype

def clearEntry (k : Nat) : Option Label :=
  if h : k < 7 then some (.clear ⟨k, h⟩) else none

theorem owner_output_eq_ownerPrefix (H : BaseTable) (t : GraphTables.Table) (k : Nat) :
    (Header.headerBits PreprocessingRegularTables.internalDegree t ++ oldPrefix H t t.darts) ++
        ownerPrefix H t k =
      PreprocessingRegularBounds.ownerPrefix t (PreprocessingRegularTables.padding t)
        (PreprocessingRegularTables.familyCloudTable H t) k := by
  have oldBits : MachineRegularOriginalBody.emittedBits H t =
      PreprocessingRegularWords.originalVertexBits t (PreprocessingRegularTables.padding t)
        (PreprocessingRegularTables.familyCloudTable H t) := rfl
  have ownerBits : MachineRegularOwnerBody.ownerBits H t =
      PreprocessingRegularBounds.ownerBits t (PreprocessingRegularTables.padding t)
        (PreprocessingRegularTables.familyCloudTable H t) := rfl
  simp only [Header.headerBits, Header.vertexTotal, Header.dartTotal, oldPrefix,
    ownerPrefix, PreprocessingRegularLoopWords.blocksPrefix_all,
    PreprocessingRegularBounds.ownerPrefix, PreprocessingRegularBounds.header]
  rw [oldBits, ownerBits]

theorem finalOutput_eq (H : BaseTable) (t : GraphTables.Table) :
    finalOutput H t = PortTables.tableBits (PreprocessingRegularTables.regularize H t) := by
  change finalOutput H t = PortTables.tableBits (PreprocessingRegularTables.ofCloudTables t
    (PreprocessingRegularTables.padding t) (PreprocessingRegularTables.familyCloudTable H t))
  rw [PreprocessingRegularWords.tableBits_ofCloudTables]
  have oldBits : MachineRegularOriginalBody.emittedBits H t =
      PreprocessingRegularWords.originalVertexBits t (PreprocessingRegularTables.padding t)
        (PreprocessingRegularTables.familyCloudTable H t) := rfl
  have ownerBits : MachineRegularOwnerBody.ownerBits H t =
      (fun v => (List.ofFn (PreprocessingRegularWords.dummyVertexBits t
        (PreprocessingRegularTables.padding t) (PreprocessingRegularTables.familyCloudTable H t) v)).flatten) := rfl
  simp only [finalOutput, oldOutput, headerOutput, Header.headerBits, Header.vertexTotal,
    Header.dartTotal, oldPrefix, ownerPrefix, PreprocessingRegularLoopWords.blocksPrefix_all,
    List.append_assoc]
  rw [oldBits, ownerBits]

end Top

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedRows

open InitialParameters UpperParameterScalars
open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Fourier

noncomputable section

variable {δ : ℚ} (plan : Plan δ)

def cutoff (hδ : 0 < δ) : Nat :=
  DescendingRows.commonCutoff (useful_pos hδ) plan.density_pos (inverse_pos hδ)
    plan.order plan.depth plan.rootFirstRows

theorem cutoff_pos (hδ : 0 < δ) : 0 < cutoff plan hδ :=
  DescendingRows.commonCutoff_pos (useful_pos hδ) plan.density_pos (inverse_pos hδ)
    plan.order plan.depth plan.rootFirstRows

instance cutoff_neZero (hδ : 0 < δ) : NeZero (cutoff plan hδ) :=
  ⟨Nat.ne_of_gt (cutoff_pos plan hδ)⟩

def sourceLength (hδ : 0 < δ) : Nat :=
  SourceOddLists.repetitionLength PCPSource.sourceGap (cutoff plan hδ)
    PCPSource.sourceGap_pos PCPSource.sourceGap_le_one

end
end PerfectCompleteness.FixedRows

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalChildBlocks
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalChildBlocks

open PointwiseSpaces RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalChildScalars
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def sourceLaw (calls : Nat) (rows repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    FiniteDistribution (SourceTape calls rows repeats chosen q slots) :=
  (callsLaw calls repeats chosen q slots).product
    (WholeArraySampler.tapeLaw rows repeats (.step chosen q) slots)

def observed (calls : Nat) (rows repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : SourceTape calls rows repeats chosen q slots) :
    CutChildGrouping.Assembled (C := Fin calls) slots rows :=
  (fun call => RecursiveSampler.evaluate F2 repeats (.step chosen q) (LeafDomain slots) (ω.1 call),
    OriginalBelowCut.below rows repeats chosen q slots ω.2)

end
end PerfectCompleteness.OriginalChildBlocks

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceKeyBoundsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SourceKeyBounds


open CanonicalKeys CanonicalKeyShape ClauseSupport MixedSupport
open UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

variable {width : Nat} {Y : Type*}

theorem retained_length_le (slots : Fin width → Slot) (support : Fin width → SupportMode) :
    (retained slots support).length ≤ width := by
  unfold retained
  exact (List.length_filter_le _ _).trans_eq (by simp)

theorem key_retained_length (side : Side) (slots : Fin width → Slot)
    (f : Assignment slots → Y) : (CanonicalKeys.key side slots f).retained.length ≤ width := by
  change (retainedKeys slots f).length ≤ width
  rw [retainedKeys_recover]
  exact retained_length_le slots _

end

end PerfectCompleteness.SourceKeyBounds



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeCutCallsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.OriginalCutCalls

open RecursiveSpaces DescendantSpaces TerminalCalls
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m : Nat}

theorem card_step (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) :
    Fintype.card (Index rows repeats (.step i p)) =
      (2 ^ rows (n + 1) - 1) * Fintype.card (TerminalIndex repeats (.step i p)) +
        Fintype.card (Index rows repeats p) := by
  change Fintype.card
    ((BucketSampler.Direction (rows (n + 1)) × TerminalIndex repeats (.step i p)) ⊕
      Index rows repeats p) = _
  rw [Fintype.card_sum, Fintype.card_prod, WholeCutCalls.direction_card]

theorem card_eq_formula (rows repeats : Nat → Nat) (p : Path branch n m) :
    Fintype.card (Index rows repeats p) = (2 ^ rows m - 1) +
      ∑ h ∈ Finset.Ioc m n, (2 ^ rows h - 1) *
        ∏ k ∈ Finset.Ioc m h, 2 * repeats k := by
  induction p with
  | refl m => simp only [card_refl, Finset.Ioc_self, Finset.sum_empty, Nat.add_zero]
  | @step n m i p ih =>
      rw [card_step, TerminalCalls.card_eq_prod, ih,
        Finset.sum_Ioc_succ_top p.height_le]
      omega

theorem card_eq_count (rows repeats : Nat → Nat) (p : Path branch n m) :
    Fintype.card (Index rows repeats p) = count rows repeats n m :=
  card_eq_formula rows repeats p

end
end PerfectCompleteness.OriginalCutCalls

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_ExactTargetOnlineEncoding
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ExactTargetOnlineEncoding

open UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v) (rows repeats : Nat → Nat)
    (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

local notation "order" => CompletedVisitOrder.completedOrder
  (t := t) clauses rows repeats hn hbranch hrows δ
local notation "target" => ExactPreliminaryTarget.construct
  (t := t) clauses rows repeats hn hbranch hrows δ
local notation "edge" => ExactPreliminaryTarget.entry
  (t := t) clauses rows repeats hn hbranch hrows δ

theorem target_gameBits :
    Encoding.gameBits target =
      encodeWords [(order).length, (order).length,
        FinitePreliminaryCompletion.alphabet branch n t δ, (order).length] ++
      (order).flatMap (fun e => encodeWords (Encoding.edgeWords (edge e))) := by
  change encodeWords
    ([(CompletedVisitOrder.rawOrder (t := t) clauses rows repeats hn hbranch hrows δ).length,
      (CompletedVisitOrder.rawOrder (t := t) clauses rows repeats hn hbranch hrows δ).length,
      FinitePreliminaryCompletion.alphabet branch n t δ, ((order).map edge).length] ++
        ((order).map edge).flatMap Encoding.edgeWords) = _
  rw [encodeWords_append, encodeWords_flatMap]
  apply congrArg₂ List.append
  · apply congrArg encodeWords
    simp only [List.length_map]
    simp only [CompletedVisitOrder.rawOrder, List.length_map]
  · simp only [List.flatMap_map]

end
end PerfectCompleteness.ExactTargetOnlineEncoding

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_PreliminaryOutputLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.PreliminaryOutput

open HierarchicalArrays
open scoped Classical

noncomputable section

variable {v m : Nat} [NeZero m]

def value (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) : ℝ := by
  let F := PreliminarySampler.family clauses branch n t rows repeats
  let : Fintype (HierarchicalGame.LeftVertex F) := Fintype.ofFinite _
  let : Fintype (HierarchicalGame.RightVertex F) := Fintype.ofFinite _
  let : ∀ x, Fintype (HierarchicalGame.LeftLabel F x) := fun _ => Fintype.ofFinite _
  let : ∀ y, Fintype (HierarchicalGame.RightLabel F y) := fun _ => Fintype.ofFinite _
  exact (PreliminarySampler.game clauses branch n t rows repeats hn hbranch hrows).value

end
end PerfectCompleteness.PreliminaryOutput


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_FilledUniformSampler
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FilledUniformSampler

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (m + 1) → Fin t → MixedSupport.Slot)

abbrev Exterior := WholeCutGrouping.Exterior rows repeats p
  (CutSlotAssembly.fill p outside placeholder)

def exteriorEquiv (inside : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    Exterior rows repeats p outside placeholder ≃
      WholeCutGrouping.Exterior rows repeats p (CutSlotAssembly.fill p outside inside) :=
  WholeCutExteriorTransport.equiv rows repeats p
    (CutSlotAssembly.fill p outside placeholder) (CutSlotAssembly.fill p outside inside)
    (CutSlotAssembly.fill_outside_eq p outside placeholder inside)

def filledSplitEquiv (inside : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    (Exterior rows repeats p outside placeholder ×
      CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows) ≃
        WholeCutSampler.Tape rows repeats p (CutSlotAssembly.fill p outside inside) :=
  (Equiv.prodCongr (exteriorEquiv rows repeats p outside placeholder inside)
    (childrenEquiv rows repeats p outside inside)).trans
      (WholeCutGrouping.splitTape rows repeats p (CutSlotAssembly.fill p outside inside)).symm

def evaluate (inside : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (x : Exterior rows repeats p outside placeholder ×
      CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows) :
    Arrays (CutSlotAssembly.fill p outside inside) rows :=
  WholeCutSampler.evaluate rows repeats p (CutSlotAssembly.fill p outside inside)
    (filledSplitEquiv rows repeats p outside placeholder inside x)

end
end PerfectCompleteness.FilledUniformSampler

end

end OAI
end


