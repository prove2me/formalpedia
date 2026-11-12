-- Prove2me | Definitions.Def_OAIQ252P020
-- name    : OAIQ252P020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T08:01:13.994203+00:00
-- url     : https://prove2.me/theorems/5c0fdaa9-6f6c-4dea-a0b9-5b1e68d7d3bf
-- title:
--   Definitions bundle OAIQ252P020 of the split of OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 21 declarations of OpenAI's Lean: 19 definitions and 2 theorems. The definitions and types are `OAI.PerfectCompleteness.StoppedUsefulPairLaw.liftFresh`, `OAI.PerfectCompleteness.UpperScalarCutLaw.assembledLaw`, `OAI.PerfectCompleteness.UpperScalarCutLaw.freshValuesLaw`, `OAI.PerfectCompleteness.UpperScalarCutLaw.recordLaw`, `OAI.PerfectCompleteness.UpperScalarCutLaw.valuesLaw`, `OAI.PerfectCompleteness.UpperScalarCutProjection.backgroundFintype`, `OAI.PerfectCompleteness.UpperScalarCutProjection.exteriorEquiv`, `OAI.PerfectCompleteness.UpperScalarCutProjection.numberedRecordPullback`, `OAI.PerfectCompleteness.UpperScalarCutProjection.oldRecordPullback`, `OAI.PerfectCompleteness.UpperScalarCutProjection.recordPullback`, `OAI.PerfectCompleteness.UpperScalarCutProjection.stoppedRead`, `OAI.PerfectCompleteness.UpperScalarCutReconstruction.packEquiv`, `OAI.PerfectCompleteness.UpperScalarCutReconstruction.read`, `OAI.PerfectCompleteness.UpperScalarCutReference.freshReferenceLaw`, `OAI.PerfectCompleteness.UpperScalarCutReference.freshStoppedTapeEquiv`, `OAI.PerfectCompleteness.UpperScalarCutReference.numberedReferenceLaw`, `OAI.PerfectCompleteness.UpperScalarCutReference.referenceLaw`, `OAI.PerfectCompleteness.UpperScalarFreshProjection.freshExteriorEquiv`, `OAI.PerfectCompleteness.UpperScalarPairAveraging.pathPairLaw`.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: [`PerfectCompleteness_Decoding_UpperScalarCutLaw`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Decoding/UpperScalarCutLaw.lean), [`PerfectCompleteness_Decoding_UpperScalarCutProjection`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Decoding/UpperScalarCutProjection.lean), [`PerfectCompleteness_Decoding_UpperScalarCutReconstructionLemmas`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Decoding/UpperScalarCutReconstructionLemmas.lean), [`PerfectCompleteness_Decoding_UpperScalarCutReference`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Decoding/UpperScalarCutReference.lean), [`PerfectCompleteness_Decoding_UpperScalarFreshProjectionLemmas`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Decoding/UpperScalarFreshProjectionLemmas.lean), [`PerfectCompleteness_Decoding_UpperScalarPairAveraging`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Decoding/UpperScalarPairAveraging.lean), [`PerfectCompleteness_Sampling_StoppedUsefulPairLaw`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/PerfectCompleteness/Sampling/StoppedUsefulPairLaw.lean).
--
--   **Imports.** It imports the bundles `OAIQ252P018` and `OAIQ252P019` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.PerfectCompleteness.UpperScalarCutProjection.fixed_projected_law`, `OAI.PerfectCompleteness.UpperScalarCutProjection.pairRecord_pullback` and `OAI.PerfectCompleteness.UpperScalarPairAveraging.fixed_pairLaw`; the proofs of `OAI.PerfectCompleteness.StoppedSourcePairLaw.prefix_pair_law`, `OAI.PerfectCompleteness.StoppedUsefulPairLaw.actualPair_law`, `OAI.PerfectCompleteness.StoppedUsefulPairLaw.observe_law`, `OAI.PerfectCompleteness.UpperCutTriangle.modified_reference_variation`, `OAI.PerfectCompleteness.UpperScalarCutProjection.fixed_projected_law`, `OAI.PerfectCompleteness.UpperScalarCutProjection.pairRecord_pullback` and `OAI.PerfectCompleteness.UpperScalarPairAveraging.fixed_pairLaw`.
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
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
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
import Definitions.Def_OAIQ252P018
import Definitions.Def_OAIQ252P019

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_UpperScalarCutReconstructionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UpperScalarCutReconstruction

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n j i k t : Nat}

def packEquiv (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (OriginalWholeCut.Record rows repeats (p.append r) slots × FreshRecord repeats p r slots) ≃
      Record rows repeats p r slots where
  toFun z := pack rows repeats p r slots z.1 z.2
  invFun z := (oldRecord rows repeats p r slots z, freshRecord rows repeats p r slots z)
  left_inv _ := rfl
  right_inv z := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext call
        cases call <;> rfl
      · rfl

def read (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tapes : WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots ×
      RecursiveSampler.Tape F2 repeats (r.append (.step chosen q)) (LeafDomain (cutSlots p slots))) :
    Record rows repeats p r slots :=
  pack rows repeats p r slots
    (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots tapes.1)
    (readFresh repeats p r (.step chosen q) slots tapes.2)

end
end PerfectCompleteness.UpperScalarCutReconstruction

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_UpperScalarCutLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UpperScalarCutLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape UpperScalarCutReconstruction
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n j i k t : Nat}

def freshValuesLaw (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (suffix : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (FreshValues repeats p r slots) :=
  FiniteProduct.law (fun _ : TerminalCalls.TerminalIndex repeats r =>
    RecursiveSampler.law F2 repeats suffix (LeafDomain (cutSlots (p.append r) slots)))

def valuesLaw (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (suffix : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (UpperScalarCutCalls.Index rows repeats p r →
      H (cutSlots (p.append r) slots)) :=
  FiniteProduct.law (fun _ : UpperScalarCutCalls.Index rows repeats p r =>
    RecursiveSampler.law F2 repeats suffix (LeafDomain (cutSlots (p.append r) slots)))

def assembledLaw (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (CutChildGrouping.Assembled
      (C := UpperScalarCutCalls.Index rows repeats p r) (cutSlots (p.append r) slots) rows) :=
  @FiniteDistribution.transport
    ((UpperScalarCutCalls.Index rows repeats p r → H (cutSlots (p.append r) slots)) ×
      OriginalWholeCut.ChildArrays rows (cutSlots (p.append r) slots))
    (CutChildGrouping.Assembled (C := UpperScalarCutCalls.Index rows repeats p r)
      (cutSlots (p.append r) slots) rows)
    (instFintypeProd _ _)
    (CutChildGrouping.assembledFintype (C := UpperScalarCutCalls.Index rows repeats p r)
      (cutSlots (p.append r) slots) rows)
    ((valuesLaw rows repeats p r (.step chosen q) slots).product
      (OriginalWholeCutLaw.belowArraysLaw rows repeats chosen q (cutSlots (p.append r) slots)))
    (assembledEquiv rows repeats p r slots)

def recordLaw (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (UpperScalarCutReconstruction.Record rows repeats p r slots) :=
  (exteriorLaw rows repeats p r slots).product (assembledLaw rows repeats p r chosen q slots)

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

end
end PerfectCompleteness.UpperScalarCutLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_UpperScalarCutReference
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UpperScalarCutReference

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape UpperScalarCutReconstruction
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n j i t : Nat}

def freshReferenceLaw (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (FreshRecord repeats p r slots) :=
  (FiniteDistribution.uniform (FreshValues repeats p r slots)).product
    (UpperScalarCutLaw.freshExteriorLaw repeats p r slots)

def freshStoppedTapeEquiv (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FreshRecord repeats p r slots ≃
      RecursiveSampler.Tape F2 repeats r (LeafDomain (cutSlots p slots)) :=
  (Equiv.prodCongr
    (Equiv.arrowCongr (Equiv.refl (TerminalCalls.TerminalIndex repeats r))
      (cutSpaceEquiv p r slots))
    (Equiv.refl (FreshExterior repeats p r slots))).trans
      (OriginalScalarReconstruction.prefixSplit F2 repeats r
        (LeafDomain (cutSlots p slots))).symm

def referenceLaw (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (UpperScalarCutReconstruction.Record rows repeats p r slots) :=
  (UpperScalarCutLaw.exteriorLaw rows repeats p r slots).product
    (FiniteDistribution.uniform (CutChildGrouping.Assembled
      (C := UpperScalarCutCalls.Index rows repeats p r) (cutSlots (p.append r) slots) rows))

def numberedReferenceLaw (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (UpperScalarCutReconstruction.NumberedRecord rows repeats p r slots) :=
  (UpperScalarCutLaw.exteriorLaw rows repeats p r slots).product
    (FiniteDistribution.uniform (CutChildGrouping.Assembled
      (C := Fin (UpperScalarCutCalls.count rows repeats n j (i + 1)))
      (cutSlots (p.append r) slots) rows))

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

end
end PerfectCompleteness.UpperScalarCutReference

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_UpperScalarFreshProjectionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UpperScalarFreshProjection

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape UpperScalarCutReconstruction
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n j i t : Nat}

theorem outside_append (p : Path branch n j) (r : Path branch j i)
    (s : Slots branch j) (hs : WholeCutExteriorTransport.Outside r s) :
    WholeCutExteriorTransport.Outside (p.append r) (p.slotEmbedding s) := by
  rintro ⟨u, hu⟩
  apply hs
  refine ⟨u, p.slotEmbedding_injective ?_⟩
  exact (p.slotEmbedding_append r u).symm.trans hu

theorem restricted_outside_eq (p : Path branch n j) (r : Path branch j i)
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → left s = right s) :
    ∀ s, WholeCutExteriorTransport.Outside r s → cutSlots p left s = cutSlots p right s :=
  fun s h => hs (p.slotEmbedding s) (outside_append p r s h)

def freshExteriorEquiv (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → left s = right s) :
    FreshExterior repeats p r right ≃ FreshExterior repeats p r left :=
  Equiv.cast (OriginalScalarProjection.scalarExterior_eq repeats r
    (cutSlots p right) (cutSlots p left)
    (fun s h => (restricted_outside_eq p r left right hs s h).symm))

end
end PerfectCompleteness.UpperScalarFreshProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_UpperScalarCutProjection
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UpperScalarCutProjection

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n j i t : Nat}

def oldRecordPullback (rows repeats : Nat → Nat) (p : Path branch n (i + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
    (record : OriginalWholeCut.Record rows repeats p right) :
    OriginalWholeCut.Record rows repeats p left :=
  (OriginalWholeCutProjection.exteriorEquiv rows repeats p right left
      (fun s h => (hs s h).symm) record.1,
    ChildAssemblyProjection.assembledPullback rows (CutGroupedProjection.cutProjection p q) record.2)

def exteriorEquiv (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → left s = right s) :
    UpperScalarCutReconstruction.Exterior rows repeats p r right ≃
      UpperScalarCutReconstruction.Exterior rows repeats p r left :=
  Equiv.prodCongr
    (OriginalWholeCutProjection.exteriorEquiv rows repeats (p.append r) right left
      (fun s h => (hs s h).symm))
    (UpperScalarFreshProjection.freshExteriorEquiv repeats p r left right hs)

def recordPullback (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → left s = right s)
    (record : UpperScalarCutReconstruction.Record rows repeats p r right) :
    UpperScalarCutReconstruction.Record rows repeats p r left :=
  (exteriorEquiv rows repeats p r left right hs record.1,
    ChildAssemblyProjection.assembledPullback rows
      (CutGroupedProjection.cutProjection (p.append r) q) record.2)

def numberedRecordPullback (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → left s = right s)
    (record : UpperScalarCutReconstruction.NumberedRecord rows repeats p r right) :
    UpperScalarCutReconstruction.NumberedRecord rows repeats p r left :=
  (exteriorEquiv rows repeats p r left right hs record.1,
    ChildAssemblyProjection.assembledPullback rows
      (CutGroupedProjection.cutProjection (p.append r) q) record.2)

def stoppedRead (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : UpperScalarCutReconstruction.Record rows repeats p r slots) :
    WholeArraySampler.Tape rows repeats (p.append r) slots × H (cutSlots p slots) :=
  (OriginalUniformCut.toStoppedTape rows repeats (p.append r) slots
      (UpperScalarCutReconstruction.oldRecord rows repeats p r slots record),
    UpperScalarCutReconstruction.reconstructFresh repeats p r slots
      (UpperScalarCutReconstruction.freshRecord rows repeats p r slots record))

attribute [local instance] linearMapFintype

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) slots (upperNode p)) :=
  Fintype.ofFinite _

end
end PerfectCompleteness.UpperScalarCutProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_UpperScalarPairAveraging
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UpperScalarPairAveraging

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped BigOperators Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n j i k t : Nat}

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

attribute [local instance] OAI.PerfectCompleteness.UpperScalarPairAveraging.backgroundFintype
local instance rowSpaceFintype_r2f2f7b_1 (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _
def pathPairLaw (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1)))) :
    Path branch (j + 1) 0 →
      FiniteDistribution (HierarchicalAgreementMean.PairRecord (rows := rows) slots (upperNode p))
  | .step chosen q =>
      (directions.product
        (((OriginalWholeCutLaw.recordLaw rows repeats p chosen q slots).pushforward
          (OriginalWholeCutBridge.numberRecord rows repeats p slots)).product
            (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots))))).pushforward
          (OriginalCutCollision.pairRecord rows repeats p slots)

end
end PerfectCompleteness.UpperScalarPairAveraging

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_StoppedUsefulPairLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedUsefulPairLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {N j i t : Nat}

attribute [local instance] OAI.PerfectCompleteness.StoppedUsefulPairLaw.rowSpaceFintype
attribute [local instance] OAI.PerfectCompleteness.StoppedUsefulPairLaw.backgroundFintype
def liftFresh (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (sample : Sample rows repeats p chosen q right) :
    BucketSampler.Direction (rows (j + 1)) ×
      (WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) right × H (cutSlots p native)) :=
  (sample.1, (sample.2.1, HPullback (CutGroupedProjection.cutProjection p projection) sample.2.2))

end
end PerfectCompleteness.StoppedUsefulPairLaw

end

end OAI
end


