-- Prove2me | Definitions.Def_Q260K061
-- name    : Q260K061
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:14:12.809598+00:00
-- url     : https://prove2.me/theorems/f01bde10-7650-4830-a2af-7b203d46d8ce
-- title:
--   Definitions bundle Q260K061 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 47 declarations of OpenAI's Lean: 24 definitions, 9 inductive types or structures, 1 instance and 13 theorems. The definitions and types are `OAI.KadisonKastler.BoundedMapDatum`, `OAI.KadisonKastler.CountableProjectionCopies`, `OAI.KadisonKastler.CountableProjectionCopies.fullMatrixCorner`, `OAI.KadisonKastler.CountableProjectionCopies.rebasedPartial`, `OAI.KadisonKastler.FamilyRowInvariant`, `OAI.KadisonKastler.FiniteCoefficientConjugations`, `OAI.KadisonKastler.FiniteFullMatrixCornerData`, `OAI.KadisonKastler.FiniteProjectionIn`, `OAI.KadisonKastler.HasFixedRowFactorization`, `OAI.KadisonKastler.HasOperatorValues`, `OAI.KadisonKastler.MatrixTypeIIIFactorModel`, `OAI.KadisonKastler.ProperlyInfiniteIdentity`, `OAI.KadisonKastler.PublishedFieldTomiyama`, `OAI.KadisonKastler.PublishedFiniteType`, `OAI.KadisonKastler.PublishedInfiniteFactorProperlyInfinite`, `OAI.KadisonKastler.PublishedProperInfiniteProjectionCopies`, `OAI.KadisonKastler.PublishedTypeIIIProjectionComparison`, `OAI.KadisonKastler.TraceQuotientMap`, `OAI.KadisonKastler.TraceQuotientMap.comapEquiv`, `OAI.KadisonKastler.TraceSeparable`, `OAI.KadisonKastler.TracialUltrapower`, `OAI.KadisonKastler.TypeIIIFactor`, `OAI.KadisonKastler.TypeIIInfinityFactor`, `OAI.KadisonKastler.UniversalMapFamily`, `OAI.KadisonKastler.boundedSequenceConst`, `OAI.KadisonKastler.boundedSequenceMapEquiv`, `OAI.KadisonKastler.boundedSequenceMapHom`, `OAI.KadisonKastler.concreteFactorTrace`, `OAI.KadisonKastler.cyclicFactorLeft`, `OAI.KadisonKastler.cyclicFactorRepresentation`, `OAI.KadisonKastler.factorizationCyclicSpace`, `OAI.KadisonKastler.familyRowAverage`, `OAI.KadisonKastler.universalRowOrder`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `KadisonKastler_ConcreteFiniteTrace`, `KadisonKastler_FactorizationCyclicSpace`, `KadisonKastler_FiniteCoefficientTests`, `KadisonKastler_OperatorFieldValues`, `KadisonKastler_OperatorMeanStar`, `KadisonKastler_PublishedFieldTomiyama`, `KadisonKastler_PublishedFiniteType`, `KadisonKastler_PublishedIndependence`, `KadisonKastler_PublishedInfiniteType`, `KadisonKastler_PublishedProperInfiniteProjection`, `KadisonKastler_PublishedTypeIIIProjection`, `KadisonKastler_PublishedUltrapower`, `KadisonKastler_SemifiniteFactor`, `KadisonKastler_SequenceTransport`, `KadisonKastler_SimultaneousRowFamily`, `KadisonKastler_SimultaneousRowUltralimit`, `KadisonKastler_TypeIIIUltraproduct`, `KadisonKastler_UltrapowerExpectation`, `KadisonKastler_UniformInfinitesimalCutoff`, `KadisonKastler_WeakRowFactorization`.
--
--   **Imports.** It imports the published bundle `Def_StrongKadisonKastler`; the bundles `Q260K021` and `Q260K022` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q260K062`; the statements `OAI.KadisonKastler.FullMatrixCorner.representedCorner_isII1`, `OAI.KadisonKastler.TypeIIIFactor.commutant_properlyInfinite`, `OAI.KadisonKastler.TypeIIIFactor.exists_relative_matrix_spatial_equiv`, `OAI.KadisonKastler.TypeIIIFactor.of_starAlgEquiv`, `OAI.KadisonKastler.TypeIIInfinityFactor.nonempty_finiteMatrixCornerData`, `OAI.KadisonKastler.TypeIIInfinityFactor.of_starAlgEquiv`, `OAI.KadisonKastler.exists_properInfinite_matrix_preparation_of_embedding`, `OAI.KadisonKastler.exists_selfAdjoint_split_of_finite_typeI_commutant`, `OAI.KadisonKastler.exists_selfAdjoint_split_of_reducing_finite_corner`, `OAI.KadisonKastler.hasFixedRowFactorization_of_mem_orbitClosure`, `OAI.KadisonKastler.isII1Factor_of_near_of_published`, `OAI.KadisonKastler.projectionSemifinite_of_finite_projection`, `OAI.KadisonKastler.projection_equivalent_one_of_not_finite` and `OAI.KadisonKastler.separableSpace_of_traceHilbert`; the proofs of `OAI.KadisonKastler.FullMatrixCorner.representedCorner_isII1`, `OAI.KadisonKastler.TypeIIIFactor.of_starAlgEquiv`, `OAI.KadisonKastler.TypeIIInfinityFactor.nonempty_finiteMatrixCornerData`, `OAI.KadisonKastler.equivalent_corner_projection_vector_norm`, `OAI.KadisonKastler.exists_countable_source_partition`, `OAI.KadisonKastler.exists_countable_source_partition_of_full`, `OAI_KadisonKastler_expectedMatrixSubfactorModel_of_bicentralizer`, `OAI.KadisonKastler.isII1Factor_of_near_of_published`, `OAI.KadisonKastler.projectionSemifinite_of_finite_projection`, `OAI.KadisonKastler.projection_equivalent_one_of_not_finite`, `OAI.KadisonKastler.separableSpace_of_traceHilbert` and `OAI_KadisonKastler_uniform_typeIII_selfAdjoint_infinitesimal_estimate`.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.Ultrafilter
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K021
import Definitions.Def_Q260K022

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConcreteFiniteTrace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The faithful normal trace of a concrete finite diffuse factor

The projection-dimension trace gives a faithful normal tracial state
on a concrete finite diffuse factor.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonKastler.finiteTraceOrder
local instance finiteTracePreorder_r3ab31d_1 : Preorder (Algebra M) := (CStarAlgebra.spectralOrder _).toPreorder
local instance finiteTraceLE_r3ab31d_1 : LE (Algebra M) := (CStarAlgebra.spectralOrder _).toLE
attribute [local instance] OAI.KadisonKastler.finiteTraceStarOrder
/-- The trace is a complex-valued faithful tracial state with the
continuity required by amplification. -/
def concreteFactorTrace (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    FaithfulTracialState (Algebra M) where
  toLinearMap := (Generator.Tracial.traceFreeTrace (factor_central hM) hM.diffuse hM.finite
    (factor_one_ne_zero hM)).toLinearMap
  map_one := (Generator.Tracial.traceFreeTrace_spec (factor_central hM) hM.diffuse hM.finite
    (factor_one_ne_zero hM)).2.1
  positive x := (Generator.Tracial.traceFreeTrace_spec (factor_central hM) hM.diffuse hM.finite
    (factor_one_ne_zero hM)).2.2.1 _ (star_mul_self_nonneg _)
  positive_im x := by
    have h := (Generator.Tracial.traceFreeTrace_spec (factor_central hM) hM.diffuse hM.finite
      (factor_one_ne_zero hM)).2.2.2.1 (star x * x)
    rw [star_mul, star_star] at h
    have hi := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at hi
    have hz : ((Generator.Tracial.traceFreeTrace (factor_central hM) hM.diffuse hM.finite
      (factor_one_ne_zero hM)) (star x * x)).im = 0 := by linarith
    exact hz
  faithful x hx := by
    have hs := (Generator.Tracial.traceFreeTrace_faithful (factor_central hM) hM.diffuse hM.finite
      (factor_one_ne_zero hM) (star x * x) (star_mul_self_nonneg _)).mp hx
    exact (CStarRing.star_mul_self_eq_zero_iff x).mp hs
  tracial := (Generator.Tracial.traceFreeTrace_spec (factor_central hM) hM.diffuse hM.finite
    (factor_one_ne_zero hM)).2.2.2.2

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedUltrapower
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The published tracial-ultraproduct construction

Popa, *Independence properties in subalgebras of ultraproduct II₁
factors*, J. Funct. Anal. 266 (2014), §1.6 (arXiv:1308.3982v3,
printed pp. 7–8), recalls the tracial ultraproduct as a finite von
Neumann algebra, with trace the ultralimit of the coordinate traces.
For a constant sequence of II₁ factors it is again a II₁ factor.

The input below contains exactly that construction. The two-norm kernel
property used by clipping is derived afterwards from faithfulness and
the trace formula; it is not an additional input.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

variable {B : Type u} [CStarAlgebra B]

/-- A represented tracial ultrapower, with the published coordinate
trace formula. The quotient is a concrete von Neumann algebra. -/
structure TracialUltrapower (τ : FaithfulTracialState B) (ω : Ultrafilter ℕ) where
  H : Type u
  [normedAddCommGroup : NormedAddCommGroup H]
  [innerProductSpace : InnerProductSpace ℂ H]
  [completeSpace : CompleteSpace H]
  algebra : VonNeumannAlgebra H
  factor : Generator.IsII1Factor algebra.toStarSubalgebra
  quotient : BoundedSequence B →⋆ₐ[ℂ] Algebra algebra
  surjective : Function.Surjective quotient
  trace_limit : ∀ x : BoundedSequence B,
    Tendsto (fun j => τ.toLinearMap (x j)) (ω : Filter ℕ)
      (𝓝 ((concreteFactorTrace factor).toLinearMap (quotient x)))

attribute [instance] TracialUltrapower.normedAddCommGroup
  TracialUltrapower.innerProductSpace TracialUltrapower.completeSpace

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UltrapowerExpectation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.varyingSequenceMap_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The actual expectation onto the constant copy

Weak compactness constructs the expectation value inside the original
von Neumann algebra. The finite-vector normal trace identifies it by
trace pairings. This constructs, rather than assumes, the expectation
used in the scalar-recovery weak limit.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B : Type*} [CStarAlgebra B]

/-- Constant sequences as a unital star homomorphism. -/
def boundedSequenceConst : B →⋆ₐ[ℂ] BoundedSequence B where
  toFun := BoundedContinuousFunction.const ℕ
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp]
theorem boundedSequenceConst_apply (b : B) (j : ℕ) : boundedSequenceConst b j = b := rfl

/-- The trace formula and quotient map furnished by a tracial ultrapower.
The target trace is an explicit parameter so its construction stays separate
from the elementary expectation proofs. -/
structure TraceQuotientMap {C : Type*} [CStarAlgebra C]
    (τ : FaithfulTracialState B) (σ : FaithfulTracialState C) (ω : Ultrafilter ℕ) where
  quotient : BoundedSequence B →⋆ₐ[ℂ] C
  surjective : Function.Surjective quotient
  trace_limit : ∀ s, Tendsto (fun j => τ.toLinearMap (s j)) (ω : Filter ℕ)
    (𝓝 (σ.toLinearMap (quotient s)))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FactorizationCyclicSpace
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! The reducing subspace generated by the left operator in a factorization.
It retains every coefficient of the factored map and removes undetectable
vectors from the auxiliary representation. -/

namespace KadisonKastler

noncomputable section

open scoped InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H}

def factorizationCyclicSpace (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (L : H →L[ℂ] K) : Submodule ℂ K :=
  (Submodule.span ℂ (Set.range (fun p : Algebra M × H => π p.1 (L p.2)))).topologicalClosure

theorem mem_factorizationCyclicSpace (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (L : H →L[ℂ] K) (a : Algebra M) (ξ : H) :
    π a (L ξ) ∈ factorizationCyclicSpace π L :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(a, ξ), rfl⟩)

theorem left_mem_factorizationCyclicSpace (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (L : H →L[ℂ] K) (ξ : H) : L ξ ∈ factorizationCyclicSpace π L := by
  simpa only [map_one, one_apply_eq_self] using mem_factorizationCyclicSpace π L 1 ξ

theorem factorizationCyclicSpace_invariant (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (L : H →L[ℂ] K) (b : Algebra M) {x : K}
    (hx : x ∈ factorizationCyclicSpace π L) : π b x ∈ factorizationCyclicSpace π L := by
  have h : factorizationCyclicSpace π L ≤
      (factorizationCyclicSpace π L).comap (π b).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨a, ξ⟩, rfl⟩
      change π b (π a (L ξ)) ∈ factorizationCyclicSpace π L
      simpa only [map_mul, mul_apply_eq_comp] using mem_factorizationCyclicSpace π L (b * a) ξ
    · exact (Submodule.isClosed_topologicalClosure _).preimage (π b).continuous
  exact h hx

instance factorizationCyclicSpace_complete (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (L : H →L[ℂ] K) : CompleteSpace (factorizationCyclicSpace π L) :=
  Submodule.topologicalClosure.completeSpace _

def cyclicFactorRepresentation (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (L : H →L[ℂ] K) : Algebra M →⋆ₐ[ℂ]
      (factorizationCyclicSpace π L →L[ℂ] factorizationCyclicSpace π L) where
  toFun a := (π a).restrict (fun _ hx => factorizationCyclicSpace_invariant π L a hx)
  map_zero' := by
    ext x
    change π 0 (x : K) = 0
    exact congrArg (fun T : K →L[ℂ] K => T (x : K)) π.toAlgHom.map_zero
  map_one' := by
    ext x
    change π 1 (x : K) = (x : K)
    exact congrArg (fun T : K →L[ℂ] K => T (x : K)) π.toAlgHom.map_one
  map_add' a b := by
    ext x
    change π (a + b) (x : K) = π a (x : K) + π b (x : K)
    exact congrArg (fun T : K →L[ℂ] K => T (x : K)) (π.toAlgHom.map_add a b)
  map_mul' a b := by
    ext x
    change π (a * b) (x : K) = π a (π b (x : K))
    exact congrArg (fun T : K →L[ℂ] K => T (x : K)) (π.toAlgHom.map_mul a b)
  commutes' c := by
    ext x
    change π (algebraMap ℂ (Algebra M) c) (x : K) = c • (x : K)
    exact congrArg (fun T : K →L[ℂ] K => T (x : K)) (π.toAlgHom.commutes c)
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ (y : K) (π (star a) (x : K)) =
      inner ℂ y ((star ((π a).restrict
        (fun _ hx => factorizationCyclicSpace_invariant π L a hx))) x)
    rw [map_star]
    simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    rfl

@[simp] theorem cyclicFactorRepresentation_apply
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K)
    (a : Algebra M) (x : factorizationCyclicSpace π L) :
    (cyclicFactorRepresentation π L a x : K) = π a (x : K) := rfl

def cyclicFactorLeft (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K) :
    H →L[ℂ] factorizationCyclicSpace π L :=
  L.codRestrict (factorizationCyclicSpace π L) (left_mem_factorizationCyclicSpace π L)

@[simp] theorem cyclicFactorLeft_apply
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K) (ξ : H) :
    (cyclicFactorLeft π L ξ : K) = L ξ := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteCoefficientTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Directed finite tests on arbitrary Hilbert spaces

Local approximations need not agree on overlapping tests. An ultrafilter
extending the directed test filter produces the coefficient limits needed
by the UCP criterion.
-/

namespace KadisonKastler

open Filter
open scoped Topology CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N : VonNeumannAlgebra H}

local instance testFactorOrder_r3ab31d_1 (P : VonNeumannAlgebra H) : PartialOrder (Algebra P) :=
  CStarAlgebra.spectralOrder _
local instance testFactorStarOrder_r3ab31d_1 (P : VonNeumannAlgebra H) : StarOrderedRing (Algebra P) :=
  CStarAlgebra.spectralOrderedRing _
/-- The finite coefficient condition supplied by separable restrictions in
the manuscript. It asserts no global range inclusion for a local conjugacy. -/
def FiniteCoefficientConjugations (M N : VonNeumannAlgebra H) (a : ℝ) : Prop :=
  ∀ (E : Finset (Algebra M)) (V : Finset H) (k : ℕ),
    ∃ U : unitary (H →L[ℂ] H), ‖(U : H →L[ℂ] H) - 1‖ ≤ a ∧
      ∀ x ∈ E, ∃ b : Algebra N, ∀ ξ ∈ V, ∀ η ∈ V,
        ‖inner ℂ η (((b : H →L[ℂ] H) -
          (U : H →L[ℂ] H) * (x : H →L[ℂ] H) * star (U : H →L[ℂ] H)) ξ)‖ <
            1 / (k + 1 : ℝ)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedIndependence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Popa's finite-base independence input

Popa, *Independence properties in subalgebras of ultraproduct II1
factors*, J. Funct. Anal. 266 (2014), Theorem 0.1(b), Theorem 4.3 and
its proof, printed pp. 20 and 24 (arXiv:1308.3982v3).

Theorem 4.3 explicitly permits both endpoint letters to be one. Its proof
constructs the diffuse abelian algebra from a Haar unitary. We retain
exactly that unitary and the mixed-moment identity, only for a finite
base algebra. Testing the conditional expectation against base elements
is its faithful-trace characterization. No controlled coordinate lift or
scalar freeness of a conjugated matrix model is assumed here.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {C : Type*} [CStarAlgebra C]

/-- Separability for the tracial two-norm, rather than the operator norm. -/
def TraceSeparable (τ : FaithfulTracialState C) (S : Set C) : Prop :=
  ∃ D : Set C, D.Countable ∧ D ⊆ S ∧
    ∀ x ∈ S, ∀ ε : ℝ, 0 < ε → ∃ y ∈ D, traceTwoNorm τ (x - y) < ε

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_OperatorMeanStar
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Adjoint preservation of operator-field averaging -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorRepresentative

theorem coefficient_star (F : WeakOperatorRepresentative (H := H) μ) (ξ η : H) :
    coefficient (star F) ξ η = star (coefficient F η ξ) := by
  apply Lp.ext
  filter_upwards [coefficient_ae (star F) ξ η, coefficient_ae F η ξ,
    Lp.coeFn_star (coefficient F η ξ)] with x ha hb hs
  simp only [Pi.star_apply] at hs
  rw [ha, hs, hb, eval_star]
  change inner ℂ η ((eval F x).adjoint ξ) = star (inner ℂ ξ (eval F x η))
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm _ _).symm

end WeakOperatorRepresentative

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedFieldTomiyama
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 800000

namespace OAI

/-! # The precise Tomiyama input for the operator-field mean

Tomiyama, *On the projection of norm one in W*-algebras*, Proceedings of
 the Japan Academy 33 (1957), 608–612, Theorem 1(2), pp. 608–609,
 DOI 10.3792/pja/1195524885.

Only the bimodule conclusion for the constant-field inclusion is retained.
The contractive retraction and its adjoint preservation are constructed in
`OperatorCoefficientMean` and `OperatorMeanStar`, not assumed here.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : MeasureTheory.Measure D} [MeasureTheory.IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- The constant-field specialization of Tomiyama's Theorem 1(2).
This is an explicit published-input hypothesis, not an axiom. -/
def PublishedFieldTomiyama : Prop :=
  ∀ E : (G →ᵇ WeakOperatorField (H := H) μ) →L[ℂ] WeakOperatorField (H := H) μ,
    (∀ F, ‖E F‖ ≤ ‖F‖) →
    (∀ T, E (operatorFieldDiagonal T) = T) →
    (∀ T F, E (operatorFieldDiagonal T * F) = T * E F) ∧
      (∀ F T, E (F * operatorFieldDiagonal T) = E F * T)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_OperatorFieldValues
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Von Neumann algebra values of measurable operator fields

Commuting with constant operators in the commutant is a norm-closed
condition. Countably many strong-operator tests identify this condition
with pointwise membership outside one null set.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Pointwise BoundedContinuousFunction

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Pointwise algebra membership of the canonical representative. -/
def HasOperatorValues (M : VonNeumannAlgebra H) (q : WeakOperatorField (H := H) μ) : Prop :=
  ∀ᵐ x ∂μ, WeakOperatorRepresentative.eval (WeakOperatorField.representative q) x ∈ M

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedFiniteType
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The type-II part of the published type stability lemma

Christensen--Sinclair--Smith--White, *Perturbations of C*-algebraic invariants*,
GAFA 20 (2010), 368--397, Lemma 3.5 (author manuscript pp. 9--10), proves
that two von Neumann algebras with the same centre and distance less than
`1/10` have the same finite type I, type II₁ and infinite central parts.
Here only diffuseness of the neighbour of a II₁ factor is retained.
The centre and finiteness conclusions are already proved locally.

Primary author manuscript: https://eprints.gla.ac.uk/25426/1/25426.pdf
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The application-specific part of CSSW (2010), Lemma 3.5. No spatial
equivalence or perturbation estimate is included in this published input. -/
def PublishedFiniteType : Prop :=
  ∀ (M N : VonNeumannAlgebra H), concreteCenter M = concreteCenter N →
    Generator.IsII1Factor M.toStarSubalgebra → kkDistance M N < 1 / 10 →
    ∀ p : Algebra N, IsStarProjection p → p ≠ 0 →
      ∃ q : Algebra N, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedTypeIIIProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The two projection inputs needed for type III compression

Blackadar, *Operator Algebras* (2006), I.6.1.2--5 and I.9.2.1(iv),
give a nonzero spectral projection above any positive threshold below
the norm of a positive element. III.1.3.5--7 and III.1.4.2 give equivalence
of every nonzero projection to the identity in a countably decomposable
type III factor. Only these projection statements are assumed below.
Neither input asserts simplicity of an ultraproduct or a perturbation bound.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance typeIIIAlgebraLE_r3ab31d_1 (M : VonNeumannAlgebra H) : LE (Algebra M) :=
  (CStarAlgebra.spectralOrder (Algebra M)).toLE
local instance typeIIIAlgebraOrder_r3ab31d_1 (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance typeIIIAlgebraStarOrder_r3ab31d_1 (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
/-- Finiteness of a projection: an isometry with initial projection `p`
and range under `p` has range exactly `p`. -/
def FiniteProjectionIn (M : VonNeumannAlgebra H) (p : Algebra M) : Prop :=
  ∀ v : Algebra M, star v * v = p → p * v = v → v * star v = p

/-- The ordinary nonzero type III factor conditions, with type III
expressed as absence of nonzero finite projections. -/
structure TypeIIIFactor (M : VonNeumannAlgebra H) : Prop where
  nonzero : (1 : H →L[ℂ] H) ≠ 0
  factor : ScalarCenter M
  purelyInfinite : ∀ p : Algebra M, IsStarProjection p → FiniteProjectionIn M p → p = 0

def PublishedTypeIIIProjectionComparison : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H],
    ∀ (M : VonNeumannAlgebra H), TypeIIIFactor M →
      ∀ p : Algebra M, IsStarProjection p → p ≠ 0 →
        ∃ v : Algebra M, star v * v = 1 ∧ v * star v = p

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedProperInfiniteProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable copies of a full projection

Blackadar, *Operator Algebras*, III.1.3.6 (author PDF, printed p.243),
asserts that a full projection in a properly infinite, locally countably
 decomposable von Neumann algebra admits a countable orthogonal family of
 equivalent projections with strong sum one. Separably acting algebras are
 countably decomposable. The input below is only this projection assertion.

The projection's central support is the already constructed orbit-closure
projection. Proper infiniteness is expressed by two isometries with
orthogonal ranges. No trace, corner type, or perturbation conclusion is part
of this published input.

Primary source: https://bruceblackadar.com/Mathematics/Cycr.pdf
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- The ordinary two-isometry description of a nonzero properly infinite
identity. The cross product states that the two range projections are orthogonal. -/
structure ProperlyInfiniteIdentity (M : VonNeumannAlgebra H) : Prop where
  nonzero : (1 : H →L[ℂ] H) ≠ 0
  isometries : ∃ v w : Algebra M,
    star v * v = 1 ∧ star w * w = 1 ∧ star v * w = 0

/-- Actual equivalent projection copies and their strong sum. -/
structure CountableProjectionCopies (M : VonNeumannAlgebra H) (p : AlgebraProjection M) where
  projection : ℕ → AlgebraProjection M
  witness : ℕ → Algebra M
  initial : ∀ i, star (witness i) * witness i = p.val
  final : ∀ i, witness i * star (witness i) = (projection i).val
  orthogonal : Pairwise (fun i j => (projection i).val * (projection j).val = 0)
  total : ∀ x : H, HasSum (fun i => ((projection i).val : H →L[ℂ] H) x) x

/-- Blackadar III.1.3.6 restricted to separably acting algebras. -/
def PublishedProperInfiniteProjectionCopies : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H], ∀ M : VonNeumannAlgebra H,
    ProperlyInfiniteIdentity M → ∀ p : AlgebraProjection M,
      (centralSupport p).val = 1 → Nonempty (CountableProjectionCopies M p)

namespace CountableProjectionCopies

variable {p : AlgebraProjection M} (D : CountableProjectionCopies M p)

def rebasedPartial (i : ℕ) : Algebra M := D.witness i * star (D.witness 0)

theorem rebased_initial (i : ℕ) :
    star (D.rebasedPartial i) * D.rebasedPartial i = (D.projection 0).val := by
  let V : PartialIsometry M := ⟨p, D.witness 0, D.initial 0⟩
  change star (D.witness i * star (D.witness 0)) *
    (D.witness i * star (D.witness 0)) = (D.projection 0).val
  rw [star_mul, star_star]
  calc
    _ = (D.witness 0 * (star (D.witness i) * D.witness i)) * star (D.witness 0) := by
      noncomm_ring
    _ = (D.projection 0).val := by rw [D.initial, V.mul_support, D.final]

theorem rebased_final (i : ℕ) :
    D.rebasedPartial i * star (D.rebasedPartial i) = (D.projection i).val := by
  let V : PartialIsometry M := ⟨p, D.witness i, D.initial i⟩
  change (D.witness i * star (D.witness 0)) *
    star (D.witness i * star (D.witness 0)) = (D.projection i).val
  rw [star_mul, star_star]
  calc
    _ = (D.witness i * (star (D.witness 0) * D.witness 0)) * star (D.witness i) := by
      noncomm_ring
    _ = (D.projection i).val := by rw [D.initial, V.mul_support, D.final]

/-- The actual countable matrix units after rebasing to the first final projection. -/
def fullMatrixCorner : FullMatrixCorner (typeIIIInitialSpace (D.projection 0)) :=
  FullMatrixCorner.ofEquivalentProjectionFamily (typeIIIInitialSpace (D.projection 0))
    D.projection D.rebasedPartial D.rebased_initial D.rebased_final D.orthogonal
    (typeIIIInitialSpace_projection (D.projection 0)) D.total

end CountableProjectionCopies

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedInfiniteType
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Infinite identities in factors

Blackadar, *Operator Algebras*, III.1.3.4--5 (pp.242--243), proves that
an infinite projection has a nonzero properly infinite central part.
In a factor the central part is the identity. Only the resulting pair
of orthogonal isometries is retained here.
-/

namespace KadisonKastler

universe u

def PublishedInfiniteFactorProperlyInfinite : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H), ScalarCenter M →
      ¬ FiniteProjectionIn M 1 → ProperlyInfiniteIdentity M

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SemifiniteFactor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite matrix corners in semifinite diffuse factors

The type-II-infinity predicate uses scalar center, two orthogonal isometries,
projection semifiniteness, and diffuseness. Choosing one finite nonzero
projection and applying the countable-copy theorem constructs the
matrix corner and its II₁ factor structure. There is no trace or stability
conclusion in the type predicate. Projection semifiniteness is exactly the
criterion in Blackadar III.1.4.2; III.1.4.6 identifies the properly infinite
continuous semifinite part as type II∞.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- The projection-theoretic description of a type II∞ factor. -/
structure TypeIIInfinityFactor (M : VonNeumannAlgebra H) : Prop where
  factor : ScalarCenter M
  properlyInfinite : ProperlyInfiniteIdentity M
  semifinite : ∀ p : AlgebraProjection M, p.val ≠ 0 →
    ∃ q : AlgebraProjection M, q ≤ p ∧ q.val ≠ 0 ∧ FiniteProjectionIn M q.val
  diffuse : ∀ p : Algebra M, IsStarProjection p → p ≠ 0 →
    ∃ q : Algebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q

/-- The geometric corner data, including the proved II₁ structure of the
initial represented corner. -/
structure FiniteFullMatrixCornerData (M : VonNeumannAlgebra H) where
  projection : AlgebraProjection M
  projection_nonzero : projection.val ≠ 0
  projection_finite : FiniteProjectionIn M projection.val
  matrix : FullMatrixCorner (typeIIIInitialSpace projection)
  matrix_mem : ∀ i j, matrix.entry i j ∈ M
  corner_isII1 : Generator.IsII1Factor
    (representedCorner (typeIIIInitialSpace projection) M
      (matrix.zero_zero ▸ matrix_mem 0 0)).toStarSubalgebra

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SequenceTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.realTrace_apply _root_.OAI.KadisonKastler.traceCenter_apply _root_.OAI.KadisonKastler.traceStateRepresentation_vector _root_.OAI.KadisonKastler.traceStateRight_vector _root_.OAI.KadisonKastler.traceStateVector_sub _root_.OAI.KadisonKastler.traceTwoNorm_eq_zero_iff _root_.OAI.KadisonKastler.traceTwoNorm_neg _root_.OAI.KadisonKastler.traceTwoNorm_zero _root_.OAI.KadisonKastler.trace_traceCenter _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceContinuous_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.tracialSequenceValue_one _root_.OAI.KadisonKastler.varyingSequenceMap_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Transport of bounded sequences and their trace quotients -/

namespace KadisonKastler

noncomputable section

variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

/-- Apply a contractive star homomorphism at every coordinate. -/
def boundedSequenceMapHom (φ : A →⋆ₐ[ℂ] B) : BoundedSequence A →⋆ₐ[ℂ] BoundedSequence B where
  toFun x := BoundedContinuousFunction.mkOfDiscrete (fun j => φ (x j)) (2 * ‖x‖) (by
    intro i j
    calc
      dist (φ (x i)) (φ (x j)) ≤ ‖φ (x i)‖ + ‖φ (x j)‖ := dist_le_norm_add_norm _ _
      _ ≤ ‖x i‖ + ‖x j‖ := add_le_add (NonUnitalStarAlgHom.norm_apply_le φ _)
        (NonUnitalStarAlgHom.norm_apply_le φ _)
      _ ≤ 2 * ‖x‖ := by linarith [x.norm_coe_le_norm i, x.norm_coe_le_norm j])
  map_one' := by ext j; exact map_one φ
  map_mul' x y := by ext j; exact map_mul φ (x j) (y j)
  map_zero' := by ext j; exact map_zero φ
  map_add' x y := by ext j; exact map_add φ (x j) (y j)
  commutes' z := by ext j; exact φ.commutes z
  map_star' x := by ext j; exact map_star φ (x j)

@[simp]
theorem boundedSequenceMapHom_apply (φ : A →⋆ₐ[ℂ] B) (x : BoundedSequence A) (j : ℕ) :
    boundedSequenceMapHom φ x j = φ (x j) := rfl

def boundedSequenceMapEquiv (e : A ≃⋆ₐ[ℂ] B) :
    BoundedSequence A ≃⋆ₐ[ℂ] BoundedSequence B :=
  StarAlgEquiv.ofBijective (boundedSequenceMapHom e.toStarAlgHom) (by
    constructor
    · intro x y h
      apply BoundedContinuousFunction.ext
      intro j
      exact e.injective (congrArg (fun z : BoundedSequence B => z j) h)
    · intro y
      refine ⟨boundedSequenceMapHom e.symm.toStarAlgHom y, ?_⟩
      apply BoundedContinuousFunction.ext
      intro j
      exact e.apply_symm_apply (y j))

namespace TraceQuotientMap

variable {τA : FaithfulTracialState A} {τB : FaithfulTracialState B}
variable {σ : FaithfulTracialState C} {ω : Ultrafilter ℕ}

/-- A change of the concrete model for the source changes neither the
represented quotient nor its trace. -/
def comapEquiv (Q : TraceQuotientMap τB σ ω) (e : A ≃⋆ₐ[ℂ] B)
    (hτ : ∀ a, τB.toLinearMap (e a) = τA.toLinearMap a) :
    TraceQuotientMap τA σ ω where
  quotient := Q.quotient.comp (boundedSequenceMapHom e.toStarAlgHom)
  surjective := Q.surjective.comp (boundedSequenceMapEquiv e).surjective
  trace_limit x := by
    have h := Q.trace_limit (boundedSequenceMapHom e.toStarAlgHom x)
    simpa only [boundedSequenceMapHom_apply, StarAlgEquiv.toStarAlgHom_apply, hτ,
      StarAlgHom.comp_apply] using h

@[simp]
theorem comapEquiv_quotient (Q : TraceQuotientMap τB σ ω) (e : A ≃⋆ₐ[ℂ] B)
    (hτ : ∀ a, τB.toLinearMap (e a) = τA.toLinearMap a) (x : BoundedSequence A) :
    (Q.comapEquiv e hτ).quotient x = Q.quotient (boundedSequenceMapHom e.toStarAlgHom x) := rfl

end TraceQuotientMap

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakRowFactorization
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! A single operator representation factors the entire weak row-orbit closure.
Only its bounded right-hand operator varies at cluster points. -/

namespace KadisonKastler

noncomputable section

open scoped Topology InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def HasFixedRowFactorization {M : VonNeumannAlgebra H} {c : ℝ}
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K) (d : ℝ)
    (F : BoundedWeakAlgebraMap M c) : Prop :=
  ∃ R : H →L[ℂ] K, ‖R‖ ≤ d ∧ ∀ a,
    (F.map a : H →L[ℂ] H) = L.adjoint.comp ((π a).comp R)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SimultaneousRowFamily
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! A compact product keeps the same normalized rows for an entire family
of completely bounded maps. Minimality descends to each coordinate. -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {J : Type*} {c : J → ℝ}

def familyRowAverage (hc : ∀ j, 0 ≤ c j) {n : ℕ} (r : Fin n → Algebra M)
    (hr : ∑ i, r i * star (r i) = 1) (F : WeakMapFamily M c) : WeakMapFamily M c :=
  fun j => boundedWeakRowAverage (hc j) r hr (F j)

def FamilyRowInvariant (hc : ∀ j, 0 ≤ c j) (C : Set (WeakMapFamily M c)) : Prop :=
  ∀ (n : ℕ) (r : Fin n → Algebra M) (hr : ∑ i, r i * star (r i) = 1),
    Set.MapsTo (familyRowAverage hc r hr) C C

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SimultaneousRowUltralimit
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! A single ultrafilter of normalized rows realizes the simultaneous
modular cluster. Every completely bounded map can be included as a coordinate. -/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {J : Type*} {c : J → ℝ}

local instance universalRowOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance universalRowStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

structure BoundedMapDatum (M : VonNeumannAlgebra H) where
  bound : ℝ
  nonneg : 0 ≤ bound
  map : Algebra M →ₗ[ℂ] Algebra M
  bounded : CompletelyBoundedBy map bound

abbrev UniversalMapFamily (M : VonNeumannAlgebra H) :=
  WeakMapFamily M (fun j : BoundedMapDatum M => j.bound)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIIUltraproduct
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Simplicity and commutator correction for type III norm ultraproducts

Spectral cuts, projection comparison, and Sakai innerness give simplicity
of the norm ultraproduct and a uniform coordinate correction for its
invariant derivations.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem TypeIIIFactor.algebraNontrivial {M : VonNeumannAlgebra H}
    (hM : TypeIIIFactor M) : Nontrivial (Algebra M) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  exact hM.nonzero (congrArg Subtype.val h)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UniformInfinitesimalCutoff
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A uniform infinitesimal cutoff for represented type III factors

The tolerance is chosen before the Hilbert space and factor. The estimate
uses a countable full matrix corner.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

structure MatrixTypeIIIFactorModel where
  H : Type u
  [normedH : NormedAddCommGroup H]
  [innerH : InnerProductSpace ℂ H]
  [completeH : CompleteSpace H]
  [separableH : TopologicalSpace.SeparableSpace H]
  M : VonNeumannAlgebra H
  isTypeIII : TypeIIIFactor M
  E : Submodule ℂ H
  [completeE : CompleteSpace E]
  matrixCorner : FullMatrixCorner E
  matrix_mem : ∀ i j, matrixCorner.entry i j ∈ M

attribute [instance] MatrixTypeIIIFactorModel.normedH MatrixTypeIIIFactorModel.innerH
  MatrixTypeIIIFactorModel.completeH MatrixTypeIIIFactorModel.separableH
  MatrixTypeIIIFactorModel.completeE

end

end KadisonKastler

end OAI
end


