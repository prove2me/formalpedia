-- Prove2me | Definitions.Def_OAIQ244Duke022
-- name    : OAIQ244Duke022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:23:02.376989+00:00
-- url     : https://prove2.me/theorems/18110fa1-a072-4a38-beac-9e5b6cfac4b6
-- title:
--   Definitions bundle OAIQ244Duke022 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 205 declarations of OpenAI's Lean: 100 definitions, 4 inductive types or structures, 10 instances and 91 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.addEquivTransQuotientOfEquivMapEq`, `GlobalClassFieldTheory.Reciprocity.additiveQuotientEquiv`, `GlobalClassFieldTheory.Reciprocity.quotientAddEquivOfEquivMapEqToQuotient`, `OAI.DukePrimeDegree.BufferedRootBox`, `OAI.DukePrimeDegree.CanonicalRegularEntropyTests`, `OAI.DukePrimeDegree.CanonicalRegularEntropyUpperBounds`, `OAI.DukePrimeDegree.EliminationChain.ambientFutureMeasure`, `OAI.DukePrimeDegree.EliminationChain.basedRemainingMeasure`, `OAI.DukePrimeDegree.EliminationChain.centeredRemainingMeasure`, `OAI.DukePrimeDegree.EliminationChain.fullRootTime`, `OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel`, `OAI.DukePrimeDegree.EliminationChain.futureNormalizedKernel`, `OAI.DukePrimeDegree.EliminationChain.futureRestrictedKernel`, `OAI.DukePrimeDegree.EliminationChain.identityFinal`, `OAI.DukePrimeDegree.EliminationChain.param`, `OAI.DukePrimeDegree.EliminationChain.remainingEuclideanCoordinates`, `OAI.DukePrimeDegree.EliminationChain.remainingFutureAtom`, `OAI.DukePrimeDegree.EliminationChain.remainingGroupCenter`, `OAI.DukePrimeDegree.EliminationChain.remainingGroupCoordinates`, `OAI.DukePrimeDegree.EliminationChain.remainingGroupLeafMeasure`, `OAI.DukePrimeDegree.EliminationChain.remainingIndexEquiv`, `OAI.DukePrimeDegree.EliminationChain.remainingIntrinsicProduct`, `OAI.DukePrimeDegree.EliminationChain.remainingRebase`, `OAI.DukePrimeDegree.EliminationChain.remainingTimeProduct`, `OAI.DukePrimeDegree.EliminationChain.remainingWindow`, `OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph`, `OAI.DukePrimeDegree.EliminationChain.remainingWordMap`, `OAI.DukePrimeDegree.EliminationChain.rootDilation`, `OAI.DukePrimeDegree.EliminationChain.timeVectorHomeomorph`, `OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel`, `OAI.DukePrimeDegree.HasCyclicRayRealizations`, `OAI.DukePrimeDegree.InitialRootStep`, `OAI.DukePrimeDegree.InitialRootStep.NextRoot`, `OAI.DukePrimeDegree.InitialRootStep.includeRootRectangle`, `OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel`, `OAI.DukePrimeDegree.InitialRootStep.nextConjugation`, `OAI.DukePrimeDegree.InitialRootStep.nextConjugationHomeomorph`, `OAI.DukePrimeDegree.InitialRootStep.nextFactorRebase`, `OAI.DukePrimeDegree.InitialRootStep.nextGroupCast`, `OAI.DukePrimeDegree.InitialRootStep.nextGroupCoordinates` and 64 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `DukePrimeDegree_Arithmetic_StarkDescent`, `DukePrimeDegree_Dynamics_CentralizerFlow`, `DukePrimeDegree_Dynamics_ConjugationOrbit`, `DukePrimeDegree_Dynamics_RootShearing`, `DukePrimeDegree_Entropy_FutureKernelCovariance`, `DukePrimeDegree_Entropy_PrefixPointConditionals`, `DukePrimeDegree_Entropy_PrefixRootConditionals`, `DukePrimeDegree_Entropy_RegularRootEntropySandwich`, `DukePrimeDegree_Entropy_RemainingFutureShift`, `DukePrimeDegree_Entropy_RootPrefixFutureFibers`, `DukePrimeDegree_Entropy_WholeFutureProbabilityKernel`, `DukePrimeDegree_Geometry_AdjacentFirstRoot`, `DukePrimeDegree_Geometry_CanonicalRootBasic`, `DukePrimeDegree_Geometry_ConjugationRestrictions`, `DukePrimeDegree_Geometry_EliminationChain`, `DukePrimeDegree_Geometry_EliminationFirstRootSlice`, `DukePrimeDegree_Geometry_EliminationMatrixCoordinates`, `DukePrimeDegree_Geometry_EliminationRootChart`, `DukePrimeDegree_Geometry_EliminationRootOrder`, `DukePrimeDegree_Geometry_EliminationWordEntries`, `DukePrimeDegree_Geometry_ExtremalRemainingEntries`, `DukePrimeDegree_Geometry_ExtremalRootQuotient`, `DukePrimeDegree_Geometry_FiniteProjectionFrames`, `DukePrimeDegree_Geometry_LexicographicRootWeights`, `DukePrimeDegree_Geometry_LocalInjectivityHeight`, `DukePrimeDegree_Geometry_NeutralAction`, `DukePrimeDegree_Geometry_NeutralCoordinateMeasure`, `DukePrimeDegree_Geometry_NeutralDiagonal`, `DukePrimeDegree_Geometry_NeutralTransverseCoordinates`, `DukePrimeDegree_Geometry_NeutralUpperRootChart`, `DukePrimeDegree_Geometry_NextGroupConjugation`, `DukePrimeDegree_Geometry_NextGroupCoordinates`, `DukePrimeDegree_Geometry_NextProductChain`, `DukePrimeDegree_Geometry_OrderedRootElimination`, `DukePrimeDegree_Geometry_PhysicalRootRectangles`, `DukePrimeDegree_Geometry_PositiveRootCoordinates`, `DukePrimeDegree_Geometry_PositiveRootFactorization`, `DukePrimeDegree_Geometry_PositiveRootHolonomy`, `DukePrimeDegree_Geometry_RegularRootSymmetry`, `DukePrimeDegree_Geometry_RemainingEuclideanCoordinates`, `DukePrimeDegree_Geometry_RemainingFactorRebase`, `DukePrimeDegree_Geometry_RemainingGroupCenter`, `DukePrimeDegree_Geometry_RemainingIntrinsicProduct`, `DukePrimeDegree_Geometry_RemainingProductCoordinates`, `DukePrimeDegree_Geometry_RemainingProductKernel`, `DukePrimeDegree_Geometry_RemainingProductReorder`, `DukePrimeDegree_Geometry_RemainingProductSupport`, `DukePrimeDegree_Geometry_RemainingRebase`, `DukePrimeDegree_Geometry_RemainingRootCoordinates`, `DukePrimeDegree_Geometry_RemainingRootHolonomy`, `DukePrimeDegree_Geometry_RemainingRootProductBoxes`, `DukePrimeDegree_Geometry_RootBoxMargins`, `DukePrimeDegree_Geometry_RootFiberReference`, `DukePrimeDegree_Geometry_RootOrderCoordinates`, `DukePrimeDegree_Geometry_RootPrefixCoordinates`, `DukePrimeDegree_Geometry_RootPrefixFactorChart`, `DukePrimeDegree_Geometry_RootPrefixGroupLeaves`, `DukePrimeDegree_Geometry_RootPrefixReorder`, `DukePrimeDegree_Geometry_RootPrefixWindows`, `DukePrimeDegree_Geometry_RootRectangleInclusion`, `DukePrimeDegree_Geometry_RootRowShear`, `DukePrimeDegree_Geometry_UpperRootChart`, `DukePrimeDegree_Geometry_UpperRootDilation`, `DukePrimeDegree_Geometry_UpperRootEuclideanCoordinates`, `DukePrimeDegree_Geometry_UpperRootGlobalCoordinates`, `DukePrimeDegree_Geometry_UpperRootLongBoxes`, `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RationalComplexification`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitNormQuotient`, `KummerTheory_Concrete_SUnitPreparation_SUnitPowerQuotient`, `LocalField_DiscreteValuationField_PadicPowerIndex`, `PrimePackets_IntrinsicLeaves`, `PrimePackets_KernelScaling`, `PrimePackets_LeafNormalization`, `PrimePackets_LeafSupport`, `PrimePackets_LeafTransitions`, `PrimePackets_PacketMoments`, `PrimePackets_RayContinuation`, `PrimePackets_RayEuler`, `PrimePackets_RootCharts`, `PrimePackets_RootLeaves`, `PrimePackets_RootRelations`, `PrimePackets_ScalingCovariance`, `Ramification_HilbertRamification_DecompositionField`, `Ramification_HilbertRamification_Dedekind_CompositumUnramified`, `Ramification_HilbertRamification_Dedekind_PrimeContractions`, `Valuation_Topology_AdicCompletionInverseLimit`, `Valuation_Topology_AdicCompletionInverseLimitRing`.
--
--   **Imports.** It imports the published bundle `Def_DukePrimeDegree`; the bundles `OAIQ244Duke001`, `OAIQ244Duke005`, `OAIQ244Duke006`, `OAIQ244Duke007`, `OAIQ244Duke008`, `OAIQ244Duke010`, `OAIQ244Duke011` and `OAIQ244Duke012` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke029`, `OAIQ244Duke034`, `OAIQ244Duke035` and `OAIQ244Duke036`; the statements `OAI.DukePrimeDegree.EliminationChain.predecessor_root_information`, `OAI.DukePrimeDegree.EliminationChain.wholeFuture_conditionalInformation_integrable_integral`, `OAI.DukePrimeDegree.RootPrefixCoordinates.predecessor_entropyRate_le_root_information_add_auxiliary`, `OAI.DukePrimeDegree.atomic_positive_root_of_zero_entropy`, `OAI.DukePrimeDegree.diagonal_entropy_zero_of_atomic_positive_roots`, `OAI.DukePrimeDegree.eklPrimeInput_of_regular_entropy_upper_bounds`, `OAI.DukePrimeDegree.exceptionalRealZeroExclusion_of_ray_realizations`, `OAI.DukePrimeDegree.exists_atomic_neutral_future_cover`, `OAI.DukePrimeDegree.exists_cover_stationary_wholeFutureKernel`, `OAI.DukePrimeDegree.exists_distinct_equal_leaf_horospherical_pair`, `OAI.DukePrimeDegree.exists_nullset_neutral_root_holonomy`, `OAI.DukePrimeDegree.exists_nullset_nonparallel_root_constancy`, `OAI.DukePrimeDegree.exists_real_character_of_simple_zeta`, `OAI.DukePrimeDegree.exists_small_future_observation`, `OAI.DukePrimeDegree.extension_multiplicity_pos_of_ray_realizations`, `OAI.DukePrimeDegree.fixedFieldMultiplicity_le_extension`, `OAI.DukePrimeDegree.hasCyclicRayRealizations_unconditional`, `OAI.DukePrimeDegree.negative_diagonal_entropy_le_root_sum_of_small_auxiliary`, `OAI.DukePrimeDegree.positive_root_coefficient_of_positive_diagonal_entropy`, `OAI.DukePrimeDegree.positive_root_sum_le_diagonal_entropy`, `OAI.DukePrimeDegree.root_invariant_of_adjacent_nonatomic_leaves` and `OAI.DukePrimeDegree.root_invariant_of_atomic_companion_leaves`; the proofs of `OAI.DukePrimeDegree.EliminationChain.predecessor_root_information`, `OAI.DukePrimeDegree.diagonal_entropy_zero_of_atomic_positive_roots`, `OAI.DukePrimeDegree.exceptionalRealZeroExclusion_of_ray_realizations`, `OAI.DukePrimeDegree.exists_noncentral_neutral_return_sequence`, `OAI.DukePrimeDegree.exists_separated_exponential_cut_family` and `OAI.DukePrimeDegree.extension_multiplicity_pos_of_ray_realizations`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.GroupWithZero.Action.Prod
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Module.Shrink
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Cyclic
import Mathlib.Algebra.Order.Hom.Units
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.SuccPred.PartialSups
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.ZMod.Units
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.Dynamics.Ergodic.Action.Basic
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PrimeField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Logic.Encodable.Lattice
import Mathlib.Logic.Encodable.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.Piecewise
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.NumberTheory.Cyclotomic.Discriminant
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.ValuativeRel
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.PartialSups
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.RepresentationTheory.Homological.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AlgebraTower
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.ClassGroup.ExtendedHom
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Flat.IsBaseChange
import Mathlib.RingTheory.FormalGroup.Basic
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Valuation.Archimedean
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.WittVector.Compare
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.FrobeniusFractionField
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Homeomorph.TransferInstance
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.WithTopology
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke001
import Definitions.Def_OAIQ244Duke005
import Definitions.Def_OAIQ244Duke006
import Definitions.Def_OAIQ244Duke007
import Definitions.Def_OAIQ244Duke008
import Definitions.Def_OAIQ244Duke010
import Definitions.Def_OAIQ244Duke011
import Definitions.Def_OAIQ244Duke012

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketMoments
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace

open Filter Set Topology

open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
namespace PrimeDegreePackets
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open scoped Matrix
open Matrix

open TopologicalSpace
open scoped Topology

def thickLattices (n : ℕ) (ε : ℝ) : Set (X n) :=
  {x | ∀ g : G n, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) g = x →
    ∀ z : Fin n → ℤ, z ≠ 0 → ε ≤ ‖(fun i => (z i : ℝ)) ᵥ* g.1‖}

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootRelations
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise

open scoped Topology Classical ENNReal

open scoped Matrix Topology Classical
namespace PrimeDegreePackets

def rootPivotTranslate {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (g : RootPivot i k) (t : ℝ) : RootPivot i k :=
  ⟨g.val * Matrix.SpecialLinearGroup.transvection hij t, by
    simpa only [root_mul_entry,ite_eq_right hij,add_zero] using g.prop⟩

lemma rootParameter_translate {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (g : RootPivot i k) (t : ℝ) :
    rootParameter i j k (rootPivotTranslate hij g t).val = rootParameter i j k g.val + t := by
  simp only [rootParameter,rootPivotTranslate,root_mul_entry,ite_true, if_true,ite_eq_right hij,add_zero]
  field_simp [g.prop]

 
def rootSliceRepresentative {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (g : RootPivot i k) : RootSlice i j k :=
  ⟨g.val * Matrix.SpecialLinearGroup.transvection hij (-rootParameter i j k g.val), by
    constructor
    · simpa only [root_mul_entry,ite_eq_right hij,add_zero] using g.prop
    · simp only [root_mul_entry,ite_true, if_true,rootParameter]
      field_simp [g.prop]
      ring⟩

lemma rootSliceRepresentative_translate {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (g : RootPivot i k) (t : ℝ) :
    rootSliceRepresentative hij (rootPivotTranslate hij g t) = rootSliceRepresentative hij g := by
  apply Subtype.ext
  change (g.val * Matrix.SpecialLinearGroup.transvection hij t) *
    Matrix.SpecialLinearGroup.transvection hij (-rootParameter i j k (rootPivotTranslate hij g t).val) = _
  rw [rootParameter_translate,mul_assoc,←Matrix.SpecialLinearGroup.transvection_add]
  congr 2
  ring

lemma continuous_rootSliceRepresentative {n : ℕ} {i j k : Fin n} (hij : i ≠ j) :
    Continuous (rootSliceRepresentative (k := k) hij) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.mul
    ((continuous_rootTransvection hij).comp continuous_rootParameter.neg)

 

def rootPivotHomeomorph {n : ℕ} {i j k : Fin n} (hij : i ≠ j) :
    RootPivot i k ≃ₜ RootSlice i j k × ℝ where
  toFun g := (rootSliceRepresentative hij g, rootParameter i j k g.val)
  invFun z := rootPivotTranslate hij ⟨z.1.val,z.1.prop.1⟩ z.2
  left_inv g := by
    apply Subtype.ext
    change (g.val * Matrix.SpecialLinearGroup.transvection hij (-rootParameter i j k g.val)) *
      Matrix.SpecialLinearGroup.transvection hij (rootParameter i j k g.val) = _
    rw [mul_assoc,←Matrix.SpecialLinearGroup.transvection_add,neg_add_cancel,
      Matrix.SpecialLinearGroup.transvection_coeff_zero,mul_one]
  right_inv z := by
    have hp : rootParameter i j k z.1.val = 0 := by
      simp only [rootParameter,z.1.prop.2,zero_div]
    apply Prod.ext
    · change rootSliceRepresentative hij (rootPivotTranslate hij ⟨z.1.val,z.1.prop.1⟩ z.2) = z.1
      rw [rootSliceRepresentative_translate]
      apply Subtype.ext
      change z.1.val * Matrix.SpecialLinearGroup.transvection hij (-rootParameter i j k z.1.val) = _
      rw [hp,neg_zero,Matrix.SpecialLinearGroup.transvection_coeff_zero,mul_one]
    · simpa only [hp,zero_add] using rootParameter_translate hij ⟨z.1.val,z.1.prop.1⟩ z.2
  continuous_toFun := (continuous_rootSliceRepresentative hij).prodMk continuous_rootParameter
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul
      ((continuous_rootTransvection hij).comp continuous_snd)

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootCharts
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
namespace PrimeDegreePackets


def rootQuotientParametrization {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (z : RootSlice i j k × ℝ) : X n :=
  Quotient.mk _ ((rootPivotHomeomorph hij).symm z).val

lemma rootQuotientParametrization_localHomeomorph {n : ℕ} {i j k : Fin n} (hij : i ≠ j) :
    IsLocalHomeomorph (rootQuotientParametrization (k := k) hij) := by
  have H := ((quotient_covering n).isLocalHomeomorph.comp
    (rootPivot_isOpen i k).isOpenEmbedding_subtypeVal.isLocalHomeomorph).comp
    (rootPivotHomeomorph (k := k) hij).symm.isLocalHomeomorph
  exact H

 

theorem rootQuotientParametrization_localEmbedding {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (z : RootSlice i j k × ℝ) :
    ∃ U ∈ 𝓝 z, Topology.IsOpenEmbedding (U.domRestrict (rootQuotientParametrization hij)) :=
  isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp
    (rootQuotientParametrization_localHomeomorph hij) z

end PrimeDegreePackets


namespace PrimeDegreePackets

structure RootBox {n : ℕ} {i j : Fin n} (hij : i ≠ j) (k : Fin n) where
  transverse : Set (RootSlice i j k)
  time : Set ℝ
  transverse_open : IsOpen transverse
  time_open : IsOpen time
  embedding : Topology.IsOpenEmbedding
    ((transverse ×ˢ time).domRestrict (rootQuotientParametrization hij))

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

abbrev domain (B : RootBox hij k) := B.transverse ×ˢ B.time
abbrev param (B : RootBox hij k) := B.domain.domRestrict (rootQuotientParametrization hij)
def range (B : RootBox hij k) := Set.range B.param

lemma range_open (B : RootBox hij k) : IsOpen B.range := B.embedding.isOpen_range

 

def coordinateMeasure (B : RootBox hij k) (μ : Measure (X n)) :
    Measure (RootSlice i j k × ℝ) :=
  Measure.map Subtype.val (Measure.comap B.param μ)

instance coordinateMeasure_finite (B : RootBox hij k) (μ : Measure (X n))
    [IsFiniteMeasure μ] : IsFiniteMeasure (B.coordinateMeasure μ) := by
  have he := B.embedding.measurableEmbedding
  have : IsFiniteMeasure (Measure.comap B.param μ) := ⟨by
    rw [he.comap_apply]
    exact lt_of_le_of_lt (measure_mono (subset_univ _)) (measure_lt_top μ univ)⟩
  unfold coordinateMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def conditionalKernel (B : RootBox hij k) (μ : Measure (X n)) [IsFiniteMeasure μ] :
    Kernel (RootSlice i j k) ℝ := (B.coordinateMeasure μ).condKernel

end RootBox

theorem exists_rootBox_at_coordinates {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (z : RootSlice i j k × ℝ) : ∃ B : RootBox hij k, z ∈ B.domain := by
  obtain ⟨U,hUz,hU⟩ := rootQuotientParametrization_localEmbedding hij z
  obtain ⟨V,W,hVo,hVz,hWo,hWz,hsub⟩ := mem_nhds_prod_iff'.mp hUz
  have he := hU.comp (Topology.IsOpenEmbedding.inclusion hsub
    ((hVo.prod hWo).preimage continuous_subtype_val))
  exact ⟨⟨V,W,hVo,hWo,he⟩,hVz,hWz⟩

 

theorem exists_rootBox_at {n : ℕ} {i j : Fin n} (hij : i ≠ j) (x : X n) :
    ∃ k : Fin n, ∃ B : RootBox hij k, x ∈ B.range := by
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨k,hk⟩ := exists_rootPivot i g
    let g' : RootPivot i k := ⟨g,hk⟩
    let z := rootPivotHomeomorph hij g'
    obtain ⟨B,hB⟩ := exists_rootBox_at_coordinates hij z
    refine ⟨k,B,⟨⟨z,hB⟩,?_⟩⟩
    change Quotient.mk _ ((rootPivotHomeomorph hij).symm ((rootPivotHomeomorph hij) g')).val = _
    rw [Homeomorph.symm_apply_apply]



end PrimeDegreePackets


open scoped ENNReal ProbabilityTheory
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_KernelScaling
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory


namespace PrimeDegreePackets.RootBox

variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

def shrink (B : RootBox hij k)
    (U : Set (RootSlice i j k)) (V : Set ℝ) (hU : IsOpen U) (hV : IsOpen V)
    (hUB : U ⊆ B.transverse) (hVB : V ⊆ B.time) : RootBox hij k :=
  ⟨U,V,hU,hV,B.embedding.comp (Topology.IsOpenEmbedding.inclusion
    (Set.prod_mono hUB hVB) ((hU.prod hV).preimage continuous_subtype_val))⟩



end PrimeDegreePackets.RootBox


open Set Filter Topology

open Set Filter Topology MeasureTheory
namespace PrimeDegreePackets



theorem rootBox_contains_compact_time {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (s : RootSlice i j k)
    (hinj : Function.Injective (fun t : ℝ => rootQuotientParametrization hij (s,t)))
    (a b : ℝ) :
    ∃ B : RootBox hij k, s ∈ B.transverse ∧ Icc a b ⊆ B.time := by
  have hf := rootQuotientParametrization_localHomeomorph (k := k) hij
  have hi : Set.InjOn (rootQuotientParametrization hij) ({s} ×ˢ Icc a b) := by
    rintro ⟨s₁,t₁⟩ ⟨hs₁,ht₁⟩ ⟨s₂,t₂⟩ ⟨hs₂,ht₂⟩ heq
    have h₁ : s₁ = s := hs₁
    have h₂ : s₂ = s := hs₂
    subst s₁
    subst s₂
    exact Prod.ext rfl (hinj heq)
  obtain ⟨W,hW,hKW,hemb⟩ := compact_injective_localHomeomorph_neighborhood hf
    (isCompact_singleton.prod isCompact_Icc) hi
  obtain ⟨U,V,hU,hV,hsU,hTV,hUV⟩ := generalized_tube_lemma
    (isCompact_singleton : IsCompact ({s} : Set (RootSlice i j k)))
    (isCompact_Icc : IsCompact (Icc a b)) hW hKW
  have he := hemb.comp (Topology.IsOpenEmbedding.inclusion hUV
    ((hU.prod hV).preimage continuous_subtype_val))
  exact ⟨⟨U,V,hU,hV,he⟩,hsU (Set.mem_singleton s),hTV⟩



end PrimeDegreePackets

open MeasureTheory Set Filter Topology

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayEuler
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Module Filter Topology
open scoped BigOperators NumberField nonZeroDivisors Classical
namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
namespace EvenRayCharacter
variable {K : Type*} [Field K] [NumberField K] {N : ℕ}
variable (ψ : EvenRayCharacter K N)


@[simp] lemma allCoefficient_one : ψ.allCoefficient 1 = 1 := by
  have hc : IsCoprime (⊤ : Ideal (𝓞 K)) (rationalModulusIdeal (𝓞 K) N) :=
    by rw [← Ideal.one_eq_top]; exact isCoprime_one_left
  have ht : (⊤ : Ideal (𝓞 K)) ≠ ⊥ := top_ne_bot
  simp only [Ideal.one_eq_top, allCoefficient, dite_eq_left ht, hc,
    ite_true, if_true, integralIdealFractionalUnit_top, map_one, Units.val_one]

end EvenRayCharacter
end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayContinuation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Module Filter Topology
open scoped BigOperators NumberField nonZeroDivisors Classical ComplexConjugate
namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
namespace EvenRayCharacter
variable {K : Type*} [Field K] [NumberField K] {N : ℕ}
variable (ψ : EvenRayCharacter K N)

 

def IsNonprincipal : Prop :=
  ∃ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥),
    IsCoprime I (rationalModulusIdeal (𝓞 K) N) ∧
      ψ.idealHom (integralIdealFractionalUnit I hI) ≠ 1

end EvenRayCharacter
end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_StarkDescent
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.finiteNormalClosure_numberField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Odd-index descent of a simple zero

Cyclic Hecke factorizations supply the real characters used by Stark's
odd-degree argument. The zero order on any fixed field is an average of
signs and is therefore at most one. A positive order at an odd-index
subgroup is incompatible with a nonvanishing rational zeta function.
-/

noncomputable section
open scoped NumberField BigOperators Classical

namespace DukePrimeDegree
open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter

variable {E : Type*} [Field E] [NumberField E] [IsGalois ℚ E]
variable [NumberField.IsTotallyReal E]

/-- Even ray realizations of each cyclic subgroup's Frobenius characters. -/
def HasCyclicRayRealizations (E : Type*) [Field E] [NumberField E] [IsGalois ℚ E] : Prop :=
  ∀ (C : Subgroup (E ≃ₐ[ℚ] E)), IsCyclic C →
    ∃ N : ℕ, 0 < N ∧ (NumberField.discr E).natAbs ∣ N ∧
      ∃ ψ : ((E ≃ₐ[IntermediateField.fixedField C] E) →* ℂˣ) →
        EvenRayCharacter (IntermediateField.fixedField C) N,
        (∀ χ, (ψ χ).idealHom = idealHom (IntermediateField.fixedField C) E χ) ∧
        ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafNormalization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
namespace PrimeDegreePackets



theorem exists_countable_rootBoxes_exact_time {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (a b : ℝ) :
    ∃ C : Set (RootBox hij k), C.Countable ∧
      (∀ B ∈ C, B.time = Ioo a b) ∧
      ∀ s : RootSlice i j k,
        Function.Injective (fun t : ℝ => rootQuotientParametrization hij (s,t)) →
        ∃ B ∈ C, s ∈ B.transverse := by
  let Good := {B : RootBox hij k | B.time = Ioo a b}
  obtain ⟨C,hCG,hCc,hC⟩ := isOpen_biUnion_countable Good
    (fun B : RootBox hij k => B.transverse) (fun B _ => B.transverse_open)
  refine ⟨C,hCc,fun B hB => hCG hB,?_⟩
  intro s hs
  obtain ⟨B,hsB,hT⟩ := rootBox_contains_compact_time hij s hs a b
  let D := B.shrink B.transverse (Ioo a b) B.transverse_open isOpen_Ioo
    subset_rfl (Ioo_subset_Icc_self.trans hT)
  have hD : D ∈ Good := rfl
  have H : s ∈ ⋃ B ∈ Good, B.transverse := mem_iUnion.mpr ⟨D,mem_iUnion.mpr ⟨hD,hsB⟩⟩
  rw [←hC] at H
  simpa only [mem_iUnion,exists_prop] using H

end PrimeDegreePackets


namespace PrimeDegreePackets


variable {n : ℕ} {i j k : Fin n}

 
def rootLongBoxFamily (hij : i ≠ j) (k : Fin n) (R : ℝ) (m : ℕ) : Set (RootBox hij k) :=
  (exists_countable_rootBoxes_exact_time (k := k) hij (-(R+m)) (R+m)).choose

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 
def IsNormalizedRootLeaf (A : RootBox hij k) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : RootSlice i j k) (ν : Measure ℝ) : Prop :=
  IsLocallyFiniteMeasure ν ∧ ν A.time = 1 ∧
    ν.restrict A.time = A.conditionalKernel μ s ∧
    ∀ (m : ℕ) (B : RootBox hij k), B ∈ rootLongBoxFamily hij k R m →
      s ∈ B.transverse → ν.restrict (rootLeafWindow R m) =
        (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (rootLeafWindow R m)

 

def leafMeasure (A : RootBox hij k) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : RootSlice i j k) : Measure ℝ :=
  if h : ∃ ν : Measure ℝ, A.IsNormalizedRootLeaf R μ s ν then h.choose else 0

end PrimeDegreePackets.RootBox


open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory


namespace PrimeDegreePackets


namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 
def basedLeaf (A : RootBox hij k) (R : ℝ) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (z : RootSlice i j k × ℝ) : Measure ℝ := basedRealMeasure (A.leafMeasure R μ z.1) z.2

end RootBox
end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafTransitions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory

open scoped Matrix Topology Classical ENNReal


namespace PrimeDegreePackets
variable {n : ℕ} {i j : Fin n} (hij : i ≠ j)

structure BoundedRootBox where
  pivot : Fin n
  box : RootBox hij pivot
  radius : ℝ
  time_bound : box.time ⊆ rootLeafWindow radius 0

namespace RootBox
variable {hij} {k : Fin n}

 

def coordinates (A : RootBox hij k) (x : A.range) : A.domain :=
  A.embedding.toIsEmbedding.toHomeomorph.symm x

end RootBox

lemma exists_boundedRootBox_at (x : X n) : ∃ B : BoundedRootBox hij, x ∈ B.box.range := by
  obtain ⟨k,A,⟨z,hz⟩⟩ := exists_rootBox_at hij x
  let V := A.time ∩ Ioo (z.val.2-1) (z.val.2+1)
  let B := A.shrink A.transverse V A.transverse_open
    (A.time_open.inter isOpen_Ioo) Subset.rfl inter_subset_left
  have ht : B.time ⊆ rootLeafWindow (|z.val.2|+2) 0 := by
    intro t ht
    simp only [rootLeafWindow,Nat.cast_zero,add_zero,Set.mem_Ioo]
    have h₁ := le_abs_self z.val.2
    have h₂ := neg_abs_le z.val.2
    obtain ⟨_,hlo,hhi⟩ := ht
    constructor <;> linarith
  refine ⟨⟨k,B,|z.val.2|+2,ht⟩,?_⟩
  refine ⟨⟨z.val,⟨z.prop.1,z.prop.2,by dsimp; constructor <;> linarith⟩⟩,hz⟩

lemma exists_countable_boundedRootBox_cover :
    ∃ C : Set (BoundedRootBox hij), C.Countable ∧
      (univ : Set (X n)) ⊆ ⋃ B ∈ C, B.box.range := by
  apply isLindelof_univ.elim_countable_subcover (fun B : BoundedRootBox hij => B.box.range)
  · exact fun B => B.box.range_open
  · intro x _
    obtain ⟨B,hB⟩ := exists_boundedRootBox_at hij x
    exact mem_iUnion.mpr ⟨B,hB⟩

 

def boundedRootAtlas : Set (BoundedRootBox hij) :=
  (exists_countable_boundedRootBox_cover hij).choose

lemma boundedRootAtlas_covers (x : X n) : ∃ B : boundedRootAtlas hij, x ∈ B.val.box.range := by
  have H := (exists_countable_boundedRootBox_cover hij).choose_spec.2 (mem_univ x)
  obtain ⟨B,hx⟩ := mem_iUnion.mp H
  obtain ⟨hB,hx⟩ := mem_iUnion.mp hx
  exact ⟨⟨B,hB⟩,hx⟩

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IntrinsicLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
namespace PrimeDegreePackets
variable {n : ℕ} {i j : Fin n} (hij : i ≠ j)

 

def selectedRootBox (x : X n) : boundedRootAtlas hij := (boundedRootAtlas_covers hij x).choose

lemma selectedRootBox_mem (x : X n) : x ∈ (selectedRootBox hij x).val.box.range :=
  (boundedRootAtlas_covers hij x).choose_spec

 

def intrinsicRootLeaf (μ : Measure (X n)) [IsFiniteMeasure μ] (x : X n) : Measure ℝ :=
  let B := (selectedRootBox hij x).val
  B.box.basedLeaf B.radius μ (B.box.coordinates ⟨x,selectedRootBox_mem hij x⟩).val

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ScalingCovariance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory


namespace PrimeDegreePackets

def rootInformation {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (t : ℝ) (x : X n) : ℝ :=
  -Real.log ((intrinsicRootLeaf hij μ x) (Metric.ball 0 (Real.exp (-t)))).toReal

end PrimeDegreePackets


namespace PrimeDegreePackets

def rootInformationMean {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (rootInformation hij μ t x) ∂μ

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_RootShearing
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Polynomial shearing along a root subgroup

The exact matrix formula is the algebraic part of the low-entropy
argument: conjugation by a root unipotent is quadratic in its parameter.
The exceptional case is precisely the centralizer, and commuting with a
single nonzero root element already characterizes that case.
-/

open scoped BigOperators Classical
open Filter

namespace DukePrimeDegree

open PrimeDegreePackets

/-- A matrix centralizes the entire root group exactly when its pivot
column, pivot row and two diagonal entries satisfy these equations. -/
theorem commutes_root_one_iff {n : ℕ} {i j : Fin n} (hij : i ≠ j) (g : G n) :
    g * Matrix.SpecialLinearGroup.transvection hij 1 =
      Matrix.SpecialLinearGroup.transvection hij 1 * g ↔
      (∀ r, r ≠ i → g.1 r i = 0) ∧
      (∀ s, s ≠ j → g.1 j s = 0) ∧ g.1 i i = g.1 j j := by
  constructor
  · intro h
    have he (r s : Fin n) := congrArg (fun a : G n => a.1 r s) h
    simp only [root_mul_entry, root_left_mul_entry, mul_one, one_mul] at he
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      have h := he r j
      simp only [ite_true, if_true, ite_eq_right hr] at h
      linarith
    · intro s hs
      have h := he i s
      simp only [ite_eq_right hs, ite_true, if_true] at h
      linarith
    · have h := he i j
      simp only [ite_true, if_true] at h
      linarith
  · rintro ⟨hcol, hrow, hdiag⟩
    ext r s
    simp only [root_mul_entry, root_left_mul_entry, mul_one, one_mul]
    by_cases hr : r = i <;> by_cases hs : s = j
    · subst r
      subst s
      simp only [ite_true, if_true, hdiag]
    · subst r
      simp [hs, hrow s hs]
    · subst s
      simp [hr, hcol r hr]
    · simp [hr, hs]

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_CentralizerFlow
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small centralizer factors in late diagonal returns

The root-pair centralizer supplies a scalar double block and a complementary
matrix. A fixed neighborhood controls that complementary matrix; late
neutral diagonal times separate its spectrum and keep the scalar away
from the rational units.
-/

noncomputable section
open Set Filter Matrix
open scoped Classical Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma diagonal_mem_rootPairCentralizer {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0) (hneut : ell i = ell j) (t : ℝ) :
    diagonalOneParameter ell hell t ∈ rootPairCentralizer hij := by
  apply (mem_rootPairCentralizer hij _).mpr
  constructor
  · apply (commutes_root_one_iff hij _).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      simp [diagonalOneParameter, Matrix.diagonal, hr]
    · intro s hs
      simp [diagonalOneParameter, Matrix.diagonal, Ne.symm hs]
    · simp [diagonalOneParameter, hneut]
  · apply (commutes_root_one_iff hij.symm _).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      simp [diagonalOneParameter, Matrix.diagonal, hr]
    · intro s hs
      simp [diagonalOneParameter, Matrix.diagonal, Ne.symm hs]
    · simp [diagonalOneParameter, hneut]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ConjugationOrbit
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conjugation maps on actual lattice orbit quotients

A matrix commuting with the lattice stabilizer defines a continuous
conjugation map on the corresponding homogeneous orbit quotient. Right
invariance of a measure on that quotient gives conjugation invariance of
its pushforward. This is the geometric bridge used by the elementary
matrix-density argument.
-/

noncomputable section
open MeasureTheory Filter Set Matrix
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

/-- The subgroup of the orbit group fixing the lattice represented by `g`. -/
def pointOrbitStabilizer {n : ℕ} (g : G n) (H : Subgroup (G n)) : Subgroup H :=
  (integralGroup n).comap ((MulAut.conj g).toMonoidHom.comp H.subtype)

abbrev LatticeOrbitQuotient {n : ℕ} (g : G n) (H : Subgroup (G n)) :=
  Quotient (QuotientGroup.rightRel (pointOrbitStabilizer g H))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootBoxMargins
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Root boxes with a uniform interval margin

Every point has a smaller open root box for which a fixed positive time
interval stays inside a larger root box. Compactness makes these margins
uniform on any prescribed compact set.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

structure BufferedRootBox {n : ℕ} {i j : Fin n} (hij : i ≠ j) where
  pivot : Fin n
  box : RootBox hij pivot
  radius : ℝ
  time_bound : box.time ⊆ rootLeafWindow radius 0
  core : Set (X n)
  core_open : IsOpen core
  core_subset : core ⊆ box.range
  margin : ℝ
  margin_pos : 0 < margin
  time_margin : ∀ z ∈ box.domain, rootQuotientParametrization hij z ∈ core →
    closedBall z.2 margin ⊆ box.time

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PositiveRootFactorization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact elimination in a positive root group

Positive root patterns are exactly the groups generated by their root
lines. Removing a shortest root gives a triangular factorization with
that root as the first factor. In particular these generated groups are
already closed; no additional matrices appear on taking their closure.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma positiveRootPattern_eliminate {n : ℕ} (S : Finset (Fin n × Fin n))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ a b c : Fin n, (a, b) ∈ S → (b, c) ∈ S → (a, c) ∈ S)
    {a b : Fin n} (hab : a ≠ b) (habS : (a, b) ∈ S)
    (g : G n) (hg : PositiveRootPattern S g) :
    PositiveRootPattern (S.erase (a, b))
      (Matrix.SpecialLinearGroup.transvection hab (-g.val a b) * g) := by
  have hw := positiveRootPattern_mul S hcomp
    (positiveRootPattern_transvection S hab habS (-g.val a b)) hg
  have hbb : g.val b b = 1 := by
    have hb : (b, b) ∉ S := fun h => lt_irrefl b (hpos (b, b) h)
    simpa using hg b b hb
  intro r s hrs
  by_cases he : (r, s) = (a, b)
  · have hr : r = a := congrArg Prod.fst he
    have hs : s = b := congrArg Prod.snd he
    subst r
    subst s
    change ((1 + Matrix.single a b (-g.val a b)) * g.val) a b = _
    simp [Matrix.add_mul, hbb, hab]
  · exact hw r s (fun hS => hrs (Finset.mem_erase.mpr ⟨he, hS⟩))

/-- Every matrix with the prescribed positive pattern is a product of
the corresponding root transvections. -/
theorem positiveRootPattern_mem_generated {n : ℕ} (S : Finset (Fin n × Fin n))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ a b c : Fin n, (a, b) ∈ S → (b, c) ∈ S → (a, c) ∈ S)
    {g : G n} (hg : PositiveRootPattern S g) : g ∈ positiveRootGeneratedGroup S := by
  induction S using Finset.strongInductionOn generalizing g with
  | _ S ih =>
    by_cases hS : S.Nonempty
    · obtain ⟨p, hpS, hmin⟩ := S.exists_min_image (fun q => q.2.val - q.1.val) hS
      have hp : p.1 ≠ p.2 := ne_of_lt (hpos p hpS)
      have he := positiveRootPattern_eliminate S hpos hcomp hp hpS g hg
      have hw := ih (S.erase p) (Finset.erase_ssubset hpS)
        (fun q hq => hpos q (Finset.mem_of_mem_erase hq))
        (erase_shortest_root_closed n S hpos hcomp p hmin) he
      have hwS := positiveRootGeneratedGroup_mono (Finset.erase_subset p S) hw
      have hu := transvection_mem_positiveRootGeneratedGroup S hp hpS (g.val p.1 p.2)
      have hm := (positiveRootGeneratedGroup S).mul_mem hu hwS
      simpa only [← mul_assoc, Matrix.SpecialLinearGroup.transvection_mul_neg, one_mul] using hm
    · have hg1 : g = 1 := by
        apply Subtype.ext
        ext r s
        exact hg r s (fun h => hS ⟨(r, s), h⟩)
      rw [hg1]
      exact (positiveRootGeneratedGroup S).one_mem

theorem positiveRootGeneratedGroup_iff {n : ℕ} (S : Finset (Fin n × Fin n))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ a b c : Fin n, (a, b) ∈ S → (b, c) ∈ S → (a, c) ∈ S)
    (g : G n) : g ∈ positiveRootGeneratedGroup S ↔ PositiveRootPattern S g :=
  ⟨positiveRootGeneratedGroup_pattern S hcomp, positiveRootPattern_mem_generated S hpos hcomp⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PositiveRootCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coordinates separating an extremal root

Multiplication identifies a positive-root group with one real root
coordinate and the group of remaining roots. Both directions are
continuous, and the first coordinate is the corresponding matrix entry.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma positiveRootPattern_eliminate_right {n : ℕ} (S : Finset (Fin n × Fin n))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ i j k : Fin n, (i, j) ∈ S → (j, k) ∈ S → (i, k) ∈ S)
    {a b : Fin n} (hab : a ≠ b) (habS : (a, b) ∈ S)
    (g : G n) (hg : PositiveRootPattern S g) :
    PositiveRootPattern (S.erase (a, b))
      (g * Matrix.SpecialLinearGroup.transvection hab (-g.val a b)) := by
  have hw := positiveRootPattern_mul S hcomp hg
    (positiveRootPattern_transvection S hab habS (-g.val a b))
  have haa : g.val a a = 1 := by
    have ha : (a, a) ∉ S := fun h => lt_irrefl a (hpos (a, a) h)
    simpa using hg a a ha
  intro r s hrs
  by_cases he : (r, s) = (a, b)
  · have hr : r = a := congrArg Prod.fst he
    have hs : s = b := congrArg Prod.snd he
    subst r
    subst s
    simp only [root_entry_mul_transvection, haa, one_mul, add_neg_cancel,
      Matrix.one_apply, hab, ite_false, if_false]
  · exact hw r s (fun hS => hrs (Finset.mem_erase.mpr ⟨he, hS⟩))

/-- With the root factor last, its coordinate lines are actual right
root orbits. These are the coordinates used for disintegration. -/
def positiveRootRightFactorHomeomorph {n : ℕ} (S : Finset (Fin n × Fin n))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ i j k : Fin n, (i, j) ∈ S → (j, k) ∈ S → (i, k) ∈ S)
    {a b : Fin n} (hab : a ≠ b) (habS : (a, b) ∈ S)
    (herase : ∀ i j k : Fin n, (i, j) ∈ S.erase (a, b) →
      (j, k) ∈ S.erase (a, b) → (i, k) ∈ S.erase (a, b)) :
    (positiveRootGeneratedGroup (S.erase (a, b)) × ℝ) ≃ₜ positiveRootGeneratedGroup S where
  toFun z := ⟨z.1.val * Matrix.SpecialLinearGroup.transvection hab z.2,
    (positiveRootGeneratedGroup S).mul_mem
      (positiveRootGeneratedGroup_mono (Finset.erase_subset (a, b) S) z.1.prop)
      (transvection_mem_positiveRootGeneratedGroup S hab habS z.2)⟩
  invFun g := (⟨g.val * Matrix.SpecialLinearGroup.transvection hab (-g.val.val a b),
      positiveRootPattern_mem_generated (S.erase (a, b))
        (fun p hp => hpos p (Finset.mem_of_mem_erase hp)) herase
        (positiveRootPattern_eliminate_right S hpos hcomp hab habS g.val
          (positiveRootGeneratedGroup_pattern S hcomp g.prop))⟩, g.val.val a b)
  left_inv := by
    rintro ⟨w, t⟩
    have hp := positiveRootGeneratedGroup_pattern (S.erase (a, b)) herase w.prop
    have ha : w.val.val a a = 1 := by
      apply (show w.val.val a a = (1 : Matrix (Fin n) (Fin n) ℝ) a a from
        hp a a (fun h => lt_irrefl a (hpos (a, a) (Finset.mem_of_mem_erase h)))).trans
      simp
    have hw := (remaining_root_entry S hpos hab herase w).1
    have ht : (w.val * Matrix.SpecialLinearGroup.transvection hab t).val a b = t := by
      rw [root_entry_mul_transvection, ha, hw, one_mul, zero_add]
    apply Prod.ext
    · apply Subtype.ext
      change (w.val * Matrix.SpecialLinearGroup.transvection hab t) *
        Matrix.SpecialLinearGroup.transvection hab
          (-(w.val * Matrix.SpecialLinearGroup.transvection hab t).val a b) = w.val
      rw [ht, mul_assoc, Matrix.SpecialLinearGroup.transvection_mul_neg, mul_one]
    · exact ht
  right_inv := by
    intro g
    apply Subtype.ext
    change (g.val * Matrix.SpecialLinearGroup.transvection hab (-g.val.val a b)) *
      Matrix.SpecialLinearGroup.transvection hab (g.val.val a b) = g.val
    rw [mul_assoc, ← Matrix.SpecialLinearGroup.transvection_add, neg_add_cancel]
    simp only [Matrix.SpecialLinearGroup.transvection_coeff_zero, mul_one]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul
      ((continuous_rootTransvection hab).comp continuous_snd)
  continuous_invFun := by
    have hc : Continuous (fun g : positiveRootGeneratedGroup S => g.val.val a b) := by
      fun_prop
    exact (Continuous.subtype_mk
      (continuous_subtype_val.mul ((continuous_rootTransvection hab).comp hc.neg)) _).prodMk hc

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralDiagonal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The neutral diagonal group

The kernel of one root character, inside trace-zero real weights, is the
group used for the ergodic decomposition in EKL's low-entropy argument.
Its diagonal representation takes values in the opposite-root centralizer.
-/

noncomputable section
open Set Matrix
open scoped Topology Classical BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def neutralDiagonalHom {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Multiplicative (neutralWeightSubgroup i j) →* rootPairCentralizer hij where
  toFun u := ⟨diagonalOneParameter u.toAdd.val u.toAdd.property.1 1,
    diagonal_mem_rootPairCentralizer hij _ _ u.toAdd.property.2 1⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    simp [diagonalOneParameter]
  map_mul' u v := by
    apply Subtype.ext
    exact diagonalOneParameter_add_weights _ _ u.toAdd.property.1 v.toAdd.property.1 1

/-- The opposite representation matches the right action on lattices. -/
def neutralDiagonalOppositeHom {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Multiplicative (neutralWeightSubgroup i j) →* MulOpposite (rootPairCentralizer hij) where
  toFun u := MulOpposite.op (neutralDiagonalHom hij u)
  map_one' := by simp
  map_mul' u v := by
    apply MulOpposite.unop_injective
    change neutralDiagonalHom hij (u * v) = neutralDiagonalHom hij v * neutralDiagonalHom hij u
    rw [← map_mul, mul_comm]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PositiveRootHolonomy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Holonomy across a positive-root pattern

A flow neutral on one root and contracting every other allowed matrix
entry sends every element of the pattern to its selected root entry.
The proved neutral holonomy theorem then identifies the actual leaves.
-/

noncomputable section
open Matrix MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem rootPattern_isolated_limit
    (d : ℕ) (S : Finset (Fin (d + 1) × Fin (d + 1)))
    (hdiag : ∀ r, (r, r) ∉ S) {a b : Fin (d + 1)} (hab : a ≠ b)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ r, ell r = 0) (hneut : ell a = ell b)
    (hdecay : ∀ p ∈ S, p ≠ (a, b) → ell p.1 < ell p.2)
    (g : G (d + 1)) (hg : PositiveRootPattern S g) :
    Tendsto (fun t : ℝ => diagonalOneParameter ell hell t * g *
      diagonalOneParameter ell hell (-t)) atTop
      (𝓝 (Matrix.SpecialLinearGroup.transvection hab (g.val a b))) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro r
  apply tendsto_pi_nhds.mpr
  intro s
  have he (t : ℝ) := conjugation_entry ell hell g t r s
  simp_rw [he]
  by_cases hrs : r = s
  · subst s
    have hd := hg r r (hdiag r)
    simp only [sub_self, zero_mul, Real.exp_zero, one_mul, hd]
    convert (tendsto_const_nhds : Tendsto (fun _ : ℝ =>
      (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) r r) atTop (𝓝 _)) using 1
    all_goals try with_reducible_and_instances rfl
    by_cases hra : r = a
    · subst r
      simp [Matrix.SpecialLinearGroup.transvection_coe, hab.symm]
    · simp [Matrix.SpecialLinearGroup.transvection_coe, Ne.symm hra]
  by_cases hrab : r = a ∧ s = b
  · obtain ⟨hra, hsb⟩ := hrab
    subst r
    subst s
    simp only [hneut, sub_self, zero_mul, Real.exp_zero, one_mul]
    convert (tendsto_const_nhds : Tendsto (fun _ : ℝ => g.val a b) atTop (𝓝 _)) using 1
    all_goals try with_reducible_and_instances rfl
    simp [Matrix.SpecialLinearGroup.transvection_coe, hab]
  have htarget : (Matrix.SpecialLinearGroup.transvection hab (g.val a b)).val r s = 0 := by
    simp_all [Matrix.SpecialLinearGroup.transvection_coe, eq_comm]
  rw [htarget]
  by_cases hS : (r, s) ∈ S
  · have hne : (r, s) ≠ (a, b) := by
      intro h
      cases h
      exact hrab ⟨rfl, rfl⟩
    have hneg := hdecay (r, s) hS hne
    have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.Tendsto.const_mul_atTop (sub_pos.mpr hneg) tendsto_id)
    have hlim := ht.mul_const (g.val r s)
    have hsign (t : ℝ) : -((ell s - ell r) * t) = (ell r - ell s) * t := by ring
    simpa only [Function.comp_def, id_eq, hsign, zero_mul] using hlim
  · have hz : g.val r s = 0 := by
      simpa only [Matrix.one_apply, hrs, ite_false, if_false] using hg r s hS
    simp only [hz, mul_zero]
    exact tendsto_const_nhds

theorem positiveRootPattern_isolated_limit
    (d : ℕ) (S : Finset (Fin (d + 1) × Fin (d + 1)))
    (hpos : ∀ p ∈ S, p.1 < p.2) {a b : Fin (d + 1)} (hab : a ≠ b)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ r, ell r = 0) (hneut : ell a = ell b)
    (hdecay : ∀ p ∈ S, p ≠ (a, b) → ell p.1 < ell p.2)
    (g : G (d + 1)) (hg : PositiveRootPattern S g) :
    Tendsto (fun t : ℝ => diagonalOneParameter ell hell t * g *
      diagonalOneParameter ell hell (-t)) atTop
      (𝓝 (Matrix.SpecialLinearGroup.transvection hab (g.val a b))) :=
  rootPattern_isolated_limit d S (fun r h => lt_irrefl r (hpos (r, r) h))
    hab ell hell hneut hdecay g hg

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_ExtremalRootQuotient
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The real quotient by the remaining roots

The extremal matrix entry is additive on its positive-root group.
Its kernel is precisely the remaining root group. Thus the subgroup
removed in the product induction is normal, as required by EK2003,
Proposition 8.3.
-/

noncomputable section
open Matrix Filter Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem neutral_root_entry_mul
    (d : ℕ) (S : Finset (Fin (d + 1) × Fin (d + 1)))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ i j k : Fin (d + 1), (i, j) ∈ S → (j, k) ∈ S → (i, k) ∈ S)
    {a b : Fin (d + 1)} (hab : a ≠ b)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0) (hneut : ell a = ell b)
    (hdecay : ∀ p ∈ S, p ≠ (a, b) → ell p.1 < ell p.2)
    {g h : G (d + 1)} (hg : PositiveRootPattern S g) (hh : PositiveRootPattern S h) :
    (g * h).val a b = g.val a b + h.val a b := by
  have hlim := (positiveRootPattern_isolated_limit d S hpos hab ell hell hneut hdecay g hg).mul
    (positiveRootPattern_isolated_limit d S hpos hab ell hell hneut hdecay h hh)
  have hfun (t : ℝ) :
      (diagonalOneParameter ell hell t * g * diagonalOneParameter ell hell (-t)) *
        (diagonalOneParameter ell hell t * h * diagonalOneParameter ell hell (-t)) =
      diagonalOneParameter ell hell t * (g * h) * diagonalOneParameter ell hell (-t) := by
    rw [diagonalOneParameter_neg]
    group
  simp_rw [hfun] at hlim
  have heq := tendsto_nhds_unique
    (positiveRootPattern_isolated_limit d S hpos hab ell hell hneut hdecay (g * h)
      (positiveRootPattern_mul S hcomp hg hh)) hlim
  rw [← Matrix.SpecialLinearGroup.transvection_add] at heq
  have he := congrArg (fun u : G (d + 1) => u.val a b) heq
  simpa [Matrix.SpecialLinearGroup.transvection_coe, hab] using he

def neutralRootEntryHom
    (d : ℕ) (S : Finset (Fin (d + 1) × Fin (d + 1)))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ i j k : Fin (d + 1), (i, j) ∈ S → (j, k) ∈ S → (i, k) ∈ S)
    {a b : Fin (d + 1)} (hab : a ≠ b)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0) (hneut : ell a = ell b)
    (hdecay : ∀ p ∈ S, p ≠ (a, b) → ell p.1 < ell p.2) :
    positiveRootGeneratedGroup S →* Multiplicative ℝ where
  toFun g := Multiplicative.ofAdd (g.val.val a b)
  map_one' := by
    change (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) a b = 0
    simp [hab]
  map_mul' g h := by
    change (g.val * h.val).val a b = g.val.val a b + h.val.val a b
    exact neutral_root_entry_mul d S hpos hcomp hab ell hell hneut hdecay
      (positiveRootGeneratedGroup_pattern S hcomp g.prop)
      (positiveRootGeneratedGroup_pattern S hcomp h.prop)

theorem neutralRootEntryHom_ker
    (d : ℕ) (S : Finset (Fin (d + 1) × Fin (d + 1)))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ i j k : Fin (d + 1), (i, j) ∈ S → (j, k) ∈ S → (i, k) ∈ S)
    {a b : Fin (d + 1)} (hab : a ≠ b)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0) (hneut : ell a = ell b)
    (hdecay : ∀ p ∈ S, p ≠ (a, b) → ell p.1 < ell p.2) :
    (neutralRootEntryHom d S hpos hcomp hab ell hell hneut hdecay).ker =
      (positiveRootGeneratedGroup (S.erase (a, b))).comap (positiveRootGeneratedGroup S).subtype := by
  ext g
  change g.val.val a b = 0 ↔ g.val ∈ positiveRootGeneratedGroup (S.erase (a, b))
  have herase := erase_neutral_root_closed S hcomp (a, b) ell hneut hdecay
  rw [positiveRootGeneratedGroup_iff (S.erase (a, b))
    (fun p hp => hpos p (Finset.mem_of_mem_erase hp)) herase]
  constructor
  · intro hz r s hrs
    by_cases h : (r, s) = (a, b)
    · obtain ⟨hr, hs⟩ := Prod.mk.inj h
      subst r
      subst s
      simpa only [Matrix.one_apply, hab, ite_false, if_false] using hz
    · exact positiveRootGeneratedGroup_pattern S hcomp g.prop r s
        (fun hS => hrs (Finset.mem_erase.mpr ⟨h, hS⟩))
  · intro hg
    simpa only [Matrix.one_apply, hab, ite_false, if_false] using hg a b (by simp)

theorem remaining_roots_normal
    (d : ℕ) (S : Finset (Fin (d + 1) × Fin (d + 1)))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ i j k : Fin (d + 1), (i, j) ∈ S → (j, k) ∈ S → (i, k) ∈ S)
    {a b : Fin (d + 1)} (hab : a ≠ b)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0) (hneut : ell a = ell b)
    (hdecay : ∀ p ∈ S, p ≠ (a, b) → ell p.1 < ell p.2) :
    ((positiveRootGeneratedGroup (S.erase (a, b))).comap
      (positiveRootGeneratedGroup S).subtype).Normal := by
  rw [← neutralRootEntryHom_ker d S hpos hcomp hab ell hell hneut hdecay]
  infer_instance

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_EliminationRootChart
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Root charts preserving earlier Gaussian eliminations

A root translation preserves all previously eliminated entries when
each affected source entry is already zero. Restricting the actual root
chart gives the next coordinate chart without losing the earlier zeros
or the already chosen nonzero diagonal pivots.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

/-- One Gaussian coordinate, restricted to the already eliminated
entries and nonzero pivots. The new transverse slice records the next
zero and pivot exactly. -/
def eliminationRootHomeomorph {n : ℕ} (P : Finset (Fin n × Fin n))
    (D : Finset (Fin n)) {a b : Fin n} (hab : a ≠ b)
    (hP : ∀ r, (r, b) ∈ P → (r, a) ∈ P) (hb : b ∉ D) :
    {g : EliminationSlice P D // g.val.val a a ≠ 0} ≃ₜ
      EliminationSlice (insert (a, b) P) (insert a D) × ℝ where
  toFun g :=
    let q : RootPivot a a := ⟨g.val.val, g.prop⟩
    let s := PrimeDegreePackets.rootSliceRepresentative hab q
    (⟨s.val, by
      constructor
      · intro p hp
        rcases Finset.mem_insert.mp hp with he | hp
        · subst p
          exact s.prop.2
        · exact zeroPattern_root_translate P hab hP g.val.prop.1 _ p hp
      · intro r hr
        rcases Finset.mem_insert.mp hr with he | hr
        · subst r
          exact s.prop.1
        · exact nonzeroPivots_root_translate D hab hb g.val.prop.2 _ r hr⟩,
      rootParameter a b a g.val.val)
  invFun z :=
    let s : RootSlice a b a := ⟨z.1.val,
      z.1.prop.2 a (Finset.mem_insert_self _ _),
      z.1.prop.1 (a, b) (Finset.mem_insert_self _ _)⟩
    let q := rootPivotTranslate hab ⟨s.val, s.prop.1⟩ z.2
    ⟨⟨q.val, by
      constructor
      · apply zeroPattern_root_translate P hab hP
        intro p hp
        exact z.1.prop.1 p (Finset.mem_insert_of_mem hp)
      · apply nonzeroPivots_root_translate D hab hb
        intro r hr
        exact z.1.prop.2 r (Finset.mem_insert_of_mem hr)⟩, q.prop⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : RootPivot a a => q.val) ((rootPivotHomeomorph (k := a) hab).left_inv
      ⟨g.val.val, g.prop⟩)
  right_inv z := by
    let s : RootSlice a b a := ⟨z.1.val,
      z.1.prop.2 a (Finset.mem_insert_self _ _),
      z.1.prop.1 (a, b) (Finset.mem_insert_self _ _)⟩
    have H := (rootPivotHomeomorph (k := a) hab).right_inv (s, z.2)
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun p : RootSlice a b a × ℝ => p.1.val) H
    · exact congrArg (fun p : RootSlice a b a × ℝ => p.2) H
  continuous_toFun := by
    have hq : Continuous (fun g : {g : EliminationSlice P D // g.val.val a a ≠ 0} =>
        (⟨g.val.val, g.prop⟩ : RootPivot a a)) :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    exact (((continuous_rootSliceRepresentative hab).comp hq).subtype_val.subtype_mk _).prodMk
      (continuous_rootParameter.comp hq)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul
      ((continuous_rootTransvection hab).comp continuous_snd)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_OrderedRootElimination
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian root elimination in row order

Clearing positive roots in lexicographic row order preserves all earlier
zeros. The restricted one-root chart is an open embedding into the
previous slice, so successive steps can build a chart for the full
upper unipotent group.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

/-- The next root factor gives an open coordinate embedding into the
slice left by the earlier eliminations. -/
theorem eliminationRoot_isOpenEmbedding {n : ℕ}
    (P : Finset (Fin n × Fin n)) (D : Finset (Fin n))
    {a b : Fin n} (hab : a ≠ b)
    (hP : ∀ r, (r, b) ∈ P → (r, a) ∈ P) (hb : b ∉ D) :
    Topology.IsOpenEmbedding
      (fun z : EliminationSlice (insert (a, b) P) (insert a D) × ℝ =>
        ((eliminationRootHomeomorph P D hab hP hb).symm z).val) :=
  (elimination_pivot_isOpen P D a).isOpenEmbedding_subtypeVal.comp
    (eliminationRootHomeomorph P D hab hP hb).symm.isOpenEmbedding

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_EliminationChain
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.time_borelSpace _root_.OAI.DukePrimeDegree.EliminationChain.time_measurableSpace _root_.OAI.DukePrimeDegree.EliminationChain.time_nonempty _root_.OAI.DukePrimeDegree.EliminationChain.time_polish _root_.OAI.DukePrimeDegree.EliminationChain.time_secondCountable _root_.OAI.DukePrimeDegree.EliminationChain.time_standardBorel _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Composing Gaussian root-coordinate charts

A finite sequence of compatible eliminations gives an actual open
embedding of the final transverse slice and all its real root
coordinates. Its parametrization is multiplication by the ordered
product of the elementary root matrices.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

namespace EliminationChain

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def param : {P : Finset (Fin n × Fin n)} → {D : Finset (Fin n)} →
    (c : EliminationChain P D) → c.FinalSlice × c.Time → EliminationSlice P D
  | _, _, .done, z => z.1
  | P, D, .step _ _ hab hP hb tail, z =>
      ((eliminationRootHomeomorph P D hab hP hb).symm
        (tail.param (z.1, z.2.1), z.2.2)).val

theorem param_isOpenEmbedding (c : EliminationChain P D) :
    Topology.IsOpenEmbedding c.param := by
  induction c with
  | done => exact (Homeomorph.prodPUnit _).isOpenEmbedding
  | @step P D a b hab hP hb tail ih =>
      exact ((eliminationRoot_isOpenEmbedding P D hab hP hb).comp
        (ih.prodMap (Topology.IsOpenEmbedding.id (X := ℝ)))).comp
          (Homeomorph.prodAssoc _ _ _).symm.isOpenEmbedding

theorem param_val (c : EliminationChain P D) (s : c.FinalSlice) (t : c.Time) :
    (c.param (s, t)).val = s.val * c.word t := by
  induction c with
  | done => exact (mul_one s.val).symm
  | step a b hab hP hb tail ih =>
      change tail.FinalSlice at s
      change tail.Time × ℝ at t
      change (tail.param (s, t.1)).val * Matrix.SpecialLinearGroup.transvection hab t.2 =
        s.val * (tail.word t.1 * Matrix.SpecialLinearGroup.transvection hab t.2)
      exact (congrArg (fun g : G n => g * Matrix.SpecialLinearGroup.transvection hab t.2)
        (ih s t.1)).trans (mul_assoc _ _ _)

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootChart
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.time_borelSpace _root_.OAI.DukePrimeDegree.EliminationChain.time_polish _root_.OAI.DukePrimeDegree.EliminationChain.time_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual charts for the full upper unipotent group

The complete Gaussian elimination chain supplies an open group chart.
Left translation and the discrete lattice covering then give local
product charts in the arithmetic quotient around every point. Every
time factor is an actual ordered product of positive-root matrices.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def upperRootParam (n : ℕ) (z : UpperRootTransverse n × UpperRootTime n) : G n :=
  ((completeRootChain n).param z).val

theorem upperRootParam_isOpenEmbedding (n : ℕ) :
    Topology.IsOpenEmbedding (upperRootParam n) :=
  (emptyEliminationHomeomorph n).isOpenEmbedding.comp
    (completeRootChain n).param_isOpenEmbedding

lemma upperRootParam_eq_mul (n : ℕ) (s : UpperRootTransverse n) (t : UpperRootTime n) :
    upperRootParam n (s, t) = s.val * (completeRootChain n).word t :=
  (completeRootChain n).param_val s t

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootLongBoxes
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Long boxes for the full positive-root group

The ordered root word is injective. Generic arithmetic lattices have
free upper unipotent orbits, so every compact set of full root times
fits into one actual quotient box containing the chosen basepoint.
-/

noncomputable section
open Matrix MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem upperRootWord_injective (n : ℕ) : Function.Injective (completeRootChain n).word := by
  intro t u h
  have he : upperRootParam n (upperRootIdentity n, t) =
      upperRootParam n (upperRootIdentity n, u) := by
    rw [upperRootParam_eq_mul, upperRootParam_eq_mul, h]
  exact congrArg Prod.snd ((upperRootParam_isOpenEmbedding n).injective he)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootGlobalCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Global coordinates on the upper unipotent group

Gaussian elimination never encounters a zero pivot on a unipotent
upper triangular matrix. Consequently the ordered root word covers
that entire group, and is a homeomorphism onto it.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

theorem exists_param_of_upperRoot (c : EliminationChain P D)
    (hS : c.finalEntries ⊆ allPositiveRoots n) (q : EliminationSlice P D)
    (hq : q.val ∈ positiveRootGeneratedGroup (allPositiveRoots n)) :
    ∃ (s : c.FinalSlice) (t : c.Time), c.param (s, t) = q ∧
      s.val ∈ positiveRootGeneratedGroup (allPositiveRoots n) := by
  induction c with
  | done => exact ⟨q, PUnit.unit, rfl, hq⟩
  | @step P D a b hab hP hb tail ih =>
      have ha : q.val.val a a ≠ 0 := by rw [upperRoot_diagonal hq a]; exact one_ne_zero
      let E := eliminationRootHomeomorph P D hab hP hb
      let z := E ⟨q, ha⟩
      have habS : (a, b) ∈ allPositiveRoots n :=
        hS (tail.entries_subset_final (Finset.mem_insert_self _ _))
      have hz : z.1.val ∈ positiveRootGeneratedGroup (allPositiveRoots n) := by
        change q.val * Matrix.SpecialLinearGroup.transvection hab
          (-rootParameter a b a q.val) ∈ positiveRootGeneratedGroup (allPositiveRoots n)
        exact (positiveRootGeneratedGroup _).mul_mem hq
          (transvection_mem_positiveRootGeneratedGroup _ hab habS _)
      obtain ⟨s, t, hst, hs⟩ := ih hS z.1 hz
      refine ⟨s, (t, z.2), ?_, hs⟩
      change (E.symm (tail.param (s, t), z.2)).val = q
      rw [hst]
      exact congrArg Subtype.val (E.symm_apply_apply ⟨q, ha⟩)

end EliminationChain

theorem upperRootWord_surjective (n : ℕ)
    (g : positiveRootGeneratedGroup (allPositiveRoots n)) :
    ∃ t : UpperRootTime n, (completeRootChain n).word t = g.val := by
  let q : EliminationSlice (∅ : Finset (Fin n × Fin n)) ∅ :=
    ⟨g.val, by constructor <;> simp [ZeroPattern, NonzeroPivots]⟩
  obtain ⟨s, t, he, hs⟩ := (completeRootChain n).exists_param_of_upperRoot
    (by rw [completeRootChain_final]) q g.prop
  have hs1 : s.val = 1 := upperRoot_zeroPattern_eq_one hs (by
    simpa only [←completeRootChain_final n] using s.prop.1)
  have hv := congrArg (fun a : EliminationSlice (∅ : Finset (Fin n × Fin n)) ∅ => a.val) he
  change ((completeRootChain n).param (s, t)).val = g.val at hv
  rw [EliminationChain.param_val, hs1, one_mul] at hv
  exact ⟨t, hv⟩

theorem upperRootWordMap_bijective (n : ℕ) : Function.Bijective (upperRootWordMap n) := by
  constructor
  · intro t u h
    exact upperRootWord_injective n (congrArg Subtype.val h)
  · intro g
    obtain ⟨t, ht⟩ := upperRootWord_surjective n g
    exact ⟨t, Subtype.ext ht⟩

theorem upperRootWord_isEmbedding (n : ℕ) :
    Topology.IsEmbedding (fun t : UpperRootTime n => (completeRootChain n).word t) := by
  have he := (upperRootParam_isOpenEmbedding n).isEmbedding.comp
    (isEmbedding_prodMkRight (upperRootIdentity n))
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  rw [Function.comp_apply, upperRootParam_eq_mul]
  exact (one_mul _).symm

theorem upperRootWordMap_isEmbedding (n : ℕ) : Topology.IsEmbedding (upperRootWordMap n) :=
  Topology.IsEmbedding.subtypeVal.of_comp_iff.mp (upperRootWord_isEmbedding n)

def upperRootWordHomeomorph (n : ℕ) :
    UpperRootTime n ≃ₜ positiveRootGeneratedGroup (allPositiveRoots n) :=
  (upperRootWordMap_isEmbedding n).toHomeomorphOfSurjective (upperRootWordMap_bijective n).2

@[simp] lemma upperRootWordHomeomorph_apply (n : ℕ) (t : UpperRootTime n) :
    (upperRootWordHomeomorph n t).val = (completeRootChain n).word t := rfl

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_EliminationRootOrder
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Every positive root occurs exactly once

The chart compatibility conditions prohibit repeating an eliminated
root: a repeat would force an eliminated diagonal entry. A complete
chain therefore lists exactly the positive roots, without repetitions.
-/

noncomputable section
open Matrix Set

namespace DukePrimeDegree
open PrimeDegreePackets

lemma completeRootChain_roots_toFinset (n : ℕ) :
    (completeRootChain n).roots.toFinset = allPositiveRoots n := by
  have h := (completeRootChain n).finalEntries_eq_union_roots
  simpa only [completeRootChain_final, Finset.empty_union] using h.symm

lemma completeRootChain_roots_nodup (n : ℕ) : (completeRootChain n).roots.Nodup := by
  apply (completeRootChain n).roots_nodup
  intro p hp
  rw [completeRootChain_final] at hp
  exact (Finset.mem_filter.mp hp).2

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootDilation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Diagonal dynamics in ordered upper-root coordinates

Conjugation by a diagonal element is exactly the product of the root
coordinate dilations, with each factor carrying its own root weight.
-/

noncomputable section
open Matrix Set
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def rootDilation : {P : Finset (Fin n × Fin n)} → {D : Finset (Fin n)} →
    (c : EliminationChain P D) → (Fin n → ℝ) → ℝ → c.Time ≃ₜ c.Time
  | _, _, .done, _, _ => Homeomorph.refl _
  | _, _, .step a b _ _ _ tail, ell, r =>
      (tail.rootDilation ell r).prodCongr
        (Homeomorph.mulLeft₀ (Real.exp ((ell a - ell b) * r)) (Real.exp_ne_zero _))

theorem word_rootDilation (c : EliminationChain P D) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (r : ℝ) (t : c.Time) :
    c.word (c.rootDilation ell r t) =
      diagonalOneParameter ell hell r * c.word t * diagonalOneParameter ell hell (-r) := by
  induction c with
  | done =>
      change 1 = diagonalOneParameter ell hell r * 1 * diagonalOneParameter ell hell (-r)
      rw [mul_one, diagonalOneParameter_neg, mul_inv_cancel]
  | step a b hab hP hb tail ih =>
      change tail.Time × ℝ at t
      change tail.word (tail.rootDilation ell r t.1) *
        Matrix.SpecialLinearGroup.transvection hab (Real.exp ((ell a - ell b) * r) * t.2) =
          diagonalOneParameter ell hell r *
            (tail.word t.1 * Matrix.SpecialLinearGroup.transvection hab t.2) *
              diagonalOneParameter ell hell (-r)
      rw [ih, ←diagonal_conjugation_transvection ell hell hab t.2 r,
        diagonalOneParameter_neg]
      group

end EliminationChain

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootEuclideanCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One real coordinate for each positive root

The elimination time space is canonically a finite product of real
lines, indexed without repetition by the positive roots. Diagonal
conjugation scales each coordinate by its own root character.
-/

noncomputable section
open Matrix Set
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def timeVectorHomeomorph : {P : Finset (Fin n × Fin n)} → {D : Finset (Fin n)} →
    (c : EliminationChain P D) → c.Time ≃ₜ (Fin c.roots.length → ℝ)
  | _, _, .done => Homeomorph.homeomorphOfUnique PUnit (Fin 0 → ℝ)
  | _, _, .step _ _ _ _ _ tail =>
      ((tail.timeVectorHomeomorph).prodCongr (Homeomorph.refl ℝ)).trans
        (realVectorConsHomeomorph tail.roots.length)

end EliminationChain

def upperRootIndexEquiv (n : ℕ) :
    Fin (completeRootChain n).roots.length ≃ (allPositiveRoots n) :=
  (List.Nodup.getEquiv _ (completeRootChain_roots_nodup n)).trans
    (Equiv.setCongr (by
      ext p
      change p ∈ (completeRootChain n).roots ↔ p ∈ allPositiveRoots n
      rw [←List.mem_toFinset, completeRootChain_roots_toFinset]))

@[simp] lemma upperRootIndexEquiv_val (n : ℕ) (k : Fin (completeRootChain n).roots.length) :
    (upperRootIndexEquiv n k).val = (completeRootChain n).roots.get k := rfl

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_EliminationWordEntries
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian word coordinates are the actual upper matrix entries -/

noncomputable section
open Matrix Set
open scoped BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma word_column_of_pivot (c : EliminationChain P D) (t : c.Time)
    (i : Fin n) (hi : i ∈ D) (r : Fin n) :
    (c.word t).val r i = if r = i then 1 else 0 := by
  induction c with
  | done => simp [word,Matrix.one_apply]
  | @step P D a b hab hP hb tail ih =>
      change tail.Time × ℝ at t
      have hib : i ≠ b := by intro h; exact hb (h ▸ hi)
      change ((tail.word t.1).val * Matrix.transvection a b t.2) r i = _
      rw [Matrix.mul_transvection_apply_of_ne (i := a) (j := b) r i hib]
      exact ih t.1 (Finset.mem_insert_of_mem hi)

lemma word_step_add_single {a b : Fin n} (hab : a ≠ b)
    (hP : ∀ r, (r,b) ∈ P → (r,a) ∈ P) (hb : b ∉ D)
    (tail : EliminationChain (insert (a,b) P) (insert a D)) (t : tail.Time) (s : ℝ) :
    ((EliminationChain.step a b hab hP hb tail).word (t,s)).val =
      (tail.word t).val + Matrix.single a b s := by
  ext r i
  change ((tail.word t).val * Matrix.transvection a b s) r i = _
  by_cases hi : i = b
  · subst i
    rw [Matrix.mul_transvection_apply_same,Matrix.add_apply,
      tail.word_column_of_pivot t a (Finset.mem_insert_self _ _) r]
    by_cases hr : r = a
    · subst r; simp
    · simp [hr,Ne.symm hr]
  · rw [Matrix.mul_transvection_apply_of_ne (i := a) (j := b) r i hi,Matrix.add_apply]
    simp [Ne.symm hi]

theorem word_val_eq_sum_single (c : EliminationChain P D) (t : c.Time) :
    (c.word t).val = 1 + ∑ k : Fin c.roots.length,
      Matrix.single (c.roots.get k).1 (c.roots.get k).2 (c.timeVectorHomeomorph t k) := by
  induction c with
  | done =>
      change (1 : Matrix (Fin n) (Fin n) ℝ) = 1 + ∑ k : Fin 0, _
      simp
  | @step P D a b hab hP hb tail ih =>
      change tail.Time × ℝ at t
      calc
        _ = (tail.word t.1).val + Matrix.single a b t.2 := word_step_add_single hab hP hb tail _ _
        _ = _ := ?_
      rw [ih]
      change 1 + (∑ k : Fin tail.roots.length, Matrix.single (tail.roots.get k).1
        (tail.roots.get k).2 (tail.timeVectorHomeomorph t.1 k)) + Matrix.single a b t.2 =
        1 + ∑ k : Fin (tail.roots.length+1), Matrix.single (((a,b)::tail.roots).get k).1
          (((a,b)::tail.roots).get k).2
          (Fin.cons t.2 (tail.timeVectorHomeomorph t.1) k)
      rw [Fin.sum_univ_succ]
      simp only [List.get_eq_getElem,Fin.val_zero,List.getElem_cons_zero,Fin.cons_zero,
        Fin.val_succ,List.getElem_cons_succ,Fin.cons_succ]
      abel

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_EliminationMatrixCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Each Gaussian root parameter is its corresponding matrix entry -/

noncomputable section
open Matrix Set
open scoped BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

theorem word_entry_eq_time (c : EliminationChain P D)
    (hpos : ∀ p ∈ c.finalEntries, p.1 < p.2) (t : c.Time) (k : Fin c.roots.length) :
    (c.word t).val (c.roots.get k).1 (c.roots.get k).2 = c.timeVectorHomeomorph t k := by
  have hp : c.roots.get k ∈ c.finalEntries := by
    rw [c.finalEntries_eq_union_roots]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.get_mem _ _))
  have hne := ne_of_lt (hpos _ hp)
  have H := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ =>
    M (c.roots.get k).1 (c.roots.get k).2) (c.word_val_eq_sum_single t)
  simp only [Matrix.add_apply,Matrix.sum_apply,Matrix.one_apply,ite_eq_right hne,zero_add] at H
  rw [H,Finset.sum_eq_single k]
  · simp
  · intro l _ hl
    have hr : c.roots.get l ≠ c.roots.get k :=
      fun he => hl ((c.roots_nodup hpos).injective_get he)
    rw [Matrix.single_apply]
    split_ifs with h
    · exact (hr (Prod.ext h.1 h.2)).elim
    · rfl
  · simp

end EliminationChain

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_EliminationFirstRootSlice
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The first root factor as an actual one-root chart

The remaining Gaussian chart embeds openly into the standard root
transversal. Its fibers are the same right root orbits used to define
the intrinsic one-dimensional leaf measures.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma word_mem_generated_of_roots (c : EliminationChain P D)
    (S : Finset (Fin n × Fin n)) (hS : ∀ p ∈ c.roots, p ∈ S) (t : c.Time) :
    c.word t ∈ positiveRootGeneratedGroup S := by
  induction c with
  | done => exact (positiveRootGeneratedGroup S).one_mem
  | step a b hab hP hb tail ih =>
      apply (positiveRootGeneratedGroup S).mul_mem
      · exact ih (fun p hp => hS p (List.mem_cons_of_mem _ hp)) t.1
      · exact transvection_mem_positiveRootGeneratedGroup S hab
          (hS (a, b) (List.mem_cons_self)) t.2

end EliminationChain

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_AdjacentFirstRoot
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A concrete first adjacent-root product step

The first adjacent root admits a neutral contracting diagonal direction.
Starting the Gaussian chain with this root gives actual local charts to
which the proved conditional-product theorem applies.
-/

noncomputable section
open Matrix Set MeasureTheory Filter
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_complete_elimination_chain_from_initial {n : ℕ}
    (P : Finset (Fin n × Fin n)) (D : Finset (Fin n))
    (hP : InitialRootPattern P) (hD : PivotsFromPattern P D) :
    ∃ c : EliminationChain P D, c.finalEntries = allPositiveRoots n := by
  suffices ∀ m : ℕ, ∀ (P : Finset (Fin n × Fin n)) (D : Finset (Fin n)),
      (allPositiveRoots n \ P).card = m → InitialRootPattern P → PivotsFromPattern P D →
      ∃ c : EliminationChain P D, c.finalEntries = allPositiveRoots n by
    exact this _ P D rfl hP hD
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro P D hcard hP hD
      by_cases hempty : allPositiveRoots n \ P = ∅
      · refine ⟨.done, ?_⟩
        change P = allPositiveRoots n
        apply Finset.Subset.antisymm
        · exact fun p hp => (hP p hp).1
        · exact Finset.sdiff_eq_empty_iff_subset.mp hempty
      · obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image (allPositiveRoots n \ P)
          (fun q => toLex q) (Finset.nonempty_iff_ne_empty.mpr hempty)
        have hab : p.1 < p.2 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
        have hnot : p ∉ P := (Finset.mem_sdiff.mp hp).2
        have hless : (allPositiveRoots n \ insert p P).card < m := by
          rw [Finset.sdiff_insert, ← hcard]
          exact Finset.card_erase_lt_of_mem hp
        obtain ⟨c, hc⟩ := ih _ hless (insert p P) (insert p.1 D) rfl
          (initialRootPattern_insert_min hP p hp hmin) (pivotsFromPattern_insert hD p.1 p.2)
        exact ⟨.step p.1 p.2 (ne_of_lt hab)
          (initialRootPattern_stable hP hab hnot)
          (initialRootPattern_pivot_notMem hP hD hab hnot) c, hc⟩


end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LexicographicRootWeights
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Neutral weights for every lexicographic elimination step

The least remaining root can be kept neutral while all other remaining
root directions contract. Thus the actual Gaussian elimination order
has the weights needed by the conditional product induction.
-/

noncomputable section
open Matrix Set
open scoped BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma lexicographicNeutralRaw_strict {n : ℕ}
    (S : Finset (Fin n × Fin n)) {a b : Fin n}
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hmin : ∀ p ∈ S, toLex (a,b) ≤ toLex p)
    (p : Fin n × Fin n) (hp : p ∈ S) (hne : p ≠ (a,b)) :
    lexicographicNeutralRaw a b p.1 < lexicographicNeutralRaw a b p.2 := by
  have har : a ≤ p.1 := by
    by_contra h
    exact not_lt_of_ge (hmin p hp)
      (Prod.Lex.toLex_lt_toLex.mpr (Or.inl (lt_of_not_ge h)))
  have hca : p.2 ≠ a := by
    intro h
    have hlt : p.1 < a := by simpa only [h] using hpos p hp
    exact not_lt_of_ge har hlt
  by_cases hra : p.1 = a
  · have hbc : b < p.2 := by
      have hle : b ≤ p.2 := by
        by_contra h
        exact not_lt_of_ge (hmin p hp)
          (Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hra, lt_of_not_ge h⟩))
      refine lt_of_le_of_ne hle ?_
      intro h
      exact hne (Prod.ext hra h.symm)
    simpa only [lexicographicNeutralRaw, ite_eq_left hra, ite_eq_right hca] using
      (show (b.val : ℝ) < p.2.val by exact_mod_cast hbc)
  · simpa only [lexicographicNeutralRaw, ite_eq_right hra, ite_eq_right hca] using
      (show (p.1.val : ℝ) < p.2.val by exact_mod_cast hpos p hp)

theorem exists_lexicographic_root_weights (d : ℕ)
    (S : Finset (Fin (d + 1) × Fin (d + 1))) {a b : Fin (d + 1)}
    (hab : a < b) (hpos : ∀ p ∈ S, p.1 < p.2)
    (hmin : ∀ p ∈ S, toLex (a,b) ≤ toLex p) :
    ∃ ell : Fin (d + 1) → ℝ, (∑ i, ell i) = 0 ∧ ell a = ell b ∧
      ∀ p ∈ S, p ≠ (a,b) → ell p.1 < ell p.2 := by
  refine ⟨centerWeights d (lexicographicNeutralRaw a b), centerWeights_sum _ _, ?_, ?_⟩
  · unfold centerWeights
    rw [lexicographicNeutralRaw_equal hab]
  · intro p hp hne
    apply sub_neg.mp
    rw [centerWeights_sub]
    exact sub_neg.mpr (lexicographicNeutralRaw_strict S hpos hmin p hp hne)

lemma initialRemaining_roots_closed {n : ℕ}
    (P : Finset (Fin n × Fin n)) (hP : InitialRootPattern P) :
    ∀ a b c : Fin n, (a,b) ∈ allPositiveRoots n \ P →
      (b,c) ∈ allPositiveRoots n \ P → (a,c) ∈ allPositiveRoots n \ P := by
  intro a b c hab hbc
  obtain ⟨hab, habP⟩ := Finset.mem_sdiff.mp hab
  obtain ⟨hbc, _⟩ := Finset.mem_sdiff.mp hbc
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      lt_trans (Finset.mem_filter.mp hab).2 (Finset.mem_filter.mp hbc).2⟩
  · intro hacP
    exact habP ((hP (a,c) hacP).2 (a,b) hab
      (Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, (Finset.mem_filter.mp hbc).2⟩)))

lemma initialRemaining_erase {n : ℕ} (P : Finset (Fin n × Fin n)) (p : Fin n × Fin n) :
    (allPositiveRoots n \ P).erase p = allPositiveRoots n \ insert p P := by
  ext q
  simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
  tauto

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingRootCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Global coordinates on each remaining Gaussian root subgroup -/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def identityFinal (c : EliminationChain P D) (hfinal : c.finalEntries = allPositiveRoots n) :
    c.FinalSlice :=
  ⟨1, by
    constructor
    · intro p hp
      rw [hfinal] at hp
      have hne := ne_of_lt (Finset.mem_filter.mp hp).2
      change (1 : Matrix (Fin n) (Fin n) ℝ) p.1 p.2 = 0
      simp [hne]
    · intro r _
      change (1 : Matrix (Fin n) (Fin n) ℝ) r r ≠ 0
      simp⟩

lemma word_mem_remaining (c : EliminationChain P D)
    (hfinal : c.finalEntries = allPositiveRoots n) (t : c.Time) :
    c.word t ∈ positiveRootGeneratedGroup (allPositiveRoots n \ P) := by
  apply c.word_mem_generated_of_roots
  intro p hp
  have hpos : ∀ q ∈ c.finalEntries, q.1 < q.2 := by
    intro q hq
    rw [hfinal] at hq
    exact (Finset.mem_filter.mp hq).2
  refine Finset.mem_sdiff.mpr ⟨?_, c.roots_notMem_initial hpos p hp⟩
  rw [←hfinal, c.finalEntries_eq_union_roots]
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr hp)

theorem word_surjective_remaining (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n)
    (g : positiveRootGeneratedGroup (allPositiveRoots n \ P)) :
    ∃ t : c.Time, c.word t = g.val := by
  have hgU : g.val ∈ positiveRootGeneratedGroup (allPositiveRoots n) :=
    positiveRootGeneratedGroup_mono Finset.sdiff_subset g.prop
  have hpat := positiveRootGeneratedGroup_pattern (allPositiveRoots n \ P)
    (initialRemaining_roots_closed P hP) g.prop
  let q : EliminationSlice P D := ⟨g.val, by
    constructor
    · intro p hp
      have hn : p ∉ allPositiveRoots n \ P := by
        intro h
        exact (Finset.mem_sdiff.mp h).2 hp
      have hz := hpat p.1 p.2 hn
      have hne := ne_of_lt (Finset.mem_filter.mp (hP p hp).1).2
      simpa only [Matrix.one_apply, hne, ite_false, if_false] using hz
    · intro a _
      rw [upperRoot_diagonal hgU a]
      exact one_ne_zero⟩
  obtain ⟨s, t, he, hs⟩ := c.exists_param_of_upperRoot (by rw [hfinal]) q hgU
  have hs1 : s.val = 1 := upperRoot_zeroPattern_eq_one hs (by
    simpa only [hfinal] using s.prop.1)
  have hv := congrArg (fun z : EliminationSlice P D => z.val) he
  change (c.param (s,t)).val = g.val at hv
  rw [c.param_val, hs1, one_mul] at hv
  exact ⟨t,hv⟩

theorem word_isEmbedding_remaining (c : EliminationChain P D)
    (hfinal : c.finalEntries = allPositiveRoots n) :
    Topology.IsEmbedding c.word := by
  have he := Topology.IsEmbedding.subtypeVal.comp
    (c.param_isOpenEmbedding.isEmbedding.comp (isEmbedding_prodMkRight (c.identityFinal hfinal)))
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  rw [Function.comp_apply, Function.comp_apply, c.param_val]
  exact (one_mul _).symm

def remainingWordMap (c : EliminationChain P D)
    (hfinal : c.finalEntries = allPositiveRoots n) (t : c.Time) :
    positiveRootGeneratedGroup (allPositiveRoots n \ P) :=
  ⟨c.word t, c.word_mem_remaining hfinal t⟩

theorem remainingWordMap_isEmbedding (c : EliminationChain P D)
    (hfinal : c.finalEntries = allPositiveRoots n) :
    Topology.IsEmbedding (c.remainingWordMap hfinal) :=
  Topology.IsEmbedding.subtypeVal.of_comp_iff.mp (c.word_isEmbedding_remaining hfinal)

theorem remainingWordMap_surjective (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n) :
    Function.Surjective (c.remainingWordMap hfinal) := by
  intro g
  obtain ⟨t,ht⟩ := c.word_surjective_remaining hP hfinal g
  exact ⟨t,Subtype.ext ht⟩

def remainingWordHomeomorph (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n) :
    c.Time ≃ₜ positiveRootGeneratedGroup (allPositiveRoots n \ P) :=
  (c.remainingWordMap_isEmbedding hfinal).toHomeomorphOfSurjective
    (c.remainingWordMap_surjective hP hfinal)

@[simp] lemma remainingWordHomeomorph_apply (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n) (t : c.Time) :
    (c.remainingWordHomeomorph hP hfinal t).val = c.word t := rfl

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingEuclideanCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matrix-entry coordinates on every remaining Gaussian subgroup -/

noncomputable section
open Matrix Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma roots_toFinset_remaining (c : EliminationChain P D)
    (hfinal : c.finalEntries = allPositiveRoots n) :
    c.roots.toFinset = allPositiveRoots n \ P := by
  have hpos : ∀ p ∈ c.finalEntries, p.1 < p.2 := by
    intro p hp
    rw [hfinal] at hp
    exact (Finset.mem_filter.mp hp).2
  ext p
  constructor
  · intro hp
    refine Finset.mem_sdiff.mpr ⟨?_,c.roots_notMem_initial hpos p (List.mem_toFinset.mp hp)⟩
    rw [←hfinal,c.finalEntries_eq_union_roots]
    exact Finset.mem_union_right P hp
  · intro hp
    have hf : p ∈ c.finalEntries := by rw [hfinal]; exact (Finset.mem_sdiff.mp hp).1
    rw [c.finalEntries_eq_union_roots] at hf
    exact (Finset.mem_union.mp hf).resolve_left (Finset.mem_sdiff.mp hp).2

def remainingIndexEquiv (c : EliminationChain P D)
    (hfinal : c.finalEntries = allPositiveRoots n) :
    Fin c.roots.length ≃ ↥(allPositiveRoots n \ P) :=
  (List.Nodup.getEquiv _ (c.roots_nodup (by
    intro p hp
    rw [hfinal] at hp
    exact (Finset.mem_filter.mp hp).2))).trans
    (Equiv.setCongr (by
      ext p
      change p ∈ c.roots ↔ p ∈ allPositiveRoots n \ P
      rw [←List.mem_toFinset,c.roots_toFinset_remaining hfinal]))

def remainingEuclideanCoordinates (c : EliminationChain P D)
    (hfinal : c.finalEntries = allPositiveRoots n) :
    c.Time ≃ₜ (↥(allPositiveRoots n \ P) → ℝ) :=
  c.timeVectorHomeomorph.trans (realCoordinatesReindex (c.remainingIndexEquiv hfinal))

lemma remainingEuclideanCoordinates_entry (c : EliminationChain P D)
    (hfinal : c.finalEntries = allPositiveRoots n) (t : c.Time)
    (p : ↥(allPositiveRoots n \ P)) :
    (c.word t).val p.val.1 p.val.2 = c.remainingEuclideanCoordinates hfinal t p := by
  have he : c.roots.get ((c.remainingIndexEquiv hfinal).symm p) = p.val :=
    congrArg Subtype.val ((c.remainingIndexEquiv hfinal).apply_symm_apply p)
  have H := c.word_entry_eq_time (by
    intro q hq
    rw [hfinal] at hq
    exact (Finset.mem_filter.mp hq).2) t ((c.remainingIndexEquiv hfinal).symm p)
  change (c.word t).val p.val.1 p.val.2 =
    c.timeVectorHomeomorph t ((c.remainingIndexEquiv hfinal).symm p)
  simpa only [he] using H

def remainingGroupCoordinates (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n) :
    positiveRootGeneratedGroup (allPositiveRoots n \ P) ≃ₜ (↥(allPositiveRoots n \ P) → ℝ) :=
  (c.remainingWordHomeomorph hP hfinal).symm.trans (c.remainingEuclideanCoordinates hfinal)

lemma remainingGroupCoordinates_apply (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n)
    (g : positiveRootGeneratedGroup (allPositiveRoots n \ P))
    (p : ↥(allPositiveRoots n \ P)) :
    c.remainingGroupCoordinates hP hfinal g p = g.val.val p.val.1 p.val.2 := by
  have he : c.word ((c.remainingWordHomeomorph hP hfinal).symm g) = g.val :=
    congrArg Subtype.val ((c.remainingWordHomeomorph hP hfinal).apply_symm_apply g)
  change c.remainingEuclideanCoordinates hfinal
    ((c.remainingWordHomeomorph hP hfinal).symm g) p = _
  rw [←he]
  exact (c.remainingEuclideanCoordinates_entry hfinal _ p).symm

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingIntrinsicProduct
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The intrinsic root product on each remaining subgroup

Its coordinates are actual matrix entries, so the measure is independent
of the Gaussian elimination chain used to define the coordinate chart.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D E : Finset (Fin n)}

def remainingIntrinsicProduct (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (x : X n) :
    Measure (positiveRootGeneratedGroup (allPositiveRoots n \ P)) :=
  (Measure.pi fun p : ↥(allPositiveRoots n \ P) =>
    intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x).map
      (c.remainingGroupCoordinates hP hfinal).symm

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingRootHolonomy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous holonomy for the full Gaussian root induction

One common null set controls every lexicographic elimination step. At
each step the remaining subgroup is normal and the selected root leaf
is constant along its cosets, with the exact root displacement retained.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def InitialRootStep (n : ℕ) :=
  {z : Finset (Fin n × Fin n) × (Fin n × Fin n) //
    InitialRootPattern z.1 ∧ z.2 ∈ allPositiveRoots n \ z.1 ∧
      ∀ q ∈ allPositiveRoots n \ z.1, toLex z.2 ≤ toLex q}

namespace InitialRootStep
variable {n : ℕ}

def processed (s : InitialRootStep n) : Finset (Fin n × Fin n) := s.val.1
def root (s : InitialRootStep n) : Fin n × Fin n := s.val.2
def remaining (s : InitialRootStep n) : Finset (Fin n × Fin n) := allPositiveRoots n \ s.processed

lemma initial (s : InitialRootStep n) : InitialRootPattern s.processed := s.prop.1
lemma mem_remaining (s : InitialRootStep n) : s.root ∈ s.remaining := s.prop.2.1
lemma least (s : InitialRootStep n) : ∀ q ∈ s.remaining, toLex s.root ≤ toLex q := s.prop.2.2
lemma positive (s : InitialRootStep n) : s.root.1 < s.root.2 :=
  (Finset.mem_filter.mp (Finset.mem_sdiff.mp s.mem_remaining).1).2
lemma distinct (s : InitialRootStep n) : s.root.1 ≠ s.root.2 := ne_of_lt s.positive
lemma remaining_positive (s : InitialRootStep n) : ∀ q ∈ s.remaining, q.1 < q.2 :=
  fun _ hq => (Finset.mem_filter.mp (Finset.mem_sdiff.mp hq).1).2
lemma remaining_closed (s : InitialRootStep n) :
    ∀ a b c : Fin n, (a,b) ∈ s.remaining → (b,c) ∈ s.remaining → (a,c) ∈ s.remaining :=
  initialRemaining_roots_closed s.processed s.initial

theorem next_normal (d : ℕ) (s : InitialRootStep (d + 1)) :
    ((positiveRootGeneratedGroup (s.remaining.erase s.root)).comap
      (positiveRootGeneratedGroup s.remaining).subtype).Normal := by
  obtain ⟨ell,hell,hneut,hdecay⟩ := exists_lexicographic_root_weights d s.remaining
    s.positive s.remaining_positive s.least
  exact remaining_roots_normal d s.remaining s.remaining_positive s.remaining_closed
    s.distinct ell hell hneut hdecay

end InitialRootStep

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinates with the processed roots before the remaining subgroup

These coordinates keep the remaining subgroup on the right, so its
fibers are actual right orbits at every step of the product induction.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

structure RootPrefixCoordinates (n : ℕ) (P : Finset (Fin n × Fin n))
    (T : Type*) [TopologicalSpace T] where
  base : T → G n
  equiv : (T × positiveRootGeneratedGroup (allPositiveRoots n \ P)) ≃ₜ
    positiveRootGeneratedGroup (allPositiveRoots n)
  param_eq_mul : ∀ t w, (equiv (t,w)).val = base t * w.val

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixWindows
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countable long-box exhaustions for each remaining subgroup -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
def remainingWindow (c : EliminationChain P D) (R : ℝ) (m : ℕ) : Set c.Time := c.cube (R+m)
lemma remainingWindow_open (c : EliminationChain P D) (R : ℝ) (m : ℕ) :
    IsOpen (c.remainingWindow R m) := c.cube_open _
lemma remainingWindow_mono (c : EliminationChain P D) (R : ℝ) : Monotone (c.remainingWindow R) := by
  intro a b hab
  apply c.cube_mono
  simpa only [add_comm] using add_le_add_left (Nat.cast_le.mpr hab) R
lemma remainingWindow_cover (c : EliminationChain P D) (R : ℝ) :
    ⋃ m, c.remainingWindow R m = univ := c.cubes_cover R
end EliminationChain

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixGroupLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual group-valued leaf measures for the remaining subgroups -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def remainingGroupLeafMeasure (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n) (ν : Measure c.Time) :
    Measure (positiveRootGeneratedGroup (allPositiveRoots n \ P)) :=
  ν.map (c.remainingWordHomeomorph hP hfinal)

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingRebase
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rebasing a remaining-subgroup leaf at its current coordinate -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def remainingRebase (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n) (t : c.Time) : c.Time ≃ₜ c.Time :=
  (c.remainingWordHomeomorph hP hfinal).trans
    ((Homeomorph.mulLeft (c.remainingWordHomeomorph hP hfinal t)⁻¹).trans
      (c.remainingWordHomeomorph hP hfinal).symm)

def centeredRemainingMeasure (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n) (ν : Measure c.Time) (t : c.Time) :
    Measure c.Time := ν.map (c.remainingRebase hP hfinal t)

def basedRemainingMeasure (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n) (ν : Measure c.Time) (t : c.Time) :
    Measure c.Time := anchorNormalize (c.centeredRemainingMeasure hP hfinal ν t) (c.cube 1)

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingProductSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Support of the actual intrinsic product in root coordinates -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def remainingTimeProduct (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots n)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (x : X n) : Measure c.Time :=
  (c.remainingIntrinsicProduct hP hf μ x).map (c.remainingWordHomeomorph hP hf).symm

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RemainingFutureShift
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact shift of future atoms along remaining-root leaves -/

noncomputable section
open Set
open MeasureTheory
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def remainingFutureAtom (c : EliminationChain P D) (ell : Fin n → ℝ)
    (hell : ∑ k, ell k = 0) (Q : X n → ℕ) (m : ℕ) (x : X n) : Set c.Time :=
  {u | ∀ k : ℕ,
    Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+m]
      (rightAction x (c.word u))) =
    Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+m] x)}

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CanonicalRootBasic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mean root coefficients and their elementary properties

The coefficient is the mean leaf information at unit scale. Diagonal
covariance makes real-time mean information linear in time.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

/-- The actual mean information at unit scale, with zero diagonal. -/
def canonicalRootCoefficient (d : ℕ) (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (i j : Fin (d + 1)) : ℝ :=
  if hij : i = j then 0 else (rootInformationMean hij μ 1).toReal

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingProductKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A measurable version of the actual remaining-root product

This supplies measurability of the mass of a whole future atom, rather
than imposing measurability as an additional dynamical hypothesis.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

lemma measurableSet_remainingFutureRelation {n : ℕ}
    {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    (c : EliminationChain P D) (hf : c.finalEntries = allPositiveRoots n)
    (ell : Fin n → ℝ) (hell : ∑ k, ell k = 0) (Q : X n → ℕ)
    (hQ : Measurable Q) (m : ℕ) :
    MeasurableSet {z : X n × c.Time | z.2 ∈ c.remainingFutureAtom ell hell Q m z.1} := by
  let T : X n → X n := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  have hT : Measurable T := (continuous_rightAction _).measurable
  have hF : Measurable (fun z : X n × c.Time => rightAction z.1 (c.word z.2)) :=
    (continuous_rightAction_uncurry n).measurable.comp
      (measurable_fst.prodMk ((c.word_isEmbedding_remaining hf).continuous.measurable.comp
        measurable_snd))
  change MeasurableSet {z : X n × c.Time |
    ∀ k : ℕ, Q (T^[k+m] (rightAction z.1 (c.word z.2))) = Q (T^[k+m] z.1)}
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  exact measurableSet_eq_fun (hQ.comp ((hT.iterate (k+m)).comp hF))
    (hQ.comp ((hT.iterate (k+m)).comp measurable_fst))

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralAction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The neutral diagonal action on the lattice quotient

The concrete neutral weight subgroup acts continuously by right diagonal
translations. Its measure-preserving action follows from full diagonal
invariance, and every trace-zero neutral weight is represented in it.
-/

noncomputable section
open MeasureTheory Set
open scoped Topology Classical BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

@[instance_reducible] def neutralDiagonalAction {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    MulAction (Multiplicative (neutralWeightSubgroup i j)) (X n) :=
  let := rightSubgroupAction (rootPairCentralizer hij)
  MulAction.compHom (X n) (neutralDiagonalOppositeHom hij)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LocalInjectivityHeight
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A measurable chart height with bounded diagonal increments

Local quotient injectivity is encoded on a geometric sequence of radii.
The least admissible index is measurable and changes by at most one under
a fixed diagonal translation. This supplies chart-size control without
an integrability assumption on the height itself.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

def LocalInjectivityAt {n : ℕ} (r : ℝ) (x : X n) : Prop :=
  ∃ U : Set (X n), IsOpen U ∧ x ∈ U ∧
    ∀ y ∈ U, Set.InjOn (fun g => rightAction y g) (matrixBall n r)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RootPrefixFutureFibers
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive future fibers for the remaining-root product charts -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def fullRootTime (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots n) (t : c.Time) : UpperRootTime n :=
  (upperRootWordHomeomorph n).symm
    ⟨(c.remainingWordHomeomorph hP hf t).val,
      positiveRootGeneratedGroup_mono Finset.sdiff_subset
        (c.remainingWordHomeomorph hP hf t).prop⟩

end EliminationChain

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_FutureKernelCovariance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Covariance of the actual normalized future measures -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

namespace EliminationChain

def ambientFutureMeasure
    {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots n)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (ell : Fin n → ℝ) (hell : ∑ k, ell k=0)
    (Q : X n → ℕ) (m : ℕ) (x : X n) : Measure (X n) :=
  ((anchorNormalize (c.remainingTimeProduct hP hf μ x)
    (c.remainingFutureAtom ell hell Q m x)).restrict
    (c.remainingFutureAtom ell hell Q m x)).map (fun u => rightAction x (c.word u))

end EliminationChain

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixFactorChart
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual one-root transversals inside every remaining-group chart -/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

namespace RootPrefixCoordinates
variable {n : ℕ} (s : InitialRootStep n) {T : Type*} [TopologicalSpace T]
  (C : RootPrefixCoordinates n s.processed T) (g : G n)

abbrev FactorTransverse :=
  (UpperRootTransverse n × T) × positiveRootGeneratedGroup (s.remaining.erase s.root)

def factorBase (z : FactorTransverse s (T := T)) : G n :=
  g * (z.1.1.val * (C.base z.1.2 * z.2.val))

def factorPivotDomain (k : Fin n) : Set (FactorTransverse s (T := T)) :=
  {z | (C.factorBase s g z).val k s.root.1 ≠ 0}

def factorPivot (k : Fin n) (z : C.factorPivotDomain s g k) : RootPivot s.root.1 k :=
  ⟨C.factorBase s g z.val,z.prop⟩

def factorSlice (k : Fin n) (z : C.factorPivotDomain s g k) : RootSlice s.root.1 s.root.2 k :=
  rootSliceRepresentative s.distinct (C.factorPivot s g k z)

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingRootProductBoxes
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unconditional local product boxes at every ordered-root step -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

instance positiveRootGeneratedGroup_secondCountable {n : ℕ} (S : Finset (Fin n × Fin n)) :
    SecondCountableTopology (positiveRootGeneratedGroup S) := by
  let : SecondCountableTopology (G n) := inferInstance
  exact TopologicalSpace.secondCountableTopology_induced _ (G n) Subtype.val

namespace RootPrefixCoordinates
variable {n : ℕ} (q : InitialRootStep n) {T : Type*} [TopologicalSpace T]
  (C : RootPrefixCoordinates n q.processed T) (g : G n) (k : Fin n)

def factorTime (z : C.factorPivotDomain q g k) : ℝ :=
  rootParameter q.root.1 q.root.2 k (C.factorBase q g z.val)

def rectangleSlice (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) :
    Q.first × Q.second → RootSlice q.root.1 q.root.2 k := C.factorSlice q g k ∘ Q.inclusion

def rectangleTime (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) :
    Q.first × Q.second → ℝ := C.factorTime q g k ∘ Q.inclusion

end RootPrefixCoordinates

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_ExtremalRemainingEntries
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact entries of extremal-root conjugation on the remaining group -/

noncomputable section
open Matrix Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {n : ℕ}

lemma first_le (q : InitialRootStep n) (p : Fin n × Fin n) (hp : p ∈ q.remaining) :
    q.root.1 ≤ p.1 := by
  by_contra h
  exact not_lt_of_ge (q.least p hp)
    (Prod.Lex.toLex_lt_toLex.mpr (Or.inl (lt_of_not_ge h)))

lemma remaining_standard_column (q : InitialRootStep n)
    (g : positiveRootGeneratedGroup q.remaining) (i : Fin n) :
    g.val.val i q.root.1 = if i = q.root.1 then 1 else 0 := by
  have hnot : (i,q.root.1) ∉ q.remaining := by
    intro h
    exact not_lt_of_ge (q.first_le _ h) (q.remaining_positive _ h)
  exact positiveRootGeneratedGroup_pattern q.remaining q.remaining_closed g.prop i q.root.1 hnot

end InitialRootStep
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootRowShear
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugation by the next root is the product of its row shears -/

noncomputable section
open Matrix MeasureTheory Set
open scoped Classical
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {n : ℕ}

abbrev NextRoot (q : InitialRootStep n) := ↥(q.remaining.erase q.root)

end InitialRootStep
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NextGroupCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entry-coordinate homeomorphism for the next remaining root group -/

noncomputable section
open Matrix Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {n : ℕ}

lemma next_initial (q : InitialRootStep n) : InitialRootPattern (insert q.root q.processed) :=
  initialRootPattern_insert_min q.initial q.root q.mem_remaining q.least

lemma next_closed (q : InitialRootStep n) : ∀ a b c : Fin n,
    (a,b) ∈ q.remaining.erase q.root → (b,c) ∈ q.remaining.erase q.root →
    (a,c) ∈ q.remaining.erase q.root := by
  simpa only [remaining,initialRemaining_erase] using
    initialRemaining_roots_closed (insert q.root q.processed) q.next_initial

lemma exists_nextGroupCoordinates (q : InitialRootStep n) :
    ∃ E : positiveRootGeneratedGroup (q.remaining.erase q.root) ≃ₜ (q.NextRoot → ℝ),
      ∀ g p, E g p = g.val.val p.val.1 p.val.2 := by
  obtain ⟨c,hc⟩ := exists_complete_elimination_chain_from_initial
    (insert q.root q.processed) ∅ q.next_initial (by intro a ha; simp at ha)
  have h : ∃ E : positiveRootGeneratedGroup (allPositiveRoots n \ insert q.root q.processed) ≃ₜ
      (↥(allPositiveRoots n \ insert q.root q.processed) → ℝ),
      ∀ g p, E g p = g.val.val p.val.1 p.val.2 :=
    ⟨c.remainingGroupCoordinates q.next_initial hc,c.remainingGroupCoordinates_apply q.next_initial hc⟩
  have hT : allPositiveRoots n \ insert q.root q.processed = q.remaining.erase q.root :=
    (initialRemaining_erase q.processed q.root).symm
  rw [hT] at h
  exact h

def nextGroupCoordinates (q : InitialRootStep n) :
    positiveRootGeneratedGroup (q.remaining.erase q.root) ≃ₜ (q.NextRoot → ℝ) :=
  q.exists_nextGroupCoordinates.choose

end InitialRootStep
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NextGroupConjugation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugation preserves the intrinsic product on the actual next subgroup -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep

lemma next_conjugation_mem (d : ℕ) (q : InitialRootStep (d+1))
    (g : positiveRootGeneratedGroup (q.remaining.erase q.root)) (r : ℝ) :
    Matrix.SpecialLinearGroup.transvection q.distinct (-r) * g.val *
      Matrix.SpecialLinearGroup.transvection q.distinct r ∈
        positiveRootGeneratedGroup (q.remaining.erase q.root) := by
  let w : positiveRootGeneratedGroup q.remaining :=
    ⟨g.val,positiveRootGeneratedGroup_mono (Finset.erase_subset _ _) g.prop⟩
  let u : positiveRootGeneratedGroup q.remaining :=
    ⟨Matrix.SpecialLinearGroup.transvection q.distinct (-r),
      transvection_mem_positiveRootGeneratedGroup _ q.distinct q.mem_remaining (-r)⟩
  have hg : w ∈ (positiveRootGeneratedGroup (q.remaining.erase q.root)).comap
      (positiveRootGeneratedGroup q.remaining).subtype := g.prop
  have hn := (q.next_normal d).conj_mem w hg u
  change u.val * w.val * u.val⁻¹ ∈ positiveRootGeneratedGroup (q.remaining.erase q.root) at hn
  simpa only [u,w,Matrix.SpecialLinearGroup.transvection_inv,neg_neg] using hn

def nextConjugation (d : ℕ) (q : InitialRootStep (d+1)) (r : ℝ)
    (g : positiveRootGeneratedGroup (q.remaining.erase q.root)) :
    positiveRootGeneratedGroup (q.remaining.erase q.root) :=
  ⟨Matrix.SpecialLinearGroup.transvection q.distinct (-r) * g.val *
    Matrix.SpecialLinearGroup.transvection q.distinct r,q.next_conjugation_mem d g r⟩

lemma continuous_nextConjugation (d : ℕ) (q : InitialRootStep (d+1)) (r : ℝ) :
    Continuous (q.nextConjugation d r) :=
  ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

def nextIntrinsicProduct (d : ℕ) (q : InitialRootStep (d+1))
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ] (x : X (d+1)) :
    Measure (positiveRootGeneratedGroup (q.remaining.erase q.root)) :=
  (Measure.pi fun p : q.NextRoot =>
    intrinsicRootLeaf (ne_of_lt (q.remaining_positive p.val (Finset.mem_erase.mp p.prop).2)) μ x).map
      q.nextGroupCoordinates.symm

end InitialRootStep

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingProductReorder
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Moving the selected root through the actual remaining product -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Function
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep

lemma continuous_conjugationSkew (d : ℕ) (q : InitialRootStep (d+1)) :
    Continuous (fun z : ℝ × positiveRootGeneratedGroup (q.remaining.erase q.root) =>
      (z.1,q.nextConjugation d z.1 z.2)) := by
  have hU := continuous_rootTransvection q.distinct
  apply continuous_fst.prodMk
  exact (((hU.comp continuous_fst.neg).mul
    (continuous_subtype_val.comp continuous_snd)).mul (hU.comp continuous_fst)).subtype_mk _

def rootBeforeRemaining (d : ℕ) (q : InitialRootStep (d+1))
    (z : ℝ × positiveRootGeneratedGroup (q.remaining.erase q.root)) : G (d+1) :=
  Matrix.SpecialLinearGroup.transvection q.distinct z.1 * z.2.val

def remainingBeforeRoot (d : ℕ) (q : InitialRootStep (d+1))
    (z : positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ) : G (d+1) :=
  z.1.val * Matrix.SpecialLinearGroup.transvection q.distinct z.2

end InitialRootStep

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootOrderCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The homeomorphism exchanging the selected root and remaining group -/

noncomputable section
open Matrix MeasureTheory
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep

lemma nextConjugation_neg_cancel (d : ℕ) (q : InitialRootStep (d+1)) (r : ℝ)
    (w : positiveRootGeneratedGroup (q.remaining.erase q.root)) :
    q.nextConjugation d r (q.nextConjugation d (-r) w) = w := by
  apply Subtype.ext
  change Matrix.SpecialLinearGroup.transvection q.distinct (-r) *
      (Matrix.SpecialLinearGroup.transvection q.distinct (-(-r)) * w.val *
        Matrix.SpecialLinearGroup.transvection q.distinct (-r)) *
      Matrix.SpecialLinearGroup.transvection q.distinct r = w.val
  rw [neg_neg,←Matrix.SpecialLinearGroup.transvection_inv]
  group

def rootOrderCoordinates (d : ℕ) (q : InitialRootStep (d+1)) :
    (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ) ≃ₜ
      (ℝ × positiveRootGeneratedGroup (q.remaining.erase q.root)) where
  toFun z := (z.2,q.nextConjugation d z.2 z.1)
  invFun z := (q.nextConjugation d (-z.1) z.2,z.1)
  left_inv z := by
    apply Prod.ext
    · simpa only [neg_neg] using q.nextConjugation_neg_cancel d (-z.2) z.1
    · rfl
  right_inv z := by
    apply Prod.ext
    · rfl
    · exact q.nextConjugation_neg_cancel d z.1 z.2
  continuous_toFun := (q.continuous_conjugationSkew d).comp continuous_swap
  continuous_invFun := by
    have h := (q.continuous_conjugationSkew d).comp (continuous_fst.neg.prodMk continuous_snd)
    exact h.snd.prodMk continuous_fst

end InitialRootStep
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_PrefixRootConditionals
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nested conditionals in exchanged prefix-root coordinates -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {S : Type*} [MeasurableSpace S]

def prefixRootExchange (d : ℕ) (q : InitialRootStep (d+1))
    (z : S × (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)) :
    (S × ℝ) × positiveRootGeneratedGroup (q.remaining.erase q.root) :=
  ((z.1,z.2.2),q.nextConjugation d z.2.2 z.2.1)

end InitialRootStep
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_PrefixPointConditionals
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exchanged conditional measures at almost every original sample -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {S : Type*} [MeasurableSpace S]

def nextConjugatedKernel (d : ℕ) (q : InitialRootStep (d+1))
    (κ : Kernel S (positiveRootGeneratedGroup (q.remaining.erase q.root))) [IsSFiniteKernel κ] :
    Kernel (S × ℝ) (positiveRootGeneratedGroup (q.remaining.erase q.root)) where
  toFun z := (κ z.1).map (q.nextConjugation d z.2)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro U hU
    have H := Kernel.measurable_kernel_prodMk_left (κ := Kernel.prodMkRight ℝ κ)
      (((q.continuous_conjugationSkew d).snd.measurable.comp
        (measurable_fst.snd.prodMk measurable_snd)) hU)
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    exact Measure.map_apply (q.continuous_nextConjugation d z.2).measurable hU

instance nextConjugatedKernel_markov (d : ℕ) (q : InitialRootStep (d+1))
    (κ : Kernel S (positiveRootGeneratedGroup (q.remaining.erase q.root))) [IsMarkovKernel κ] :
    IsMarkovKernel (q.nextConjugatedKernel d κ) where
  isProbabilityMeasure z := by
    change IsProbabilityMeasure ((κ z.1).map (q.nextConjugation d z.2))
    apply (Measure.isProbabilityMeasure_map_iff
      (q.continuous_nextConjugation d z.2).measurable.aemeasurable).mpr
    first | exact Measure.isProbabilityMeasure_map (by first | (apply Continuous.aemeasurable; apply q.continuous_nextConjugation <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end InitialRootStep
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralTransverseCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual neutral coordinate in the upper-root chart

On the positive-diagonal chart the transverse slice is the product of its
unit-diagonal part and the trace-zero logarithmic diagonal. Right diagonal
translation fixes the first coordinate and translates the second. This is
the local center coordinate needed for comparison with the root kernel.
-/

noncomputable section
open Matrix Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

abbrev UnitDiagonalTransverse (n : ℕ) :=
  {s : UpperRootTransverse n // ∀ i, s.val.val i i=1}

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralUpperRootChart
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Move the neutral coordinate to the right of the root coordinate

The parametrization is now lower-unitriangular, upper-unipotent, diagonal.
Consequently right translation by the diagonal group is translation in the
last coordinate, with the other two coordinates fixed.
-/

noncomputable section
open Matrix Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

namespace EliminationChain

theorem continuous_rootDilation {n : ℕ} {P : Finset (Fin n × Fin n)}
    {D : Finset (Fin n)} (c : EliminationChain P D)
    {Y : Type*} [TopologicalSpace Y]
    (ell : Y → Fin n → ℝ) (r : Y → ℝ) (u : Y → c.Time)
    (hell : Continuous ell) (hr : Continuous r) (hu : Continuous u) :
    Continuous (fun y => c.rootDilation (ell y) (r y) (u y)) := by
  induction c with
  | done => exact hu
  | step a b hab hP hb tail ih =>
      change Continuous (fun y =>
        (tail.rootDilation (ell y) (r y) (u y).1,
          Real.exp (((ell y) a-(ell y) b)*r y)*(u y).2))
      exact (ih _ hu.fst).prodMk
        ((Real.continuous_exp.comp ((((continuous_apply a).comp hell).sub
          ((continuous_apply b).comp hell)).mul hr)).mul hu.snd)

end EliminationChain

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralCoordinateMeasure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Translation invariance in the actual neutral product chart -/

noncomputable section
open MeasureTheory Set
open scoped Topology ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

abbrev NeutralCoordinateBase (n : ℕ) := UnitDiagonalTransverse n × UpperRootTime n

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PhysicalRootRectangles
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical root rectangles represent the actual ambient measure -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

variable {T B : Type*} [MeasurableSpace T] [MeasurableSpace B]

def physicalRootCoordinates {n : ℕ} {a b k : Fin n}
    (e : T × B → RootSlice a b k) (τ : T × B → ℝ) (z : T × (B × ℝ)) :
    RootSlice a b k × ℝ := (e (z.1,z.2.1),z.2.2 + τ (z.1,z.2.1))

def physicalRootParam {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (e : T × B → RootSlice a b k) (τ : T × B → ℝ) : T × (B × ℝ) → X n :=
  rootQuotientParametrization hab ∘ physicalRootCoordinates e τ

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixReorder
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The root-order exchange in the actual quotient parametrizations -/

noncomputable section
open Matrix MeasureTheory Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {n : ℕ}

def nextGroupCast (q : InitialRootStep n) :
    positiveRootGeneratedGroup (q.remaining.erase q.root) ≃ₜ
      positiveRootGeneratedGroup (allPositiveRoots n \ insert q.root q.processed) :=
  Homeomorph.setCongr (by rw [remaining,initialRemaining_erase])

@[simp] lemma nextGroupCast_val (q : InitialRootStep n)
    (w : positiveRootGeneratedGroup (q.remaining.erase q.root)) :
    (q.nextGroupCast w).val = w.val := rfl

end InitialRootStep
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NextProductChain
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The next intrinsic product in any extended-prefix Gaussian chart -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {n : ℕ}

def nextRootIndex (q : InitialRootStep n) :
    q.NextRoot ≃ ↥(allPositiveRoots n \ insert q.root q.processed) where
  toFun p := ⟨p.val,by simpa only [remaining,initialRemaining_erase] using p.prop⟩
  invFun p := ⟨p.val,by simpa only [remaining,initialRemaining_erase] using p.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

end InitialRootStep
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingProductCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting off the next root in the actual product coordinates -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Classical
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {n : ℕ}

def rootOptionIndex (q : InitialRootStep n) : Option q.NextRoot ≃ ↥q.remaining where
  toFun p := match p with
    | none => ⟨q.root,q.mem_remaining⟩
    | some p => ⟨p.val,(Finset.mem_erase.mp p.prop).2⟩
  invFun p := if h : p.val = q.root then none else some ⟨p.val,Finset.mem_erase.mpr ⟨h,p.prop⟩⟩
  left_inv p := by
    cases p with
    | none => simp
    | some p => simp [(Finset.mem_erase.mp p.prop).1]
  right_inv p := by
    dsimp
    split_ifs with h
    · exact Subtype.ext h.symm
    · rfl

def splitRootCoordinates (q : InitialRootStep n) :
    (↥q.remaining → ℝ) ≃ᵐ ((q.NextRoot → ℝ) × ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : ↥q.remaining => ℝ) q.rootOptionIndex).symm.trans
    (MeasurableEquiv.piOptionEquivProd (fun _ => ℝ))

def remainingFactor (q : InitialRootStep n) :
    (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ) ≃ₜ
      positiveRootGeneratedGroup q.remaining :=
  positiveRootRightFactorHomeomorph q.remaining q.remaining_positive q.remaining_closed
    q.distinct q.mem_remaining q.next_closed

lemma remainingFactor_val (q : InitialRootStep n)
    (z : positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ) :
    (q.remainingFactor z).val = z.1.val * Matrix.SpecialLinearGroup.transvection q.distinct z.2 := rfl

end InitialRootStep
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootFiberReference
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common sampled reference on each independent root fiber -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {S : Type*} [MeasurableSpace S]

def rootFiberPoint (d : ℕ) (q : InitialRootStep (d+1)) (b : S → X (d+1))
    (z : S × (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)) : X (d+1) :=
  rightAction (b z.1) (q.remainingBeforeRoot d z.2)

end InitialRootStep
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootRectangleInclusion
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Including an independent rectangle in the actual remaining subgroup -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep
variable {S B : Type*} [MeasurableSpace S] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]

def includeRootRectangle (d : ℕ) (q : InitialRootStep (d+1))
    (i : B → positiveRootGeneratedGroup (q.remaining.erase q.root))
    (z : S × (B × ℝ)) : S × (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ) :=
  (z.1,(i z.2.1,z.2.2))

end InitialRootStep
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_ConjugationRestrictions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized restrictions under extremal conjugation -/

noncomputable section
open Matrix MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep

def nextConjugationHomeomorph (d : ℕ) (q : InitialRootStep (d+1)) (r : ℝ) :
    positiveRootGeneratedGroup (q.remaining.erase q.root) ≃ₜ
      positiveRootGeneratedGroup (q.remaining.erase q.root) where
  toFun := q.nextConjugation d r
  invFun := q.nextConjugation d (-r)
  left_inv w := by simpa only [neg_neg] using q.nextConjugation_neg_cancel d (-r) w
  right_inv := q.nextConjugation_neg_cancel d r
  continuous_toFun := q.continuous_nextConjugation d r
  continuous_invFun := q.continuous_nextConjugation d (-r)

end InitialRootStep
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingFactorRebase
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rebasing the actual product of remaining-root coordinates -/

noncomputable section
open Matrix MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep

def nextFactorRebase (d : ℕ) (q : InitialRootStep (d+1))
    (w : positiveRootGeneratedGroup (q.remaining.erase q.root)) (s : ℝ) :
    positiveRootGeneratedGroup (q.remaining.erase q.root) ≃ₜ
      positiveRootGeneratedGroup (q.remaining.erase q.root) :=
  (Homeomorph.mulLeft w⁻¹).trans (q.nextConjugationHomeomorph d s)

end InitialRootStep
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingGroupCenter
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Centered Gaussian coordinates with values in the actual subgroup -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def remainingGroupCenter (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots n) (t : c.Time) :
    c.Time ≃ₜ positiveRootGeneratedGroup (allPositiveRoots n \ P) :=
  (c.remainingWordHomeomorph hP hf).trans
    (Homeomorph.mulLeft (c.remainingWordHomeomorph hP hf t)⁻¹)

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_WholeFutureProbabilityKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A probability kernel on the entire subordinate future

The intrinsic product has an s-finite measurable version. Restricting it
on the jointly measurable future relation and normalizing gives an actual
probability kernel. On the exceptional zero/infinite-mass set we use a
point mass; the intrinsic formula holds almost everywhere whenever the
proved positive finite future-mass condition applies.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def futureRestrictedKernel (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots n)
    (κ : Kernel (X n) c.Time) [IsSFiniteKernel κ]
    (ell : Fin n → ℝ) (hell : ∑ k, ell k=0) (Q : X n → ℕ)
    (hQ : Measurable Q) (m : ℕ) : Kernel (X n) c.Time where
  toFun x := (κ x).restrict (c.remainingFutureAtom ell hell Q m x)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    simp_rw [Measure.restrict_apply hA]
    exact Kernel.measurable_kernel_prodMk_left
      ((measurable_snd hA).inter (c.measurableSet_remainingFutureRelation hf ell hell Q hQ m))

def futureNormalizedKernel (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots n)
    (κ : Kernel (X n) c.Time) [IsSFiniteKernel κ]
    (ell : Fin n → ℝ) (hell : ∑ k, ell k=0) (Q : X n → ℕ)
    (hQ : Measurable Q) (m : ℕ) : Kernel (X n) c.Time where
  toFun x :=
    let ν := c.futureRestrictedKernel hf κ ell hell Q hQ m x
    (ν univ)⁻¹ • ν
  measurable' := by
    let ν := c.futureRestrictedKernel hf κ ell hell Q hQ m
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    change Measurable (fun x => (ν x univ)⁻¹ * ν x A)
    exact (ν.measurable_coe MeasurableSet.univ).inv.mul (ν.measurable_coe hA)

/-- Normalize where the full-future mass is positive finite, using a
fixed point mass on the remaining measurable exceptional set. -/
def wholeFutureProbabilityKernel (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots n)
    (κ : Kernel (X n) c.Time) [IsSFiniteKernel κ]
    (ell : Fin n → ℝ) (hell : ∑ k, ell k=0) (Q : X n → ℕ)
    (hQ : Measurable Q) (m : ℕ) : Kernel (X n) c.Time :=
  let ν := c.futureRestrictedKernel hf κ ell hell Q hQ m
  have hgood : MeasurableSet {x | ν x univ ≠ 0 ∧ ν x univ ≠ ∞} :=
    (measurableSet_eq_fun (ν.measurable_coe MeasurableSet.univ) measurable_const).compl.inter
      (measurableSet_eq_fun (ν.measurable_coe MeasurableSet.univ) measurable_const).compl
  Kernel.piecewise hgood
    (c.futureNormalizedKernel hf κ ell hell Q hQ m)
    (Kernel.const (X n) (Measure.dirac c.zeroTime))

instance wholeFutureProbabilityKernel_markov (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots n)
    (κ : Kernel (X n) c.Time) [IsSFiniteKernel κ]
    (ell : Fin n → ℝ) (hell : ∑ k, ell k=0) (Q : X n → ℕ)
    (hQ : Measurable Q) (m : ℕ) :
    IsMarkovKernel (c.wholeFutureProbabilityKernel hf κ ell hell Q hQ m) := by
  refine ⟨fun x => ⟨?_⟩⟩
  change (if (c.futureRestrictedKernel hf κ ell hell Q hQ m x) univ ≠ 0 ∧
      (c.futureRestrictedKernel hf κ ell hell Q hQ m x) univ ≠ ∞ then
      c.futureNormalizedKernel hf κ ell hell Q hQ m x else Measure.dirac c.zeroTime) univ = 1
  split_ifs with hx
  · change ((c.futureRestrictedKernel hf κ ell hell Q hQ m x univ)⁻¹ •
      c.futureRestrictedKernel hf κ ell hell Q hQ m x) univ = 1
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hx.1 hx.2
  · simp

/-- Push a time-coordinate kernel to the actual right root orbits. -/
def futureAmbientKernel (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots n)
    (κ : Kernel (X n) c.Time) [IsSFiniteKernel κ] : Kernel (X n) (X n) where
  toFun x := (κ x).map (fun u => rightAction x (c.word u))
  measurable' := by
    have hF : Measurable (fun z : X n × c.Time => rightAction z.1 (c.word z.2)) :=
      (continuous_rightAction_uncurry n).measurable.comp
        (measurable_fst.prodMk ((c.word_isEmbedding_remaining hf).continuous.measurable.comp
          measurable_snd))
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    change Measurable (fun x => ((κ x).map (fun u => rightAction x (c.word u))) A)
    have heq (x : X n) : ((κ x).map (fun u => rightAction x (c.word u))) A =
        κ x ((fun u => rightAction x (c.word u)) ⁻¹' A) :=
      Measure.map_apply (hF.comp measurable_prodMk_left) hA
    simp_rw [heq]
    exact Kernel.measurable_kernel_prodMk_left (hF hA)

instance futureAmbientKernel_markov (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots n)
    (κ : Kernel (X n) c.Time) [IsMarkovKernel κ] :
    IsMarkovKernel (c.futureAmbientKernel hf κ) := by
  refine ⟨fun x => ⟨?_⟩⟩
  have hF : Measurable (fun u => rightAction x (c.word u)) :=
    ((continuous_rightAction_uncurry n).comp
      (continuous_const.prodMk (c.word_isEmbedding_remaining hf).continuous)).measurable
  change (κ x).map (fun u => rightAction x (c.word u)) univ = 1
  rw [Measure.map_apply hF MeasurableSet.univ,Set.preimage_univ,measure_univ]

end EliminationChain

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_FiniteProjectionFrames
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite frame selection by Gram determinants

The projected coordinate vectors form a finite measurable spanning family.
Maximal nonzero Gram minors select a basis from that family. All tests used
in the selection are measurable real determinants, so this does not assume
a measurable tangent-frame theorem.
-/

noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators InnerProductSpace

namespace DukePrimeDegree

section GramFrames

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def IsMaximalGramFrame (v : I → E) (S : Finset I) : Prop :=
  finiteGramDet v S ≠ 0 ∧
    ∀ T : Finset I, S.card < T.card → finiteGramDet v T = 0

end GramFrames

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RegularRootSymmetry
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite regular entropy tests and prime-degree rigidity

The finite regular entropy identities balance incoming and outgoing root
coefficients. This makes the invariant-root relation symmetric, yielding
Haar classification in prime degree when regular entropy is positive.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

/-- The finite family of entropy identities used by the prime-degree
application.  Both time directions are retained explicitly. -/
def CanonicalRegularEntropyTests (d : ℕ) (μ : Measure (X (d + 1)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ a : Option (Fin (d + 1)),
    measureEntropy μ (fun x => rightAction x
      (diagonalOneParameter (regularEntropyTest d a) (regularEntropyTest_sum d a) 1)) =
        ENNReal.ofReal (rootEntropyForm (canonicalRootCoefficient d μ) (regularEntropyTest d a)) ∧
    measureEntropy μ (fun x => rightAction x
      (diagonalOneParameter (regularEntropyTest d a) (regularEntropyTest_sum d a) (-1))) =
        ENNReal.ofReal (rootEntropyForm (canonicalRootCoefficient d μ)
          (fun i => -regularEntropyTest d a i))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RegularRootEntropySandwich
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regular entropy lower bounds and the upper-bound criterion

The expanding-root kernel gives one chamber's lower bound. Weyl
covariance transports it to the opposite chamber. The finite regular
upper estimates therefore imply the entropy identities and coefficient
balance required by prime-degree rigidity.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

/-- The finite regular upper estimates, expressed without entropy identities. -/
def CanonicalRegularEntropyUpperBounds (d : ℕ) (μ : Measure (X (d + 1)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ a : Option (Fin (d + 1)),
    measureEntropy μ (fun x => rightAction x
      (diagonalOneParameter (regularEntropyTest d a) (regularEntropyTest_sum d a) 1)) ≤
        ENNReal.ofReal (rootEntropyForm (canonicalRootCoefficient d μ) (regularEntropyTest d a)) ∧
    measureEntropy μ (fun x => rightAction x
      (diagonalOneParameter (regularEntropyTest d a) (regularEntropyTest_sum d a) (-1))) ≤
        ENNReal.ofReal (rootEntropyForm (canonicalRootCoefficient d μ)
          (fun i => -regularEntropyTest d a i))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_DecompositionField
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Decomposition field

The decomposition field is the fixed field of the decomposition group.  This
formulation uses absolute values and therefore includes the archimedean case.
-/

noncomputable section

universe u v

namespace HilbertRamification

open scoped Pointwise Topology

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The decomposition group is closed in the Krull topology.  A failure to
preserve the valuation class is witnessed by one element `x`; the coset of
the open subgroup fixing `K(x)` is then contained in the complement. -/
theorem absoluteValueDecompositionGroup_isClosed
    [Algebra.IsAlgebraic K L] (w : AbsoluteValue L ℝ) :
    IsClosed (absoluteValueDecompositionGroup K w : Set (L ≃ₐ[K] L)) where
  isOpen_compl := isOpen_iff_mem_nhds.mpr fun σ hσ => by
    rw [Set.mem_compl_iff, SetLike.mem_coe,
      mem_absoluteValueDecompositionGroup_iff] at hσ
    rcases Classical.not_forall.mp hσ with ⟨x, hx⟩
    let E : IntermediateField K L := IntermediateField.adjoin K {x}
    let : FiniteDimensional K E :=
      IntermediateField.adjoin.finiteDimensional
        (Algebra.IsIntegral.isIntegral x)
    apply mem_nhds_iff.mpr
    refine ⟨σ • (E.fixingSubgroup : Set (L ≃ₐ[K] L)), ?_, ?_, ?_⟩
    · intro τ hτ
      rcases Set.mem_smul_set.mp hτ with ⟨g, hg, rfl⟩
      rw [Set.mem_compl_iff, SetLike.mem_coe,
        mem_absoluteValueDecompositionGroup_iff]
      intro hmem
      apply hx
      have hgx : g x = x :=
        (IntermediateField.mem_fixingSubgroup_iff E g).mp hg x
          (IntermediateField.subset_adjoin (F := K) (S := {x}) (by simp))
      simpa [AlgEquiv.mul_apply, hgx] using hmem x
    · exact E.fixingSubgroup_isOpen.smul σ
    · exact ⟨1, E.fixingSubgroup.one_mem, by simp⟩

end HilbertRamification
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_Dedekind_PrimeContractions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Hilbert ramification theory: number-field prime contractions

This file specializes the fixed fields `Z_P` and `T_P` to rings of integers
of number fields and defines the contracted primes `p`, `P_Z`, and `P_T`.
-/

noncomputable section

namespace HilbertRamification
namespace Dedekind

open Algebra NumberField
open scoped Pointwise

attribute [local instance] Ideal.Quotient.field

variable {K L : Type*}
variable [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable (G : Type*) [Group G] [MulSemiringAction G L] [SMulCommClass G K L]

/-- The top prime lies over its contraction to the base ring of integers. -/
instance basePrime_liesOver
    (P : Ideal (𝓞 L)) :
    P.LiesOver (basePrime (K := K) P) :=
  ⟨rfl⟩

end Dedekind
end HilbertRamification
end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Topology_AdicCompletionInverseLimitRing
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Adic completion and inverse limits

This file contains the algebraic and topological projective-limit descriptions
of adically complete rings, complete discrete valuation rings, and their unit
groups.
-/

noncomputable section

namespace LubinTate
namespace Valuations

open ValuationTheory.DiscreteValuationField
open ValuationTheory.Valuations
open Filter Set Topology
open scoped Valued

namespace DiscreteAdicQuotient

/-- A discrete adic quotient inherits its commutative ring structure from the concrete quotient. -/
instance instCommRing {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    CommRing (DiscreteAdicQuotient I n) :=
  (equiv I n).commRing

end DiscreteAdicQuotient

/-- The canonical prodiscrete topology on the all-level inverse limit.  The
finite quotient stages are discrete inside this one representation boundary;
their raw topology instances do not escape into public theorem statements. -/
noncomputable instance adicQuotientInverseLimit.instTopologicalSpace
    {R : Type*} [CommRing R] (I : Ideal R) :
    TopologicalSpace (adicQuotientInverseLimit I) := by
  letI : (n : ℕ) → TopologicalSpace (R ⧸ I ^ n) := fun _ => ⊥
  exact (adicQuotientInverseLimitCompatibleFamiliesEquiv I).topologicalSpace

end Valuations
end LubinTate
end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_Topology_AdicCompletionInverseLimit
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Adic unit and higher-unit inverse limits

This file contains the algebraic and topological projective-limit descriptions
of unit groups of adically complete rings and complete discrete valuation
rings.  The underlying adic ring inverse-limit theory lives in
`AdicCompletionInverseLimitRing`.
-/

noncomputable section

namespace LubinTate
namespace Valuations

universe u v

open ValuationTheory.DiscreteValuationField
open ValuationTheory.Valuations
open Filter Set Topology
open scoped Valued

namespace DiscreteHigherUnitQuotient

/-- A discrete higher-unit quotient inherits its commutative group structure
from the concrete quotient. -/
instance instCommGroup {O : Type*} [CommRing O] (π : O) (n : ℕ) :
    CommGroup (DiscreteHigherUnitQuotient π n) :=
  (equiv π n).commGroup

end DiscreteHigherUnitQuotient

/-! ### Direct complete-valued-field form of the adic inverse-limit equivalence -/

end Valuations
end LubinTate
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RationalComplexification
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The rational cyclotomic complexification

This module realizes the quadratic complexification as the fourth-root
cyclotomic field and proves the rational principal-idele Artin formula.
-/

open scoped BigOperators Classical IsMulCommutative NumberField
open NumberField IsDedekindDomain
open IdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

local instance rationalComplexificationPrimeFact_r796ff1_1 :
    Fact rationalComplexificationPrime.1.Prime :=
  ⟨rationalComplexificationPrime.2⟩
local instance rationalComplexificationPrimeSquareNeZero :
    NeZero (rationalComplexificationPrime.1 ^ 2) :=
  ⟨pow_ne_zero 2 rationalComplexificationPrime.2.ne_zero⟩

/-- The concrete fourth-root field is stable under complex
conjugation. -/
theorem complexFourthRootField_map_complexConjugation :
    complexFourthRootField.map
        (Complex.conjAe.restrictScalars ℚ).toAlgHom =
      complexFourthRootField := by
  rw [complexFourthRootField, IntermediateField.adjoin_map]
  congr 1
  ext z
  constructor
  · rintro ⟨x, ⟨n, hn, hn0, hx⟩, rfl⟩
    refine ⟨n, hn, hn0, ?_⟩
    rw [← map_pow, hx, map_one]
  · intro hz
    refine ⟨star z, ?_, ?_⟩
    rcases hz with ⟨n, hn, hn0, hz⟩
    refine ⟨n, hn, hn0, ?_⟩
    rw [← star_pow, hz, star_one]
    change star (star z) = z
    exact star_star z

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitNormQuotient
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite norm quotients for rational fixed fields

The abstract finite norm subgroup and quotient are identified with the
ordinary idele-class norm range and quotient of the actual fixed-field extension.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology

noncomputable def additiveQuotientEquiv
    {G : Type*} [CommGroup G] (H : Subgroup G) :
    (Additive G ⧸ H.toAddSubgroup) ≃+
      Additive (G ⧸ H) := by
  let normAdd : Additive G →+ Additive (G ⧸ H) :=
    MonoidHom.toAdditive (QuotientGroup.mk' H)
  let T := normAdd.ker
  have hT : H.toAddSubgroup = T := by
    ext g
    change
      Additive.toMul g ∈ H ↔
        QuotientGroup.mk' H (Additive.toMul g) = 1
    exact (QuotientGroup.eq_one_iff (Additive.toMul g)).symm
  have hmap :
      H.toAddSubgroup.map
          (AddEquiv.refl (Additive G)).symm.toAddMonoidHom = T := by
    change
      H.toAddSubgroup.map (AddMonoidHom.id (Additive G)) = T
    rw [AddSubgroup.map_id]
    exact hT
  let modelEquiv :
      (Additive G ⧸ H.toAddSubgroup) ≃+
        (Additive G ⧸ T) :=
    quotientAddEquivOfEquivMapEq
      H.toAddSubgroup T (AddEquiv.refl (Additive G)) hmap
  have hsurjective : Function.Surjective normAdd := by
    intro q
    obtain ⟨g, hg⟩ :=
      QuotientGroup.mk'_surjective H (Additive.toMul q)
    refine ⟨Additive.ofMul g, ?_⟩
    apply Additive.toMul.injective
    change QuotientGroup.mk' H g = Additive.toMul q
    exact hg
  exact modelEquiv.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      normAdd hsurjective)

noncomputable def quotientAddEquivOfEquivMapEqToQuotient
    {A G : Type*} [AddCommGroup A] [CommGroup G]
    (S : AddSubgroup A) (N : Subgroup G) [N.Normal]
    (e : Additive G ≃+ A)
    (hmap : S.map e.symm.toAddMonoidHom = N.toAddSubgroup) :
    (A ⧸ S) ≃+ Additive (G ⧸ N) :=
  (quotientAddEquivOfEquivMapEq S N.toAddSubgroup e hmap).trans
    (additiveQuotientEquiv N)

noncomputable def addEquivTransQuotientOfEquivMapEq
    {Q A G : Type*}
    [AddCommGroup Q] [AddCommGroup A] [CommGroup G]
    (S : AddSubgroup A) (N : Subgroup G) [N.Normal]
    (eConcrete : Q ≃+ (A ⧸ S)) (e : Additive G ≃+ A)
    (hmap : S.map e.symm.toAddMonoidHom = N.toAddSubgroup) :
    Q ≃+ Additive (G ⧸ N) :=
  eConcrete.trans
    (quotientAddEquivOfEquivMapEqToQuotient S N e hmap)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_SUnitPowerQuotient
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Power quotients of S-unit groups

The finite `n`-th-power quotient of an `S`-unit group, its cardinality, and explicit `ZMod n` coordinates.
-/

open scoped NumberField Classical IsMulCommutative NNReal ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace KummerTheory

variable {K : Type*} [Field K]
    [numberFieldK : NumberField K]

/-- The number of places in the `S`-unit theorem is one more than the
free rank of the `S`-unit group.  The extra coordinate is the
roots-of-unity coordinate. -/
theorem totalPlaceCard_eq_sUnitLogRank_add_one
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    totalPlaceCard (K := K) S =
      SUnitGroup.logRank (K := K) S + 1 := by
  unfold totalPlaceCard SUnitGroup.logRank
  have hinfinite :
      0 < Fintype.card (InfinitePlace K) :=
    Fintype.card_pos
  omega

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PadicPowerIndex
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The `n`-fold multiple quotient of `Z_p`

This is the free p-adic factor in the local-field structure theory, the local-field power-index formula.
-/

noncomputable section

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory

namespace LocalFieldTheory.DiscreteValuationField

variable {p : ℕ} [Fact p.Prime]

/-- If `n` is nonzero and prime to `p`, the quotient of an arbitrary product
of copies of `Z_p` is finite (indeed, a singleton). -/
noncomputable instance finite_padicInt_pi_nsmulQuotient_of_coprime
    {ι : Type u} (n : ℕ) [NeZero n] [Fact (Nat.Coprime n p)] :
    Finite ((ι → ℤ_[p]) ⧸ LocalFieldTheory.nsmulAddSubgroup (ι → ℤ_[p]) n) := by
  have hpnd : ¬ p ∣ n :=
    (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp
      (Fact.out : Nat.Coprime n p).symm
  have hv : padicValNat p n = 0 :=
    padicValNat.eq_zero_of_not_dvd hpnd
  let target := ι → ZMod (p ^ padicValNat p n)
  let toUnit : target → PUnit := fun _ => PUnit.unit
  have hsub : Subsingleton target := by
    dsimp only [target]
    rw [hv, pow_zero]
    infer_instance
  let : Finite target :=
    Finite.of_injective toUnit fun x y _ => hsub.elim x y
  exact Finite.of_equiv target
    (padicIntPiNsmulQuotientEquiv
      (p := p) (ι := ι) n (NeZero.ne n)).symm.toEquiv

end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_Dedekind_CompositumUnramified
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Unramifiedness in a compositum

This file contains reusable criteria for proving that a prime in a number
field compositum is unramified from the inertia groups of its two factors.
-/

noncomputable section

namespace HilbertRamification.Dedekind

open NumberField
open scoped NumberField

attribute [local instance] Ideal.Quotient.field

/-- Algebraic unramifiedness at a prime of a finite Galois number-field
extension forces the corresponding inertia group to be trivial. -/
theorem inertiaGroup_eq_bot_of_isUnramifiedAt
    {K M : Type*}
    [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (P : Ideal (𝓞 M)) [P.IsPrime] [P.IsMaximal]
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) P) :
    inertiaGroup P Gal(M/K) = ⊥ := by
  let p : Ideal (𝓞 K) := P.under (𝓞 K)
  let : p.IsPrime := inferInstance
  let : P.LiesOver p := ⟨rfl⟩
  have hP0 : P ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (M := P) inferInstance (RingOfIntegers.not_isField M)
  have hp0 : p ≠ ⊥ :=
    Ideal.under_ne_bot (𝓞 K) hP0
  let : Algebra.IsUnramifiedAt (𝓞 K) P := hunram
  apply inertiaGroup_eq_bot_of_ramificationIdx_eq_one
    (K := K) (M := M) p P hp0
  exact Ideal.ramificationIdx_eq_one P (𝓞 K)

/-- Trivial inertia at a prime of a finite Galois number-field
extension gives algebraic unramifiedness at that prime. -/
theorem isUnramifiedAt_of_inertiaGroup_eq_bot
    {K M : Type*}
    [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (P : Ideal (𝓞 M)) [P.IsPrime] [P.IsMaximal]
    (hI : inertiaGroup P Gal(M/K) = ⊥) :
    Algebra.IsUnramifiedAt (𝓞 K) P := by
  let p : Ideal (𝓞 K) := P.under (𝓞 K)
  let : p.IsPrime := inferInstance
  let : P.LiesOver p := ⟨rfl⟩
  have hP0 : P ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (M := P) inferInstance (RingOfIntegers.not_isField M)
  have hp0 : p ≠ ⊥ :=
    Ideal.under_ne_bot (𝓞 K) hP0
  let : p.IsMaximal :=
    (inferInstance : p.IsPrime).isMaximal hp0
  let : Finite ((𝓞 K) ⧸ p) :=
    Ideal.finiteQuotientOfFreeOfNeBot p hp0
  let : PerfectField ((𝓞 K) ⧸ p) :=
    PerfectField.ofFinite
  let : Algebra.IsSeparable
      ((𝓞 K) ⧸ p) ((𝓞 M) ⧸ P) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have he :
      P.ramificationIdx (𝓞 K) = 1 := by
    rw [← inertia_card_eq_ramificationIdx
      (A := 𝓞 K) (B := 𝓞 M)
      p P Gal(M/K) hp0, hI]
    simp
  exact Ideal.ramificationIdx_eq_one_iff.mp he

end HilbertRamification.Dedekind
end
end


