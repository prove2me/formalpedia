-- Prove2me | Definitions.Def_OAIQ244Duke036
-- name    : OAIQ244Duke036
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:33:24.415546+00:00
-- url     : https://prove2.me/theorems/7001b20a-c348-498e-ba61-6609c6d9d27e
-- title:
--   Definitions bundle OAIQ244Duke036 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 233 declarations of OpenAI's Lean: 82 definitions, 21 instances and 130 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.infinitePlaceRatEmbeddedExtensionField`, `GlobalClassFieldTheory.Reciprocity.infinitePlaceRatFourthRootField`, `OAI.DukePrimeDegree.compactNeutralDisplacements`, `OAI.DukePrimeDegree.conjugationOrbitMap`, `OAI.DukePrimeDegree.coordinateVelocityFrame`, `OAI.DukePrimeDegree.euclideanVelocityColumns`, `OAI.DukePrimeDegree.euclideanVelocitySpace`, `OAI.DukePrimeDegree.invarianceDefect`, `OAI.DukePrimeDegree.latticeOrbitPoint`, `OAI.DukePrimeDegree.latticeOrbitRightAction`, `OAI.DukePrimeDegree.maximalGramFrame`, `OAI.DukePrimeDegree.maximalGramFrameIndex`, `OAI.DukePrimeDegree.neutralRootSkewHomeomorph`, `OAI.DukePrimeDegree.predecessorPackingRadius`, `OAI.DukePrimeDegree.rightCompactObservable`, `OAI.DukePrimeDegree.rightLatticeOppositeAction`, `OAI.DukePrimeDegree.rightSubgroupOrbit`, `OAI.DukePrimeDegree.rootProductInformation`, `OAI.DukePrimeDegree.selectedFrameVector`, `OAI.DukePrimeDegree.transferredVelocitySpace`, `OAI.DukePrimeDegree.transverseColumnRatios`, `OAI.DukePrimeDegree.upperRootEuclideanCoordinates`, `OAI.DukePrimeDegree.upperRootSize`, `OAI.DukePrimeDegree.velocityFrame`, `OAI.DukePrimeDegree.velocityFrameCard`, `OAI.PrimeDegreePackets.EvenRayCharacter.badEulerCorrection`, `OAI.PrimeDegreePackets.EvenRayCharacter.classEulerCorrection`, `OAI.PrimeDegreePackets.EvenRayCharacter.coefficientHom`, `OAI.PrimeDegreePackets.EvenRayCharacter.idealTerm`, `OAI.PrimeDegreePackets.EvenRayCharacter.normTerm`, `OAI.PrimeDegreePackets.PrincipalRay.realize`, `OAI.PrimeDegreePackets.RootBox.HasHaarConditionals`, `OAI.PrimeDegreePackets.RootBox.diagonal`, `OAI.PrimeDegreePackets.RootBox.overlapBox`, `OAI.PrimeDegreePackets.actualLocalModel`, `OAI.PrimeDegreePackets.actualLocalZ`, `OAI.PrimeDegreePackets.actualTupleNorm`, `OAI.PrimeDegreePackets.actualTupleWeight`, `OAI.PrimeDegreePackets.actualValuationTuples`, `OAI.PrimeDegreePackets.allSignedGlobalLabelOrbit` and 42 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Idele_LocallyCompact`, `DukePrimeDegree_Dynamics_CompactStabilizerSeparation`, `DukePrimeDegree_Dynamics_ConjugationOrbit`, `DukePrimeDegree_Dynamics_EuclideanVelocityProjection`, `DukePrimeDegree_Dynamics_GenericMatrixPairs`, `DukePrimeDegree_Dynamics_KernelVelocityFrames`, `DukePrimeDegree_Dynamics_OrbitGenericity`, `DukePrimeDegree_Dynamics_TransferredVelocity`, `DukePrimeDegree_Entropy_CoverPredecessorPacking`, `DukePrimeDegree_Entropy_RootProductInformation`, `DukePrimeDegree_Geometry_CompactNeutralFibers`, `DukePrimeDegree_Geometry_FiniteProjectionFrames`, `DukePrimeDegree_Geometry_MatrixCoordinateFrames`, `DukePrimeDegree_Geometry_NeutralUpperRootHomeomorph`, `DukePrimeDegree_Geometry_PositiveRootFactorization`, `DukePrimeDegree_Geometry_RemainingRootProductBoxes`, `DukePrimeDegree_Geometry_RightObservableUniformity`, `DukePrimeDegree_Geometry_TransverseDiagonalData`, `DukePrimeDegree_Geometry_TransverseDiagonalFactorization`, `DukePrimeDegree_Geometry_UpperRootContraction`, `DukePrimeDegree_Geometry_UpperRootEuclideanCoordinates`, `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_InfinitePlaceOverfield`, `PrimePackets_CuspMass`, `PrimePackets_IdealSupport`, `PrimePackets_IdealThetaFlow`, `PrimePackets_IntegerEmbeddings`, `PrimePackets_IntrinsicLeaves`, `PrimePackets_KernelScaling`, `PrimePackets_LeafTransitions`, `PrimePackets_LocalEuler`, `PrimePackets_LocalModels`, `PrimePackets_PacketAlgebra`, `PrimePackets_PacketMoments`, `PrimePackets_PrimeFactors`, `PrimePackets_RayDescent`, `PrimePackets_RayEuler`, `PrimePackets_RayRealization`, `PrimePackets_RayUnramified`, `PrimePackets_RootCharts`, `PrimePackets_RootOverlaps`, `PrimePackets_RootRelations`, `PrimePackets_RootSubgroups`, `PrimePackets_ScalingCovariance`, `PrimePackets_UnitOrbitIntegrals`, `PrimePackets_ZetaDerivatives`, `PrimePackets_ZetaResidues`, `Valuation_DiscreteValuationField_Complete`.
--
--   **Imports.** It imports the published bundle `Def_DukePrimeDegree`; the bundles `OAIQ244Duke017`, `OAIQ244Duke020`, `OAIQ244Duke021`, `OAIQ244Duke022`, `OAIQ244Duke023` and `OAIQ244Duke024` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ244Duke044`; the statements `OAI.DukePrimeDegree.ae_normalized_component_velocity_support`, `OAI.DukePrimeDegree.exists_branching_cover_future_observation`, `OAI.DukePrimeDegree.exists_positive_singleBlock_orbit`, `OAI.DukePrimeDegree.isHaar_of_prime_symmetric_invariant_roots`, `OAI.DukePrimeDegree.packet_limit_isHaar_of_scale_and_EKL`, `OAI.DukePrimeDegree.prime_degree_packet_equidistribution_of_real_zero_exclusion`, `OAI.DukePrimeDegree.rootInvarianceRelation_symmetric_of_regular_tests`, `OAI.PrimeDegreePackets.globalContainment_eq_relativeIdealWeight`, `OAI.PrimeDegreePackets.packetMeasure_lintegral_signedLogAverage`, `OAI.PrimeDegreePackets.packet_limit_ball_bound_of_zeta_scale`, `OAI.PrimeDegreePackets.packet_probability_subsequence_of_zeta_scale`, `OAI.PrimeDegreePackets.packet_tight_of_zeta_scale`, `OAI.PrimeDegreePackets.primaryIdeal_reciprocal_tail`, `OAI.PrimeDegreePackets.residueMellinKernel_eq_ideal_sum`, `OAI.PrimeDegreePackets.signedLabel_siegelTransform_lintegral`, `OAI.PrimeDegreePackets.weightedIdeal_realInterval_of_zeta_scale` and `OAI.PrimeDegreePackets.weightedIdeal_small_norm_bound`; the proofs of `OAI.DukePrimeDegree.RootPrefixCoordinates.predecessor_entropyRate_le_root_information_add_auxiliary`, `OAI.DukePrimeDegree.RootPrefixCoordinates.wholeFutureKernel_stationary`, `OAI.DukePrimeDegree.ae_normalized_component_velocity_support`, `OAI.DukePrimeDegree.countable_patch_name_entropy_sublinear`, `OAI.DukePrimeDegree.eklPrimeInput_unconditional`, `OAI.DukePrimeDegree.exists_bounded_branching_subordinate_observation_with_lifts`, `OAI.DukePrimeDegree.exists_bounded_cover_subordinate_observation`, `OAI.DukePrimeDegree.exists_branching_cover_future_observation`, `OAI.DukePrimeDegree.exists_controlled_cover_future_observation`, `OAI.DukePrimeDegree.exists_positive_singleBlock_orbit`, `OAI.DukePrimeDegree.exists_singleBlock_terminal_generic_set`, `OAI.DukePrimeDegree.exists_small_future_observation`, `OAI.DukePrimeDegree.isHaar_of_prime_symmetric_invariant_roots`, `OAI.DukePrimeDegree.measureEntropy_le_of_bilateral_heightClip_bounds`, `OAI.DukePrimeDegree.packet_limit_isHaar_of_scale_and_EKL`, `OAI.DukePrimeDegree.prime_degree_packet_equidistribution_of_real_zero_exclusion`, `OAI.DukePrimeDegree.root_invariant_of_atomic_companion_leaves`, `OAI.PrimeDegreePackets.EvenRayCharacter.continued_eq_dirichlet`, `OAI.PrimeDegreePackets.HeckeMellin.fractionalIdealTheta_mellin_lintegral_totallyReal`, `OAI.PrimeDegreePackets.globalContainment_eq_relativeIdealWeight`, `OAI.PrimeDegreePackets.integral_unitOrbitMellinKernel`, `OAI.PrimeDegreePackets.packetMeasure_lintegral_signedLogAverage`, `OAI.PrimeDegreePackets.packet_limit_ball_bound_of_zeta_scale`, `OAI.PrimeDegreePackets.packet_probability_subsequence_of_zeta_scale`, `OAI.PrimeDegreePackets.packet_tight_of_zeta_scale`, `OAI.PrimeDegreePackets.primaryIdeal_reciprocal_tail`, `OAI.PrimeDegreePackets.residueMellinKernel_eq_ideal_sum`, `OAI.PrimeDegreePackets.signedLabel_siegelTransform_lintegral`, `OAI.PrimeDegreePackets.tsum_lintegral_weightedUnitOrbitMellinKernel_ne_top`, `OAI.PrimeDegreePackets.weightedIdeal_realInterval_of_zeta_scale` and `OAI.PrimeDegreePackets.weightedIdeal_small_norm_bound`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
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
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
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
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
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
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
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
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.WithTopology
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke017
import Definitions.Def_OAIQ244Duke020
import Definitions.Def_OAIQ244Duke021
import Definitions.Def_OAIQ244Duke022
import Definitions.Def_OAIQ244Duke023
import Definitions.Def_OAIQ244Duke024

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_LocallyCompact
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xLocallyCompact _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Local compactness of the idele group

The topology on the finite ideles is the restricted-product topology from
`AlgebraicNumberTheory.Idele.Topology`.  We prove local compactness by showing
that every finite completion is proper, that its integral unit group is
compact, and then applying the restricted-product theorem.
-/

open scoped NumberField RestrictedProduct Valued
open NumberField IsDedekindDomain

noncomputable section


variable (K : Type*) [Field K] [NumberField K]

/-- The correctly topologized finite idele group is locally compact. -/
instance finiteIdeleGroupLocallyCompactSpace :
    LocallyCompactSpace (FiniteIdeleGroup K) := by
  apply RestrictedProduct.locallyCompactSpace_of_group
    (fun v : HeightOneSpectrum (𝓞 K) ↦ (v.adicCompletion K)ˣ)
  exact Filter.Eventually.of_forall (isCompact_finiteLocalUnits K)

/-- The archimedean factor of the idele group is locally compact. -/
instance infiniteIdeleGroupLocallyCompactSpace :
    LocallyCompactSpace (InfiniteIdeleGroup K) :=
  inferInstance

/-- The idele group, with its restricted-product topology, is
locally compact. -/
instance ideleGroupLocallyCompactSpace :
    LocallyCompactSpace (IdeleGroup K) :=
  inferInstance
end
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketAlgebra
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xLocallyCompact _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupLocallyCompactSpace _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.FullLattice.toPacket_carrier _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.globalLabels_smul_val _root_.infinitePlace_mult_smul
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
namespace PrimeDegreePackets



theorem fullLattice_carrier_eq_of_completions_eq
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (h : ∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩;
      completedLattice p M = completedLattice p N) : M.carrier = N.carrier := by
  ext x
  rw [mem_fullLattice_iff_forall_completed M hn x,mem_fullLattice_iff_forall_completed N hn x]
  exact forall_congr' (fun p => forall_congr' (fun hp => by rw [h p hp]))



open scoped NumberField Pointwise nonZeroDivisors
open NumberField



theorem completedFractionalIdeal_principal {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) =
      (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) a •
        completedFractionalIdeal p (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  let P : FractionalIdeal (𝓞 K)⁰ K := FractionalIdeal.spanSingleton (𝓞 K)⁰ (p : K) * I
  have hPI : P ≤ I := by
    apply FractionalIdeal.spanSingleton_mul_le_iff.mpr
    intro x hx
    have H := (I : Submodule (𝓞 K) K).toAddSubgroup.nsmul_mem hx p
    simp only [nsmul_eq_mul] at H
    exact H
  have hpn : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hP : P ≠ 0 := mul_ne_zero (FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hpn) hI
  obtain ⟨a,ha⟩ := IsDedekindDomain.exists_add_spanSingleton_mul_eq
    (b := (1 : FractionalIdeal (𝓞 K)⁰ K)) hPI hP one_ne_zero
  rw [mul_one] at ha
  have hA : completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) =
      completedFractionalIdeal p (FractionalIdeal.spanSingleton (𝓞 K)⁰ a) := by
    have hle : completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) ≤
        completedFractionalIdeal p (FractionalIdeal.spanSingleton (𝓞 K)⁰ a) ⊔
        Ideal.span {(p : PadicInt p)} • completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [Submodule.ideal_span_singleton_smul, ← completedFractionalIdeal_nat_mul]
      rw [← completedFractionalIdeal_add, add_comm]
      exact (congrArg (completedFractionalIdeal p) ha).ge
    apply le_antisymm
    · apply Submodule.le_of_le_smul_of_le_jacobson_bot (completedFractionalIdeal_fg p I) _ hle
      rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top, PadicInt.maximalIdeal_eq_span_p]
    · apply completedFractionalIdeal_mono p
      rw [← ha]
      exact le_sup_right
  have ha0 : a ≠ 0 := by
    intro he
    rw [he,FractionalIdeal.spanSingleton_zero,completedFractionalIdeal_zero] at hA
    exact completedFractionalIdeal_ne_bot p hI hA
  refine ⟨a,ha0,?_⟩
  rw [hA, ← completedFractionalIdeal_singleton_mul,mul_one]


theorem fractionalIdeal_eq_of_completions_eq {K : Type*} [Field K] [NumberField K]
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : ∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩;
      completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) =
        completedFractionalIdeal p (J : FractionalIdeal (𝓞 K)⁰ K)) :
    (I : FractionalIdeal (𝓞 K)⁰ K) = J := by
  have H := fullLattice_carrier_eq_of_completions_eq
    (fractionalIdealFullLattice rfl I) (fractionalIdealFullLattice rfl J) rfl h
  exact FractionalIdeal.coeToSubmodule_injective (Submodule.ext (fun x =>
    show x ∈ (I : Submodule (𝓞 K) K) ↔ x ∈ (J : Submodule (𝓞 K) K) from
      Iff.of_eq (congrArg (fun A : Submodule ℤ K => x ∈ A) H)))

lemma le_saturation {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : M.carrier ≤ saturation M := by
  intro x hx
  exact Submodule.subset_span hx

lemma saturation_fg {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : (saturation M).FG := by
  apply Submodule.FG.restrictScalars
  rw [← fullLattice_span_basis M, Submodule.span_span_of_tower]
  exact Submodule.fg_span (Set.finite_range _)



lemma saturationIndex_ne_zero {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : saturationIndex M ≠ 0 := by
  let S := (saturation M).toAddSubgroup
  let A := M.carrier.toAddSubgroup.addSubgroupOf S
  let : AddGroup.FG S := (AddGroup.fg_iff_addSubgroup_fg S).mpr
    (Submodule.fg_toAddSubgroup (saturation_fg M))
  have ht : Module.IsTorsion ℤ (S ⧸ A) := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨z, hz, hzx⟩ := fullLattice_clear_denominator M (x : K)
      refine ⟨⟨z, mem_nonZeroDivisors_iff_ne_zero.mpr hz⟩, ?_⟩
      change z • (QuotientAddGroup.mk x : S ⧸ A) = 0
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
      exact hzx
  let : Finite (S ⧸ A) := Module.finite_of_fg_torsion _ ht
  exact Nat.card_pos.ne'

 
lemma saturationIndex_smul_mem {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) {x : K} (hx : x ∈ saturation M) :
    saturationIndex M • x ∈ M.carrier :=
  M.carrier.toAddSubgroup.nsmul_relIndex_mem hx

 

lemma exists_idealLocalGenerator {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ u : (LocalAlgebra p K)ˣ,
      completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) =
        (u : LocalAlgebra p K) • (completedMaximalOrder (K := K) p).toSubmodule := by
  have hI : (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := I.ne_zero
  obtain ⟨a,ha,h⟩ := completedFractionalIdeal_principal p
    (I : FractionalIdeal (𝓞 K)⁰ K) hI
  let u : Kˣ := Units.mk0 a ha
  let f : K →* LocalAlgebra p K :=
    (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K).toMonoidHom
  refine ⟨Units.map f u,?_⟩
  exact h

 

def idealLocalGenerator {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (LocalAlgebra p K)ˣ :=
  (exists_idealLocalGenerator p I).choose

lemma idealLocalGenerator_spec {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) =
      (idealLocalGenerator p I : LocalAlgebra p K) •
        (completedMaximalOrder (K := K) p).toSubmodule :=
  (exists_idealLocalGenerator p I).choose_spec


lemma saturationLocalGenerator_spec {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime] :
    completedFractionalIdeal p (saturationFractionalIdeal M) =
      (idealLocalGenerator p (saturationIdealUnit M) : LocalAlgebra p K) •
        (completedMaximalOrder (K := K) p).toSubmodule :=
  idealLocalGenerator_spec p (saturationIdealUnit M)


def normalizedLocalModule {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime] :
    Submodule (PadicInt p) (LocalAlgebra p K) :=
  (↑((idealLocalGenerator p (saturationIdealUnit M))⁻¹) : LocalAlgebra p K) •
    completedLattice p M

lemma normalizedLocalModule_le {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime] :
    normalizedLocalModule M p ≤ (completedMaximalOrder (K := K) p).toSubmodule := by
  have h : completedLattice p M ≤ completedFractionalIdeal p (saturationIdealUnit M) :=
    Submodule.span_mono (Set.image_mono (fun x hx => Submodule.subset_span hx))
  have H := local_smul_mono p (↑((idealLocalGenerator p (saturationIdealUnit M))⁻¹) :
    LocalAlgebra p K) h
  rw [idealLocalGenerator_spec,← mul_smul,Units.inv_mul,one_smul] at H
  exact H

lemma normalizedLocalModule_saturation {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime] :
    (completedMaximalOrder (K := K) p).toSubmodule * normalizedLocalModule M p =
      (completedMaximalOrder (K := K) p).toSubmodule := by
  rw [normalizedLocalModule,mul_smul_comm,← completed_saturation,
    saturationLocalGenerator_spec,← mul_smul,Units.inv_mul,one_smul]

lemma normalizedLocalModule_saturationIndex_mem
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] {x : LocalAlgebra p K}
    (hx : x ∈ completedMaximalOrder (K := K) p) :
    (saturationIndex M : PadicInt p) • x ∈ normalizedLocalModule M p := by
  let j := idealLocalGenerator p (saturationIdealUnit M)
  have hjx : (j : LocalAlgebra p K) * x ∈
      completedLattice p (fractionalIdealFullLattice hn (saturationIdealUnit M)) := by
    rw [completedLattice_fractionalIdealFullLattice,idealLocalGenerator_spec]
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨x,hx,rfl⟩
  have H := completedLattice_smul_mem (saturationIndex M)
    (M := fractionalIdealFullLattice hn (saturationIdealUnit M)) (N := M)
    (fun a ha => by simpa only [natCast_zsmul] using saturationIndex_smul_mem M ha)
    p hjx
  apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
  refine ⟨(saturationIndex M : PadicInt p) • ((j : LocalAlgebra p K)*x),H,?_⟩
  change (↑(j⁻¹) : LocalAlgebra p K) * _ = _
  rw [mul_smul_comm,← mul_assoc,Units.inv_mul,one_mul]

 
def localModuleChoices {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] : Set (Submodule (PadicInt p) (LocalAlgebra p K)) :=
  Set.range fun z : (completedMaximalOrder (K := K) p)ˣ =>
    ((idealLocalGenerator p I : LocalAlgebra p K) *
      ((z : completedMaximalOrder (K := K) p) : LocalAlgebra p K)) • normalizedLocalModule M p

lemma localModuleChoices_nonempty {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] : (localModuleChoices M I p).Nonempty :=
  Set.range_nonempty _

lemma localModuleChoices_le {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] {N : Submodule (PadicInt p) (LocalAlgebra p K)}
    (hN : N ∈ localModuleChoices M I p) : N ≤ completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) := by
  obtain ⟨z,rfl⟩ := hN
  dsimp only
  rw [mul_smul,idealLocalGenerator_spec]
  apply local_smul_mono
  calc
    _ ≤ (↑(z : completedMaximalOrder (K := K) p) : LocalAlgebra p K) •
        (completedMaximalOrder (K := K) p).toSubmodule :=
      local_smul_mono p _ (normalizedLocalModule_le M p)
    _ = _ := completedMaximalOrder_unit_smul p z

lemma localModuleChoices_saturation {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] {N : Submodule (PadicInt p) (LocalAlgebra p K)}
    (hN : N ∈ localModuleChoices M I p) :
    (completedMaximalOrder (K := K) p).toSubmodule * N = completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) := by
  obtain ⟨z,rfl⟩ := hN
  dsimp only
  rw [mul_smul_comm,normalizedLocalModule_saturation,mul_smul,
    completedMaximalOrder_unit_smul,idealLocalGenerator_spec]

lemma localModuleChoices_saturationIndex_mem
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (p : ℕ) [Fact p.Prime]
    {N : Submodule (PadicInt p) (LocalAlgebra p K)} (hN : N ∈ localModuleChoices M I p)
    {x : LocalAlgebra p K} (hx : x ∈ completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K)) :
    (saturationIndex M : PadicInt p) • x ∈ N := by
  obtain ⟨z,rfl⟩ := hN
  dsimp only
  rw [idealLocalGenerator_spec] at hx
  obtain ⟨b,hb,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  let R := completedMaximalOrder (K := K) p
  have hz : ((z : R) : LocalAlgebra p K) * ((↑(z⁻¹) : R) : LocalAlgebra p K) = 1 :=
    congrArg (fun a : R => (a : LocalAlgebra p K)) z.mul_inv
  have hL := normalizedLocalModule_saturationIndex_mem M hn p
    (R.mul_mem (↑(z⁻¹) : R).property hb)
  apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
  refine ⟨(saturationIndex M : PadicInt p) •
    (((↑(z⁻¹) : R) : LocalAlgebra p K) * b),hL,?_⟩
  change ((idealLocalGenerator p I : LocalAlgebra p K) * ((z : R) : LocalAlgebra p K)) *
      ((saturationIndex M : PadicInt p) • _) = _
  rw [mul_smul_comm]
  congr 1
  change _ = (idealLocalGenerator p I : LocalAlgebra p K) * b
  calc
    _ = (idealLocalGenerator p I : LocalAlgebra p K) *
        ((((z : R) : LocalAlgebra p K) * ((↑(z⁻¹) : R) : LocalAlgebra p K)) * b) := by ring
    _ = _ := by rw [hz,one_mul]

lemma localModuleChoices_primePower_mem
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (p : ℕ) [Fact p.Prime]
    {N : Submodule (PadicInt p) (LocalAlgebra p K)} (hN : N ∈ localModuleChoices M I p)
    {x : LocalAlgebra p K} (hx : x ∈ completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K)) :
    (p : PadicInt p)^((saturationIndex M).factorization p) • x ∈ N := by
  let q := saturationIndex M
  let r := ordCompl[p] q
  have hc : Nat.Coprime p r := Nat.coprime_ordCompl Fact.out (saturationIndex_ne_zero M)
  obtain ⟨u,hu⟩ := PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hc)
  have H := N.smul_mem (↑(u⁻¹) : PadicInt p)
    (localModuleChoices_saturationIndex_mem M hn I p hN hx)
  have hqr : q = p^(q.factorization p)*r := (Nat.ordProj_mul_ordCompl_eq_self q p).symm
  change (↑(u⁻¹) : PadicInt p) • ((q : PadicInt p) • x) ∈ N at H
  rw [smul_smul,hqr,Nat.cast_mul,Nat.cast_pow,← hu] at H
  have he : (↑(u⁻¹) : PadicInt p) * ((p : PadicInt p)^(q.factorization p) * u) =
      (p : PadicInt p)^(q.factorization p) := by
    rw [mul_left_comm,Units.inv_mul,mul_one]
  rwa [he] at H

lemma localModuleChoices_eq_off
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (p : ℕ) [Fact p.Prime]
    (hp : ¬p ∣ saturationIndex M)
    {N : Submodule (PadicInt p) (LocalAlgebra p K)} (hN : N ∈ localModuleChoices M I p) :
    N = completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) := by
  apply le_antisymm (localModuleChoices_le M I p hN)
  intro x hx
  have H := localModuleChoices_primePower_mem M hn I p hN hx
  simpa only [Nat.factorization_eq_zero_of_not_dvd hp,pow_zero,one_smul] using H



lemma localModuleChoices_transport
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] {N : Submodule (PadicInt p) (LocalAlgebra p K)}
    (hN : N ∈ localModuleChoices M I p) :
    (↑(idealLocalGenerator p J * (idealLocalGenerator p I)⁻¹) : LocalAlgebra p K) • N ∈
      localModuleChoices M J p := by
  obtain ⟨z,rfl⟩ := hN
  refine ⟨z,?_⟩
  simp only [Units.val_mul,← mul_smul,mul_assoc,Units.inv_mul_cancel_left]

 

def localModuleChoicesEquiv
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] : localModuleChoices M I p ≃ localModuleChoices M J p where
  toFun N := ⟨(↑(idealLocalGenerator p J * (idealLocalGenerator p I)⁻¹) : LocalAlgebra p K) • N.1,
    localModuleChoices_transport M I J p N.2⟩
  invFun N := ⟨(↑(idealLocalGenerator p I * (idealLocalGenerator p J)⁻¹) : LocalAlgebra p K) • N.1,
    localModuleChoices_transport M J I p N.2⟩
  left_inv N := by
    apply Subtype.ext
    simp only [Units.val_mul,← mul_smul,mul_assoc,Units.inv_mul_cancel_left,Units.mul_inv,one_smul]
  right_inv N := by
    apply Subtype.ext
    simp only [Units.val_mul,← mul_smul,mul_assoc,Units.inv_mul_cancel_left,Units.mul_inv,one_smul]

lemma localModuleChoices_homothety
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] {N : Submodule (PadicInt p) (LocalAlgebra p K)}
    (hN : N ∈ localModuleChoices M I p) :
    ∃ c : (LocalAlgebra p K)ˣ, N = (c : LocalAlgebra p K) • completedLattice p M := by
  obtain ⟨z,rfl⟩ := hN
  let v : (LocalAlgebra p K)ˣ := Units.map (completedMaximalOrder (K := K) p).subtype.toMonoidHom z
  refine ⟨idealLocalGenerator p I * v * (idealLocalGenerator p (saturationIdealUnit M))⁻¹,?_⟩
  simp only [normalizedLocalModule,← mul_smul,Units.val_mul]
  rfl

lemma completedLattice_mem_localModuleChoices
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hNI : saturationFractionalIdeal N = I) (hMN : LocallyHomothetic M N)
    (p : ℕ) [Fact p.Prime] : completedLattice p N ∈ localModuleChoices M I p := by
  obtain ⟨c,hc⟩ := hMN p Fact.out
  have h : completedLattice p N = (c : LocalAlgebra p K) • completedLattice p M :=
    SetLike.coe_injective hc
  have hi : completedFractionalIdeal p (saturationFractionalIdeal N) =
      (idealLocalGenerator p I : LocalAlgebra p K) •
        (completedMaximalOrder (K := K) p).toSubmodule := by
    rw [hNI,idealLocalGenerator_spec]
  obtain ⟨z,hz⟩ := local_scalar_choice M N p (idealLocalGenerator p I)
    (idealLocalGenerator p (saturationIdealUnit M)) c hi (saturationLocalGenerator_spec M p) h
  refine ⟨z,?_⟩
  simpa only [normalizedLocalModule,← mul_smul] using hz.symm



theorem patch_localModuleChoices
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (N : ∀ p : labelPrimes M, Submodule (PadicInt p.val) (LocalAlgebra p.val K))
    (hN : ∀ p, N p ∈ localModuleChoices M I p.val) :
    ∃ L : FullLattice n K, LocallyHomothetic M L ∧
      saturationFractionalIdeal L = (I : FractionalIdeal (𝓞 K)⁰ K) ∧
      ∀ p : labelPrimes M, completedLattice p.val L = N p := by
  classical
  obtain ⟨L,hLI,hL,hLoff⟩ := patch_fullLattice_completions (fractionalIdealFullLattice hn I) hn
    (fun p : labelPrimes M => p.val) Subtype.val_injective
    (fun p => (saturationIndex M).factorization p.val) N
    (fun p => localModuleChoices_le M I p.val (hN p))
    (fun p x hx => localModuleChoices_primePower_mem M hn I p.val (hN p) hx)
  have hchoices (p : ℕ) (hp : p.Prime) : letI : Fact p.Prime := ⟨hp⟩;
      completedLattice p L ∈ localModuleChoices M I p := by
    let : Fact p.Prime := ⟨hp⟩
    by_cases hs : p ∈ (saturationIndex M).primeFactors
    · exact (hL ⟨p,hs⟩).symm ▸ hN ⟨p,hs⟩
    · have hnot : p ∉ Set.range (fun r : labelPrimes M => r.val) := by
        rintro ⟨r,hr⟩
        exact hs (hr ▸ r.property)
      have hpd : ¬p ∣ saturationIndex M := fun h =>
        hs (Nat.mem_primeFactors.mpr ⟨hp,h,saturationIndex_ne_zero M⟩)
      obtain ⟨A,hA⟩ := localModuleChoices_nonempty M I p
      rw [hLoff p hp hnot,completedLattice_fractionalIdealFullLattice,
        ← localModuleChoices_eq_off M hn I p hpd hA]
      exact hA
  refine ⟨L,?_,?_,hL⟩
  · intro p hp
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨c,hc⟩ := localModuleChoices_homothety M I p (hchoices p hp)
    refine ⟨c,?_⟩
    rw [hc]
    rfl
  · apply fractionalIdeal_eq_of_completions_eq (saturationIdealUnit L) I
    intro p hp
    let : Fact p.Prime := ⟨hp⟩
    change completedFractionalIdeal p (saturationFractionalIdeal L) = _
    rw [completed_saturation]
    exact localModuleChoices_saturation M I p (hchoices p hp)



def globalLabelCompletions {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (N : globalLabels M I) : ∀ p : labelPrimes M, localModuleChoices M I p.val :=
  fun p => ⟨completedLattice p.val (globalLabelLattice M I N),
    completedLattice_mem_localModuleChoices M (globalLabelLattice M I N) I
      (globalLabelLattice_spec M I N).2.2 (globalLabelLattice_spec M I N).2.1 p.val⟩

lemma globalLabelCompletions_injective {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Function.Injective (globalLabelCompletions M I) := by
  intro N N' he
  apply Subtype.ext
  rw [← (globalLabelLattice_spec M I N).1,← (globalLabelLattice_spec M I N').1]
  apply fullLattice_carrier_eq_of_completions_eq _ _ hn
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  by_cases hs : p ∈ (saturationIndex M).primeFactors
  · exact congrArg Subtype.val (congrFun he ⟨p,hs⟩)
  · have hpd : ¬p ∣ saturationIndex M := fun h =>
      hs (Nat.mem_primeFactors.mpr ⟨hp,h,saturationIndex_ne_zero M⟩)
    have h (A : globalLabels M I) : completedLattice p (globalLabelLattice M I A) =
        completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) :=
      localModuleChoices_eq_off M hn I p hpd
        (completedLattice_mem_localModuleChoices M (globalLabelLattice M I A) I
          (globalLabelLattice_spec M I A).2.2 (globalLabelLattice_spec M I A).2.1 p)
    exact (h N).trans (h N').symm

lemma globalLabelCompletions_surjective {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Function.Surjective (globalLabelCompletions M I) := by
  intro A
  obtain ⟨L,hML,hLI,hL⟩ := patch_localModuleChoices M hn I (fun p => (A p).val)
    (fun p => (A p).property)
  let N : globalLabels M I := ⟨L.carrier,⟨L,rfl,hML,hLI⟩⟩
  refine ⟨N,?_⟩
  funext p
  apply Subtype.ext
  change completedLattice p.val (globalLabelLattice M I N) = (A p).val
  have hc : (globalLabelLattice M I N).carrier = L.carrier := (globalLabelLattice_spec M I N).1
  rw [completedLattice,hc,← completedLattice]
  exact hL p

 

def globalLabelEquiv {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    globalLabels M I ≃ (∀ p : labelPrimes M, localModuleChoices M I p.val) :=
  Equiv.ofBijective (globalLabelCompletions M I)
    ⟨globalLabelCompletions_injective M hn I,globalLabelCompletions_surjective M hn I⟩


def globalLabelsEquiv {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : globalLabels M I ≃ globalLabels M J :=
  let e : (∀ p : labelPrimes M, localModuleChoices M I p.val) ≃
      (∀ p : labelPrimes M, localModuleChoices M J p.val) :=
    Equiv.piCongrRight (fun p : labelPrimes M => localModuleChoicesEquiv M I J p.val)
  (globalLabelEquiv M hn I).trans (e.trans (globalLabelEquiv M hn J).symm)



theorem localLatticeQuotientMap_simultaneous_surjective
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (hn : Module.finrank ℚ K = n)
    {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ j, Fact (p j).Prime]
    (hp : Function.Injective p) (k : ι → ℕ)
    (hpow : ∀ j x, x ∈ completedLattice (p j) M →
      (p j : PadicInt (p j))^(k j) • x ∈ completedLattice (p j) N) :
    Function.Surjective (AddMonoidHom.pi (fun j => localLatticeQuotientMap M N (p j))) := by
  intro z
  choose y hy using fun j => QuotientAddGroup.mk'_surjective
    ((completedLattice (p j) N).comap (completedLattice (p j) M).subtype).toAddSubgroup (z j)
  obtain ⟨x,hx⟩ := completedReduction_simultaneous_surjective M hn p hp k
    (fun j => completedReduction M hn (p j) (k j) (y j))
  refine ⟨x,?_⟩
  funext j
  change QuotientAddGroup.mk (completionEmbedding M (p j) x) = z j
  rw [← hy j]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  have hk : completionEmbedding M (p j) x - y j ∈ (completedReduction M hn (p j) (k j)).ker := by
    change completedReduction M hn (p j) (k j) (_ - _) = 0
    rw [map_sub,hx j,sub_self]
  obtain ⟨v,hv⟩ := (completedReduction_eq_zero_iff M hn (p j) (k j) _).mp hk
  change ((completionEmbedding M (p j) x - y j : completedLattice (p j) M) : LocalAlgebra (p j) K) ∈ completedLattice (p j) N
  rw [hv]
  exact hpow j v v.property

 

theorem fullLattice_relIndex_eq_prod_local
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (hn : Module.finrank ℚ K = n)
    {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ j, Fact (p j).Prime]
    (hp : Function.Injective p) (k : ι → ℕ)
    (hpow : ∀ j x, x ∈ completedLattice (p j) M →
      (p j : PadicInt (p j))^(k j) • x ∈ completedLattice (p j) N)
    (hoff : ∀ (r : ℕ) (hr : r.Prime), letI : Fact r.Prime := ⟨hr⟩;
      r ∉ Set.range p → completedLattice r N = completedLattice r M) :
    N.carrier.toAddSubgroup.relIndex M.carrier.toAddSubgroup =
      ∏ j, (completedLattice (p j) N).toAddSubgroup.relIndex
        (completedLattice (p j) M).toAddSubgroup := by
  classical
  let f := AddMonoidHom.pi (fun j => localLatticeQuotientMap M N (p j))
  have hf : Function.Surjective f := localLatticeQuotientMap_simultaneous_surjective M N hn p hp k hpow
  have hker : f.ker = (N.carrier.comap M.carrier.subtype).toAddSubgroup := by
    ext x
    change f x = 0 ↔ (x : K) ∈ N.carrier
    rw [mem_fullLattice_iff_forall_completed N hn]
    constructor
    · intro hx r hr
      let : Fact r.Prime := ⟨hr⟩
      by_cases hs : r ∈ Set.range p
      · obtain ⟨j,rfl⟩ := hs
        have H := congrFun hx j
        exact QuotientAddGroup.eq_zero_iff _ |>.mp H
      · rw [hoff r hr hs]
        exact (completionEmbedding M r x).property
    · intro hx
      funext j
      exact (QuotientAddGroup.eq_zero_iff _).mpr (hx (p j) Fact.out)
  change (N.carrier.comap M.carrier.subtype).toAddSubgroup.index = _
  rw [← hker,AddSubgroup.index_ker,AddMonoidHom.range_eq_top.mpr hf]
  rw [AddSubgroup.card_top,Nat.card_pi]
  rfl



lemma globalLabel_contains_iff
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (N : globalLabels M I)
    (a : K) (ha : a ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) :
    a ∈ N.val ↔ ∀ p : labelPrimes M,
      (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p.val K) a ∈
        (globalLabelCompletions M I N p).val := by
  rw [← (globalLabelLattice_spec M I N).1,
    mem_fullLattice_iff_forall_completed (globalLabelLattice M I N) hn]
  constructor
  · intro h p
    exact h p.val Fact.out
  · intro h p hp
    let : Fact p.Prime := ⟨hp⟩
    by_cases hs : p ∈ (saturationIndex M).primeFactors
    · exact h ⟨p,hs⟩
    · have hpd : ¬p ∣ saturationIndex M := fun h =>
        hs (Nat.mem_primeFactors.mpr ⟨hp,h,saturationIndex_ne_zero M⟩)
      have hN := completedLattice_mem_localModuleChoices M (globalLabelLattice M I N) I
        (globalLabelLattice_spec M I N).2.2 (globalLabelLattice_spec M I N).2.1 p
      rw [localModuleChoices_eq_off M hn I p hpd hN]
      exact Submodule.subset_span ⟨a,ha,rfl⟩

def localContainmentLabels {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] (x : LocalAlgebra p K) :=
  {N : localModuleChoices M I p // x ∈ N.val}

 
def globalContainmentEquiv
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : K)
    (ha : a ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) :
    {N : globalLabels M I // a ∈ N.val} ≃
      (∀ p : labelPrimes M, localContainmentLabels M I p.val
        ((Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p.val K) a)) :=
  let e : {N : globalLabels M I // a ∈ N.val} ≃
      {f : ∀ p : labelPrimes M, localModuleChoices M I p.val // ∀ p,
        (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p.val K) a ∈ (f p).val} :=
    Equiv.subtypeEquiv (globalLabelEquiv M hn I) (fun N => globalLabel_contains_iff M hn I N a ha)
  e.trans (Equiv.subtypePiEquivPi (p := fun (p : labelPrimes M)
    (L : localModuleChoices M I p.val) =>
      (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p.val K) a ∈ L.val))



def localContainmentProbability
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] (x : LocalAlgebra p K) : ℝ :=
  (Nat.card (localContainmentLabels M I p x) : ℝ) / Nat.card (localModuleChoices M I p)


open Topology
open scoped Pointwise
instance instT2SpaceLocalAlgebra {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] :
    T2Space (LocalAlgebra p K) := (localAlgebraCoordinates p (Module.Free.chooseBasis ℚ K)).toHomeomorph.isEmbedding.t2Space
instance instLocallyCompactSpaceLocalAlgebra {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] :
    LocallyCompactSpace (LocalAlgebra p K) := (localAlgebraCoordinates p (Module.Free.chooseBasis ℚ K)).toHomeomorph.isClosedEmbedding.locallyCompactSpace


lemma localIntegralSpan_compact {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
    (p : ℕ) [Fact p.Prime] (b : Basis ι ℚ K) :
    IsCompact (localIntegralSpan p b : Set (LocalAlgebra p K)) := by
  let f : (ι → PadicInt p) → LocalAlgebra p K := fun v => (localAlgebraCoordinates p b).symm (fun i => (v i : Padic p))
  have hf : Continuous f := (localAlgebraCoordinates p b).symm.continuous.comp
    (continuous_pi (fun i => PadicInt.isOpenEmbedding_coe.continuous.comp (continuous_apply i)))
  have he : (localIntegralSpan p b : Set (LocalAlgebra p K)) = Set.range f := by
    ext x
    rw [SetLike.mem_coe,localIntegralSpan_mem]
    constructor
    · intro hx
      refine ⟨fun i => ⟨localAlgebraCoordinates p b x i,hx i⟩,?_⟩
      exact (localAlgebraCoordinates p b).symm_apply_apply x
    · rintro ⟨v,rfl⟩
      intro i
      simpa [f] using (v i).property
  rw [he]
  exact isCompact_range hf

lemma completedLattice_compact {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (p : ℕ) [Fact p.Prime] :
    IsCompact (completedLattice p M : Set (LocalAlgebra p K)) := by
  have h := localIntegralSpan_compact p (fullLatticeRatBasis M hn)
  simpa [localIntegralSpan,completedLattice_eq_span_basis] using h

instance completedMaximalOrderCompactSpace {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] : CompactSpace (completedMaximalOrder (K := K) p) := by
  apply isCompact_iff_compactSpace.mp
  exact completedLattice_compact (fractionalIdealFullLattice rfl 1) rfl p

instance localUnitsMeasurableSpace {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] : MeasurableSpace (completedMaximalOrder (K := K) p)ˣ := borel _
instance localUnitsBorelSpace {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] : BorelSpace (completedMaximalOrder (K := K) p)ˣ := ⟨rfl⟩

open Polynomial



open scoped NNReal

open Polynomial
open scoped BigOperators

open IsDiscreteValuationRing IsLocalRing Module


theorem finite_padic_dvr_degree
    (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Algebra (PadicInt p) R]
    [Module.Finite (PadicInt p) R] [FaithfulSMul (PadicInt p) R]
    [Finite (ResidueField R)] :
    ∃ e f : ℕ, 0 < e ∧ 0 < f ∧ addVal R (algebraMap (PadicInt p) R p) = e ∧
      Nat.card (ResidueField R) = p^f ∧ e*f = Module.finrank (PadicInt p) R := by
  let h := (ResidueField.map (algebraMap (PadicInt p) R)).comp (PadicInt.residueField (p := p)).symm.toRingHom
  let : Algebra (ZMod p) (ResidueField R) := h.toAlgebra
  let : Module.Finite (ZMod p) (ResidueField R) := Module.Finite.of_finite
  let f := Module.finrank (ZMod p) (ResidueField R)
  have hf : 0 < f := Module.finrank_pos
  have hc : Nat.card (ResidueField R) = p^f := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p)]
    simp [f]
  have hp0 : (p : PadicInt p) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpR : algebraMap (PadicInt p) R p ≠ 0 := by
    intro H
    apply hp0
    apply FaithfulSMul.algebraMap_injective (PadicInt p) R
    simpa using H
  have hefin : addVal R (algebraMap (PadicInt p) R p) ≠ ⊤ := addVal_eq_top_iff.not.mpr hpR
  let e := (addVal R (algebraMap (PadicInt p) R p)).toNat
  have he : addVal R (algebraMap (PadicInt p) R p) = e := (ENat.natCast_toNat hefin).symm
  have hen : e ≠ 0 := by
    intro he0
    have hu : IsUnit (algebraMap (PadicInt p) R p) := addVal_eq_zero_iff.mp (by simpa [he0] using he)
    have hu' := (isUnit_map_iff (algebraMap (PadicInt p) R) (p : PadicInt p)).mp hu
    have : ‖(p : PadicInt p)‖ < 1 := by
      rw [PadicInt.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    exact (ne_of_lt this) (PadicInt.isUnit_iff.mp hu')
  have hspan : Ideal.span {(p : R)} = IsLocalRing.maximalIdeal R ^ e := by
    obtain ⟨π,hπ⟩ := exists_irreducible R
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
    ext x
    rw [Ideal.mem_span_singleton,Ideal.mem_span_singleton,← addVal_le_iff_dvd,← addVal_le_iff_dvd,hπ.addVal_pow]
    rw [show addVal R (p : R) = (e : ℕ∞) by simpa only [map_natCast] using he]
  have hdim : e*f = Module.finrank (PadicInt p) R := by
    have H := cardQuot_span_prime_of_free p R
    rw [hspan,cardQuot_pow_of_prime (fun hz => IsDiscreteValuationRing.not_isField R
        (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hz)),Submodule.cardQuot_apply] at H
    change (Nat.card (ResidueField R)) ^ e = p ^ Module.finrank (PadicInt p) R at H
    rw [hc,← pow_mul,mul_comm f e] at H
    exact (Nat.pow_right_injective (Fact.out : p.Prime).one_lt) H
  exact ⟨e,f,Nat.pos_iff_ne_zero.mpr hen,hf,he,hc,hdim⟩



theorem completedMaximalOrder_exists_full_local_model
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K] :
    ∃ (I : Type u) (_ : Fintype I) (R : I → Type u) (_ : ∀ i, CommRing (R i))
      (_ : ∀ i, IsDomain (R i)) (_ : ∀ i, IsDiscreteValuationRing (R i))
      (_ : ∀ i, Algebra (PadicInt p) (R i))
      (_ : ∀ i, Finite (IsLocalRing.ResidueField (R i)))
      (_ : ∀ i, TopologicalSpace (R i)) (_ : ∀ i, IsTopologicalRing (R i))
      (_ : ∀ i, CompactSpace (R i)) (_ : ∀ i, T2Space (R i))
      (_ : ∀ i, SecondCountableTopology (R i))
      (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] Π i, R i)
      (e f : I → ℕ), Continuous E ∧ Continuous E.symm ∧
      (∀ i, 0 < e i) ∧ (∀ i, 0 < f i) ∧
      (∀ i, addVal (R i) (algebraMap (PadicInt p) (R i) p) = e i) ∧
      (∀ i, Nat.card (IsLocalRing.ResidueField (R i)) = p ^ f i) ∧
      ∑ i, f i * e i = Module.finrank ℚ K := by
  obtain ⟨I,hI,R,hR,hd,hDVR,hA,hk,hT,hTR,hc,ht,hsc,hfin,hfaith,E,hE,hE'⟩ :=
    completedMaximalOrder_exists_topological_dvr_product p K
  let : Fintype I := Fintype.ofFinite I
  choose e f he hf hv hk' hef using fun i => finite_padic_dvr_degree p (R i)
  refine ⟨I,inferInstance,R,hR,hd,hDVR,hA,hk,hT,hTR,hc,ht,hsc,E,e,f,hE,hE',he,hf,hv,hk',?_⟩
  calc
    ∑ i, f i * e i = ∑ i, Module.finrank (PadicInt p) (R i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Nat.mul_comm _ _).trans (hef i)
    _ = Module.finrank (PadicInt p) (Π i, R i) := (Module.finrank_pi_fintype _).symm
    _ = Module.finrank (PadicInt p) (completedMaximalOrder (K := K) p) := E.toLinearEquiv.finrank_eq.symm
    _ = Module.finrank ℚ K := completedMaximalOrder_finrank p K


def integralNormalizedModule {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime] :
    Submodule (PadicInt p) (completedMaximalOrder (K := K) p) :=
  (normalizedLocalModule M p).comap (completedMaximalOrder (K := K) p).val.toLinearMap



def modelLocalModule {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [Algebra (PadicInt p) R]
    (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] R) : Submodule (PadicInt p) R :=
  (integralNormalizedModule M p).map E.toLinearMap

open MeasureTheory
open scoped ENNReal


def localChoiceBase {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] : Submodule (PadicInt p) (LocalAlgebra p K) :=
  (idealLocalGenerator p I : LocalAlgebra p K) • normalizedLocalModule M p


def localUnitHaarProbability {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] : Measure (completedMaximalOrder (K := K) p)ˣ :=
  Measure.haarMeasure (⟨⟨Set.univ,isCompact_univ⟩,by simp⟩ :
    TopologicalSpace.PositiveCompacts (completedMaximalOrder (K := K) p)ˣ)

instance localUnitHaarProbability_isProbability {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] : IsProbabilityMeasure (localUnitHaarProbability (K := K) p) := by
  constructor
  exact Measure.haarMeasure_self

instance localUnitHaarProbability_isHaar {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] : (localUnitHaarProbability (K := K) p).IsHaarMeasure :=
  inferInstanceAs (Measure.haarMeasure _).IsHaarMeasure



def localIdealWeight {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime]
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ≥0∞ :=
  localUnitHaarProbability p {z : (completedMaximalOrder (K := K) p)ˣ |
    (idealLocalGenerator p J : LocalAlgebra p K) ∈
      ((z : completedMaximalOrder (K := K) p) : LocalAlgebra p K) • normalizedLocalModule M p}


def globalIdealWeight {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ≥0∞ :=
  ∏ p : labelPrimes M, localIdealWeight M p.val J

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PrimeFactors
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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


namespace PrimeDegreePackets
open MeasureTheory NumberField IsDiscreteValuationRing
open scoped ENNReal Pointwise nonZeroDivisors

 

def modelUnitProbability {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [Algebra (PadicInt p) R]
    [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace Rˣ] [BorelSpace Rˣ]
    (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] R) : Measure Rˣ :=
  (localUnitHaarProbability (K := K) p).map (Units.mapEquiv E.toMulEquiv)

lemma integral_idealLocalGenerator {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1) :
    (idealLocalGenerator p J : LocalAlgebra p K) ∈ completedMaximalOrder (K := K) p := by
  have hle := completedFractionalIdeal_mono p hJ
  apply hle
  rw [idealLocalGenerator_spec]
  simpa using Submodule.smul_mem_pointwise_smul
    (1 : LocalAlgebra p K) (idealLocalGenerator p J : LocalAlgebra p K)
    (completedMaximalOrder (K := K) p).toSubmodule (completedMaximalOrder (K := K) p).one_mem

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LocalModels
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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
namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators



lemma actualLocalModel_nonempty (p : ℕ) [Fact p.Prime] (K : Type u)
    [Field K] [NumberField K] : Nonempty (ActualLocalModel p K) := by
  obtain ⟨I,hI,R,hR,hd,hDVR,hA,hk,hT,hTR,hc,ht,hsc,E,e,f,hE,hE',he,hf,hv,hk',hef⟩ :=
    completedMaximalOrder_exists_full_local_model p K
  exact ⟨⟨I,hI,R,hR,hd,hDVR,hA,hk,hT,hTR,hc,ht,hsc,E,e,f,hE,hE',he,hf,hv,hk',hef⟩⟩

def actualLocalModel (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K] :
    ActualLocalModel p K := (actualLocalModel_nonempty p K).some

instance model_measurableSpace {p : ℕ} [Fact p.Prime] {K : Type u} [Field K] [NumberField K]
    (T : ActualLocalModel p K) (i : T.Index) : MeasurableSpace (T.Ring i) := borel _

instance model_borelSpace {p : ℕ} [Fact p.Prime] {K : Type u} [Field K] [NumberField K]
    (T : ActualLocalModel p K) (i : T.Index) : BorelSpace (T.Ring i) := ⟨rfl⟩

instance model_units_measurableSpace {p : ℕ} [Fact p.Prime] {K : Type u}
    [Field K] [NumberField K] (T : ActualLocalModel p K) :
    MeasurableSpace (∀ i, T.Ring i)ˣ := borel _

instance model_units_borelSpace {p : ℕ} [Fact p.Prime] {K : Type u}
    [Field K] [NumberField K] (T : ActualLocalModel p K) :
    BorelSpace (∀ i, T.Ring i)ˣ := ⟨rfl⟩

 
def modelAddHaarProbability {p : ℕ} [Fact p.Prime] {K : Type u} [Field K] [NumberField K]
    (T : ActualLocalModel p K) (i : T.Index) : Measure (T.Ring i) :=
  Measure.addHaarMeasure (⟨⟨Set.univ,isCompact_univ⟩,by simp⟩ :
    TopologicalSpace.PositiveCompacts (T.Ring i))

instance modelAddHaarProbability_isProbability {p : ℕ} [Fact p.Prime] {K : Type u}
    [Field K] [NumberField K] (T : ActualLocalModel p K) (i : T.Index) :
    IsProbabilityMeasure (modelAddHaarProbability T i) := by
  constructor
  exact Measure.addHaarMeasure_self

instance modelAddHaarProbability_isHaar {p : ℕ} [Fact p.Prime] {K : Type u}
    [Field K] [NumberField K] (T : ActualLocalModel p K) (i : T.Index) :
    (modelAddHaarProbability T i).IsAddHaarMeasure :=
  inferInstanceAs (Measure.addHaarMeasure _).IsAddHaarMeasure


abbrev actualValuationTuples {n : ℕ} {K : Type u} [Field K] [NumberField K]
    (M : FullLattice n K) := ∀ p : labelPrimes M, (actualLocalModel p.val K).Index → ℕ

def actualTupleWeight {n : ℕ} {K : Type u} [Field K] [NumberField K]
    (M : FullLattice n K) (k : actualValuationTuples M) : ℝ≥0∞ :=
  ∏ p : labelPrimes M, localShellProbability (actualLocalModel p.val K).Ring
    (modelUnitProbability p.val (actualLocalModel p.val K).equiv)
    (modelLocalModule M p.val (actualLocalModel p.val K).equiv) (k p)

def actualTupleNorm {n : ℕ} {K : Type u} [Field K] [NumberField K]
    (M : FullLattice n K) (k : actualValuationTuples M) : ℝ≥0∞ :=
  ∏ p : labelPrimes M, shellNorm (actualLocalModel p.val K).Ring (k p)

def actualLocalZ {n : ℕ} {K : Type u} [Field K] [NumberField K]
    (M : FullLattice n K) : ℝ≥0∞ :=
  ∏ p : labelPrimes M, (localZinv (actualLocalModel p.val K).Ring)⁻¹

end PrimeDegreePackets


namespace PrimeDegreePackets
open IsDiscreteValuationRing
open scoped BigOperators Pointwise NumberField nonZeroDivisors


def integralCompletedIdeal {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule (PadicInt p) (completedMaximalOrder (K := K) p) :=
  (completedFractionalIdeal p J).comap (completedMaximalOrder (K := K) p).val.toLinearMap

lemma integralCompletedIdeal_eq_span {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1) :
    integralCompletedIdeal p J =
      (Ideal.span ({⟨idealLocalGenerator p J, integral_idealLocalGenerator p J hJ⟩} :
        Set (completedMaximalOrder (K := K) p))).restrictScalars (PadicInt p) := by
  ext x
  change (x : LocalAlgebra p K) ∈ completedFractionalIdeal p (J : FractionalIdeal (𝓞 K)⁰ K) ↔ _
  rw [idealLocalGenerator_spec]
  change _ ↔ x ∈ Ideal.span ({⟨idealLocalGenerator p J, integral_idealLocalGenerator p J hJ⟩} :
    Set (completedMaximalOrder (K := K) p))
  rw [Ideal.mem_span_singleton]
  constructor
  · intro hx
    obtain ⟨y,hy,hxy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    refine ⟨⟨y,hy⟩, ?_⟩
    apply Subtype.ext
    exact hxy.symm
  · rintro ⟨y,hy⟩
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨y,y.property,?_⟩
    exact (congrArg Subtype.val hy).symm


def integralIdealValuations {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (T : ActualLocalModel p K)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1) : T.Index → ℕ :=
  fun i => (addVal (T.Ring i)
    (T.equiv ⟨idealLocalGenerator p J, integral_idealLocalGenerator p J hJ⟩ i)).toNat

lemma integralCompletedIdeal_model {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (T : ActualLocalModel p K)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1) :
    (integralCompletedIdeal p J).map T.equiv.toLinearMap =
      (Ideal.pi (fun i => IsLocalRing.maximalIdeal (T.Ring i) ^
        integralIdealValuations p T J hJ i)).restrictScalars (PadicInt p) := by
  rw [integralCompletedIdeal_eq_span p J hJ, map_principal_restrictScalars,
    product_dvr_principal_eq]
  · rfl
  · exact model_generator_components_ne_zero p T.equiv _ _

lemma integralCompletedIdeal_cardQuot {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (T : ActualLocalModel p K)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1) :
    (integralCompletedIdeal p J).cardQuot =
      ∏ i, p ^ (T.f i * integralIdealValuations p T J hJ i) := by
  rw [← cardQuot_map_equiv T.equiv.toLinearEquiv, integralCompletedIdeal_model p T J hJ,
    cardQuot_product_dvr_powers]
  apply Finset.prod_congr rfl
  intro i _
  rw [T.card_residue, pow_mul]

end PrimeDegreePackets


namespace PrimeDegreePackets
open NumberField
open scoped BigOperators Pointwise NumberField nonZeroDivisors ENNReal


lemma completed_ideal_primePower_mem {K : Type*} [Field K] [NumberField K]
    (J : {I : Ideal (𝓞 K) // I ≠ ⊥}) (p : ℕ) [Fact p.Prime]
    {x : LocalAlgebra p K} (hx : x ∈ completedFractionalIdeal p (1 : FractionalIdeal (𝓞 K)⁰ K)) :
    (p : PadicInt p)^((Ideal.absNorm J.1).factorization p) • x ∈
      completedFractionalIdeal p (nonzeroIntegralIdealUnit J : FractionalIdeal (𝓞 K)⁰ K) := by
  apply completedLattice_primePower_mem
    (M := fractionalIdealFullLattice (n := Module.finrank ℚ K) rfl 1)
    (N := fractionalIdealFullLattice rfl (nonzeroIntegralIdealUnit J))
    (Ideal.absNorm J.1) (fun _ hx => absNorm_smul_integral J.1 hx) p _
    (ordCompl[p] (Ideal.absNorm J.1))
    (Nat.ordProj_mul_ordCompl_eq_self (Ideal.absNorm J.1) p).symm
    (Nat.coprime_ordCompl Fact.out (Ideal.absNorm_eq_zero_iff.not.mpr J.2)) hx

lemma completed_ideal_eq_off {K : Type*} [Field K] [NumberField K]
    (J : {I : Ideal (𝓞 K) // I ≠ ⊥}) (p : ℕ) [Fact p.Prime]
    (hp : ¬ p ∣ Ideal.absNorm J.1) :
    completedFractionalIdeal p (nonzeroIntegralIdealUnit J : FractionalIdeal (𝓞 K)⁰ K) =
      completedFractionalIdeal p (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  apply le_antisymm (completedFractionalIdeal_mono p (nonzeroIntegralIdealUnit_le_one J))
  intro x hx
  simpa [Nat.factorization_eq_zero_of_not_dvd hp] using completed_ideal_primePower_mem J p hx

lemma integralCompletedIdeal_relIndex {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (integralCompletedIdeal p J).cardQuot =
      (completedFractionalIdeal p (J : FractionalIdeal (𝓞 K)⁰ K)).toAddSubgroup.relIndex
        (completedFractionalIdeal p (1 : FractionalIdeal (𝓞 K)⁰ K)).toAddSubgroup := rfl


lemma completedFractionalIdeal_eq_of_integralCompletedIdeal_eq
    {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hI : (I : FractionalIdeal (𝓞 K)⁰ K) ≤ 1)
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1)
    (h : integralCompletedIdeal p I = integralCompletedIdeal p J) :
    completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) =
      completedFractionalIdeal p (J : FractionalIdeal (𝓞 K)⁰ K) := by
  ext x
  constructor
  · intro hx
    have hx' : x ∈ completedMaximalOrder (K := K) p := completedFractionalIdeal_mono p hI hx
    have H : (⟨x,hx'⟩ : completedMaximalOrder (K := K) p) ∈ integralCompletedIdeal p I := hx
    rw [h] at H
    exact H
  · intro hx
    have hx' : x ∈ completedMaximalOrder (K := K) p := completedFractionalIdeal_mono p hJ hx
    have H : (⟨x,hx'⟩ : completedMaximalOrder (K := K) p) ∈ integralCompletedIdeal p J := hx
    rw [← h] at H
    exact H

lemma integralIdeal_completions_eq_of_valuations_eq {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (T : ActualLocalModel p K)
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hI : (I : FractionalIdeal (𝓞 K)⁰ K) ≤ 1)
    (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1)
    (h : integralIdealValuations p T I hI = integralIdealValuations p T J hJ) :
    completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) =
      completedFractionalIdeal p (J : FractionalIdeal (𝓞 K)⁰ K) := by
  apply completedFractionalIdeal_eq_of_integralCompletedIdeal_eq p I J hI hJ
  apply Submodule.map_injective_of_injective (f := T.equiv.toLinearMap) T.equiv.injective
  rw [integralCompletedIdeal_model p T I hI, integralCompletedIdeal_model p T J hJ, h]


def primaryIdealValuations {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) [∀ p : S, Fact p.val.Prime] (T : ∀ p : S, ActualLocalModel p.val K)
    (J : primaryIntegralIdeals K S) : ∀ p : S, (T p).Index → ℕ :=
  fun p => integralIdealValuations p.val (T p) (nonzeroIntegralIdealUnit J.1)
    (nonzeroIntegralIdealUnit_le_one J.1)

 

theorem primaryIdealValuations_injective {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) [∀ p : S, Fact p.val.Prime] (T : ∀ p : S, ActualLocalModel p.val K) :
    Function.Injective (primaryIdealValuations S T) := by
  intro I J h
  have H : (nonzeroIntegralIdealUnit I.1 : FractionalIdeal (𝓞 K)⁰ K) =
      (nonzeroIntegralIdealUnit J.1 : FractionalIdeal (𝓞 K)⁰ K) := by
    apply fractionalIdeal_eq_of_completions_eq
    intro p hp
    let : Fact p.Prime := ⟨hp⟩
    by_cases hs : p ∈ S
    · exact integralIdeal_completions_eq_of_valuations_eq p (T ⟨p,hs⟩) _ _ _ _ (congrFun h ⟨p,hs⟩)
    · rw [completed_ideal_eq_off I.1 p (fun hd => hs (I.2 p hp hd)),
        completed_ideal_eq_off J.1 p (fun hd => hs (J.2 p hp hd))]
  apply Subtype.ext
  apply Subtype.ext
  exact FractionalIdeal.coeIdeal_injective H

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.FullLattice.toPacket_carrier _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.globalLabels_smul_val _root_.infinitePlace_mult_smul
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


namespace PrimeDegreePackets
open NumberField IsDiscreteValuationRing
open scoped BigOperators Pointwise NumberField nonZeroDivisors ENNReal

 
def completedOrderIdealModule {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : Ideal (completedMaximalOrder (K := K) p)) :
    Submodule (PadicInt p) (LocalAlgebra p K) :=
  (I.restrictScalars (PadicInt p)).map (completedMaximalOrder (K := K) p).val.toLinearMap

lemma completedOrderIdealModule_le {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : Ideal (completedMaximalOrder (K := K) p)) :
    completedOrderIdealModule p I ≤ (completedMaximalOrder (K := K) p).toSubmodule := by
  rintro _ ⟨x,_hx,rfl⟩
  exact x.2

lemma completedOrderIdealModule_saturated {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : Ideal (completedMaximalOrder (K := K) p)) :
    (completedMaximalOrder (K := K) p).toSubmodule * completedOrderIdealModule p I =
      completedOrderIdealModule p I := by
  apply le_antisymm
  · apply Submodule.mul_le.mpr
    intro x hx y hy
    obtain ⟨z,hz,rfl⟩ := hy
    exact Submodule.mem_map.mpr ⟨(⟨x,hx⟩ : completedMaximalOrder (K := K) p) * z,
      I.mul_mem_left _ hz,rfl⟩
  · intro x hx
    have h1 : (1 : LocalAlgebra p K) ∈ (completedMaximalOrder (K := K) p).toSubmodule :=
      (completedMaximalOrder (K := K) p).one_mem
    simpa only [one_mul] using Submodule.mul_mem_mul h1 hx

lemma completedOrderIdealModule_pow_mem {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : Ideal (completedMaximalOrder (K := K) p)) (k : ℕ)
    (hk : (p : completedMaximalOrder (K := K) p)^k ∈ I)
    {x : LocalAlgebra p K} (hx : x ∈ (completedMaximalOrder (K := K) p).toSubmodule) :
    (p : PadicInt p)^k • x ∈ completedOrderIdealModule p I := by
  refine Submodule.mem_map.mpr ⟨(p : completedMaximalOrder (K := K) p)^k * ⟨x,hx⟩,
    I.mul_mem_right _ hk,?_⟩
  rw [Algebra.smul_def, map_pow, map_natCast]
  simp only [AlgHom.toLinearMap_apply, map_mul, map_pow, map_natCast, Subalgebra.val_apply]

 

theorem patch_completedOrder_ideals {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) [∀ p : S, Fact p.val.Prime]
    (I : ∀ p : S, Ideal (completedMaximalOrder (K := K) p.val))
    (k : S → ℕ) (hk : ∀ p, (p.val : completedMaximalOrder (K := K) p.val)^(k p) ∈ I p) :
    ∃ J : {J : Ideal (𝓞 K) // J ≠ ⊥},
      (∀ p : S, completedFractionalIdeal p.val (J.1 : FractionalIdeal (𝓞 K)⁰ K) =
        completedOrderIdealModule p.val (I p)) ∧
      ∀ (r : ℕ) (hr : r.Prime), letI : Fact r.Prime := ⟨hr⟩;
        r ∉ S → completedFractionalIdeal r (J.1 : FractionalIdeal (𝓞 K)⁰ K) =
          completedFractionalIdeal r (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  classical
  let M := fractionalIdealFullLattice (K := K) rfl (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  obtain ⟨L,hLM,hL,hLoff⟩ := patch_fullLattice_completions M rfl
    (fun p : S => p.val) Subtype.val_injective k
    (fun p => completedOrderIdealModule p.val (I p))
    (fun p => completedOrderIdealModule_le p.val (I p))
    (fun p _ hx => completedOrderIdealModule_pow_mem p.val (I p) (k p) (hk p) hx)
  have hle : saturationFractionalIdeal L ≤ 1 := by
    change Submodule.span (𝓞 K) (L.carrier : Set K) ≤ _
    exact Submodule.span_le.mpr hLM
  obtain ⟨J,hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hJ0 : J ≠ ⊥ := by
    intro hz
    have H := saturationFractionalIdeal_ne_zero L
    exact H (by simpa [hz] using hJ.symm)
  refine ⟨⟨J,hJ0⟩,?_,?_⟩
  · intro p
    rw [hJ,completed_saturation,hL p,completedOrderIdealModule_saturated]
  · intro r hr
    let : Fact r.Prime := ⟨hr⟩
    intro hnot
    rw [hJ,completed_saturation,hLoff r hr (by simpa using hnot)]
    exact (completedMaximalOrder (K := K) r).isIdempotentElem_toSubmodule.eq

lemma integralIdeal_norm_product_of_off {K : Type*} [Field K] [NumberField K]
    (J : {I : Ideal (𝓞 K) // I ≠ ⊥}) (S : Finset ℕ) [∀ p : S, Fact p.val.Prime]
    (hoff : ∀ (r : ℕ) (hr : r.Prime), letI : Fact r.Prime := ⟨hr⟩;
      r ∉ S → completedFractionalIdeal r (J.1 : FractionalIdeal (𝓞 K)⁰ K) =
        completedFractionalIdeal r (1 : FractionalIdeal (𝓞 K)⁰ K))
    (T : ∀ p : S, ActualLocalModel p.val K) :
    Ideal.absNorm J.1 = ∏ p : S, ∏ i, p.val ^ ((T p).f i *
      integralIdealValuations p.val (T p) (nonzeroIntegralIdealUnit J)
        (nonzeroIntegralIdealUnit_le_one J) i) := by
  let U := nonzeroIntegralIdealUnit J
  have H := fullLattice_relIndex_eq_prod_local
    (fractionalIdealFullLattice (n := Module.finrank ℚ K) rfl 1)
    (fractionalIdealFullLattice rfl U) rfl (fun p : S => p.val) Subtype.val_injective
    (fun p => (Ideal.absNorm J.1).factorization p.val)
    (fun p _ hx => completed_ideal_primePower_mem J p.val hx)
    (by
      intro p hp
      let : Fact p.Prime := ⟨hp⟩
      intro hnot
      exact hoff p hp (fun hd => hnot ⟨⟨p,hd⟩,rfl⟩))
  rw [fullLattice_ideal_relIndex] at H
  apply H.trans
  apply Finset.prod_congr rfl
  intro p _
  change (completedFractionalIdeal p.val (U : FractionalIdeal (𝓞 K)⁰ K)).toAddSubgroup.relIndex
    (completedFractionalIdeal p.val (1 : FractionalIdeal (𝓞 K)⁰ K)).toAddSubgroup = _
  rw [← integralCompletedIdeal_relIndex]
  exact integralCompletedIdeal_cardQuot p.val (T p) U (nonzeroIntegralIdealUnit_le_one J)

lemma integralIdeal_support_of_off {K : Type*} [Field K] [NumberField K]
    (J : {I : Ideal (𝓞 K) // I ≠ ⊥}) (S : Finset ℕ) [∀ p : S, Fact p.val.Prime]
    (hoff : ∀ (r : ℕ) (hr : r.Prime), letI : Fact r.Prime := ⟨hr⟩;
      r ∉ S → completedFractionalIdeal r (J.1 : FractionalIdeal (𝓞 K)⁰ K) =
        completedFractionalIdeal r (1 : FractionalIdeal (𝓞 K)⁰ K)) :
    ∀ r, r.Prime → r ∣ Ideal.absNorm J.1 → r ∈ S := by
  classical
  intro r hr hd
  rw [integralIdeal_norm_product_of_off J S hoff (fun p => actualLocalModel p.val K)] at hd
  obtain ⟨p,_hp,hd⟩ := (hr.prime.dvd_finsetProd_iff _).mp hd
  obtain ⟨i,_hi,hd⟩ := (hr.prime.dvd_finsetProd_iff _).mp hd
  have he : r = p.val := ((Nat.dvd_prime (Fact.out : p.val.Prime)).mp (hr.dvd_of_dvd_pow hd)).resolve_left hr.ne_one
  exact he ▸ p.2

lemma modelIdeal_pow_mem {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (T : ActualLocalModel p K) (k : T.Index → ℕ) :
    (p : completedMaximalOrder (K := K) p)^(∑ i, k i) ∈
      Ideal.comap T.equiv.toRingHom (Ideal.pi (fun i => IsLocalRing.maximalIdeal (T.Ring i)^k i)) := by
  classical
  rw [Ideal.mem_comap]
  change T.equiv ((p : completedMaximalOrder (K := K) p)^(∑ i, k i)) ∈ _
  rw [map_pow,map_natCast]
  intro i
  rw [mem_maximalIdeal_pow_iff_addVal]
  change (k i : ℕ∞) ≤ addVal (T.Ring i) ((p : T.Ring i)^(∑ j, k j))
  rw [addVal_pow, show addVal (T.Ring i) (p : T.Ring i) = T.e i from by
    simpa only [map_natCast] using T.valuation_p i]
  simp only [nsmul_eq_mul, ← Nat.cast_mul]
  exact_mod_cast (Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)).trans
    (Nat.le_mul_of_pos_right _ (T.e_pos i))


theorem primaryIdealValuations_surjective {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) [∀ p : S, Fact p.val.Prime] (T : ∀ p : S, ActualLocalModel p.val K) :
    Function.Surjective (primaryIdealValuations S T) := by
  classical
  intro k
  let I (p : S) := Ideal.comap (T p).equiv.toRingHom
    (Ideal.pi (fun i => IsLocalRing.maximalIdeal ((T p).Ring i) ^ k p i))
  obtain ⟨J,hJ,hJoff⟩ := patch_completedOrder_ideals S I (fun p => ∑ i, k p i)
    (fun p => modelIdeal_pow_mem p.val (T p) (k p))
  let J' : primaryIntegralIdeals K S := ⟨J,integralIdeal_support_of_off J S hJoff⟩
  refine ⟨J', ?_⟩
  funext p
  have hc : integralCompletedIdeal p.val (nonzeroIntegralIdealUnit J) =
      (I p).restrictScalars (PadicInt p.val) := by
    change (completedFractionalIdeal p.val (J.1 : FractionalIdeal (𝓞 K)⁰ K)).comap _ = _
    rw [hJ p]
    exact Submodule.comap_map_eq_of_injective
      (Subtype.val_injective : Function.Injective
        (completedMaximalOrder (K := K) p.val).val.toLinearMap) _
  have hm : ((I p).restrictScalars (PadicInt p.val)).map (T p).equiv.toLinearMap =
      (Ideal.pi (fun i => IsLocalRing.maximalIdeal ((T p).Ring i) ^ k p i)).restrictScalars
        (PadicInt p.val) := by
    change (Submodule.comap (T p).equiv.toLinearMap
      ((Ideal.pi (fun i => IsLocalRing.maximalIdeal ((T p).Ring i) ^ k p i)).restrictScalars
        (PadicInt p.val))).map (T p).equiv.toLinearMap = _
    exact Submodule.map_comap_eq_of_surjective (T p).equiv.surjective _
  have H := integralCompletedIdeal_model p.val (T p) (nonzeroIntegralIdealUnit J)
    (nonzeroIntegralIdealUnit_le_one J)
  rw [hc,hm] at H
  have HI : Ideal.pi (fun i => IsLocalRing.maximalIdeal ((T p).Ring i) ^ k p i) =
      Ideal.pi (fun i => IsLocalRing.maximalIdeal ((T p).Ring i) ^
        primaryIdealValuations S T J' p i) := by
    ext x
    exact SetLike.ext_iff.mp H x
  have Hp := ideal_pi_injective (T p).Ring HI
  funext i
  apply dvr_power_injective ((T p).Ring i)
  exact (congrFun Hp i).symm

def primaryIdealValuationEquiv {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) [∀ p : S, Fact p.val.Prime] (T : ∀ p : S, ActualLocalModel p.val K) :
    primaryIntegralIdeals K S ≃ (∀ p : S, (T p).Index → ℕ) :=
  Equiv.ofBijective (primaryIdealValuations S T)
    ⟨primaryIdealValuations_injective S T,primaryIdealValuations_surjective S T⟩

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LocalEuler
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid


namespace PrimeDegreePackets
open NumberField Finset
open scoped BigOperators ENNReal nonZeroDivisors


noncomputable def weightedIdealInterval {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (a b : ℕ) : ℝ≥0∞ :=
  ∑' I : {J : Ideal (𝓞 K) // J ≠ ⊥},
    if a < Ideal.absNorm I.1 ∧ Ideal.absNorm I.1 ≤ b
    then globalIdealWeight M (nonzeroIntegralIdealUnit I) else 0



end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaResidues
attribute [-instance] _root_.CyclicCohomology.permutationSublattice_discreteTopology _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.coordinateLattice_discrete _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.EmbeddingOrder.toRealOrder_apply _root_.OAI.DukePrimeDegree.FullLattice.toPacket_carrier _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.euclideanRowBasis_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk _root_.OAI.PrimeDegreePackets.rowBasis_apply _root_.infinitePlace_mult_smul
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
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField


namespace PrimeDegreePackets
open Filter Topology
open scoped ENNReal NumberField

 

noncomputable def weightedIdealRealInterval {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (x y : ℝ) : ℝ≥0∞ :=
  ∑' I : {J : Ideal (𝓞 K) // J ≠ ⊥},
    if x-y < (Ideal.absNorm I.1:ℝ) ∧ (Ideal.absNorm I.1:ℝ) ≤ x
    then globalIdealWeight M (nonzeroIntegralIdealUnit I) else 0

end PrimeDegreePackets

open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
namespace PrimeDegreePackets

open scoped NumberField nonZeroDivisors



lemma scaled_integralElements_le_multiplierOrder {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) :
    (integralElements K).map (nsmulAddMonoidHom (saturationIndex M)) ≤ multiplierOrder M := by
  rintro _ ⟨a, ha, rfl⟩ x hx
  change (saturationIndex M • a) * x ∈ M.carrier
  rw [smul_mul_assoc]
  apply saturationIndex_smul_mem
  change a * x ∈ Submodule.span (𝓞 K) (M.carrier : Set K)
  exact Submodule.smul_mem _ (⟨a, ha⟩ : 𝓞 K) (Submodule.subset_span hx)



def packetScale {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : ℝ := saturationIndex M * Real.sqrt |(NumberField.discr K : ℝ)|



def unitsReduction {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) :
    (𝓞 K)ˣ →* (𝓞 K ⧸ Ideal.span {(saturationIndex M : 𝓞 K)})ˣ :=
  Units.map (Ideal.Quotient.mk (Ideal.span {(saturationIndex M : 𝓞 K)})).toMonoidHom

lemma unitsReduction_one_preserves {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (u : (𝓞 K)ˣ) (hu : unitsReduction M u = 1)
    {x : K} (hx : x ∈ M.carrier) : (integralUnit u : K) * x ∈ M.carrier := by
  have hu' : Ideal.Quotient.mk (Ideal.span {(saturationIndex M : 𝓞 K)}) (u : 𝓞 K) = 1 :=
    congrArg Units.val hu
  have hz : (u : 𝓞 K) - 1 ∈ Ideal.span {(saturationIndex M : 𝓞 K)} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, hu', map_one, sub_self]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hz
  have hax : (a : K) * x ∈ saturation M := by
    exact Submodule.smul_mem (Submodule.span (𝓞 K) (M.carrier : Set K)) a
      (Submodule.subset_span hx)
  have hqx := saturationIndex_smul_mem M hax
  have heq : (integralUnit u : K) * x = x + saturationIndex M • ((a : K) * x) := by
    have H := congrArg (algebraMap (𝓞 K) K) ha
    change ((u : 𝓞 K) : K) * x = _
    simp only [map_sub, map_one, map_mul, map_natCast] at H
    rw [nsmul_eq_mul]
    linear_combination H * x
  rw [heq]
  exact M.carrier.add_mem hx hqx

lemma unitsReduction_ker_le_stabilizer {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : (unitsReduction M).ker ≤ unitStabilizer M := by
  intro u hu
  change unitsReduction M u = 1 at hu
  intro x
  constructor
  · exact unitsReduction_one_preserves M u hu
  · intro hx
    have h := unitsReduction_one_preserves M u⁻¹ (by simp [hu]) hx
    simpa [← mul_assoc] using h



theorem positiveUnitStabilizer_finiteIndex {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) :
    (positiveUnitStabilizer M σ).FiniteIndex := by
  have hq : (saturationIndex M : 𝓞 K) ≠ 0 := by
    exact_mod_cast saturationIndex_ne_zero M
  let : Finite (𝓞 K ⧸ Ideal.span {(saturationIndex M : 𝓞 K)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hq)
  apply Subgroup.finiteIndex_of_le (H := ((unitsReduction M).prod (unitSigns σ)).ker)
  intro u hu
  have h : unitsReduction M u = 1 ∧ unitSigns σ u = 1 := by
    change (unitsReduction M u, unitSigns σ u) = (1, 1) at hu
    exact Prod.mk.inj hu
  exact ⟨unitsReduction_ker_le_stabilizer M h.1, h.2⟩



theorem positiveStabilizer_fullLogLattice {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d + 1) K)
    (σ : OrderedEmbeddings (d + 1) K) :
    DiscreteTopology (orderedLogSubgroup σ (positiveUnitStabilizer M σ)) ∧
      IsZLattice ℝ (orderedLogSubgroup σ (positiveUnitStabilizer M σ)) := by
  let := positiveUnitStabilizer_finiteIndex M σ
  exact ⟨inferInstance, inferInstance⟩



lemma exists_integral_mul_of_rowLattice_eq {n : ℕ} (g h : G n)
    (hgh : rowLattice g.1 = rowLattice h.1) :
    ∃ A : Matrix.SpecialLinearGroup (Fin n) ℤ,
      g = Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A * h := by
  obtain ⟨A, hA⟩ := exists_int_matrix_of_rowLattice_le g.1 h.1 hgh.le
  have hdet : A.det = 1 := by
    have hd := congrArg Matrix.det hA
    rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, Matrix.SpecialLinearGroup.det_coe,
      mul_one] at hd
    have hmap : (A.map (Int.castRingHom ℝ)).det = (A.det : ℝ) :=
      (Int.castRingHom ℝ).map_det A |>.symm
    rw [hmap] at hd
    exact_mod_cast hd.symm
  refine ⟨⟨A, hdet⟩, ?_⟩
  exact Subtype.ext hA

 

theorem quotient_eq_iff_rowLattice_eq {n : ℕ} (g h : G n) :
    (Quotient.mk (QuotientGroup.rightRel (integralGroup n)) g : X n) = Quotient.mk _ h ↔
      rowLattice g.1 = rowLattice h.1 := by
  constructor
  · intro heq
    have H := Quotient.exact heq
    change (QuotientGroup.rightRel (integralGroup n)) g h at H
    rw [QuotientGroup.rightRel_apply] at H
    obtain ⟨A, hA⟩ := H
    have hh : h = Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A * g := by
      rw [hA, inv_mul_cancel_right]
    rw [hh]
    exact (rowLattice_integral_mul A g).symm
  · intro H
    obtain ⟨A, rfl⟩ := exists_integral_mul_of_rowLattice_eq g h H
    apply Quotient.sound
    change (QuotientGroup.rightRel (integralGroup n))
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A * h) h
    rw [QuotientGroup.rightRel_apply]
    exact ⟨A⁻¹, by simp [mul_inv_rev]⟩



theorem diagonal_into_lattice_is_field_multiplication
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (σ : OrderedEmbeddings n K) (t : Fin n → ℝ)
    (h : M.carrier.map ((diagonalLinear n t).comp (realEmbeddingMap σ)) ≤
      N.carrier.map (realEmbeddingMap σ)) :
    ∃ b : K, ∀ i, t i = σ i b := by
  obtain ⟨α, hα, hα0⟩ := fullLattice_exists_ne_zero M
  have hv := h (Submodule.mem_map.mpr ⟨α, hα, rfl⟩)
  obtain ⟨β, _, hβ⟩ := Submodule.mem_map.mp hv
  refine ⟨β / α, fun i => ?_⟩
  have hi : σ i β = t i * σ i α := congrFun hβ i
  rw [map_div₀]
  exact (eq_div_iff ((map_ne_zero (σ i)).mpr hα0)).mpr hi.symm

 

theorem diagonal_lattice_equality_iff_homothety
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (σ : OrderedEmbeddings n K) (hn : 0 < n)
    (t : Fin n → ℝ) (ht : ∀ i, t i ≠ 0)
    (h : M.carrier.map ((diagonalLinear n t).comp (realEmbeddingMap σ)) =
      N.carrier.map (realEmbeddingMap σ)) :
    ∃ b : K, b ≠ 0 ∧ (∀ i, t i = σ i b) ∧
      (N.carrier : Set K) = (fun x => b * x) '' (M.carrier : Set K) := by
  obtain ⟨b, hb⟩ := diagonal_into_lattice_is_field_multiplication M N σ t h.le
  refine ⟨b, ?_, hb, ?_⟩
  · intro hb0
    exact ht ⟨0, hn⟩ (by simp [hb, hb0])
  · ext x
    constructor
    · intro hx
      have he : realEmbeddingMap σ x ∈ N.carrier.map (realEmbeddingMap σ) :=
        Submodule.mem_map.mpr ⟨x, hx, rfl⟩
      rw [← h] at he
      obtain ⟨y, hy, he⟩ := Submodule.mem_map.mp he
      refine ⟨y, hy, ?_⟩
      apply realEmbeddingMap_injective σ hn
      ext i
      change σ i (b * y) = σ i x
      rw [map_mul, ← hb i]
      exact congrFun he i
    · rintro ⟨y, hy, rfl⟩
      have he : (diagonalLinear n t).comp (realEmbeddingMap σ) y ∈
          M.carrier.map ((diagonalLinear n t).comp (realEmbeddingMap σ)) :=
        Submodule.mem_map.mpr ⟨y, hy, rfl⟩
      rw [h] at he
      obtain ⟨x, hx, he⟩ := Submodule.mem_map.mp he
      have hxy : x = b * y := by
        apply realEmbeddingMap_injective σ hn
        ext i
        change σ i x = σ i (b * y)
        rw [map_mul, ← hb i]
        exact congrFun he i
      change b * y ∈ N.carrier
      rwa [← hxy]

lemma rowLattice_smul {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    rowLattice (c • B) = (rowLattice B).map (diagonalLinear n (fun _ => c)) := by
  unfold rowLattice
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

lemma diagonalLinear_commute {n : ℕ} (s t : Fin n → ℝ) :
    (diagonalLinear n s).comp (diagonalLinear n t) =
      (diagonalLinear n t).comp (diagonalLinear n s) := by
  ext x i
  simp [diagonalLinear, mul_left_comm]

 

lemma embeddedLattice_unit_invariant {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (u : (𝓞 K)ˣ)
    (hu : u ∈ unitStabilizer M) :
    (M.carrier.map (realEmbeddingMap σ)).map
      (diagonalLinear n (fun i => σ i (u : K))) = M.carrier.map (realEmbeddingMap σ) := by
  apply le_antisymm
  · rintro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    refine Submodule.mem_map.mpr ⟨(u : K) * z, (hu z).mp hz, ?_⟩
    ext i
    exact map_mul (σ i) _ _
  · rintro x hx
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hx
    refine Submodule.mem_map.mpr ⟨realEmbeddingMap σ ((↑u⁻¹ : K) * z),
      Submodule.mem_map.mpr ⟨_, ((unitStabilizer M).inv_mem hu z).mp hz, rfl⟩, ?_⟩
    ext i
    change σ i (u : K) * σ i ((↑u⁻¹ : K) * z) = σ i z
    rw [map_mul, ← mul_assoc, ← map_mul]
    simp

 

lemma normalizedLattice_unit_invariant {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (u : (𝓞 K)ˣ)
    (hu : u ∈ unitStabilizer M) :
    (normalizedLattice M σ).map (diagonalLinear n (fun i => σ i (u : K))) =
      normalizedLattice M σ := by
  unfold normalizedLattice
  rw [rowLattice_smul, rowLattice_embeddingMatrix, ← Submodule.map_comp,
    diagonalLinear_commute, Submodule.map_comp, embeddedLattice_unit_invariant M σ u hu]

lemma latticePoint_eq_of_rowLattice_eq {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (g : G n)
    (hg : rowLattice g.1 = normalizedLattice M σ) :
    latticePoint M σ = Quotient.mk _ g := by
  have H : ∃ g : G n, rowLattice g.1 = normalizedLattice M σ := ⟨g, hg⟩
  unfold latticePoint
  rw [dite_eq_left H]
  exact (quotient_eq_iff_rowLattice_eq _ _).mpr (H.choose_spec.trans hg.symm)

 

theorem orderedLogSubgroup_le_periodGroup {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d + 1) K)
    (σ : OrderedEmbeddings (d + 1) K) (hn : Module.finrank ℚ K = d + 1)
    (hodd : Odd (d + 1)) :
    (orderedLogSubgroup σ (positiveUnitStabilizer M σ)).toAddSubgroup ≤
      periodGroup (latticePoint M σ) := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := (mem_orderedLogSubgroup σ _ v).mp hv
  have H := (mem_positiveUnitStabilizer M σ u).mp hu
  obtain ⟨g, hg⟩ := exists_SL_normalizedLattice M σ hn hodd
  change orbitMap (latticePoint M σ) (orderedUnitLog σ (Additive.ofMul u)) = _
  rw [latticePoint_eq_of_rowLattice_eq M σ g hg]
  apply (quotient_eq_iff_rowLattice_eq _ _).mpr
  change rowLattice (g.1 * (diagonalFlow (orderedUnitLog σ (Additive.ofMul u))).1) = _
  rw [diagonalFlow_orderedUnitLog σ u H.2, rowLattice_mul_diagonal, hg]
  exact normalizedLattice_unit_invariant M σ u H.1



theorem latticePoint_period_isZLattice {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d + 1) K)
    (σ : OrderedEmbeddings (d + 1) K) (hn : Module.finrank ℚ K = d + 1)
    (hodd : Odd (d + 1)) : IsZLattice ℝ (periodGroup (latticePoint M σ)).toIntSubmodule := by
  let L := orderedLogSubgroup σ (positiveUnitStabilizer M σ)
  let : IsZLattice ℝ L := (positiveStabilizer_fullLogLattice M σ).2
  constructor
  apply top_unique
  rw [← IsZLattice.span_top (K := ℝ) (L := L)]
  apply Submodule.span_mono
  exact orderedLogSubgroup_le_periodGroup M σ hn hodd



theorem packetBasepoint_period_isZLattice {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {M : FullLattice (d + 1) K}
    {σ : OrderedEmbeddings (d + 1) K} (hn : Module.finrank ℚ K = d + 1)
    (hodd : Odd (d + 1)) (O : packetOrbits M σ) :
    IsZLattice ℝ (periodGroup (orbitBasepoint O)).toIntSubmodule := by
  obtain ⟨M', _, w, hw, hO⟩ := O.property
  have heq := periodGroup_eq_of_diagonalOrbit_eq ((orbitBasepoint_spec O).trans hO)
  rw [periodGroup_rightAction_of_diagonal _ _ hw.1] at heq
  constructor
  change Submodule.span ℝ (↑(periodGroup (orbitBasepoint O)) : Set (LogCoordinates d)) = ⊤
  rw [heq]
  exact (latticePoint_period_isZLattice M' σ hn hodd).span_top

theorem packetBasepoint_volume_pos_finite {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {M : FullLattice (d + 1) K}
    {σ : OrderedEmbeddings (d + 1) K} (hn : Module.finrank ℚ K = d + 1)
    (hodd : Odd (d + 1)) (O : packetOrbits M σ) :
    orbitVolume (orbitBasepoint O) ≠ 0 ∧ orbitVolume (orbitBasepoint O) ≠ ⊤ := by
  let := packetBasepoint_period_isZLattice hn hodd O
  exact orbitVolume_ne_zero_ne_top _

theorem packetBasepoint_probability {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {M : FullLattice (d + 1) K}
    {σ : OrderedEmbeddings (d + 1) K} (hn : Module.finrank ℚ K = d + 1)
    (hodd : Odd (d + 1)) (O : packetOrbits M σ) :
    IsProbabilityMeasure (orbitProbability (orbitBasepoint O)) := by
  let := packetBasepoint_period_isZLattice hn hodd O
  exact orbitProbability_isProbabilityMeasure _



theorem multiplierOrder_eq_of_locallyHomothetic {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (hn : Module.finrank ℚ K = n) (hMN : LocallyHomothetic M N) :
    multiplierOrder M = multiplierOrder N := by
  ext a
  constructor
  · intro ha x hx
    apply (mem_fullLattice_iff_forall_completed N hn (a * x)).mpr
    intro p hp
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨c, hc⟩ := hMN p hp
    have hx' : Algebra.TensorProduct.includeRight (R := ℚ) (A := Padic p) x ∈
        (completedLattice p N : Set (LocalAlgebra p K)) :=
      Submodule.subset_span ⟨x, hx, rfl⟩
    rw [hc] at hx'
    obtain ⟨z, hz, heq⟩ := hx'
    rw [map_mul]
    change _ ∈ (completedLattice p N : Set (LocalAlgebra p K))
    rw [hc]
    refine ⟨Algebra.TensorProduct.includeRight (R := ℚ) (A := Padic p) a * z,
      completedLattice_mul_mem M ha p hz, ?_⟩
    rw [← heq]
    ring
  · intro ha x hx
    apply (mem_fullLattice_iff_forall_completed M hn (a * x)).mpr
    intro p hp
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨c, hc⟩ := hMN p hp
    have hx' : (c : LocalAlgebra p K) * Algebra.TensorProduct.includeRight (R := ℚ) (A := Padic p) x ∈
        completedLattice p N := by
      change _ ∈ (completedLattice p N : Set (LocalAlgebra p K))
      rw [hc]
      exact ⟨_, Submodule.subset_span ⟨x, hx, rfl⟩, rfl⟩
    have H := completedLattice_mul_mem N ha p hx'
    change _ ∈ (completedLattice p N : Set (LocalAlgebra p K)) at H
    rw [hc] at H
    obtain ⟨z, hz, heq⟩ := H
    have hz' : z = Algebra.TensorProduct.includeRight (R := ℚ) (A := Padic p) (a * x) := by
      apply (Units.isUnit c).mul_left_cancel
      rw [map_mul]
      change (c : LocalAlgebra p K) * z = _ at heq
      rw [heq]
      ring
    rwa [← hz']

theorem uniform_saturation_denominator {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (hn : Module.finrank ℚ K = n) (hMN : LocallyHomothetic M N)
    {x : K} (hx : x ∈ saturation N) : saturationIndex M • x ∈ N.carrier := by
  have horder := multiplierOrder_eq_of_locallyHomothetic M N hn hMN
  have hmult (r : 𝓞 K) : saturationIndex M • (r : K) ∈ multiplierOrder N := by
    rw [← horder]
    apply scaled_integralElements_le_multiplierOrder M
    exact ⟨r, r.property, rfl⟩
  have H : ∀ r : 𝓞 K, (saturationIndex M • (r : K)) * x ∈ N.carrier := by
    change x ∈ Submodule.span (𝓞 K) (N.carrier : Set K) at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact fun r => hmult r y hy
    | zero => simp
    | add y z hy hz ihy ihz =>
      intro r
      rw [mul_add]
      exact N.carrier.add_mem (ihy r) (ihz r)
    | smul a y hy ih =>
      intro r
      simpa [Algebra.smul_def, nsmul_eq_mul, mul_assoc] using ih (r * a)
  simpa using H 1

open scoped Pointwise



theorem finite_packet_labels {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (J : Submodule ℤ K)
    (hJ : J.FG) :
    {P : Submodule ℤ K | ∃ N : FullLattice n K,
      LocallyHomothetic M N ∧ saturation N = J ∧ N.carrier = P}.Finite := by
  apply (finite_submodules_between J hJ (saturationIndex M) (saturationIndex_ne_zero M)).subset
  rintro P ⟨N, hMN, rfl, rfl⟩
  refine ⟨?_, le_saturation N⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  simpa using uniform_saturation_denominator M N hn hMN hy

open FractionalIdeal



theorem exists_scale_to_classRepresentative (K : Type*) [Field K] [NumberField K]
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    ∃ c : ClassGroup (𝓞 K), ∃ x : K, x ≠ 0 ∧
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x * I = classRepresentative K c := by
  let U := Units.mk0 I hI
  let c := ClassGroup.mk K U
  have heq : ClassGroup.mk K U = ClassGroup.mk K (classRepresentative K c) := by
    rw [classRepresentative_spec]
  exact ⟨c, (fractionalIdeal_same_class U (classRepresentative K c)).mp heq⟩



theorem exists_scale_to_representative {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : ∃ a : Kˣ, ∃ c : ClassGroup (𝓞 K),
      saturationFractionalIdeal (scaleFullLattice M a) = classRepresentative K c := by
  obtain ⟨c, x, hx, he⟩ := exists_scale_to_classRepresentative K
    (saturationFractionalIdeal M) (saturationFractionalIdeal_ne_zero M)
  refine ⟨Units.mk0 x hx, c, ?_⟩
  rw [saturationFractionalIdeal_scale]
  exact he

 

theorem finite_normalized_packet_carriers {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) :
    {P : Submodule ℤ K | ∃ N : FullLattice n K, LocallyHomothetic M N ∧
      (∃ c : ClassGroup (𝓞 K), saturationFractionalIdeal N = classRepresentative K c) ∧
      N.carrier = P}.Finite := by
  let J : ClassGroup (𝓞 K) → Submodule ℤ K := fun c =>
    (((classRepresentative K c : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K).restrictScalars ℤ
  have hJ (c : ClassGroup (𝓞 K)) : (J c).FG :=
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl
      ((classRepresentative K c : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)).restrictScalars
  apply (Set.finite_iUnion fun c => finite_packet_labels M hn (J c) (hJ c)).subset
  rintro P ⟨N, hMN, ⟨c, hc⟩, rfl⟩
  apply Set.mem_iUnion.mpr
  refine ⟨c, N, hMN, ?_, rfl⟩
  exact congrArg (fun I : FractionalIdeal (𝓞 K)⁰ K =>
    (I : Submodule (𝓞 K) K).restrictScalars ℤ) hc



theorem normalizedLattice_eq_of_carrier_eq {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n)
    (hMN : M.carrier = N.carrier) : normalizedLattice M σ = normalizedLattice N σ := by
  have hrow : rowLattice (embeddingMatrix M σ) = rowLattice (embeddingMatrix N σ) := by
    rw [rowLattice_embeddingMatrix, rowLattice_embeddingMatrix, hMN]
  have hdet := abs_det_eq_of_rowLattice_eq _ _ (embeddingMatrix_det_ne_zero M σ hn)
    (embeddingMatrix_det_ne_zero N σ hn) hrow
  dsimp only [normalizedLattice]
  rw [rowLattice_smul, rowLattice_smul, hdet, hrow]

 

theorem latticePoint_eq_of_carrier_eq {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n)
    (hodd : Odd n) (hMN : M.carrier = N.carrier) : latticePoint M σ = latticePoint N σ := by
  obtain ⟨g, hg⟩ := exists_SL_normalizedLattice M σ hn hodd
  have hgN : rowLattice g.1 = normalizedLattice N σ :=
    hg.trans (normalizedLattice_eq_of_carrier_eq M N σ hn hMN)
  rw [latticePoint_eq_of_rowLattice_eq M σ g hg, latticePoint_eq_of_rowLattice_eq N σ g hgN]

 

theorem normalizedLattice_scale_diagonal {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n)
    (hpos : 0 < n) (a : Kˣ) :
    ∃ t : Fin n → ℝ, |(Matrix.diagonal t).det| = 1 ∧
      normalizedLattice (scaleFullLattice M a) σ =
        (normalizedLattice M σ).map (diagonalLinear n t) := by
  let B := embeddingMatrix M σ
  let C := embeddingMatrix (scaleFullLattice M a) σ
  let b : ℝ := |B.det| ^ (-(1 : ℝ) / n)
  let c : ℝ := |C.det| ^ (-(1 : ℝ) / n)
  have hb : b ≠ 0 := (Real.rpow_pos_of_pos
    (abs_pos.mpr (embeddingMatrix_det_ne_zero M σ hn)) _).ne'
  let t : Fin n → ℝ := fun i => c / b * σ i (a : K)
  have he : c • C = (b • B) * Matrix.diagonal t := by
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    change c * σ j ((scaleFullLattice M a).basis i : K) =
      b * σ j (M.basis i : K) * (c / b * σ j (a : K))
    rw [scaleFullLattice_basis, map_mul]
    field_simp [hb]
  have hdB : |(b • B).det| = 1 := normalizedMatrix_abs_det B hpos
    (embeddingMatrix_det_ne_zero M σ hn)
  have hdC : |(c • C).det| = 1 := normalizedMatrix_abs_det C hpos
    (embeddingMatrix_det_ne_zero (scaleFullLattice M a) σ hn)
  rw [he, Matrix.det_mul, abs_mul, hdB, one_mul] at hdC
  refine ⟨t, hdC, ?_⟩
  change rowLattice (c • C) = (rowLattice (b • B)).map (diagonalLinear n t)
  rw [he, rowLattice_mul_diagonal]

 

theorem latticePoint_scale_diagonal {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n)
    (hodd : Odd n) (a : Kˣ) :
    ∃ D : G n, (∀ i j, i ≠ j → D.1 i j = 0) ∧
      latticePoint (scaleFullLattice M a) σ = rightAction (latticePoint M σ) D := by
  obtain ⟨t, hdet, ht⟩ := normalizedLattice_scale_diagonal M σ hn hodd.pos a
  obtain ⟨g, hg⟩ := exists_SL_normalizedLattice M σ hn hodd
  have hrow : rowLattice (g.1 * Matrix.diagonal t) =
      normalizedLattice (scaleFullLattice M a) σ := by
    rw [rowLattice_mul_diagonal, hg, ← ht]
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hdet with hd | hd
  · let D : G n := ⟨Matrix.diagonal t, hd⟩
    refine ⟨D, fun i j hij => Matrix.diagonal_apply_ne _ hij, ?_⟩
    rw [latticePoint_eq_of_rowLattice_eq M σ g hg,
      latticePoint_eq_of_rowLattice_eq (scaleFullLattice M a) σ (g * D) hrow]
    rfl
  · have hneg : (-Matrix.diagonal t).det = 1 := by
      rw [Matrix.det_neg, Fintype.card_fin, hodd.neg_one_pow, hd]
      norm_num
    let D : G n := ⟨-Matrix.diagonal t, hneg⟩
    have hrow' : rowLattice (g * D).1 = normalizedLattice (scaleFullLattice M a) σ := by
      change rowLattice (g.1 * -Matrix.diagonal t) = _
      rw [Matrix.mul_neg, rowLattice_neg, hrow]
    refine ⟨D, ?_, ?_⟩
    · intro i j hij
      change -(Matrix.diagonal t i j) = 0
      rw [Matrix.diagonal_apply_ne _ hij, neg_zero]
    · rw [latticePoint_eq_of_rowLattice_eq M σ g hg,
        latticePoint_eq_of_rowLattice_eq (scaleFullLattice M a) σ (g * D) hrow']
      rfl



theorem packetOrbits_finite {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d + 1) K) (σ : OrderedEmbeddings (d + 1) K)
    (hn : Module.finrank ℚ K = d + 1) (hodd : Odd (d + 1)) :
    (packetOrbits M σ).Finite := by
  let C := {P : Submodule ℤ K | ∃ N : FullLattice (d + 1) K, LocallyHomothetic M N ∧
    (∃ c : ClassGroup (𝓞 K), saturationFractionalIdeal N = classRepresentative K c) ∧
    N.carrier = P}
  have hC : C.Finite := finite_normalized_packet_carriers M hn
  let F : C → FullLattice (d + 1) K := fun P => Classical.choose P.property
  have hF (P : C) : (F P).carrier = P.1 := (Classical.choose_spec P.property).2.2
  let : Finite C := hC.to_subtype
  let : Finite (signMatrices (d + 1)) := (signMatrices_finite (d + 1)).to_subtype
  let f : C × signMatrices (d + 1) → Set (X (d + 1)) := fun Pw =>
    diagonalOrbit (rightAction (latticePoint (F Pw.1) σ) Pw.2.1)
  apply (Set.finite_range f).subset
  rintro O ⟨N, hMN, w, hw, rfl⟩
  obtain ⟨a, c, hc⟩ := exists_scale_to_representative N
  let P : C := ⟨(scaleFullLattice N a).carrier,
    scaleFullLattice N a, locallyHomothetic_trans hMN (locallyHomothetic_scale N a),
    ⟨c, hc⟩, rfl⟩
  have hFP : latticePoint (F P) σ = latticePoint (scaleFullLattice N a) σ :=
    latticePoint_eq_of_carrier_eq (F P) (scaleFullLattice N a) σ hn hodd (hF P)
  obtain ⟨D, hD, heD⟩ := latticePoint_scale_diagonal N σ hn hodd a
  have heN : latticePoint N σ = rightAction (latticePoint (F P) σ) D⁻¹ := by
    rw [hFP, heD, rightAction_mul, mul_inv_cancel, rightAction_one]
  have hDw := diagonal_mul D⁻¹ w (diagonal_inv D hD) hw.1
  obtain ⟨v, hv, u, he⟩ := diagonal_eq_sign_mul_flow (D⁻¹ * w) hDw
  refine ⟨(P, ⟨v, hv⟩), ?_⟩
  change diagonalOrbit (rightAction (latticePoint (F P) σ) v) =
    diagonalOrbit (rightAction (latticePoint N σ) w)
  rw [heN, rightAction_mul, he, ← rightAction_mul]
  exact (diagonalOrbit_orbitMap (rightAction (latticePoint (F P) σ) v) u).symm

 

theorem packetVolume_ne_zero_ne_top {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d + 1) K)
    (σ : OrderedEmbeddings (d + 1) K) (hn : Module.finrank ℚ K = d + 1)
    (hodd : Odd (d + 1)) :
    (∑' O : packetOrbits M σ, orbitVolume (orbitBasepoint O)) ≠ 0 ∧
    (∑' O : packetOrbits M σ, orbitVolume (orbitBasepoint O)) ≠ ⊤ := by
  let : Fintype (packetOrbits M σ) := (packetOrbits_finite M σ hn hodd).fintype
  rw [tsum_fintype]
  constructor
  · obtain ⟨O, hO⟩ := packetOrbits_nonempty M σ
    let o : packetOrbits M σ := ⟨O, hO⟩
    intro hzero
    have H := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (packetOrbits M σ))) =>
      show (0 : ℝ≥0∞) ≤ orbitVolume (orbitBasepoint i) from bot_le) (Finset.mem_univ o)
    rw [hzero] at H
    exact (packetBasepoint_volume_pos_finite hn hodd o).1 (le_antisymm H bot_le)
  · exact ENNReal.sum_ne_top.mpr (fun O _ => (packetBasepoint_volume_pos_finite hn hodd O).2)

 

theorem packetMeasure_isProbabilityMeasure {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d + 1) K)
    (σ : OrderedEmbeddings (d + 1) K) (hn : Module.finrank ℚ K = d + 1)
    (hodd : Odd (d + 1)) : IsProbabilityMeasure (packetMeasure M σ) := by
  have hv (O : packetOrbits M σ) : orbitProbability (orbitBasepoint O) Set.univ = 1 :=
    (packetBasepoint_probability hn hodd O).measure_univ
  constructor
  rw [packetMeasure, Measure.smul_apply,
    Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, hv, smul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (packetVolume_ne_zero_ne_top M σ hn hodd).1
    (packetVolume_ne_zero_ne_top M σ hn hodd).2



def positiveSignMatrix {n : ℕ} (hn : Odd n) (w : Fin n → SignTypeˣ) : G n :=
  ⟨Matrix.diagonal (fun i => signValue ((∏ j, w j)*w i)), by
    rw [Matrix.det_diagonal]
    simp only [map_mul, Finset.prod_mul_distrib, Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    rw [← map_prod,signValue_pow_odd _ hn,← sq,signValue_sq]⟩

lemma positiveSignMatrix_one {n : ℕ} (hn : Odd n) : positiveSignMatrix hn 1 = 1 := by
  apply Subtype.ext
  simp [positiveSignMatrix]

lemma positiveSignMatrix_mul {n : ℕ} (hn : Odd n) (w v : Fin n → SignTypeˣ) :
    positiveSignMatrix hn (w*v) = positiveSignMatrix hn w * positiveSignMatrix hn v := by
  apply Subtype.ext
  change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simp only [Pi.mul_apply,Finset.prod_mul_distrib,map_mul]
  ring

lemma positiveSignMatrix_diagonal {n : ℕ} (hn : Odd n) (w : Fin n → SignTypeˣ)
    (i j : Fin n) (hij : i ≠ j) : (positiveSignMatrix hn w).1 i j = 0 :=
  Matrix.diagonal_apply_ne _ hij

lemma positiveSignMatrix_entries {n : ℕ} (hn : Odd n) (w : Fin n → SignTypeˣ)
    (i : Fin n) : (positiveSignMatrix hn w).1 i i = 1 ∨
      (positiveSignMatrix hn w).1 i i = -1 := by
  change Matrix.diagonal _ i i = 1 ∨ Matrix.diagonal _ i i = -1
  simp only [Matrix.diagonal_apply_eq]
  exact signValue_eq_one_or_neg_one _



lemma positiveSignMatrix_mem_signMatrices {n : ℕ} (hn : Odd n) (w : Fin n → SignTypeˣ) :
    positiveSignMatrix hn w ∈ signMatrices n :=
  ⟨positiveSignMatrix_diagonal hn w,positiveSignMatrix_entries hn w⟩



lemma normalizedLattice_scale_unit {n : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (N : FullLattice n K) (σ : OrderedEmbeddings n K)
    (u : (𝓞 K)ˣ) :
    normalizedLattice (scaleFullLattice N (integralUnit u)) σ =
      (normalizedLattice N σ).map (diagonalLinear n (fun i => σ i (u : K))) := by
  have hm : embeddingMatrix (scaleFullLattice N (integralUnit u)) σ =
      embeddingMatrix N σ * Matrix.diagonal (fun i => σ i (u : K)) := by
    ext i j
    simp only [Matrix.mul_diagonal,embeddingMatrix,scaleFullLattice_basis,map_mul]
    exact mul_comm _ _
  have hd : |(embeddingMatrix (scaleFullLattice N (integralUnit u)) σ).det| =
      |(embeddingMatrix N σ).det| := by
    rw [hm,Matrix.det_mul,abs_mul,Matrix.det_diagonal,Finset.abs_prod,
      prod_abs_ordered_unit σ u,mul_one]
  unfold normalizedLattice
  dsimp only
  rw [hd,hm,← Matrix.smul_mul, rowLattice_mul_diagonal]

lemma submodule_map_signed_correction {n : ℕ} (L : Submodule ℤ (Fin n → ℝ))
    (s : SignTypeˣ) (t : Fin n → ℝ) :
    L.map (diagonalLinear n (fun i => signValue s * t i)) = L.map (diagonalLinear n t) := by
  rcases signValue_eq_one_or_neg_one s with h | h
  · simp only [h,one_mul]
  · have he : diagonalLinear n (fun i => signValue s * t i) = -(diagonalLinear n t) := by
      ext x i
      simp [h,diagonalLinear]
    rw [he,Submodule.map_neg]

 

lemma unitDiagonal_matrix {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) (hodd : Odd (d+1))
    (u : (𝓞 K)ˣ) :
    (positiveSignMatrix hodd (unitSigns σ u) * diagonalFlow (orderedUnitLog σ (Additive.ofMul u))).1 =
      Matrix.diagonal (fun i => signValue (∏ j,unitSigns σ u j) * σ i (u : K)) := by
  change (positiveSignMatrix hodd (unitSigns σ u)).1 *
    (diagonalFlow (orderedUnitLog σ (Additive.ofMul u))).1 = _
  rw [diagonalFlow_abs_orderedUnitLog]
  change Matrix.diagonal _ * Matrix.diagonal _ = _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [map_mul,mul_assoc,signValue_unitSigns]

 

theorem latticePoint_scale_unit {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (N : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) (u : (𝓞 K)ˣ) :
    latticePoint (scaleFullLattice N (integralUnit u)) σ = rightAction (latticePoint N σ)
      (positiveSignMatrix hodd (unitSigns σ u) * diagonalFlow (orderedUnitLog σ (Additive.ofMul u))) := by
  obtain ⟨g,hg⟩ := exists_SL_normalizedLattice N σ hn hodd
  let U := positiveSignMatrix hodd (unitSigns σ u) * diagonalFlow (orderedUnitLog σ (Additive.ofMul u))
  have hrow : rowLattice (g*U).1 = normalizedLattice (scaleFullLattice N (integralUnit u)) σ := by
    change rowLattice (g.1 * U.1) = _
    rw [show U.1 = _ from unitDiagonal_matrix σ hodd u,rowLattice_mul_diagonal,hg,
      submodule_map_signed_correction,normalizedLattice_scale_unit]
  rw [latticePoint_eq_of_rowLattice_eq N σ g hg,
    latticePoint_eq_of_rowLattice_eq (scaleFullLattice N (integralUnit u)) σ (g*U) hrow]
  rfl

 

def signedGlobalLabelPoint {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K) (hodd : Odd (d+1))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : SignedGlobalLabel M I) : X (d+1) :=
  rightAction (latticePoint (globalLabelLattice M I x.lattice) σ) (positiveSignMatrix hodd x.signs)

lemma signedGlobalLabelPoint_mem_packet {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K) (hodd : Odd (d+1))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : SignedGlobalLabel M I) :
    diagonalOrbit (signedGlobalLabelPoint M σ hodd I x) ∈ packetOrbits M σ :=
  ⟨globalLabelLattice M I x.lattice,(globalLabelLattice_spec M I x.lattice).2.1,
    positiveSignMatrix hodd x.signs,positiveSignMatrix_mem_signMatrices hodd x.signs,rfl⟩

lemma signedGlobalLabelPoint_unit_action {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : SignedGlobalLabel M I) (u : (𝓞 K)ˣ) :
    letI := signedGlobalLabelMulAction M σ I
    signedGlobalLabelPoint M σ hodd I (u • x) =
      orbitMap (signedGlobalLabelPoint M σ hodd I x) (orderedUnitLog σ (Additive.ofMul u)) := by
  let := signedGlobalLabelMulAction M σ I
  have hcar : (globalLabelLattice M I (u • x.lattice)).carrier =
      (scaleFullLattice (globalLabelLattice M I x.lattice) (integralUnit u)).carrier := by
    rw [(globalLabelLattice_spec M I _).1,globalLabels_smul_val,integralUnit,scaleFullLattice_unit_carrier,
      (globalLabelLattice_spec M I _).1]
  have hbase := latticePoint_eq_of_carrier_eq _ _ σ hn hodd hcar
  change rightAction (latticePoint (globalLabelLattice M I (u • x.lattice)) σ)
    (positiveSignMatrix hodd ((unitSigns σ u)⁻¹*x.signs)) = _
  rw [hbase,latticePoint_scale_unit _ σ hn hodd,positiveSignMatrix_mul,rightAction_mul]
  unfold orbitMap signedGlobalLabelPoint
  rw [rightAction_mul]
  congr 1
  rw [mul_assoc,← diagonalFlow_commute_of_diagonal (positiveSignMatrix hodd ((unitSigns σ u)⁻¹)*
    positiveSignMatrix hodd x.signs) (diagonal_mul _ _
      (positiveSignMatrix_diagonal hodd _) (positiveSignMatrix_diagonal hodd _)),← mul_assoc,
    ← mul_assoc,← positiveSignMatrix_mul,mul_inv_cancel,positiveSignMatrix_one,one_mul]

lemma diagonalLinear_comp_apply {n : ℕ} (s t : Fin n → ℝ) :
    (diagonalLinear n s).comp (diagonalLinear n t) = diagonalLinear n (fun i => s i*t i) := by
  ext x i
  simp [diagonalLinear,mul_assoc]

lemma diagonalLinear_one {n : ℕ} : diagonalLinear n (fun _ => 1) = LinearMap.id := by
  ext x i
  simp [diagonalLinear]

lemma normalizedLattice_as_map {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (N : FullLattice n K) (σ : OrderedEmbeddings n K) :
    normalizedLattice N σ = (N.carrier.map (realEmbeddingMap σ)).map
      (diagonalLinear n (fun _ => |(embeddingMatrix N σ).det| ^ (-(1:ℝ)/n))) := by
  unfold normalizedLattice
  rw [rowLattice_smul,rowLattice_embeddingMatrix]

 

theorem normalizedLattice_diagonal_homothety {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (N P : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : Module.finrank ℚ K = n) (hpos : 0 < n)
    (t : Fin n → ℝ) (ht : ∀ i, t i ≠ 0)
    (h : (normalizedLattice N σ).map (diagonalLinear n t) = normalizedLattice P σ) :
    ∃ b : K, b ≠ 0 ∧
      (∀ i, |(embeddingMatrix N σ).det| ^ (-(1:ℝ)/n) /
        |(embeddingMatrix P σ).det| ^ (-(1:ℝ)/n) * t i = σ i b) ∧
      (P.carrier : Set K) = (fun x => b*x) '' (N.carrier : Set K) := by
  let c : ℝ := |(embeddingMatrix N σ).det| ^ (-(1:ℝ)/n)
  let e : ℝ := |(embeddingMatrix P σ).det| ^ (-(1:ℝ)/n)
  have hc : 0 < c := Real.rpow_pos_of_pos (abs_pos.mpr (embeddingMatrix_det_ne_zero N σ hn)) _
  have he : 0 < e := Real.rpow_pos_of_pos (abs_pos.mpr (embeddingMatrix_det_ne_zero P σ hn)) _
  rw [normalizedLattice_as_map,normalizedLattice_as_map] at h
  change ((N.carrier.map (realEmbeddingMap σ)).map (diagonalLinear n (fun _ => c))).map
    (diagonalLinear n t) = (P.carrier.map (realEmbeddingMap σ)).map (diagonalLinear n (fun _ => e)) at h
  have H := congrArg (fun L : Submodule ℤ (Fin n → ℝ) =>
    L.map (diagonalLinear n (fun _ => e⁻¹))) h
  simp only [← Submodule.map_comp] at H
  have hleft : (diagonalLinear n (fun _ => e⁻¹)).comp
      ((diagonalLinear n t).comp ((diagonalLinear n (fun _ => c)).comp (realEmbeddingMap σ))) =
      (diagonalLinear n (fun i => c/e*t i)).comp (realEmbeddingMap σ) := by
    ext x i
    simp only [LinearMap.comp_apply,diagonalLinear,LinearMap.coe_mk,AddHom.coe_mk]
    ring
  have hright : (diagonalLinear n (fun _ => e⁻¹)).comp
      ((diagonalLinear n (fun _ => e)).comp (realEmbeddingMap σ)) = realEmbeddingMap σ := by
    ext x i
    simp only [LinearMap.comp_apply,diagonalLinear,LinearMap.coe_mk,AddHom.coe_mk]
    rw [← mul_assoc,inv_mul_cancel₀ he.ne',one_mul]
  rw [hleft,hright] at H
  exact diagonal_lattice_equality_iff_homothety N P σ hpos _
    (fun i => mul_ne_zero (div_ne_zero hc.ne' he.ne') (ht i)) H

lemma latticePoint_rightAction_diagonal_homothety {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (N P : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : Module.finrank ℚ K = n) (hodd : Odd n) (D : G n)
    (hD : ∀ i j, i ≠ j → D.1 i j = 0)
    (h : rightAction (latticePoint N σ) D = latticePoint P σ) :
    ∃ b : K, b ≠ 0 ∧
      (∀ i, |(embeddingMatrix N σ).det| ^ (-(1:ℝ)/n) /
        |(embeddingMatrix P σ).det| ^ (-(1:ℝ)/n) * D.1 i i = σ i b) ∧
      (P.carrier : Set K) = (fun x => b*x) '' (N.carrier : Set K) := by
  obtain ⟨g,hg⟩ := exists_SL_normalizedLattice N σ hn hodd
  obtain ⟨k,hk⟩ := exists_SL_normalizedLattice P σ hn hodd
  have hd : D.1 = Matrix.diagonal (fun i => D.1 i i) :=
    (Matrix.IsDiag.diagonal_diag hD).symm
  have hrow : rowLattice (g.1 * D.1) = rowLattice k.1 := by
    apply (quotient_eq_iff_rowLattice_eq (g*D) k).mp
    change rightAction (Quotient.mk _ g) D = Quotient.mk _ k
    rw [← latticePoint_eq_of_rowLattice_eq N σ g hg,
      ← latticePoint_eq_of_rowLattice_eq P σ k hk]
    exact h
  rw [hd,rowLattice_mul_diagonal,hg,hk] at hrow
  have hprod : ∏ i, D.1 i i = 1 := by
    have he := D.property
    rwa [hd,Matrix.det_diagonal] at he
  apply normalizedLattice_diagonal_homothety N P σ hn hodd.pos _ _ hrow
  intro i hi
  have H := Finset.prod_eq_zero (f := fun j => D.1 j j) (Finset.mem_univ i) hi
  rw [hprod] at H
  exact one_ne_zero H

lemma rowLattice_positiveSignMatrix {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hn : Odd n) (w : Fin n → SignTypeˣ) :
    rowLattice (B * (positiveSignMatrix hn w).1) =
      (rowLattice B).map (diagonalLinear n (fun i => signValue (w i))) := by
  change rowLattice (B * Matrix.diagonal (fun i => signValue ((∏ j,w j)*w i))) = _
  simp only [map_mul]
  rw [rowLattice_mul_diagonal,submodule_map_signed_correction]



theorem signedGlobalLabel_orbit_injective {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x y : SignedGlobalLabel M I)
    (h : diagonalOrbit (signedGlobalLabelPoint M σ hodd I x) =
      diagonalOrbit (signedGlobalLabelPoint M σ hodd I y)) :
    letI := signedGlobalLabelMulAction M σ I
    ∃ u : (𝓞 K)ˣ, u • x = y := by
  let := signedGlobalLabelMulAction M σ I
  let N := globalLabelLattice M I x.lattice
  let P := globalLabelLattice M I y.lattice
  have hy := mem_diagonalOrbit_self (signedGlobalLabelPoint M σ hodd I y)
  rw [← h] at hy
  obtain ⟨v,hv⟩ := hy
  obtain ⟨g,hg⟩ := exists_SL_normalizedLattice N σ hn hodd
  obtain ⟨k,hk⟩ := exists_SL_normalizedLattice P σ hn hodd
  let t : Fin (d+1) → ℝ := Fin.snoc (fun i : Fin d => Real.exp (v i)) (Real.exp (-∑ i,v i))
  have ht (i : Fin (d+1)) : 0 < t i := by
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [t,Fin.snoc_last,Fin.snoc_castSucc] <;>
      exact Real.exp_pos _
  have hrow : rowLattice ((g.1 * (positiveSignMatrix hodd x.signs).1) * Matrix.diagonal t) =
      rowLattice (k.1 * (positiveSignMatrix hodd y.signs).1) := by
    apply (quotient_eq_iff_rowLattice_eq ((g*positiveSignMatrix hodd x.signs)*diagonalFlow v)
      (k*positiveSignMatrix hodd y.signs)).mp
    change orbitMap (rightAction (Quotient.mk _ g) (positiveSignMatrix hodd x.signs)) v =
      rightAction (Quotient.mk _ k) (positiveSignMatrix hodd y.signs)
    rw [← latticePoint_eq_of_rowLattice_eq N σ g hg,← latticePoint_eq_of_rowLattice_eq P σ k hk]
    exact hv
  rw [rowLattice_mul_diagonal,rowLattice_positiveSignMatrix,rowLattice_positiveSignMatrix,hg,hk] at hrow
  have HH := congrArg (fun L : Submodule ℤ (Fin (d+1) → ℝ) =>
    L.map (diagonalLinear (d+1) (fun i => signValue (y.signs i)))) hrow
  simp only [← Submodule.map_comp,diagonalLinear_comp_apply] at HH
  have hyy : (fun i => signValue (y.signs i)*signValue (y.signs i)) = fun _ => (1:ℝ) := by
    funext i; exact (pow_two _).symm.trans (signValue_sq _)
  rw [hyy,diagonalLinear_one,Submodule.map_id] at HH
  obtain ⟨b,hb,hbt,hset⟩ := normalizedLattice_diagonal_homothety N P σ hn (Nat.succ_pos d)
    _ (fun i => mul_ne_zero (by
      have HH := signValue_sq (y.signs i)
      intro hz; rw [hz,zero_pow (by omega)] at HH; exact zero_ne_one HH)
      (mul_ne_zero (ht i).ne' (by
        have HH := signValue_sq (x.signs i)
        intro hz; rw [hz,zero_pow (by omega)] at HH; exact zero_ne_one HH))) HH
  have hI : saturationFractionalIdeal N = saturationFractionalIdeal P :=
    (globalLabelLattice_spec M I x.lattice).2.2.trans (globalLabelLattice_spec M I y.lattice).2.2.symm
  obtain ⟨u,hu,hcar⟩ := exists_integralUnit_of_same_saturation N P b hb hset hI
  have hsign : unitSigns σ u = y.signs*x.signs := by
    funext i
    apply Units.ext
    change SignType.sign (σ i (u : K)) = (y.signs i : SignType)*(x.signs i : SignType)
    rw [hu,← hbt i]
    have hc : 0 < |(embeddingMatrix N σ).det| ^ (-(1:ℝ)/((d+1:ℕ):ℝ)) /
        |(embeddingMatrix P σ).det| ^ (-(1:ℝ)/((d+1:ℕ):ℝ)) := div_pos
      (Real.rpow_pos_of_pos (abs_pos.mpr (embeddingMatrix_det_ne_zero N σ hn)) _)
      (Real.rpow_pos_of_pos (abs_pos.mpr (embeddingMatrix_det_ne_zero P σ hn)) _)
    rw [sign_mul,sign_pos hc,one_mul,sign_mul,signValue_sign,sign_mul,sign_pos (ht i),
      one_mul,signValue_sign]
  refine ⟨u,SignedGlobalLabel.ext ?_ ?_⟩
  · apply Subtype.ext
    change u • x.lattice.val = y.lattice.val
    rw [← (globalLabelLattice_spec M I x.lattice).1,← (globalLabelLattice_spec M I y.lattice).1]
    exact hcar.symm
  · change (unitSigns σ u)⁻¹*x.signs = y.signs
    rw [hsign]
    funext i
    simp only [Pi.mul_apply,Pi.inv_apply, signUnits_inv]
    rw [mul_assoc,signUnits_sq,mul_one]

lemma exists_fullSigns_of_signMatrix {n : ℕ} (hn : Odd n) (w : G n)
    (hw : w ∈ signMatrices n) : ∃ v : Fin n → SignTypeˣ, positiveSignMatrix hn v = w := by
  have hnz (i : Fin n) : w.1 i i ≠ 0 := by
    rcases hw.2 i with h | h <;> rw [h] <;> norm_num
  let v : Fin n → SignTypeˣ := fun i =>
    Units.map (signHom : ℝ →*₀ SignType).toMonoidHom (Units.mk0 (w.1 i i) (hnz i))
  have hv (i : Fin n) : signValue (v i) = w.1 i i := by
    change ((SignType.sign (w.1 i i) : SignType) : ℝ) = w.1 i i
    rcases hw.2 i with h | h <;> simp [h]
  have hp : ∏ i,v i = 1 := by
    apply signValue_injective
    rw [map_prod,map_one]
    simp only [hv]
    have hdiag : Matrix.diagonal (fun i => w.1 i i) = w.1 := Matrix.IsDiag.diagonal_diag hw.1
    rw [← Matrix.det_diagonal, hdiag]
    exact w.property
  refine ⟨v,?_⟩
  apply Subtype.ext
  change Matrix.diagonal (fun i => signValue ((∏ j,v j)*v i)) = w.1
  simp only [hp,one_mul,hv]
  exact Matrix.IsDiag.diagonal_diag hw.1

lemma saturation_class_eq_of_signed_orbit_eq {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (N P : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) (w z : G (d+1))
    (hw : w ∈ signMatrices (d+1)) (hz : z ∈ signMatrices (d+1))
    (h : diagonalOrbit (rightAction (latticePoint N σ) w) =
      diagonalOrbit (rightAction (latticePoint P σ) z)) :
    ClassGroup.mk K (Units.mk0 (saturationFractionalIdeal N) (saturationFractionalIdeal_ne_zero N)) =
      ClassGroup.mk K (Units.mk0 (saturationFractionalIdeal P) (saturationFractionalIdeal_ne_zero P)) := by
  have hmem := mem_diagonalOrbit_self (rightAction (latticePoint P σ) z)
  rw [← h] at hmem
  obtain ⟨v,hv⟩ := hmem
  have he := congrArg (fun x : X (d+1) => rightAction x z⁻¹) hv
  change rightAction (rightAction (rightAction (latticePoint N σ) w) (diagonalFlow v)) z⁻¹ =
    rightAction (rightAction (latticePoint P σ) z) z⁻¹ at he
  simp only [rightAction_mul,mul_inv_cancel,rightAction_one] at he
  have hD := diagonal_mul (w*diagonalFlow v) z⁻¹
    (diagonal_mul w (diagonalFlow v) hw.1 (fun i j hij => Matrix.diagonal_apply_ne _ hij))
    (diagonal_inv z hz.1)
  obtain ⟨b,hb,_,hset⟩ := latticePoint_rightAction_diagonal_homothety N P σ hn hodd _ hD he
  apply (fractionalIdeal_same_class _ _).mpr
  refine ⟨b,hb,?_⟩
  let a : Kˣ := Units.mk0 b hb
  have hcar : P.carrier = (scaleFullLattice N a).carrier := by
    apply SetLike.coe_injective
    rw [scaleFullLattice_carrier]
    exact hset
  have HI := saturationFractionalIdeal_eq_of_carrier_eq P (scaleFullLattice N a) hcar
  rw [saturationFractionalIdeal_scale] at HI
  exact HI.symm



def allSignedGlobalLabelPoint {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K) (hodd : Odd (d+1))
    (x : AllSignedGlobalLabel M) : X (d+1) :=
  signedGlobalLabelPoint M σ hodd (classRepresentative K x.1) x.2

def allSignedGlobalLabelOrbit {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K) (hodd : Odd (d+1))
    (x : AllSignedGlobalLabel M) : packetOrbits M σ :=
  ⟨diagonalOrbit (allSignedGlobalLabelPoint M σ hodd x),
    signedGlobalLabelPoint_mem_packet M σ hodd _ x.2⟩

lemma allSignedGlobalLabelOrbit_unit_action {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (x : AllSignedGlobalLabel M) (u : (𝓞 K)ˣ) :
    letI := allSignedGlobalLabelMulAction M σ
    allSignedGlobalLabelOrbit M σ hodd (u • x) = allSignedGlobalLabelOrbit M σ hodd x := by
  let := allSignedGlobalLabelMulAction M σ
  let := signedGlobalLabelMulAction M σ (classRepresentative K x.1)
  apply Subtype.ext
  change diagonalOrbit (signedGlobalLabelPoint M σ hodd _ (u • x.2)) = _
  rw [signedGlobalLabelPoint_unit_action M σ hn hodd,diagonalOrbit_orbitMap]
  rfl

lemma allSignedGlobalLabelOrbit_eq_iff {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (x y : AllSignedGlobalLabel M) :
    letI := allSignedGlobalLabelMulAction M σ
    allSignedGlobalLabelOrbit M σ hodd x = allSignedGlobalLabelOrbit M σ hodd y ↔
      ∃ u : (𝓞 K)ˣ, u • x = y := by
  let := allSignedGlobalLabelMulAction M σ
  constructor
  · intro h
    rcases x with ⟨c,x⟩
    rcases y with ⟨e,y⟩
    have he := saturation_class_eq_of_signed_orbit_eq
      (globalLabelLattice M (classRepresentative K c) x.lattice)
      (globalLabelLattice M (classRepresentative K e) y.lattice) σ hn hodd
      (positiveSignMatrix hodd x.signs) (positiveSignMatrix hodd y.signs)
      (positiveSignMatrix_mem_signMatrices hodd x.signs)
      (positiveSignMatrix_mem_signMatrices hodd y.signs) (congrArg Subtype.val h)
    have hc : Units.mk0 (saturationFractionalIdeal (globalLabelLattice M (classRepresentative K c) x.lattice))
        (saturationFractionalIdeal_ne_zero _) = classRepresentative K c := by
      apply Units.ext
      exact (globalLabelLattice_spec M _ x.lattice).2.2
    have hd : Units.mk0 (saturationFractionalIdeal (globalLabelLattice M (classRepresentative K e) y.lattice))
        (saturationFractionalIdeal_ne_zero _) = classRepresentative K e := by
      apply Units.ext
      exact (globalLabelLattice_spec M _ y.lattice).2.2
    rw [hc,hd,classRepresentative_spec,classRepresentative_spec] at he
    subst e
    obtain ⟨u,hu⟩ := signedGlobalLabel_orbit_injective M σ hn hodd (classRepresentative K c) x y
      (congrArg Subtype.val h)
    exact ⟨u,congrArg (Sigma.mk c) hu⟩
  · rintro ⟨u,rfl⟩
    exact (allSignedGlobalLabelOrbit_unit_action M σ hn hodd x u).symm

lemma allSignedGlobalLabelOrbit_surjective {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) :
    Function.Surjective (allSignedGlobalLabelOrbit M σ hodd) := by
  rintro ⟨O,N,hMN,w,hw,rfl⟩
  obtain ⟨a,c,hc⟩ := exists_scale_to_representative N
  let P := scaleFullLattice N a
  let L : globalLabels M (classRepresentative K c) :=
    ⟨P.carrier,P,rfl,locallyHomothetic_trans hMN (locallyHomothetic_scale N a),hc⟩
  have hLP : latticePoint (globalLabelLattice M (classRepresentative K c) L) σ = latticePoint P σ :=
    latticePoint_eq_of_carrier_eq _ _ σ hn hodd (globalLabelLattice_spec M _ L).1
  obtain ⟨D,hD,heD⟩ := latticePoint_scale_diagonal N σ hn hodd a
  have heN : latticePoint N σ = rightAction (latticePoint P σ) D⁻¹ := by
    rw [show latticePoint P σ = rightAction (latticePoint N σ) D from heD,
      rightAction_mul,mul_inv_cancel,rightAction_one]
  obtain ⟨v,hv,u,he⟩ := diagonal_eq_sign_mul_flow (D⁻¹*w) (diagonal_mul _ _ (diagonal_inv D hD) hw.1)
  obtain ⟨s,hs⟩ := exists_fullSigns_of_signMatrix hodd v hv
  refine ⟨⟨c,⟨L,s⟩⟩,?_⟩
  apply Subtype.ext
  change diagonalOrbit (rightAction (latticePoint (globalLabelLattice M (classRepresentative K c) L) σ)
    (positiveSignMatrix hodd s)) = diagonalOrbit (rightAction (latticePoint N σ) w)
  rw [hLP,hs,heN,rightAction_mul,he,← rightAction_mul]
  exact (diagonalOrbit_orbitMap _ _).symm

 

def signedPacketOrbitEquiv {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) :
    letI := allSignedGlobalLabelMulAction M σ
    MulAction.orbitRel.Quotient (𝓞 K)ˣ (AllSignedGlobalLabel M) ≃ packetOrbits M σ := by
  letI := allSignedGlobalLabelMulAction M σ
  refine Equiv.ofBijective (Quotient.lift (allSignedGlobalLabelOrbit M σ hodd) ?_) ⟨?_,?_⟩
  · intro x y h
    change MulAction.orbitRel (𝓞 K)ˣ (AllSignedGlobalLabel M) x y at h
    rw [MulAction.orbitRel_apply] at h
    obtain ⟨u,hu⟩ := h
    exact (allSignedGlobalLabelOrbit_eq_iff M σ hn hodd x y).mpr ⟨u⁻¹,by rw [← hu]; simp⟩
  · intro x y
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        intro he
        apply Quotient.sound
        change MulAction.orbitRel (𝓞 K)ˣ (AllSignedGlobalLabel M) x y
        rw [MulAction.orbitRel_apply]
        obtain ⟨u,hu⟩ := (allSignedGlobalLabelOrbit_eq_iff M σ hn hodd x y).mp he
        exact ⟨u⁻¹,by rw [← hu]; simp⟩
  · intro O
    obtain ⟨x,hx⟩ := allSignedGlobalLabelOrbit_surjective M σ hn hodd O
    exact ⟨Quotient.mk'' x,hx⟩

def idealElementDecompositionMap {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (Σ _J : integralIdealClassFiber I, (𝓞 K)ˣ) → nonzeroIdealElements I :=
  fun x => idealElementUnitAction I x.2 (idealElementRepresentative I x.1)

 

def idealElementDecomposition {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (Σ _J : integralIdealClassFiber I, (𝓞 K)ˣ) ≃ nonzeroIdealElements I :=
  Equiv.ofBijective (idealElementDecompositionMap I) (by
    constructor
    · rintro ⟨J,z⟩ ⟨L,w⟩ h
      have he := congrArg (relativeElementClassMap I) h
      simp only [idealElementDecompositionMap,relativeElementClassMap_unitAction,
        idealElementRepresentative_spec] at he
      subst L
      have hz : z = w := idealElementUnitAction_injective I _ h
      subst w
      rfl
    · intro a
      let J := relativeElementClassMap I a
      obtain ⟨z,hz,_⟩ := exists_unique_unit_of_relativeElementClassMap_eq I
        (idealElementRepresentative I J) a (idealElementRepresentative_spec I J)
      exact ⟨⟨J,z⟩,hz⟩)



def orderedUnitLogOnto {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) :
    Additive ((𝓞 K)ˣ) →+ orderedLogSubgroup σ ⊤ :=
  (orderedUnitLog σ).codRestrict (orderedLogSubgroup σ ⊤).toAddSubgroup
    (fun u => (mem_orderedLogSubgroup σ ⊤ _).mpr ⟨u.toMul,Subgroup.mem_top _,rfl⟩)



def nonzeroIdealWeight {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (J : {J : Ideal (𝓞 K) // J ≠ ⊥}) : ℝ≥0∞ :=
  globalIdealWeight M (Units.mk0 (J.1 : FractionalIdeal (𝓞 K)⁰ K) (by simpa using J.2))



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketMoments
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk _root_.infinitePlace_mult_smul
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

lemma thickLattices_isClosed (n : ℕ) (ε : ℝ) : IsClosed (thickLattices n ε) := by
  classical
  have he : (thickLattices n ε)ᶜ =
      (Quotient.mk (QuotientGroup.rightRel (integralGroup n))) ''
        {g : G n | ∃ z : Fin n → ℤ, z ≠ 0 ∧ ‖(fun i => (z i : ℝ)) ᵥ* g.1‖ < ε} := by
    ext x
    simp [thickLattices,not_forall,not_le,and_comm]
  apply isOpen_compl_iff.mp
  rw [he]
  apply (quotient_covering n).isOpenMap
  have he' : {g : G n | ∃ z : Fin n → ℤ, z ≠ 0 ∧ ‖(fun i => (z i : ℝ)) ᵥ* g.1‖ < ε} =
      ⋃ (z : Fin n → ℤ) (_ : z ≠ 0), {g : G n | ‖(fun i => (z i : ℝ)) ᵥ* g.1‖ < ε} := by
    ext g; simp
  rw [he']
  exact isOpen_iUnion (fun z => isOpen_iUnion (fun _ =>
    isOpen_lt (continuous_integer_row n z).norm continuous_const))



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_CuspMass
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
open MeasureTheory Filter Set Topology Matrix
open scoped ENNReal BigOperators Classical



def packetProbability {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K)
    (σ : OrderedEmbeddings (d+1) K) (hn : Module.finrank ℚ K = d+1)
    (hodd : Odd (d+1)) : ProbabilityMeasure (X (d+1)) :=
  ⟨packetMeasure M σ,packetMeasure_isProbabilityMeasure M σ hn hodd⟩



end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaDerivatives
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
namespace PrimeDegreePackets

lemma mem_thickLattices_iff {n : ℕ} (x : X n) (ε : ℝ) :
    x ∈ thickLattices n ε ↔ ∀ v ∈ pointLattice x, v ≠ 0 → ε ≤ ‖v‖ := by
  constructor
  · intro hx
    induction x using Quotient.inductionOn with
    | h g =>
      intro v hv hv0
      obtain ⟨z,hz⟩ := (integerRowEquiv g).surjective ⟨v,hv⟩
      have hz' : integerRowMap g.1 z = v := congrArg Subtype.val hz
      have hz0 : z ≠ 0 := by
        intro h
        apply hv0
        rw [←hz',h,_root_.map_zero]
      simpa only [←hz',integerRowMap_apply] using hx g rfl z hz0
  · intro hx g hg z hz
    have hzne : integerRowMap g.1 z ≠ 0 := by
      intro h
      exact hz (integerRowMap_injective g (h.trans (map_zero _).symm))
    have hmem : integerRowMap g.1 z ∈ pointLattice x := by
      rw [←hg,pointLattice_mk,←integerRowMap_range]
      exact ⟨z,rfl⟩
    simpa only [integerRowMap_apply] using hx _ hmem hzne

 

lemma exists_mem_thickLattices {n : ℕ} (x : X n) :
    ∃ ε : ℝ, 0 < ε ∧ x ∈ thickLattices n ε := by
  induction x using Quotient.inductionOn with
  | h g =>
    have he : rowLattice g.1 = Submodule.span ℤ (Set.range (rowBasis g)) := by
      congr 2
      ext i j
      exact (rowBasis_apply g i j).symm
    have hd : DiscreteTopology (rowLattice g.1) := by rw [he]; infer_instance
    obtain ⟨ε,hε,H⟩ := Metric.exists_ball_inter_eq_singleton_of_mem_discrete
      (s := (rowLattice g.1 : Set (Fin n → ℝ))) DiscreteTopology.isDiscrete
      (Submodule.zero_mem _)
    refine ⟨ε,hε,(mem_thickLattices_iff _ _).mpr ?_⟩
    intro v hv hv0
    by_contra h
    have hball : v ∈ Metric.ball 0 ε := by simpa only [Metric.mem_ball,_root_.dist_zero_right] using lt_of_not_ge h
    have hm : v ∈ ({0} : Set (Fin n → ℝ)) := H ▸ ⟨hball,hv⟩
    exact hv0 (Set.mem_singleton_iff.mp hm)

lemma exists_mem_countable_thickLattices {n : ℕ} (x : X n) :
    ∃ k : ℕ, x ∈ thickLattices n ((k+1:ℝ)⁻¹) := by
  obtain ⟨ε,hε,hx⟩ := exists_mem_thickLattices x
  obtain ⟨k,hk⟩ := exists_nat_gt (ε⁻¹)
  refine ⟨k,(mem_thickLattices_iff _ _).mpr ?_⟩
  intro v hv hv0
  apply le_trans _ ((mem_thickLattices_iff _ _).mp hx v hv hv0)
  apply (inv_le_iff_one_le_mul₀ (by positivity : (0:ℝ)<k+1)).mpr
  have H := (inv_lt_iff_one_lt_mul₀ hε).mp hk
  nlinarith



lemma no_coordinate_zero_of_recurrence (d : ℕ) (j : Fin (d+1)) (x : X (d+1))
    (hrec : ∀ k : ℕ, x ∈ thickLattices (d+1) ((k+1:ℝ)⁻¹) →
      ∃ᶠ l : ℕ in atTop,
        rightAction x ((diagonalOneParameter (coordinateContractionWeights d j)
          (coordinateContractionWeights_sum d j) 1)^l) ∈
            thickLattices (d+1) ((k+1:ℝ)⁻¹)) :
    ∀ v ∈ pointLattice x, v ≠ 0 → v j ≠ 0 := by
  intro v hv hv0 hvj
  obtain ⟨k,hk⟩ := exists_mem_countable_thickLattices x
  have hthin : Tendsto (fun l : ℕ => Real.exp (-(l:ℝ))*‖v‖) atTop (𝓝 0) := by
    have he : Tendsto (fun l : ℕ => Real.exp (-(l:ℝ))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
    simpa only [zero_mul] using he.mul_const ‖v‖
  have hsmall := hthin.eventually_lt_const (by positivity : (0:ℝ)<(k+1:ℝ)⁻¹)
  obtain ⟨l,hl,hlt⟩ := ((hrec k hk).and_eventually hsmall).exists
  rw [←diagonalOneParameter_nat] at hl
  let w : Fin (d+1) → ℝ := Real.exp (-(l:ℝ)) • v
  have hw0 : w ≠ 0 := smul_ne_zero (Real.exp_ne_zero _) hv0
  have hw : w ∈ pointLattice (rightAction x
      (diagonalOneParameter (coordinateContractionWeights d j)
        (coordinateContractionWeights_sum d j) l)) := by
    rw [pointLattice_rightAction_diagonal _ _ _ rfl]
    exact ⟨v,hv,coordinateContraction_vector d j v hvj l⟩
  have H := (mem_thickLattices_iff _ _).mp hl w hw hw0
  have hn : ‖w‖ = Real.exp (-(l:ℝ))*‖v‖ := by
    simp only [w,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  rw [hn] at H
  exact (not_lt_of_ge H) hlt

 

theorem ae_no_coordinate_zero (d : ℕ) (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) μ = μ) :
    ∀ᵐ x ∂μ, ∀ v ∈ pointLattice x, v ≠ 0 → ∀ j, v j ≠ 0 := by
  have H (j : Fin (d+1)) : ∀ᵐ x ∂μ, ∀ v ∈ pointLattice x, v ≠ 0 → v j ≠ 0 := by
    let ell := coordinateContractionWeights d j
    let a := diagonalOneParameter ell (coordinateContractionWeights_sum d j) 1
    have hp : MeasurePreserving (fun x : X (d+1) => rightAction x a) μ μ := by
      refine ⟨(continuous_rightAction a).measurable,?_⟩
      rw [show a = diagonalFlow (fun i : Fin d => ell i.castSucc*1) from
        diagonalOneParameter_eq_diagonalFlow ell (coordinateContractionWeights_sum d j) 1]
      exact hA _
    have hr (k : ℕ) := hp.conservative.ae_mem_imp_frequently_image_mem
      (thickLattices_isClosed (d+1) ((k+1:ℝ)⁻¹)).measurableSet.nullMeasurableSet
    filter_upwards [ae_all_iff.mpr hr] with x hx
    apply no_coordinate_zero_of_recurrence d j x
    intro k hk
    simpa only [rightAction_iterate,a,ell] using hx k hk
  filter_upwards [ae_all_iff.mpr H] with x hx
  intro v hv hv0 j
  exact hx j v hv hv0

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootSubgroups
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
namespace PrimeDegreePackets


def rootInvarianceRelation {n : ℕ} (μ : Measure (X n)) (i j : Fin n) : Prop :=
  i = j ∨ ∃ hij : i ≠ j, ∀ a : ℝ,
    Matrix.SpecialLinearGroup.transvection hij a ∈ invariantRightSubgroup μ

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootRelations
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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


namespace PrimeDegreePackets



theorem ae_root_stabilizer_trivial (d : ℕ) (μ : Measure (X (d+1)))
    [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) μ = μ) :
    ∀ᵐ x ∂μ, ∀ (i j : Fin (d+1)) (hij : i ≠ j) (a : ℝ),
      rightAction x (Matrix.SpecialLinearGroup.transvection hij a) = x → a = 0 := by
  filter_upwards [ae_no_coordinate_zero d μ hA] with x hx
  exact root_stabilizer_trivial_of_no_coordinate_zero x hx

end PrimeDegreePackets


open scoped Topology Classical ENNReal

open scoped Matrix Topology Classical
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootCharts
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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


namespace PrimeDegreePackets



lemma rootQuotientParametrization_diagonal {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (s : RootSlice i j k) (a t : ℝ) :
    rootQuotientParametrization hij
      (rootSliceDiagonal ell hell t s, rootTimeScaling ell i j t a) =
      rightAction (rootQuotientParametrization hij (s,a)) (diagonalOneParameter ell hell t) := by
  have hC := diagonal_conjugation_transvection ell hell hij a (-t)
  have he : (ell i-ell j)*(-t) = (ell j-ell i)*t := by ring
  rw [he,diagonalOneParameter_neg,neg_neg] at hC
  change Quotient.mk _ ((s.val * diagonalOneParameter ell hell t) *
    Matrix.SpecialLinearGroup.transvection hij (Real.exp ((ell j-ell i)*t)*a)) =
    Quotient.mk _ ((s.val * Matrix.SpecialLinearGroup.transvection hij a) *
      diagonalOneParameter ell hell t)
  rw [← hC]
  congr 1
  group



end PrimeDegreePackets


namespace PrimeDegreePackets

lemma rootDiagonalCoordinates_param {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ)
    (z : RootSlice i j k × ℝ) :
    rootQuotientParametrization hij (rootDiagonalCoordinates ell hell t z) =
      rightAction (rootQuotientParametrization hij z) (diagonalOneParameter ell hell t) :=
  rootQuotientParametrization_diagonal hij ell hell z.1 z.2 t

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

def diagonal (B : RootBox hij k) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) : RootBox hij k := by
  let e := rootSliceDiagonalHomeomorph (i := i) (j := j) (k := k) ell hell t
  let f := rootTimeScaling ell i j t
  let E := e.prodCongr f
  have hiff (z : RootSlice i j k × ℝ) :
      z ∈ B.domain ↔ E z ∈ (e '' B.transverse) ×ˢ (f '' B.time) := by
    change (z.1 ∈ B.transverse ∧ z.2 ∈ B.time) ↔
      (e z.1 ∈ e '' B.transverse ∧ f z.2 ∈ f '' B.time)
    rw [e.injective.mem_set_image,f.injective.mem_set_image]
  let eb := E.subtype hiff
  refine ⟨e '' B.transverse,f '' B.time,
    e.isOpenMap _ B.transverse_open,f.isOpenMap _ B.time_open,?_⟩
  have H := (rightActionHomeomorph (diagonalOneParameter ell hell t)).isOpenEmbedding.comp
    (B.embedding.comp eb.symm.isOpenEmbedding)
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  have he : E (eb.symm z).val = z.val := congrArg Subtype.val (eb.apply_symm_apply z)
  change rootQuotientParametrization hij z.val =
    rightAction (rootQuotientParametrization hij (eb.symm z).val) (diagonalOneParameter ell hell t)
  rw [←he]
  exact rootDiagonalCoordinates_param hij ell hell t _

lemma diagonal_domain (B : RootBox hij k) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) :
    (B.diagonal ell hell t).domain = rootDiagonalCoordinates ell hell t '' B.domain := by
  exact prod_image_image_eq



end RootBox
end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_KernelScaling
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
namespace PrimeDegreePackets.RootBox

variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

def HasHaarConditionals (B : RootBox hij k) (μ : Measure (X n)) [IsFiniteMeasure μ] : Prop :=
  ∃ c : ℝ≥0, ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
    B.conditionalKernel μ s = c • (volume.restrict B.time)

end PrimeDegreePackets.RootBox
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootOverlaps
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
namespace PrimeDegreePackets.RootBox

variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

def overlapBox (B : RootBox hij k) (a : ℝ) : RootBox hij k :=
  B.shrink B.transverse (B.time ∩ (fun t : ℝ => t+a) ⁻¹' B.time)
    B.transverse_open (B.time_open.inter (B.time_open.preimage (by fun_prop)))
    subset_rfl inter_subset_left

end PrimeDegreePackets.RootBox


open MeasureTheory

open scoped BigOperators ENNReal

open NumberField Finset
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafTransitions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

namespace RootBox
variable {hij} {k : Fin n}



lemma ae_of_coordinate (A : RootBox hij k) (μ : Measure (X n)) {P : X n → Prop}
    (hP : ∀ᵐ z ∂A.coordinateMeasure μ, P (rootQuotientParametrization hij z)) :
    ∀ᵐ x ∂μ.restrict A.range, P x := by
  have he : (μ.comap A.param).map A.param = μ.restrict A.range :=
    A.embedding.measurableEmbedding.map_comap μ
  rw [←he]
  apply A.embedding.measurableEmbedding.ae_map_iff.mpr
  exact ae_of_ae_map measurable_subtype_coe.aemeasurable hP

end RootBox

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IntrinsicLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

lemma diagonal_time_bound (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ) :
    (A.diagonal ell hell t).time ⊆ rootLeafWindow (Real.exp ((ell j-ell i)*t)*R) 0 := by
  rintro _ ⟨u,hu,rfl⟩
  have h := hAR hu
  simp only [rootLeafWindow,Nat.cast_zero,add_zero,Set.mem_Ioo] at h ⊢
  change -(Real.exp ((ell j-ell i)*t)*R) < Real.exp ((ell j-ell i)*t)*u ∧
    Real.exp ((ell j-ell i)*t)*u < Real.exp ((ell j-ell i)*t)*R
  constructor
  · simpa only [mul_neg] using mul_lt_mul_of_pos_left h.1 (Real.exp_pos _)
  · exact mul_lt_mul_of_pos_left h.2 (Real.exp_pos _)

end RootBox



end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ScalingCovariance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

lemma rootCanonicalFlow_preserving (d : ℕ) (j : Fin (d+1)) (t : ℝ)
    (μ : Measure (X (d+1)))
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    MeasurePreserving (fun x => rightAction x (rootCanonicalFlow d j t)) μ μ := by
  refine ⟨(continuous_rightAction _).measurable,?_⟩
  rw [rootCanonicalFlow,diagonalOneParameter_eq_diagonalFlow]
  exact hA _


end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_CompactStabilizerSeparation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finitely many observables separate a compact set from the stabilizer

The eventual shearing contradiction only needs a fixed finite family
of generic observables. Continuity and compactness produce that family
and a uniform positive separation, directly from the actual measure
stabilizer. No empirical-convergence or homogeneous-orbit premise is used.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def invarianceDefect {n : ℕ} (μ : Measure (X n))
    (f : CompactlySupportedContinuousMap (X n) ℝ) (g : G n) : ℝ :=
  (∫ x, f (rightAction x g) ∂μ) - ∫ x, f x ∂μ

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ConjugationOrbit
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.euclideanRowBasis_apply _root_.OAI.PrimeDegreePackets.rowBasis_apply _root_.infinitePlace_mult_smul
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

instance latticeOrbitQuotientMeasurableSpace {n : ℕ} (g : G n) (H : Subgroup (G n)) :
    MeasurableSpace (LatticeOrbitQuotient g H) := borel _

instance latticeOrbitQuotientBorelSpace {n : ℕ} (g : G n) (H : Subgroup (G n)) :
    BorelSpace (LatticeOrbitQuotient g H) := ⟨rfl⟩

instance latticeOrbitQuotientSecondCountable {n : ℕ} (g : G n) (H : Subgroup (G n)) :
    SecondCountableTopology (LatticeOrbitQuotient g H) := by
  let : SecondCountableTopology H :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  change SecondCountableTopology (Quotient (MulAction.orbitRel (pointOrbitStabilizer g H) H))
  exact ContinuousConstSMul.secondCountableTopology

def latticeOrbitRightAction {n : ℕ} (g : G n) (H : Subgroup (G n))
    (x : LatticeOrbitQuotient g H) (h : H) : LatticeOrbitQuotient g H :=
  Quotient.map (fun k => k * h) (by
    intro a b hab
    change (QuotientGroup.rightRel (pointOrbitStabilizer g H)) a b at hab
    change (QuotientGroup.rightRel (pointOrbitStabilizer g H)) (a * h) (b * h)
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa only [_root_.mul_inv_rev, mul_assoc, mul_inv_cancel_left] using hab) x

/-- The conjugation orbit map exists because its value is unchanged by
the actual lattice point stabilizer. -/
def conjugationOrbitMap {n : ℕ} (g : G n) (H : Subgroup (G n))
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ s : pointOrbitStabilizer g H, Commute M s.val.val) :
    LatticeOrbitQuotient g H → Matrix (Fin n) (Fin n) ℝ :=
  Quotient.lift (fun h : H => slMatrixConjugation h.val M) (by
    intro a b hab
    change QuotientGroup.rightRel (pointOrbitStabilizer g H) a b at hab
    rw [QuotientGroup.rightRel_apply] at hab
    have hab' : a * b⁻¹ ∈ pointOrbitStabilizer g H := by
      simpa only [_root_.mul_inv_rev, inv_inv] using (pointOrbitStabilizer g H).inv_mem hab
    have hs := slMatrixConjugation_eq_self (a * b⁻¹).val M (hM ⟨a * b⁻¹, hab'⟩)
    calc
      slMatrixConjugation a.val M = slMatrixConjugation ((a * b⁻¹) * b).val M := by simp
      _ = slMatrixConjugation b.val (slMatrixConjugation (a * b⁻¹).val M) :=
        slMatrixConjugation_mul _ _ _
      _ = slMatrixConjugation b.val M := by rw [hs])

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_OrbitGenericity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing the generic-basepoint condition

A finite invariant measure on a block orbit pushes to an invariant
measure on the lattice space. Diagonal recurrence gives a generic
basepoint almost everywhere. Changing to that basepoint removes the
genericity hypothesis from the prime-degree block-orbit obstruction.
-/

noncomputable section
open Matrix Set MeasureTheory Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def latticeOrbitPoint {n : ℕ} (g : G n) (H : Subgroup (G n)) :
    LatticeOrbitQuotient g H → X n :=
  Quotient.lift (fun a : H => Quotient.mk _ (g * a.val)) (by
    intro a b hab
    apply Quotient.sound
    change QuotientGroup.rightRel (pointOrbitStabilizer g H) a b at hab
    change QuotientGroup.rightRel (integralGroup n) (g * a.val) (g * b.val)
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    change g * (b.val * a.val⁻¹) * g⁻¹ ∈ integralGroup n at hab
    simpa only [_root_.mul_inv_rev, mul_assoc] using hab)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_TransferredVelocity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Changing coordinates in the actual velocity space

Distances may be measured in any finite-dimensional real model of the
matrix space. This allows the subsequent measurable projection argument
to use Euclidean coordinates while the power estimates use an operator
norm. Every subspace here remains the actual stabilizer velocity space.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def transferredVelocitySpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (e : E ≃L[ℝ] Matrix (Fin n) (Fin n) ℝ)
    (μ : Measure (X n)) : Submodule ℝ E :=
  (matrixVelocitySpace (invariantRightSubgroup μ)).comap e.toLinearMap

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_EuclideanVelocityProjection
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Measurable projections onto the actual component velocity spaces

The matrix topology has a concrete Euclidean model. Orthogonal projection
in that model gives a finite, measurably varying spanning family for the
actual stabilizer velocity space of every probability kernel. No choice
of subgroup curves or of a tangent basis is made measurably.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace

namespace DukePrimeDegree
open PrimeDegreePackets

def euclideanVelocitySpace {n : ℕ} (μ : Measure (X n)) :
    Submodule ℝ (MatrixEuclidean n) :=
  transferredVelocitySpace (matrixEuclideanEquiv n) μ

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_GenericMatrixPairs
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small matrix lifts of generic pairs outside a subgroup orbit

If all subgroup orbits are null, a positive-mass generic set contains
arbitrarily close pairs from different orbits. Openness of the actual
quotient orbit map lifts these pairs to matrices tending to identity,
all outside the subgroup. This is a concrete input to polynomial
shearing, without a homogeneous-orbit assumption.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def rightSubgroupOrbit {n : ℕ} (L : Subgroup (G n)) (x : X n) : Set (X n) :=
  range (fun h : L => rightAction x h.val)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_FiniteProjectionFrames
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

theorem exists_maximalGramFrame (v : I → E) : ∃ S, IsMaximalGramFrame v S := by
  classical
  let F := Finset.univ.filter (fun S : Finset I => finiteGramDet v S ≠ 0)
  have hF : F.Nonempty := by
    refine ⟨∅, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    let : IsEmpty (↑(∅ : Finset I)) := ⟨fun i => Finset.notMem_empty i.val i.property⟩
    simp only [finiteGramDet, Matrix.det_isEmpty, ne_eq, one_ne_zero, not_false_eq_true]
  obtain ⟨S, hS, hmax⟩ := F.exists_max_image Finset.card hF
  refine ⟨S, (Finset.mem_filter.mp hS).2, ?_⟩
  intro T hST
  by_contra hT
  have hTF : T ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩
  exact (not_lt_of_ge (hmax T hTF)) hST

theorem exists_maximalGramFrameIndex (v : I → E) :
    ∃ k, IsMaximalGramFrame v (frameEnumeration I k) := by
  obtain ⟨S, hS⟩ := exists_maximalGramFrame v
  obtain ⟨k, hk⟩ := frameEnumeration_surjective S
  exact ⟨k, hk.symm ▸ hS⟩

def maximalGramFrameIndex (v : I → E) : ℕ := by
  classical
  exact Nat.find (exists_maximalGramFrameIndex v)

def maximalGramFrame (v : I → E) : Finset I :=
  frameEnumeration I (maximalGramFrameIndex v)

def selectedFrameVector (v : I → E) (j : ℕ) : E :=
  finiteFrameVector v (maximalGramFrame v) j

end GramFrames

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_KernelVelocityFrames
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual measurable frames for component stabilizers

Projecting the Euclidean coordinate basis and selecting a maximal Gram
minor constructs a frame of each actual stabilizer velocity space. The
frame cardinality and every fixed column are measurable along a Markov
kernel. This supplies the missing measurable input to diagonal recurrence.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace

namespace DukePrimeDegree
open PrimeDegreePackets

def euclideanVelocityColumns {n : ℕ} (μ : Measure (X n))
    (p : Fin n × Fin n) : MatrixEuclidean n :=
  (euclideanVelocitySpace μ).starProjection
    (EuclideanSpace.basisFun (Fin n × Fin n) ℝ p)

def velocityFrameCard {n : ℕ} (μ : Measure (X n)) : ℕ :=
  (maximalGramFrame (euclideanVelocityColumns μ)).card

def velocityFrame {n : ℕ} (μ : Measure (X n)) (j : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  matrixEuclideanEquiv n (selectedFrameVector (euclideanVelocityColumns μ) j)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PositiveRootFactorization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

theorem isClosed_positiveRootGeneratedGroup {n : ℕ} (S : Finset (Fin n × Fin n))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ a b c : Fin n, (a, b) ∈ S → (b, c) ∈ S → (a, c) ∈ S) :
    IsClosed (positiveRootGeneratedGroup S : Set (G n)) := by
  convert isClosed_positiveRootPattern S using 1
  all_goals try with_reducible_and_instances rfl
  ext g
  exact positiveRootGeneratedGroup_iff S hpos hcomp g

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootEuclideanCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

def upperRootEuclideanCoordinates (n : ℕ) :
    UpperRootTime n ≃ₜ ((allPositiveRoots n) → ℝ) :=
  (completeRootChain n).timeVectorHomeomorph.trans (realCoordinatesReindex (upperRootIndexEquiv n))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootContraction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Contracting diagonal dynamics on full upper-root leaves

The explicit root coordinates identify the contracting unipotent
foliation. Uniform root-weight gaps give an exponential bound on its
Euclidean size; strict gaps give convergence to the identity.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def upperRootSize (n : ℕ) (t : UpperRootTime n) : ℝ :=
  ‖upperRootEuclideanCoordinates n t‖

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_CoverPredecessorPacking
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounding predecessor covering labels after one diagonal step

A single small image cell pulls back to a uniformly small chart. The
separated-cover packing bound then controls its possible source labels.
-/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree
open PrimeDegreePackets

def predecessorPackingRadius (n : ℕ) (a : G n) (C D : ℝ) : ℝ :=
  let A := 2*(n:ℝ)*Real.exp (2*matrixLogLength a)*C
  ((n:ℝ)*A)*((n:ℝ)*D)+(n:ℝ)*A+(n:ℝ)*D+1

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RootProductInformation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Information of products of the actual root leaf measures

Rectangular information of a finite product is the sum of its root
information. Its integral is the coefficient-weighted sum of root
information integrals.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

variable {ι : Type*} [Fintype ι] (d : ℕ)
  (i j : ι → Fin (d + 1)) (hij : ∀ a, i a ≠ j a)
  (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
  (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)

/-- Rectangular information in the product of the actual normalized root
leaves, at independently prescribed real logarithmic scales. -/
def rootProductInformation (t : ι → ℝ) (x : X (d + 1)) : ℝ :=
  -Real.log ((Measure.pi (fun a => intrinsicRootLeaf (hij a) μ x))
    (Set.pi univ (fun a => ball 0 (Real.exp (-t a))))).toReal

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CompactNeutralFibers
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform finite covers of neutral itinerary fibers

The small displacement bound puts every bilateral fiber in one fixed
compact subset of the diagonal centralizer. Thus the number of reference
orbits needed for a given accuracy is independent of the base point and
the length of the observed orbit.
-/

noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

local instance instMeasurableSpaceG_1_r84a67f_1 (n : ℕ) : MeasurableSpace (G n) := borel (G n)
local instance instBorelSpaceG_1_r84a67f_1 (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
def compactNeutralDisplacements {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) :
    Set (G n) :=
  {g | (∀ i j, |g.val i j| ≤ 2) ∧
    ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t)}

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_MatrixCoordinateFrames
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coordinate frames on the actual velocity-rank events

The finite-dimensional recurrence argument uses rectangular matrices with
one natural-number row dimension. Flattening the actual matrix space is
only a linear change of coordinates. On each measurable rank event the
selected velocity frame has independent columns and spans the actual
velocity space; outside that event the rectangular frame is zero.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def coordinateVelocityFrame {n : ℕ} (μ : Measure (X n)) (k : ℕ) :
    Matrix (Fin (n * n)) (Fin k) ℝ :=
  Matrix.of (fun q j => if velocityFrameCard μ = k then
    matrixCoordinateEquiv n (velocityFrame μ j) q else 0)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_TransverseDiagonalData
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Diagonal coordinates on the transverse lower triangular slice

Column ratios are fixed by the diagonal action; the logarithms of the
absolute diagonal entries are translated linearly. These are the actual
transverse coordinates, before choosing any finite entropy approximation.
-/

noncomputable section
open Matrix Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma upperRootTransverse_lowerTriangular {n : ℕ} (s : UpperRootTransverse n) :
    s.val.val.IsLowerTriangular := by
  intro i j hij
  have h := s.prop.1 (i,j)
    (by rw [completeRootChain_final]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩)
  exact h

lemma upperRootTransverse_diagonal_ne_zero {n : ℕ} (s : UpperRootTransverse n) (i : Fin n) :
    s.val.val i i ≠ 0 := by
  have hprod : ∏ j, s.val.val j j=1 :=
    (Matrix.det_of_isLowerTriangular s.val.val (upperRootTransverse_lowerTriangular s)).symm.trans
      s.val.prop
  have hn : ∏ j, s.val.val j j ≠ 0 := by rw [hprod]; exact one_ne_zero
  exact (Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i)

def transverseColumnRatios {n : ℕ} (s : UpperRootTransverse n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => s.val.val i j/s.val.val j j

lemma continuous_transverseColumnRatios (n : ℕ) :
    Continuous (@transverseColumnRatios n) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hentry (i j : Fin n) : Continuous (fun s : UpperRootTransverse n => s.val.val i j) := by
    fun_prop
  exact (hentry i j).div (hentry j j) (fun s => upperRootTransverse_diagonal_ne_zero s j)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_TransverseDiagonalFactorization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact neutral fibers of the transverse coordinate map

On the positive-diagonal chart, equality of column ratios means that two
transverse points differ by an actual positive diagonal matrix. This
identifies the neutral coordinates without an abstract quotient factor.
-/

noncomputable section
open Matrix Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma upperRootTransverse_diagonal_prod {n : ℕ} (s : UpperRootTransverse n) :
    ∏ i, s.val.val i i=1 :=
  (Matrix.det_of_isLowerTriangular s.val.val (upperRootTransverse_lowerTriangular s)).symm.trans
    s.val.prop

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralUpperRootHomeomorph
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An actual product chart with neutral translation as its final factor -/

noncomputable section
open Matrix Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma upperRootDilation_opposite_cancel (n : ℕ)
    (v : transverseNeutralSpace n) (r : ℝ) (u : UpperRootTime n) :
    (completeRootChain n).rootDilation v.val (-r)
      ((completeRootChain n).rootDilation v.val r u)=u := by
  apply ((completeRootChain n).word_isEmbedding_remaining (completeRootChain_final n)).injective
  rw [(completeRootChain n).word_rootDilation _ v.prop,
    (completeRootChain n).word_rootDilation _ v.prop]
  rw [diagonalOneParameter_neg]
  group

def neutralRootSkewHomeomorph (n : ℕ) :
    (UnitDiagonalTransverse n × transverseNeutralSpace n) × UpperRootTime n ≃ₜ
      (UnitDiagonalTransverse n × transverseNeutralSpace n) × UpperRootTime n where
  toFun z := (z.1,(completeRootChain n).rootDilation z.1.2.val (-1) z.2)
  invFun z := (z.1,(completeRootChain n).rootDilation z.1.2.val 1 z.2)
  left_inv z := by
    apply Prod.ext
    · rfl
    change (completeRootChain n).rootDilation z.1.2.val 1
      ((completeRootChain n).rootDilation z.1.2.val (-1) z.2)=z.2
    simpa only [neg_neg] using upperRootDilation_opposite_cancel n z.1.2 (-1) z.2
  right_inv z := Prod.ext rfl (upperRootDilation_opposite_cancel n z.1.2 1 z.2)
  continuous_toFun := continuous_fst.prodMk
    ((completeRootChain n).continuous_rootDilation _ _ _
      (continuous_subtype_val.comp continuous_fst.snd) continuous_const continuous_snd)
  continuous_invFun := continuous_fst.prodMk
    ((completeRootChain n).continuous_rootDilation _ _ _
      (continuous_subtype_val.comp continuous_fst.snd) continuous_const continuous_snd)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingRootProductBoxes
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

instance initialRemainingErase_standardBorel {n : ℕ} (q : InitialRootStep n) :
    StandardBorelSpace (positiveRootGeneratedGroup (q.remaining.erase q.root)) := by
  have hcomp : ∀ a b c : Fin n, (a,b) ∈ q.remaining.erase q.root →
      (b,c) ∈ q.remaining.erase q.root → (a,c) ∈ q.remaining.erase q.root := by
    dsimp only [InitialRootStep.remaining]
    rw [initialRemaining_erase]
    exact initialRemaining_roots_closed _
      (initialRootPattern_insert_min q.initial q.root q.mem_remaining q.least)
  exact (isClosed_positiveRootGeneratedGroup _
    (fun p hp => q.remaining_positive p (Finset.mem_of_mem_erase hp)) hcomp).measurableSet.standardBorel

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RightObservableUniformity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform observables near a compact family of right translations

The tolerance is selected before the eventual shearing limit. Matrix
entry control then bounds a compact observable at every base point,
including points outside compact subsets of the lattice space.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction Matrix.Norms.Elementwise

namespace DukePrimeDegree
open PrimeDegreePackets

def rightCompactObservable {n : ℕ}
    (f : CompactlySupportedContinuousMap (X n) ℝ) (g : G n) : X n →ᵇ ℝ :=
  f.toBoundedContinuousFunction.compContinuous ⟨fun x => rightAction x g, continuous_rightAction g⟩

section OppositeAction

local instance rightLatticeOppositeAction (n : ℕ) : MulAction (G n)ᵐᵒᵖ (X n) where
  smul g x := rightAction x g.unop
  one_smul x := rightAction_one x
  mul_smul g h x := by
    change rightAction x (h.unop * g.unop) =
      rightAction (rightAction x h.unop) g.unop
    exact (rightAction_mul x h.unop g.unop).symm

end OppositeAction

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Complete
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Complete discretely valued fields
-/

noncomputable section

universe u v w

namespace DiscreteValuationField

namespace Valuation

end Valuation

namespace CompleteDVF

variable {K : Type u} [Field K]

/-- The complete DVR valuation ring carries its canonical adic-completeness instance. -/
instance instIsAdicComplete (F : CompleteDVF.{u, v} K) :
    IsAdicComplete F.maximalIdeal F.valuationSubring :=
  F.isAdicComplete

end CompleteDVF
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_InfinitePlaceOverfield
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The complex-conjugation overfield at an infinite place

This module realizes the embedded field `L(i)` inside `ℂ`, constructs its
complex place, and identifies ambient complex conjugation on that field.
-/

open scoped Classical IsMulCommutative
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

section ComplexConjugationOverextension

variable
    {K L : Type}
    [Field K]
    [Field L] [NumberField L] [Algebra K L]

variable
    [NumberField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]

attribute [local instance] GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfieldRationalAlgebra
omit [FiniteDimensional K L] in
noncomputable def infinitePlaceRatEmbeddedExtensionField
    (v : InfinitePlace K) :
    IntermediateField ℚ
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  let φ :=
    (InfinitePlace.embedding
      (chosenInfinitePlaceAbove (L := L) v)).toRatAlgHom
  φ.fieldRange.restrict
    (show
      φ.fieldRange ≤
        infinitePlaceComplexificationOverfield
          (K := K) (L := L) v from
      le_sup_left)

omit [FiniteDimensional K L] in
noncomputable def infinitePlaceRatFourthRootField
    (v : InfinitePlace K) :
    IntermediateField ℚ
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  complexFourthRootField.restrict
    (show
      complexFourthRootField ≤
        infinitePlaceComplexificationOverfield
          (K := K) (L := L) v from
      le_sup_right)

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IntegerEmbeddings
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
open MeasureTheory Set Module Filter
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate
open Module
open MeasureTheory Module
open scoped BigOperators Matrix NumberField nonZeroDivisors

open scoped BigOperators NumberField nonZeroDivisors


namespace PrimeDegreePackets
open ThetaConstruction
variable {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]

def subgroupUnitLogKernelEmbedding (σ : OrderedEmbeddings (d+1) K)
    (S : Subgroup (𝓞 K)ˣ) : (subgroupUnitLogOnto σ S).ker ↪ (orderedUnitLogOnto σ).ker where
  toFun z := ⟨Additive.ofMul z.val.toMul.val, by
    apply Subtype.ext
    exact congrArg (fun p : orderedLogSubgroup σ S => p.val)
      (show subgroupUnitLogOnto σ S z.val = 0 from z.property)⟩
  inj' := by
    intro z w h
    apply Subtype.ext
    change Additive.ofMul z.val.toMul = Additive.ofMul w.val.toMul
    apply congrArg
    apply Subtype.ext
    exact congrArg (fun a : (orderedUnitLogOnto σ).ker => a.val.toMul) h

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealThetaFlow
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
open scoped BigOperators Classical ArithmeticFunction.Moebius
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
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
open MeasureTheory Set Module Filter
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate
open Module
open MeasureTheory Module
open scoped BigOperators Matrix NumberField nonZeroDivisors
open scoped BigOperators NumberField nonZeroDivisors
open MeasureTheory Module WithLp Set

open scoped BigOperators NumberField ENNReal

open scoped BigOperators NumberField


namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
variable {K : Type*} [Field K] [NumberField K]


def idealResidueElementWeight (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) : ℂ :=
  χ (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) (idealIntegerElement I hI a))


def idealResidueCoefficient (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (N : ℕ)
    (χ : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) : ℂ :=
  idealResidueElementWeight I hI N χ (idealElementRepresentative _ J)



end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_UnitOrbitIntegrals
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
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
open scoped BigOperators Classical ArithmeticFunction.Moebius
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
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
open MeasureTheory Set Module Filter
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate
open Module
open MeasureTheory Module
open scoped BigOperators Matrix NumberField nonZeroDivisors
open scoped BigOperators NumberField nonZeroDivisors
open MeasureTheory Module WithLp Set
open scoped BigOperators NumberField ENNReal
open scoped BigOperators NumberField
open scoped BigOperators NumberField ENNReal nonZeroDivisors


namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
variable {d : ℕ} {K : Type*} [Field K] [NumberField K]


def integralIdealNonzeroEquiv (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    {a : I // a ≠ 0} ≃ nonzeroIdealElements (integralIdealFractionalUnit I hI) where
  toFun a := ⟨Units.mk0 (((a.1:I):𝓞 K):K) (by
    intro h
    apply a.2
    apply Subtype.ext
    exact NumberField.RingOfIntegers.coe_injective (by simpa using h)),
    FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ a.1.property⟩
  invFun a := ⟨⟨idealIntegerElement I hI a,
    ((FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp a.property).choose_spec.1⟩, by
    intro h
    have H := congrArg (fun x : I => ((x:𝓞 K):K)) h
    simp only [ZeroMemClass.coe_zero,_root_.map_zero,idealIntegerElement_coe] at H
    exact a.1.ne_zero H⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    apply NumberField.RingOfIntegers.coe_injective
    exact idealIntegerElement_coe I hI _
  right_inv a := by
    apply Subtype.ext
    apply Units.ext
    exact idealIntegerElement_coe I hI a

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayEuler
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
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


lemma allCoefficient_mul (I J : Ideal (𝓞 K)) :
    ψ.allCoefficient (I*J) = ψ.allCoefficient I * ψ.allCoefficient J := by
  by_cases hI : I = 0
  · simp [hI]
  by_cases hJ : J = 0
  · simp [hJ]
  change I ≠ ⊥ at hI
  change J ≠ ⊥ at hJ
  have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
  simp only [allCoefficient, dite_eq_left hI, dite_eq_left hJ, dite_eq_left hIJ,
    IsCoprime.mul_left_iff]
  by_cases hcI : IsCoprime I (rationalModulusIdeal (𝓞 K) N)
  · by_cases hcJ : IsCoprime J (rationalModulusIdeal (𝓞 K) N)
    · simp only [hcI, hcJ, and_self, ite_true, if_true]
      have H := congrArg (fun U : (FractionalIdeal (𝓞 K)⁰ K)ˣ =>
        (ψ.idealHom U : ℂ)) (integralUnit_mul I J hI hJ)
      simpa only [map_mul, Units.val_mul] using H
    · simp [hcI, hcJ]
  · simp [hcI]

 

def coefficientHom : Ideal (𝓞 K) →*₀ ℂ where
  toFun := ψ.allCoefficient
  map_zero' := ψ.allCoefficient_zero
  map_one' := ψ.allCoefficient_one
  map_mul' := ψ.allCoefficient_mul


def idealTerm {s : ℂ} (hs : 1 < s.re) : Ideal (𝓞 K) →*₀ ℂ :=
  ψ.coefficientHom * (riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs)).comp
    Ideal.absNorm


def normTerm {s : ℂ} (hs : 1 < s.re) (m : ℕ) : ℂ :=
  ∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = m}, ψ.idealTerm hs I.val

end EvenRayCharacter
end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayDescent
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
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



lemma coprime_inverse_product (hψ : ψ.residue = 1)
    (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hIc : IsCoprime I (rationalModulusIdeal (𝓞 K) N))
    (hJc : IsCoprime J (rationalModulusIdeal (𝓞 K) N))
    (hclass : ClassGroup.mk K (integralIdealFractionalUnit J hJ) =
      (ClassGroup.mk K (integralIdealFractionalUnit I hI))⁻¹) :
    ψ.idealHom (integralIdealFractionalUnit I hI) *
      ψ.idealHom (integralIdealFractionalUnit J hJ) = 1 := by
  let Jf : integralIdealClassFiber (integralIdealFractionalUnit I hI) :=
    ⟨integralIdealFractionalUnit J hJ, FractionalIdeal.coeIdeal_le_one, hclass⟩
  let a := idealIntegerElement I hI (idealElementRepresentative _ Jf)
  have ha : a ≠ 0 := generator_integer_ne_zero I hI Jf
  have hp : Ideal.span {a} = I * J := by
    have H := generator_principal_product I hI Jf
    change Ideal.span {a} = I * underlyingIdeal
      ⟨integralIdealFractionalUnit J hJ, FractionalIdeal.coeIdeal_le_one⟩ at H
    simpa only [underlyingIdeal_integralUnit] using H
  have hac : IsCoprime (Ideal.span {a}) (rationalModulusIdeal (𝓞 K) N) := by
    rw [hp]
    exact IsCoprime.mul_left_iff.mpr ⟨hIc, hJc⟩
  have H := ψ.principalLaw a ha hac
  rw [hψ, MulChar.one_apply ((quotient_isUnit_iff_span_coprime _ a).mpr hac)] at H
  have HG := generator_fractional_product I hI Jf
  change integralIdealFractionalUnit (Ideal.span {a}) _ =
    integralIdealFractionalUnit I hI * integralIdealFractionalUnit J hJ at HG
  rw [HG, map_mul, Units.val_mul] at H
  exact Units.ext H

variable [NeZero N]

 

theorem idealHom_eq_of_coprime_class (hψ : ψ.residue = 1)
    (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hIc : IsCoprime I (rationalModulusIdeal (𝓞 K) N))
    (hJc : IsCoprime J (rationalModulusIdeal (𝓞 K) N))
    (hclass : ClassGroup.mk K (integralIdealFractionalUnit I hI) =
      ClassGroup.mk K (integralIdealFractionalUnit J hJ)) :
    ψ.idealHom (integralIdealFractionalUnit I hI) =
      ψ.idealHom (integralIdealFractionalUnit J hJ) := by
  let c := ClassGroup.mk K (integralIdealFractionalUnit I hI)
  let L := (classIdeal K N c⁻¹).val
  have hL : L ≠ ⊥ := classIdeal_ne_bot c⁻¹
  have hcL : IsCoprime L (rationalModulusIdeal (𝓞 K) N) := classIdeal_coprime c⁻¹
  have hlclass : ClassGroup.mk K (integralIdealFractionalUnit L hL) = c⁻¹ :=
    classIdeal_class c⁻¹
  have HI := ψ.coprime_inverse_product hψ L I hL hI hcL hIc (by
    rw [hlclass, inv_inv])
  have HJ := ψ.coprime_inverse_product hψ L J hL hJ hcL hJc (by
    rw [hlclass, inv_inv]
    exact hclass.symm)
  exact mul_left_cancel (HI.trans HJ.symm)



end EvenRayCharacter

variable {K : Type*} [Field K] [NumberField K]

 

def classRayCharacter (χ : ClassGroup (𝓞 K) →* ℂˣ) : EvenRayCharacter K 1 where
  idealHom := χ.comp (ClassGroup.mk K)
  finiteOrder := ⟨Fintype.card (ClassGroup (𝓞 K)), Fintype.card_pos, fun J => by
    rw [MonoidHom.comp_apply, ← map_pow, pow_card_eq_one, map_one]⟩
  residue := 1
  principalLaw := by
    intro a ha hc
    rw [MulChar.one_apply ((quotient_isUnit_iff_span_coprime _ a).mpr hc)]
    have hspan : Ideal.span {a} ≠ ⊥ := by simpa using ha
    suffices H : ClassGroup.mk K (integralIdealFractionalUnit (Ideal.span {a}) hspan) = 1 by
      simp only [MonoidHom.comp_apply, H, map_one, Units.val_one]
    rw [← map_one (ClassGroup.mk K)]
    symm
    apply (fractionalIdeal_same_class _ _).mpr
    refine ⟨(a : K), (by exact_mod_cast ha), ?_⟩
    simp only [Units.val_one, mul_one]
    change FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) =
      (Ideal.span {a} : FractionalIdeal (𝓞 K)⁰ K)
    rw [FractionalIdeal.coeIdeal_span_singleton]

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayUnramified
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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


def classEulerCorrection (χ : ClassGroup (𝓞 K) →* ℂˣ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  ∏ P : idealsOverPrime K (p:ℕ),
    (1 - (classRayCharacter χ).allCoefficient P.val * (Ideal.absNorm P.val : ℂ)^(-s))

def badEulerCorrection (χ : ClassGroup (𝓞 K) →* ℂˣ) (N : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ badPrimes N, classEulerCorrection χ p s

end EvenRayCharacter
end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayRealization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module
open scoped NumberField nonZeroDivisors Classical
namespace PrimeDegreePackets.PrincipalRay
open ThetaConstruction
variable {F : Type*} [Field F] [NumberField F]
variable (φ : (FractionalIdeal (𝓞 F)⁰ F)ˣ →* ℂˣ)

def realize (N : ℕ) (hN : 0 < N) (hk : KernelLaw φ N)
    (hf : ∃ e : ℕ, 0 < e ∧ ∀ J, φ J ^ e = 1) : EvenRayCharacter F N where
  idealHom := φ
  finiteOrder := hf
  residue := MulChar.ofUnitHom (residueHom φ N hN hk)
  principalLaw a ha hc := by
    have hu := (quotient_isUnit_iff_span_coprime (rationalModulusIdeal (𝓞 F) N) a).mpr hc
    change (principalValue φ a ha : ℂ) = _
    rw [show Ideal.Quotient.mk (rationalModulusIdeal (𝓞 F) N) a = (hu.unit : (𝓞 F) ⧸ rationalModulusIdeal (𝓞 F) N) from hu.unit_spec.symm,
      MulChar.ofUnitHom_coe, residueHom_spec φ N hN hk a ha hu.unit hu.unit_spec.symm]

end PrimeDegreePackets.PrincipalRay
end

end OAI
end


