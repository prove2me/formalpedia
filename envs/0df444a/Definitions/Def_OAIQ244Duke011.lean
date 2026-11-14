-- Prove2me | Definitions.Def_OAIQ244Duke011
-- name    : OAIQ244Duke011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:11:20.580194+00:00
-- url     : https://prove2.me/theorems/c0137e48-9058-4549-89c3-b5d311182da0
-- title:
--   Definitions bundle OAIQ244Duke011 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 350 declarations of OpenAI's Lean: 147 definitions, 6 inductive types or structures, 23 instances and 174 theorems. The definitions and types are `GlobalClassFieldTheory.GlobalClassFields.infinitePlaceCompletionCongrHom`, `GlobalClassFieldTheory.Reciprocity.automorphismCyclicFixedField`, `GlobalClassFieldTheory.Reciprocity.automorphismOverCyclicFixedField`, `GlobalClassFieldTheory.Reciprocity.commutativeGroupInversionContinuousMulEquiv`, `GlobalClassFieldTheory.Reciprocity.composeMonoidHom`, `GlobalClassFieldTheory.Reciprocity.continuousSubgroupSubtype`, `GlobalClassFieldTheory.Reciprocity.quotientLiftData`, `HilbertRamification.Dedekind.decompositionGroup`, `HilbertRamification.Dedekind.dedekindRamification_decompositionQuotientInertiaEquivResidueGalois`, `HilbertRamification.Dedekind.inertiaGroup`, `HilbertRamification.Dedekind.residueStabilizerHom`, `KummerTheory.adjoinSubtypeEquivAmbientAdjoin`, `KummerTheory.multiplicativeZModProductEquivPiSucc`, `LocalFieldTheory.DiscreteValuationField.WithZeroValuation.rankOne`, `OAI.DukePrimeDegree.BasisProbability`, `OAI.DukePrimeDegree.BlockEliminationChain`, `OAI.DukePrimeDegree.BlockEliminationChain.append`, `OAI.DukePrimeDegree.BlockEliminationChain.finalEntries`, `OAI.DukePrimeDegree.BlockZeroPattern`, `OAI.DukePrimeDegree.CompletedXiGap`, `OAI.DukePrimeDegree.CyclicSubgroups`, `OAI.DukePrimeDegree.EKLPrimeInput`, `OAI.DukePrimeDegree.EliminationChain`, `OAI.DukePrimeDegree.EliminationChain.FinalSlice`, `OAI.DukePrimeDegree.EliminationChain.Time`, `OAI.DukePrimeDegree.EliminationChain.closedCube`, `OAI.DukePrimeDegree.EliminationChain.cube`, `OAI.DukePrimeDegree.EliminationChain.finalEntries`, `OAI.DukePrimeDegree.EliminationChain.finalPivots`, `OAI.DukePrimeDegree.EliminationChain.roots`, `OAI.DukePrimeDegree.EliminationChain.word`, `OAI.DukePrimeDegree.EliminationChain.zeroTime`, `OAI.DukePrimeDegree.EliminationSlice`, `OAI.DukePrimeDegree.EmbeddingOrder`, `OAI.DukePrimeDegree.EmbeddingOrder.toRealOrder`, `OAI.DukePrimeDegree.ExceptionalRealZeroExclusion`, `OAI.DukePrimeDegree.FullLattice`, `OAI.DukePrimeDegree.FullLattice.integralBasis`, `OAI.DukePrimeDegree.FullLattice.rationalBasis`, `OAI.DukePrimeDegree.FullLattice.toPacket` and 113 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Galois_FixedFieldLattice`, `AlgebraicNumberTheory_RayClass_Rational`, `AlgebraicNumberTheory_RayClass_Topology`, `DukePrimeDegree_Arithmetic_CyclicInduction`, `DukePrimeDegree_Arithmetic_FullLattice`, `DukePrimeDegree_Arithmetic_LatticeBasis`, `DukePrimeDegree_Arithmetic_PacketBridge`, `DukePrimeDegree_Arithmetic_StarkZeros`, `DukePrimeDegree_Dynamics_BlockOrbit`, `DukePrimeDegree_Dynamics_BlockTransverseElimination`, `DukePrimeDegree_Dynamics_ConjugationOrbit`, `DukePrimeDegree_Dynamics_ExtremalRootFlow`, `DukePrimeDegree_Dynamics_HorosphereIsolatingFlow`, `DukePrimeDegree_Dynamics_MatrixVelocitySpace`, `DukePrimeDegree_Dynamics_PrimeBlockRationality`, `DukePrimeDegree_Dynamics_ReverseRootFlow`, `DukePrimeDegree_Dynamics_RootCentralizer`, `DukePrimeDegree_Dynamics_RootShearing`, `DukePrimeDegree_Entropy_EntropyBalance`, `DukePrimeDegree_Entropy_InfiniteLabelEntropy`, `DukePrimeDegree_Entropy_RegularEntropyTests`, `DukePrimeDegree_Geometry_CountableWeakKernel`, `DukePrimeDegree_Geometry_EliminationChain`, `DukePrimeDegree_Geometry_EliminationRootChart`, `DukePrimeDegree_Geometry_EliminationRootOrder`, `DukePrimeDegree_Geometry_EmbeddingMatrix`, `DukePrimeDegree_Geometry_FiniteProjectionFrames`, `DukePrimeDegree_Geometry_LexicographicRootWeights`, `DukePrimeDegree_Geometry_MatrixLogLength`, `DukePrimeDegree_Geometry_NeutralDiagonal`, `DukePrimeDegree_Geometry_OrderedEliminationChain`, `DukePrimeDegree_Geometry_PositiveRootCoordinates`, `DukePrimeDegree_Geometry_PositiveRootFactorization`, `DukePrimeDegree_Geometry_PositiveRootPattern`, `DukePrimeDegree_Geometry_QuotientNeighborhoods`, `DukePrimeDegree_Geometry_RootContraction`, `DukePrimeDegree_Geometry_RootCurveExtraction`, `DukePrimeDegree_Geometry_RootInductionStep`, `DukePrimeDegree_Geometry_RootLeafLowerBound`, `DukePrimeDegree_Geometry_UpperRootChart`, `DukePrimeDegree_Geometry_UpperRootDisintegration`, `DukePrimeDegree_Geometry_UpperRootEuclideanCoordinates`, `DukePrimeDegree_Geometry_UpperRootGlobalCoordinates`, `DukePrimeDegree_Geometry_UpperRootLongBoxes`, `DukePrimeDegree_Geometry_UpperRootWindows`, `DukePrimeDegree_MainConditional`, `GlobalClassFieldTheory_GlobalClassFields_BigHilbertClassFieldNaturality`, `GlobalClassFieldTheory_GlobalClassFields_CyclotomicKummerNormDescent`, `GlobalClassFieldTheory_GlobalClassFields_SUnitKummerNormCore`, `GlobalClassFieldTheory_Reciprocity_ArithmeticNormalization`, `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_InfinitePlaceOverfield`, `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_OverextensionArtin`, `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RationalComplexification`, `GlobalClassFieldTheory_Reciprocity_CyclotomicUnramifiedLocalGlobalCompatibility`, `GlobalClassFieldTheory_Reciprocity_GlobalNormResidueNaturality`, `GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicAuxiliaryField`, `GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicCyclicData`, `GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_SeparableClosurePadicLift`, `GlobalClassFieldTheory_Reciprocity_RationalPrimeFactorization`, `KummerTheory_Concrete_SUnitKummerUnramified`, `KummerTheory_Concrete_SUnitPreparation_SUnitPowerQuotient`, `LocalClassFieldTheory_LubinTateApplication_StandardSubgroupIndex`, `LocalField_DiscreteValuationField_ValuationSubringUnits_CyclicValueGroup`, `LocalField_GroupTheory_PowerIndex`, `LocalField_Padic_ClosedAddSubgroup`, `PrimePackets_AtomMass`, `PrimePackets_CoordinateLattices`, `PrimePackets_ErgodicDecomposition`, `PrimePackets_GaussianMellin`, `PrimePackets_IdealNorms`, `PrimePackets_IdealThetaXi`, `PrimePackets_KernelScaling`, `PrimePackets_LatticeTheta`, `PrimePackets_LeafNormalization`, `PrimePackets_LeafSupport`, `PrimePackets_ObservationCovers`, `PrimePackets_PacketAlgebra`, `PrimePackets_PacketMoments`, `PrimePackets_PeriodicTheta`, `PrimePackets_PrincipalUnits`, `PrimePackets_RayCharacter`, `PrimePackets_RayEuler`, `PrimePackets_RayFrobenius`, `PrimePackets_RootCharts`, `PrimePackets_RootRelations`, `PrimePackets_RootSubgroups`, `PrimePackets_ShannonEntropy`, `PrimePackets_ThetaTails`, `PrimePackets_XiBoundary`, `PrimePackets_ZeroSeparation`, `PrimePackets_ZetaResidues`, `Ramification_HilbertRamification_Dedekind_Basic`, `Ramification_HilbertRamification_Dedekind_CompositumUnramified`, `Ramification_HilbertRamification_Dedekind_OrbitCardinality`.
--
--   **Imports.** It imports the published bundle `Def_DukePrimeDegree`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke014`, `OAIQ244Duke020`, `OAIQ244Duke021`, `OAIQ244Duke022`, `OAIQ244Duke023` and `OAIQ244Duke024`; the statements `OAI.DukePrimeDegree.completedXiGap_of_exceptionalRealZeroExclusion`, `OAI.DukePrimeDegree.eklPrimeInput_unconditional`, `OAI.DukePrimeDegree.exists_bounded_cover_subordinate_observation`, `OAI.DukePrimeDegree.exists_noncentral_neutral_return_sequence`, `OAI.DukePrimeDegree.logRegularized_deriv_bound_of_completedXi_gap`, `OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi_conj_totallyReal`, `OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi_entire`, `OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi_functionalEquation_totallyReal`, `OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi_hasSubquadraticGrowth`, `OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi_logDeriv_base_le_totallyReal`, `OAI.PrimeDegreePackets.HeckeMellin.dedekindXi_realZeroPole_nonneg_totallyReal`, `OAI.PrimeDegreePackets.HeckeMellin.idealThetaXi_entire` and `OAI.PrimeDegreePackets.HeckeMellin.idealThetaXi_reflection_totallyReal`.
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
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.Pointwise
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
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.BigOperators
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
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.LinearDisjoint
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
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.NumberTheory.Cyclotomic.Discriminant
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
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
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.Module
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
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Group.Pointwise
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

section
-- module Solutions.OAIQ244_DUKE.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `MeasurableSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean): the product structure
(InvariantIsing, q251). Explicitly named: the platform's `Def_InvariantIsing` declares an anonymous copy of the same
instance. -/
instance _root_.Matrix.compatMeasurableSpace {m n α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Matrix m n α) :=
  inferInstanceAs <| MeasurableSpace (m → n → α)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Galois_FixedFieldLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Fixed fields and subgroup lattice operations

Small order-theoretic facts about fixed fields of automorphism subgroups.
They do not depend on class field theory and belong with the general Galois
infrastructure rather than a concrete reciprocity construction.
-/

namespace IntermediateField

/-- Fixed fields turn a supremum of automorphism subgroups into the
intersection of their fixed fields. -/
theorem fixedField_sup_eq_inf
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (S T : Subgroup (Gal(Ω / k))) :
    IntermediateField.fixedField (S ⊔ T) =
      IntermediateField.fixedField S ⊓ IntermediateField.fixedField T := by
  apply le_antisymm
  · exact le_inf
      (IntermediateField.fixedField_le le_sup_left)
      (IntermediateField.fixedField_le le_sup_right)
  · intro x hx
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    let stabilizer : Subgroup (Gal(Ω / k)) :=
      MulAction.stabilizer (Gal(Ω / k)) x
    have hS : S ≤ stabilizer := by
      intro τ hτ
      change τ x = x
      exact (IntermediateField.mem_fixedField_iff S x).1 hx.1 τ hτ
    have hT : T ≤ stabilizer := by
      intro τ hτ
      change τ x = x
      exact (IntermediateField.mem_fixedField_iff T x).1 hx.2 τ hτ
    have hfix : σ ∈ stabilizer := (sup_le hS hT) hσ
    exact hfix

end IntermediateField
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_Topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The congruence topology on the idele class group

The local higher-unit groups are open,
the ray congruence subgroups are open (and hence closed) of finite index, and
the congruence subgroups are cofinal among the closed finite-index subgroups
of the idele class group.
-/

open scoped Classical NumberField RestrictedProduct WithZero
open NumberField IsDedekindDomain
open Topology

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

/-- The multiplicative topological equivalence between a complex infinite
completion and `ℂ`. -/
def complexCompletionContinuousMulEquiv
    (v : InfinitePlace K) (hv : v.IsComplex) :
    v.Completion ≃ₜ* ℂ where
  __ :=
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).toMulEquiv
  continuous_toFun :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).continuous
  continuous_invFun :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.continuous

/-- A positive real number regarded as a unit. -/
def positiveRealUnit (x : Set.Ioi (0 : ℝ)) : ℝˣ :=
  Units.mk0 x.1 x.2.ne'

/-- The map from positive real numbers to real units is continuous. -/
theorem continuous_positiveRealUnit :
    Continuous positiveRealUnit := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous
      (fun x : Set.Ioi (0 : ℝ) ↦ (x : ℝ))
    exact continuous_subtype_val
  · change Continuous
      (fun x : Set.Ioi (0 : ℝ) ↦ ((x : ℝ)⁻¹))
    exact continuous_subtype_val.inv₀
      (fun x : Set.Ioi (0 : ℝ) ↦ x.2.ne')

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_Rational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Ray class groups of the rational numbers

This file computes ray class groups of the rational numbers. A positive integer
`m` determines a full narrow ray modulus: its finite part has exponent
`m.factorization p` at `p`, and its real place imposes positivity. The
positive generator of an ideal prime to this modulus gives the explicit
isomorphism with `(ZMod m)ˣ`.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section


namespace RayClass

local instance rationalRingOfIntegersIsPrincipalIdealRing :
    IsPrincipalIdealRing (𝓞 ℚ) :=
  IsPrincipalIdealRing.of_surjective
    Rat.ringOfIntegersEquiv.symm
    Rat.ringOfIntegersEquiv.symm.surjective

local instance rationalNatGeneratorPrimeFact_rda812e_1
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.natGenerator v)) :=
  ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
local instance rationalPrimesEquivPrimeFact_rda812e_1
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Fact
      (Nat.Prime
        ((Rat.HeightOneSpectrum.primesEquiv
          (R := 𝓞 ℚ) v : Nat.Primes) : ℕ)) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv
    (R := 𝓞 ℚ) v).property⟩
theorem rational_natGenerator_injective :
    Function.Injective
      (Rat.HeightOneSpectrum.natGenerator :
        HeightOneSpectrum (𝓞 ℚ) → ℕ) := by
  intro v w hvw
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  exact Subtype.ext hvw

/-- Positive rational generators of the same principal fractional ideal
are equal. -/
theorem eq_of_spanSingleton_eq_of_pos
    {x y : ℚ} (hx : 0 < x) (hy : 0 < y)
    (h :
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ℚ)) x =
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ℚ)) y) :
    x = y := by
  obtain ⟨u, hu⟩ :=
    (FractionalIdeal.spanSingleton_eq_spanSingleton
      (S := nonZeroDivisors (𝓞 ℚ))).1 h
  rcases Rat.RingOfIntegers.isUnit_iff.mp u.isUnit with hu1 | hu1
  · simpa [Units.smul_def, Algebra.smul_def, hu1] using hu
  · have hxy : -x = y := by
      simpa [Units.smul_def, Algebra.smul_def, hu1] using hu
    linarith

/-- An element of `WithZero (Multiplicative ℤ)` with logarithm zero is
one. -/
theorem withZero_eq_one_of_log_eq_zero
    {x : WithZero (Multiplicative ℤ)} (hx : x ≠ 0)
    (hlog : WithZero.log x = 0) :
    x = 1 := by
  calc
    x = WithZero.exp (WithZero.log x) :=
      (WithZero.exp_log hx).symm
    _ = WithZero.exp 0 := congrArg WithZero.exp hlog
    _ = 1 := rfl

/-! ### The local congruence condition over `ℚ` -/

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketAlgebra
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

lemma fullLattice_span_basis {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) :
    Submodule.span ℤ (Set.range fun i => (M.basis i : K)) = M.carrier := by
  rw [show (Set.range fun i => (M.basis i : K)) =
    M.carrier.subtype '' Set.range M.basis by rw [← Set.range_comp]; rfl]
  rw [← Submodule.map_span, M.basis.span_eq, Submodule.map_top, Submodule.range_subtype]

lemma fullLattice_rat_span_basis {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) :
    Submodule.span ℚ (Set.range fun i => (M.basis i : K)) = ⊤ := by
  rw [← Submodule.span_span_of_tower ℤ ℚ, fullLattice_span_basis, M.spans]

 

def fullLatticeRatBasis {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) : Basis (Fin n) ℚ K :=
  basisOfTopLeSpanOfCardEqFinrank (fun i => (M.basis i : K))
    (fullLattice_rat_span_basis M).ge (by simpa using hn.symm)

@[simp] lemma fullLatticeRatBasis_apply {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (i : Fin n) :
    fullLatticeRatBasis M hn i = M.basis i := by
  simp [fullLatticeRatBasis, coe_basisOfTopLeSpanOfCardEqFinrank]

lemma completedLattice_eq_span_basis {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime] :
    completedLattice p M = Submodule.span (PadicInt p)
      (Set.range fun i => (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K)
        (M.basis i)) := by
  let f : K →ₐ[ℚ] LocalAlgebra p K := Algebra.TensorProduct.includeRight
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    rw [← fullLattice_span_basis M] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i,rfl⟩ := hy
      exact Submodule.subset_span ⟨i,rfl⟩
    | zero => simp
    | add x y hx hy ihx ihy =>
      change f (x+y) ∈ _
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
    | smul a x hx ih =>
      change f (a • x) ∈ _
      rw [map_zsmul]
      exact (Submodule.span (PadicInt p) (Set.range fun i => f (M.basis i))).toAddSubgroup.zsmul_mem ih a
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Submodule.subset_span ⟨M.basis i,(M.basis i).property,rfl⟩

lemma completedLattice_basis_independent {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] :
    LinearIndependent (PadicInt p)
      (fun i => (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) (M.basis i)) := by
  have H := (((fullLatticeRatBasis M hn).baseChange (Padic p)).linearIndependent).restrict_scalars'
    (PadicInt p)
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  ext i
  simp

 

def completedLatticeBasis {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] : Basis (Fin n) (PadicInt p) (completedLattice p M) :=
  (Basis.span (completedLattice_basis_independent M hn p)).map
    (LinearEquiv.ofEq _ _ (completedLattice_eq_span_basis M p).symm)

@[simp] lemma completedLatticeBasis_coe {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] (i : Fin n) :
    (completedLatticeBasis M hn p i : LocalAlgebra p K) =
      (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) (M.basis i) := by
  unfold completedLatticeBasis
  rw [Basis.map_apply, Basis.span_apply]
  rfl


def completionEmbedding {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime] :
    M.carrier →ₗ[ℤ] (completedLattice p M) where
  toFun x := ⟨Algebra.TensorProduct.includeRight x,Submodule.subset_span ⟨x,x.property,rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    change (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) (x+y) = _
    exact map_add _ _ _
  map_smul' a x := by
    apply Subtype.ext
    change (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) (a • (x : K)) = _
    exact map_zsmul _ _ _

@[simp] lemma completionEmbedding_basis {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] (i : Fin n) :
    completionEmbedding M p (M.basis i) = completedLatticeBasis M hn p i := by
  apply Subtype.ext
  exact (completedLatticeBasis_coe M hn p i).symm

open scoped NumberField Pointwise nonZeroDivisors
open NumberField

 
def completedFractionalIdeal {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : FractionalIdeal (𝓞 K)⁰ K) :
    Submodule (PadicInt p) (LocalAlgebra p K) :=
  Submodule.span (PadicInt p)
    ((Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) '' (I : Set K))

lemma completedFractionalIdeal_mul_mem {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I J : FractionalIdeal (𝓞 K)⁰ K)
    {x y : LocalAlgebra p K} (hx : x ∈ completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K))
    (hy : y ∈ completedFractionalIdeal p J) : x*y ∈ completedFractionalIdeal p (I*J) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a,ha,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b,hb,rfl⟩ := hy
      rw [← map_mul]
      exact Submodule.subset_span ⟨a*b,FractionalIdeal.mul_mem_mul ha hb,rfl⟩
    | zero => simp
    | add x y hx hy ihx ihy =>
      rw [mul_add]
      exact Submodule.add_mem _ ihx ihy
    | smul c x hx ih =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ c ih
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [add_mul]
    exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c ih



def completedMaximalOrder {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] : Subalgebra (PadicInt p) (LocalAlgebra p K) where
  carrier := completedFractionalIdeal p (1 : FractionalIdeal (𝓞 K)⁰ K)
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  mul_mem' hx hy := by
    have H := completedFractionalIdeal_mul_mem p 1 1 hx hy
    simp only [one_mul] at H
    exact H
  algebraMap_mem' a := by
    have h1 : (1 : LocalAlgebra p K) ∈ completedFractionalIdeal p (1 : FractionalIdeal (𝓞 K)⁰ K) := by
      exact Submodule.subset_span ⟨1,(FractionalIdeal.mem_one_iff (𝓞 K)⁰).mpr ⟨1,map_one _⟩,map_one _⟩
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem (completedFractionalIdeal p (1 : FractionalIdeal (𝓞 K)⁰ K)) a h1

@[simp] lemma completedMaximalOrder_toSubmodule {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] :
    (completedMaximalOrder (K := K) p).toSubmodule = completedFractionalIdeal p (1 : FractionalIdeal (𝓞 K)⁰ K) := rfl


def saturationFractionalIdeal {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : FractionalIdeal (𝓞 K)⁰ K :=
  ⟨Submodule.span (𝓞 K) (M.carrier : Set K), FractionalIdeal.isFractional_of_fg <| by
    rw [← fullLattice_span_basis M, Submodule.span_span_of_tower]
    exact Submodule.fg_span (Set.finite_range _)⟩


def fractionalIdealFullLattice {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : Module.finrank ℚ K = n) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FullLattice n K where
  carrier := (I : Submodule (𝓞 K) K).restrictScalars ℤ
  basis := (fractionalIdealBasis K I.1).reindex (Fintype.equivFinOfCardEq (by
    rw [← Module.finrank_eq_card_basis (basisOfFractionalIdeal K I)]
    exact hn))
  spans := by
    have h : ((I : Submodule (𝓞 K) K).restrictScalars ℤ : Set K) =
        (Submodule.span ℤ (Set.range (basisOfFractionalIdeal K I)) : Set K) := by
      ext x; exact (mem_span_basisOfFractionalIdeal (I := I) (x := x)).symm
    rw [h,Submodule.span_span_of_tower,(basisOfFractionalIdeal K I).span_eq]

@[simp] lemma completedLattice_fractionalIdealFullLattice
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : Module.finrank ℚ K = n) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] :
    completedLattice p (fractionalIdealFullLattice hn I) = completedFractionalIdeal p (I : FractionalIdeal (𝓞 K)⁰ K) := rfl



def globalLabels {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Set (Submodule ℤ K) :=
  {P | ∃ N : FullLattice n K, N.carrier = P ∧ LocallyHomothetic M N ∧
    saturationFractionalIdeal N = (I : FractionalIdeal (𝓞 K)⁰ K)}

def globalLabelLattice {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (N : globalLabels M I) : FullLattice n K := N.property.choose

lemma globalLabelLattice_spec {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (N : globalLabels M I) : (globalLabelLattice M I N).carrier = N.val ∧
      LocallyHomothetic M (globalLabelLattice M I N) ∧
      saturationFractionalIdeal (globalLabelLattice M I N) = (I : FractionalIdeal (𝓞 K)⁰ K) :=
  N.property.choose_spec

open Topology
open scoped Pointwise

def scaleFullLattice {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (a : Kˣ) : FullLattice n K where
  carrier := M.carrier.map ((LinearEquiv.smulOfUnit (M := K) a).restrictScalars ℤ).toLinearMap
  basis := M.basis.map (Submodule.equivMapOfInjective
    ((LinearEquiv.smulOfUnit (M := K) a).restrictScalars ℤ).toLinearMap
    ((LinearEquiv.smulOfUnit (M := K) a).restrictScalars ℤ).injective _)
  spans := by
    change Submodule.span ℚ (((LinearEquiv.smulOfUnit (M := K) a).restrictScalars ℚ).toLinearMap ''
      (M.carrier : Set K)) = ⊤
    rw [← Submodule.map_span, M.spans, Submodule.map_top, LinearEquiv.range]

@[simp] lemma scaleFullLattice_basis {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (a : Kˣ) (i : Fin n) :
    ((scaleFullLattice M a).basis i : K) = (a : K) * (M.basis i : K) := rfl

lemma scaleFullLattice_carrier {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (a : Kˣ) :
    ((scaleFullLattice M a).carrier : Set K) = (fun x => (a : K) * x) '' (M.carrier : Set K) := rfl

lemma completedLattice_scale {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (a : Kˣ) (p : ℕ) [Fact p.Prime] :
    completedLattice p (scaleFullLattice M a) =
      (completedLattice p M).map (LinearMap.mulLeft (PadicInt p)
        (Algebra.TensorProduct.includeRight (R := ℚ) (A := Padic p) (a : K))) := by
  unfold completedLattice
  rw [scaleFullLattice_carrier, Submodule.map_span, Set.image_image, Set.image_image]
  congr 1
  apply Set.image_congr
  intro x _
  exact map_mul _ _ _

open Polynomial



open scoped NNReal

open Polynomial
open scoped BigOperators

open IsDiscreteValuationRing IsLocalRing Module


open MeasureTheory
open scoped ENNReal

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaResidues
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
namespace PrimeDegreePackets

theorem embeddingMatrix_det_ne_zero {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n) :
    Matrix.det (embeddingMatrix M σ) ≠ 0 := by
  let b := fullLatticeRatBasis M hn
  let e : Fin n → (K →ₐ[ℚ] ℝ) := fun i => RingHom.equivRatAlgHom K ℝ (σ i)
  have he : Function.Injective e := (RingHom.equivRatAlgHom K ℝ).injective.comp σ.injective
  have H := (linearIndependent_algHom_toLinearMap ℚ K ℝ).comp e he
  have H' := H.map' (b.constr ℝ).symm.toLinearMap (b.constr ℝ).symm.ker
  apply Matrix.nonsingular_iff_det_ne_zero.mp
  apply Matrix.Nonsingular.of_linearIndependent_col
  have heq : (b.constr ℝ).symm.toLinearMap ∘ AlgHom.toLinearMap ∘ e =
      (embeddingMatrix M σ).col := by
    ext i j
    simp [b, e, embeddingMatrix, Matrix.col, Function.comp_def]
  rw [heq] at H'
  exact H'



open scoped NumberField nonZeroDivisors



def integralUnit {K : Type*} [Field K] [NumberField K] : (𝓞 K)ˣ →* Kˣ :=
  Units.map (algebraMap (𝓞 K) K).toMonoidHom



def unitSigns {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) : (𝓞 K)ˣ →* (Fin n → SignTypeˣ) where
  toFun u i := Units.map ((signHom : ℝ →*₀ SignType).toMonoidHom.comp
    (σ i).toMonoidHom) (integralUnit u)
  map_one' := by ext i; simp
  map_mul' u v := by ext i; simp



def logSubgroup {K : Type*} [Field K] [NumberField K] (S : Subgroup (𝓞 K)ˣ) :
    Submodule ℤ (NumberField.Units.dirichletUnitTheorem.logSpace K) :=
  Submodule.map (NumberField.Units.logEmbedding K).toIntLinearMap
    S.toAddSubgroup.toIntSubmodule

lemma logSubgroup_le_unitLattice {K : Type*} [Field K] [NumberField K]
    (S : Subgroup (𝓞 K)ˣ) : logSubgroup S ≤ NumberField.Units.unitLattice K :=
  Submodule.map_mono le_top

instance logSubgroup_discrete {K : Type*} [Field K] [NumberField K]
    (S : Subgroup (𝓞 K)ˣ) : DiscreteTopology (logSubgroup S) := by
  apply DiscreteTopology.of_continuous_injective
    (f := Submodule.inclusion (logSubgroup_le_unitLattice S))
  · exact continuous_subtype_val.subtype_mk _
  · exact Submodule.inclusion_injective _

 

theorem logSubgroup_span_eq_top {K : Type*} [Field K] [NumberField K]
    (S : Subgroup (𝓞 K)ˣ) [S.FiniteIndex] :
    Submodule.span ℝ (logSubgroup S : Set (NumberField.Units.dirichletUnitTheorem.logSpace K)) = ⊤ := by
  rw [eq_top_iff, ← NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top K]
  apply Submodule.span_le.mpr
  intro x hx
  obtain ⟨u, _, rfl⟩ := Submodule.mem_map.mp hx
  have hu : (NumberField.Units.logEmbedding K) (Additive.ofMul (u.toMul ^ S.index)) ∈
      logSubgroup S := Submodule.mem_map.mpr
    ⟨Additive.ofMul (u.toMul ^ S.index), S.pow_index_mem u.toMul, rfl⟩
  have hmul : (S.index : ℝ) • (NumberField.Units.logEmbedding K) u =
      (NumberField.Units.logEmbedding K) (Additive.ofMul (u.toMul ^ S.index)) := by
    rw [Nat.cast_smul_eq_nsmul ℝ, ← map_nsmul]
    rfl
  have hmem := Submodule.smul_mem
    (Submodule.span ℝ (logSubgroup S : Set (NumberField.Units.dirichletUnitTheorem.logSpace K))) (S.index : ℝ)⁻¹
    (Submodule.subset_span hu)
  rw [← hmul, smul_smul, inv_mul_cancel₀ (by exact_mod_cast (Subgroup.FiniteIndex.index_ne_zero (H := S))), one_smul] at hmem
  exact hmem

instance logSubgroup_isZLattice {K : Type*} [Field K] [NumberField K]
    (S : Subgroup (𝓞 K)ˣ) [S.FiniteIndex] : IsZLattice ℝ (logSubgroup S) :=
  ⟨logSubgroup_span_eq_top S⟩

 

def realPlace {K : Type*} [Field K] (σ : K →+* ℝ) : NumberField.InfinitePlace K :=
  NumberField.InfinitePlace.mk (Complex.ofRealHom.comp σ)

@[simp] theorem realPlace_apply {K : Type*} [Field K] (σ : K →+* ℝ) (x : K) :
    realPlace σ x = |σ x| := by
  simp [realPlace, NumberField.InfinitePlace.apply, Real.norm_eq_abs]

lemma realPlace_injective {K : Type*} [Field K] : Function.Injective (realPlace (K := K)) := by
  intro σ τ h
  apply RingHom.ext
  intro x
  rcases NumberField.InfinitePlace.mk_eq_iff.mp h with h | h
  · exact Complex.ofReal_injective (RingHom.congr_fun h x)
  · have H := RingHom.congr_fun h x
    simpa [NumberField.ComplexEmbedding.conjugate] using H

lemma realPlace_surjective {K : Type*} [Field K] [NumberField.IsTotallyReal K] :
    Function.Surjective (realPlace (K := K)) := by
  intro w
  refine ⟨NumberField.InfinitePlace.embedding_of_isReal (NumberField.IsTotallyReal.isReal w), ?_⟩
  unfold realPlace
  rw [show Complex.ofRealHom.comp
      (NumberField.InfinitePlace.embedding_of_isReal (NumberField.IsTotallyReal.isReal w)) =
      w.embedding by ext x; simp]
  exact NumberField.InfinitePlace.mk_embedding w

 

def orderedRealPlaces {n : ℕ} {K : Type*} [Field K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings n K) : Fin n ≃ NumberField.InfinitePlace K :=
  σ.trans (Equiv.ofBijective realPlace ⟨realPlace_injective, realPlace_surjective⟩)

@[simp] lemma orderedRealPlaces_apply {n : ℕ} {K : Type*} [Field K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings n K) (i : Fin n) (x : K) :
    orderedRealPlaces σ i x = |σ i x| := realPlace_apply _ _

 

def zeroSumSubmodule (ι : Type*) [Fintype ι] : Submodule ℝ (ι → ℝ) :=
  { carrier := {u | ∑ i, u i = 0}
    zero_mem' := by simp
    add_mem' := by intro u v hu hv; simp_all [Finset.sum_add_distrib]
    smul_mem' := by
      intro c u hu
      change ∑ i, c * u i = 0
      rw [← Finset.mul_sum, hu, mul_zero]}

@[simp] lemma mem_zeroSumSubmodule {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    u ∈ zeroSumSubmodule ι ↔ ∑ i, u i = 0 := Iff.rfl

 

def insertDeleted {ι : Type*} [Fintype ι] (i₀ : ι) :
    ({i : ι // i ≠ i₀} → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun u i := if h : i = i₀ then -∑ j, u j else u ⟨i, h⟩
  map_add' u v := by ext i; dsimp; split_ifs <;> simp [Finset.sum_add_distrib, add_comm]
  map_smul' c u := by ext i; dsimp; split_ifs <;> simp [Finset.mul_sum]

@[simp] lemma insertDeleted_self {ι : Type*} [Fintype ι] (i₀ : ι)
    (u : {i : ι // i ≠ i₀} → ℝ) : insertDeleted i₀ u i₀ = -∑ j, u j := by
  simp [insertDeleted]

@[simp] lemma insertDeleted_ne {ι : Type*} [Fintype ι] (i₀ : ι)
    (u : {i : ι // i ≠ i₀} → ℝ) (i : {i : ι // i ≠ i₀}) :
    insertDeleted i₀ u i = u i := by simp [insertDeleted, i.property]

lemma insertDeleted_sum {ι : Type*} [Fintype ι] (i₀ : ι)
    (u : {i : ι // i ≠ i₀} → ℝ) : ∑ i, insertDeleted i₀ u i = 0 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀]
  simp

 

def deletedCoordinatesEquiv {ι : Type*} [Fintype ι] (i₀ : ι) :
    ({i : ι // i ≠ i₀} → ℝ) ≃ₗ[ℝ] zeroSumSubmodule ι where
  toFun u := ⟨insertDeleted i₀ u, insertDeleted_sum i₀ u⟩
  invFun u i := u.1 i
  left_inv u := by ext i; simp
  right_inv u := by
    apply Subtype.ext
    funext i
    by_cases hi : i = i₀
    · subst i
      have h := u.property
      change ∑ i, u.1 i = 0 at h
      rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀] at h
      simp only [insertDeleted_self]
      linarith
    · exact insertDeleted_ne i₀ _ ⟨i, hi⟩
  map_add' u v := by apply Subtype.ext; exact map_add (insertDeleted i₀) u v
  map_smul' c u := by apply Subtype.ext; exact map_smul (insertDeleted i₀) c u

 

def zeroSumReindex {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    zeroSumSubmodule κ ≃ₗ[ℝ] zeroSumSubmodule ι where
  toFun u := ⟨fun i => u.1 (e i), by
    change ∑ i, u.1 (e i) = 0
    rw [Equiv.sum_comp e]
    exact u.property⟩
  invFun u := ⟨fun i => u.1 (e.symm i), by
    change ∑ i, u.1 (e.symm i) = 0
    rw [Equiv.sum_comp e.symm]
    exact u.property⟩
  left_inv u := by ext i; simp
  right_inv u := by ext i; simp
  map_add' u v := rfl
  map_smul' c u := rfl

 

def changeDeletedCoordinates {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (i₀ : ι) (j₀ : κ) :
    ({j : κ // j ≠ j₀} → ℝ) ≃ₗ[ℝ] ({i : ι // i ≠ i₀} → ℝ) :=
  ((deletedCoordinatesEquiv j₀).trans (zeroSumReindex e)).trans (deletedCoordinatesEquiv i₀).symm

@[simp] theorem changeDeletedCoordinates_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (i₀ : ι) (j₀ : κ) (u : {j : κ // j ≠ j₀} → ℝ)
    (i : {i : ι // i ≠ i₀}) :
    changeDeletedCoordinates e i₀ j₀ u i = insertDeleted j₀ u (e i) := rfl

 

def orderedLogCoordinatesEquiv {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d + 1) K) :
    NumberField.Units.dirichletUnitTheorem.logSpace K ≃ₗ[ℝ] (Fin d → ℝ) :=
  (changeDeletedCoordinates (orderedRealPlaces σ) (Fin.last d)
    NumberField.Units.dirichletUnitTheorem.w₀).trans
    (LinearEquiv.funCongrLeft ℝ ℝ (finSuccAboveEquiv (Fin.last d)))

lemma insertDeleted_logEmbedding {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (u : (𝓞 K)ˣ) (w : NumberField.InfinitePlace K) :
    insertDeleted NumberField.Units.dirichletUnitTheorem.w₀
      (NumberField.Units.logEmbedding K (Additive.ofMul u)) w = Real.log (w (u : K)) := by
  by_cases hw : w = NumberField.Units.dirichletUnitTheorem.w₀
  · subst w
    rw [insertDeleted_self, NumberField.Units.dirichletUnitTheorem.sum_logEmbedding_component]
    rw [(NumberField.IsTotallyReal.isReal _).mult_eq_one]
    simp
  · rw [show w = (⟨w, hw⟩ : {w : NumberField.InfinitePlace K //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}).val from rfl,
      insertDeleted_ne]
    rw [NumberField.Units.dirichletUnitTheorem.logEmbedding_component,
      (NumberField.IsTotallyReal.isReal _).mult_eq_one]
    simp

 

def orderedUnitLog {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d + 1) K) :
    Additive ((𝓞 K)ˣ) →+ (Fin d → ℝ) :=
  (orderedLogCoordinatesEquiv σ).toAddMonoidHom.comp (NumberField.Units.logEmbedding K)

@[simp] lemma orderedUnitLog_apply {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d + 1) K) (u : (𝓞 K)ˣ) (i : Fin d) :
    orderedUnitLog σ (Additive.ofMul u) i = Real.log |σ i.castSucc (u : K)| := by
  change insertDeleted NumberField.Units.dirichletUnitTheorem.w₀
    (NumberField.Units.logEmbedding K (Additive.ofMul u))
    (orderedRealPlaces σ ((finSuccAboveEquiv (Fin.last d) i).val)) = _
  simp only [insertDeleted_logEmbedding, finSuccAboveEquiv_apply, Fin.succAbove_last,
    orderedRealPlaces_apply]

 

def orderedLogSubgroup {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d + 1) K)
    (S : Subgroup (𝓞 K)ˣ) : Submodule ℤ (Fin d → ℝ) :=
  ZLattice.comap ℝ (logSubgroup S) (orderedLogCoordinatesEquiv σ).symm.toLinearMap

instance orderedLogSubgroup_discrete {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d + 1) K)
    (S : Subgroup (𝓞 K)ˣ) : DiscreteTopology (orderedLogSubgroup σ S) :=
  ZLattice.comap_discreteTopology ℝ (logSubgroup S)
    (orderedLogCoordinatesEquiv σ).symm.toContinuousLinearEquiv.continuous
    (orderedLogCoordinatesEquiv σ).symm.injective

instance orderedLogSubgroup_isZLattice {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d + 1) K)
    (S : Subgroup (𝓞 K)ˣ) [S.FiniteIndex] : IsZLattice ℝ (orderedLogSubgroup σ S) := by
  change IsZLattice ℝ (ZLattice.comap ℝ (logSubgroup S)
    (orderedLogCoordinatesEquiv σ).symm.toContinuousLinearEquiv.toLinearMap)
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)



lemma rowLattice_int_mul_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (g : Matrix (Fin n) (Fin n) ℝ) : rowLattice ((A.map (Int.castRingHom ℝ)) * g) ≤ rowLattice g := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have h : (fun j => ((A.map (Int.castRingHom ℝ)) * g) i j) = ∑ k, (A i k) • g k := by
    funext j
    simp [Matrix.mul_apply, Matrix.map_apply, Finset.sum_apply, zsmul_eq_mul]
  change (fun j => ((A.map (Int.castRingHom ℝ)) * g) i j) ∈ rowLattice g
  rw [h]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

 

lemma rowLattice_integral_mul {n : ℕ} (A : Matrix.SpecialLinearGroup (Fin n) ℤ)
    (g : G n) : rowLattice ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A * g).1) =
      rowLattice g.1 := by
  apply le_antisymm
  · exact rowLattice_int_mul_le A.1 g.1
  · have h := rowLattice_int_mul_le A⁻¹.1
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A * g).1
    change rowLattice ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A⁻¹ *
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A * g)).1) ≤ _ at h
    simpa using h



lemma continuous_rightAction {n : ℕ} (g : G n) :
    Continuous (fun x : X n => rightAction x g) := by
  apply continuous_quot_lift
  exact continuous_quotient_mk'.comp (continuous_id.mul continuous_const)

open scoped Pointwise



open FractionalIdeal



def classRepresentative (K : Type*) [Field K] [NumberField K]
    (c : ClassGroup (𝓞 K)) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Classical.choose (show ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ClassGroup.mk K I = c from
    ClassGroup.induction K (fun I => ⟨I, rfl⟩) c)



lemma locallyHomothetic_scale {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (a : Kˣ) : LocallyHomothetic M (scaleFullLattice M a) := by
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨Units.map (Algebra.TensorProduct.includeRight (R := ℚ) (A := Padic p)).toMonoidHom a, ?_⟩
  rw [completedLattice_scale]
  rfl

lemma locallyHomothetic_trans {n : ℕ} {K : Type*} [Field K] [NumberField K]
    {M N P : FullLattice n K} (hMN : LocallyHomothetic M N) (hNP : LocallyHomothetic N P) :
    LocallyHomothetic M P := by
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hMN p hp
  obtain ⟨b, hb⟩ := hNP p hp
  refine ⟨b * a, ?_⟩
  rw [hb, ha, Set.image_image]
  congr 1
  ext x
  exact (mul_assoc _ _ _).symm

lemma saturationFractionalIdeal_scale {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (a : Kˣ) :
    saturationFractionalIdeal (scaleFullLattice M a) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) * saturationFractionalIdeal M := by
  apply FractionalIdeal.coeToSubmodule_injective
  dsimp only
  rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton, Submodule.span_singleton_mul]
  change Submodule.span (𝓞 K) (((scaleFullLattice M a).carrier : Set K)) =
    (a : K) • Submodule.span (𝓞 K) (M.carrier : Set K)
  rw [scaleFullLattice_carrier]
  change Submodule.span (𝓞 K) ((LinearMap.mulLeft (𝓞 K) (a : K)) '' (M.carrier : Set K)) = _
  rw [← Submodule.map_span]
  rfl



lemma spanSingleton_maximalOrder_unit {K : Type*} [Field K] [NumberField K]
    (u : (𝓞 K)ˣ) : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u : 𝓞 K) : K) = 1 := by
  rw [← FractionalIdeal.spanSingleton_one, FractionalIdeal.spanSingleton_eq_spanSingleton]
  exact ⟨u⁻¹,by simp [Units.smul_def,Algebra.smul_def]⟩

lemma scaleFullLattice_unit_carrier {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (N : FullLattice n K) (u : (𝓞 K)ˣ) :
    (scaleFullLattice N (Units.map (algebraMap (𝓞 K) K).toMonoidHom u)).carrier =
      u • N.carrier := by
  rw [Units.smul_def, Submodule.pointwise_smul_def]
  rfl

lemma globalLabels_unit_smul_mem {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (N : globalLabels M I) (u : (𝓞 K)ˣ) : u • N.val ∈ globalLabels M I := by
  let A := globalLabelLattice M I N
  refine ⟨scaleFullLattice A (Units.map (algebraMap (𝓞 K) K).toMonoidHom u),?_,?_,?_⟩
  · rw [scaleFullLattice_unit_carrier,(globalLabelLattice_spec M I N).1]
  · exact locallyHomothetic_trans (globalLabelLattice_spec M I N).2.1
      (locallyHomothetic_scale A _)
  · rw [saturationFractionalIdeal_scale]
    change FractionalIdeal.spanSingleton (𝓞 K)⁰ ((u : 𝓞 K) : K) * saturationFractionalIdeal A = _
    rw [spanSingleton_maximalOrder_unit,one_mul]
    exact (globalLabelLattice_spec M I N).2.2

instance globalLabelsMulAction {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    MulAction (𝓞 K)ˣ (globalLabels M I) where
  smul u N := ⟨u • N.val,globalLabels_unit_smul_mem M I N u⟩
  one_smul N := by apply Subtype.ext; exact one_smul _ _
  mul_smul u v N := by apply Subtype.ext; exact mul_smul _ _ _

@[simp] lemma globalLabels_smul_val {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (u : (𝓞 K)ˣ) (N : globalLabels M I) : (u • N).val = u • N.val := rfl

def signValue : SignTypeˣ →* ℝ :=
  (SignType.castHom : SignType →*₀ ℝ).toMonoidHom.comp (Units.coeHom SignType)

@[simp] lemma signValue_apply (w : SignTypeˣ) : signValue w = ((w : SignType) : ℝ) := rfl


structure SignedGlobalLabel {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) where
  lattice : globalLabels M I
  signs : Fin n → SignTypeˣ

@[ext] lemma SignedGlobalLabel.ext {n : ℕ} {K : Type*} [Field K] [NumberField K]
    {M : FullLattice n K} {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    {x y : SignedGlobalLabel M I} (hN : x.lattice = y.lattice) (hw : x.signs = y.signs) : x = y := by
  cases x; cases y; cases hN; cases hw; rfl

@[instance_reducible] def signedGlobalLabelMulAction {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : MulAction (𝓞 K)ˣ (SignedGlobalLabel M I) where
  smul u x := ⟨u • x.lattice, (unitSigns σ u)⁻¹ * x.signs⟩
  one_smul x := by
    apply SignedGlobalLabel.ext
    · change (1 : (𝓞 K)ˣ) • x.lattice = x.lattice
      exact one_smul _ _
    · change (unitSigns σ 1)⁻¹ * x.signs = x.signs
      simp
  mul_smul u v x := by
    apply SignedGlobalLabel.ext
    · change (u*v) • x.lattice = u • v • x.lattice
      exact mul_smul _ _ _
    · change (unitSigns σ (u*v))⁻¹ * x.signs =
        (unitSigns σ u)⁻¹ * ((unitSigns σ v)⁻¹ * x.signs)
      simp only [map_mul, mul_inv_rev, mul_assoc, mul_left_comm]



abbrev AllSignedGlobalLabel {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) :=
  Σ c : ClassGroup (𝓞 K), SignedGlobalLabel M (classRepresentative K c)

@[instance_reducible] def allSignedGlobalLabelMulAction {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) : MulAction (𝓞 K)ˣ (AllSignedGlobalLabel M) := by
  letI (c : ClassGroup (𝓞 K)) := signedGlobalLabelMulAction M σ (classRepresentative K c)
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def inverseQuotientHomeomorph (n : ℕ) : X n ≃ₜ (G n ⧸ integralGroup n) where
  toEquiv := QuotientGroup.quotientRightRelEquivQuotientLeftRel (integralGroup n)
  continuous_toFun := by
    apply continuous_quot_lift
    exact continuous_quotient_mk'.comp continuous_inv
  continuous_invFun := by
    apply continuous_quot_lift
    exact continuous_quotient_mk'.comp continuous_inv

instance integralGroup_discrete (n : ℕ) : DiscreteTopology (integralGroup n) := by
  unfold integralGroup
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance matrixSecondCountable (n : ℕ) :
    SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℝ))

instance gSecondCountable (n : ℕ) : SecondCountableTopology (G n) :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.secondCountableTopology

instance xT2Space (n : ℕ) : T2Space (X n) :=
  (inverseQuotientHomeomorph n).symm.t2Space



def integerRowMap {n : ℕ} (g : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℝ) where
  toFun z := ∑ i, z i • g i
  map_add' z w := by simp [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' a z := by
    simp only [RingHom.id_apply,Pi.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul]

lemma integerRowMap_apply {n : ℕ} (g : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℤ) :
    integerRowMap g z = Matrix.vecMul (fun i => (z i : ℝ)) g := by
  ext i
  simp [integerRowMap,Matrix.vecMul,dotProduct,Finset.sum_apply,zsmul_eq_mul]

lemma integerRowMap_range {n : ℕ} (g : Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.range (integerRowMap g) = rowLattice g := by
  apply le_antisymm
  · rintro x ⟨z,rfl⟩
    change (∑ i, z i • g i) ∈ Submodule.span ℤ (Set.range fun i => g i)
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i,rfl⟩))
  · apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    refine ⟨Pi.single i 1,?_⟩
    change (∑ x : Fin n, ((Pi.single i (1:ℤ) : Fin n → ℤ) x) • g x) = g i
    simp only [Pi.single_apply,ite_smul,one_smul,zero_smul]
    simpa only [Finset.mem_univ,ite_true, if_true] using Finset.sum_ite_eq' Finset.univ i g

lemma integerRowMap_injective {n : ℕ} (g : G n) :
    Function.Injective (integerRowMap g.1) := by
  intro z w h
  simp only [integerRowMap_apply] at h
  have hunit : IsUnit g.1 := by
    apply (Matrix.isUnit_iff_isUnit_det g.1).mpr
    rw [g.property]
    exact isUnit_one
  have H := Matrix.vecMul_injective_of_isUnit hunit h
  exact funext (fun i => Int.cast_injective (congrFun H i))

 

def integerRowEquiv {n : ℕ} (g : G n) : (Fin n → ℤ) ≃ₗ[ℤ] rowLattice g.1 :=
  (LinearEquiv.ofInjective (integerRowMap g.1) (integerRowMap_injective g)).trans
    (LinearEquiv.ofEq _ _ (integerRowMap_range g.1))

@[simp] lemma integerRowEquiv_val {n : ℕ} (g : G n) (z : Fin n → ℤ) :
    (integerRowEquiv g z : Fin n → ℝ) = integerRowMap g.1 z := rfl



def pointLattice {n : ℕ} : X n → Submodule ℤ (Fin n → ℝ) :=
  Quotient.lift (fun g : G n => rowLattice g.1) (by
    intro g h hgh
    have H := QuotientGroup.rightRel_apply.mp hgh
    obtain ⟨A,hA⟩ := H
    have hh : h = Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A * g := by
      rw [hA, inv_mul_cancel_right]
    rw [hh]
    exact (rowLattice_integral_mul A g).symm)

@[simp] lemma pointLattice_mk {n : ℕ} (g : G n) :
    pointLattice (Quotient.mk _ g : X n) = rowLattice g.1 := rfl



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketMoments
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

def rightActionHomeomorph {n : ℕ} (g : G n) : X n ≃ₜ X n where
  toFun x := rightAction x g
  invFun x := rightAction x g⁻¹
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := continuous_rightAction g
  continuous_invFun := continuous_rightAction g⁻¹



theorem quotient_covering (n : ℕ) :
    IsCoveringMap (Quotient.mk (QuotientGroup.rightRel (integralGroup n))) := by
  exact (isQuotientMap_quotient_mk'.isQuotientCoveringMap_of_subgroup
    (integralGroup n) (isDiscrete_iff_discreteTopology.mpr (by
      change DiscreteTopology (integralGroup n)
      infer_instance))
    (by intro a b; exact Quotient.eq''.trans QuotientGroup.rightRel_apply)).isCoveringMap

 

def matrixBall (n : ℕ) (r : ℝ) : Set (G n) :=
  {h | ∀ i j, |h.1 i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j| < r}

open scoped Matrix
open Matrix

def rowBasis {n : ℕ} (g : G n) : Basis (Fin n) ℝ (Fin n → ℝ) :=
  (Pi.basisFun ℝ (Fin n)).map (Matrix.SpecialLinearGroup.toLin' g.transpose)

@[simp] lemma rowBasis_apply {n : ℕ} (g : G n) (i j : Fin n) :
    rowBasis g i j = g.1 i j := by
  simp [rowBasis,Matrix.SpecialLinearGroup.toLin'_apply,Matrix.toLin'_apply,
    Matrix.mulVec,dotProduct,Matrix.SpecialLinearGroup.coe_transpose,
    Matrix.transpose_apply,Pi.single_apply]

def euclideanRowBasis {n : ℕ} (g : G n) :
    Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  (rowBasis g).map (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toLinearEquiv

@[simp] lemma euclideanRowBasis_apply {n : ℕ} (g : G n) (i j : Fin n) :
    (euclideanRowBasis g i).ofLp j = g.1 i j := by
  simp [euclideanRowBasis]

open TopologicalSpace
open scoped Topology

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_CyclicInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cyclic subgroup coefficients for Stark descent

Möbius inversion on the finite poset of cyclic subgroups expresses the
constant function as an integer combination of their indicators.
Averaging conjugates gives the denominator-cleared cyclic permutation
identity used to compare Dedekind zeta orders.
-/

open scoped BigOperators Classical

namespace DukePrimeDegree

/-- The finite set of cyclic subgroups, retaining their actual subgroup
carrier. No choice of generators enters the coefficients. -/
abbrev CyclicSubgroups (G : Type*) [Group G] :=
  {H : Subgroup G // IsCyclic H}

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_FullLattice
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Full lattices in number fields

A full lattice is a finitely generated integer submodule spanning the
number field over the rationals. In a characteristic-zero field it is
free; the span condition forces its rank to be the field degree.
-/

namespace DukePrimeDegree

open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The lattice data appearing in Theorem 1.1, before choosing an ordering
of the real embeddings. -/
structure FullLattice where
  toSubmodule : Submodule ℤ K
  fg : toSubmodule.FG
  span_eq_top : Submodule.span ℚ (toSubmodule : Set K) = ⊤

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_LatticeBasis
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bases of full lattices

The finitely generated, rationally spanning submodules used in
`FullLattice` are free of rank equal to the field degree. Their integer
bases become rational bases without changing the underlying vectors.
-/

namespace DukePrimeDegree

variable {K : Type*} [Field K] [NumberField K]

/-- An integer basis of a full lattice is a rational basis of the field. -/
noncomputable def FullLattice.rationalBasis {ι : Type*} (M : FullLattice K)
    (b : Module.Basis ι ℤ M.toSubmodule) : Module.Basis ι ℚ K := by
  have hlin : LinearIndependent ℤ (fun i => (b i : K)) :=
    b.linearIndependent.map' M.toSubmodule.subtype (Submodule.ker_subtype _)
  have hlinQ : LinearIndependent ℚ (fun i => (b i : K)) :=
    hlin.localization ℚ (nonZeroDivisors ℤ)
  have hz : Submodule.span ℤ (Set.range fun i => (b i : K)) = M.toSubmodule := by
    rw [show (Set.range fun i => (b i : K)) =
      M.toSubmodule.subtype '' Set.range b by ext; simp]
    rw [← Submodule.map_span, b.span_eq]
    simp
  have hspan : Submodule.span ℚ (Set.range fun i => (b i : K)) = ⊤ := by
    rw [← Submodule.span_span_of_tower (R := ℤ), hz]
    exact M.span_eq_top
  exact Module.Basis.mk hlinQ hspan.ge

@[simp] lemma FullLattice.rationalBasis_apply {ι : Type*} (M : FullLattice K)
    (b : Module.Basis ι ℤ M.toSubmodule) (i : ι) :
    M.rationalBasis b i = (b i : K) := by
  simp [FullLattice.rationalBasis]

/-- The rank in the manuscript's definition follows from finite generation
and rational spanning; it is not an extra hypothesis. -/
lemma FullLattice.finrank (M : FullLattice K) :
    Module.finrank ℤ M.toSubmodule = Module.finrank ℚ K := by
  let : Module.Finite ℤ M.toSubmodule := Module.Finite.iff_fg.mpr M.fg
  let b := Module.finBasis ℤ M.toSubmodule
  simpa using (Module.finrank_eq_card_basis (M.rationalBasis b)).symm

/-- A full lattice has an integer basis indexed by the degree of the field. -/
noncomputable def FullLattice.integralBasis (M : FullLattice K) :
    Module.Basis (Fin (Module.finrank ℚ K)) ℤ M.toSubmodule := by
  let : Module.Finite ℤ M.toSubmodule := Module.Finite.iff_fg.mpr M.fg
  exact (Module.finBasis ℤ M.toSubmodule).reindex (finCongr M.finrank)

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_EmbeddingMatrix
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ordered real embeddings and lattice basis matrices

An ordering of the complex embeddings of a totally real field gives the
ordered real embeddings used in the manuscript. The matrix of any full
lattice basis under these embeddings has nonzero determinant.
-/

namespace DukePrimeDegree

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
  {n : ℕ}

/-- An ordering of all embeddings; total reality makes their values real. -/
abbrev EmbeddingOrder (K : Type*) [Field K] [NumberField K] (n : ℕ) :=
  Fin n ≃ (K →ₐ[ℚ] ℂ)

/-- The real ring embedding at one place of the ordering. -/
noncomputable def orderedRealEmbedding (σ : EmbeddingOrder K n) (j : Fin n) : K →+* ℝ :=
  (NumberField.IsTotallyReal.complexEmbedding_isReal (σ j).toRingHom).embedding

@[simp] lemma orderedRealEmbedding_complex (σ : EmbeddingOrder K n)
    (j : Fin n) (x : K) : (orderedRealEmbedding σ j x : ℂ) = σ j x :=
  NumberField.ComplexEmbedding.IsReal.coe_embedding_apply _ _

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_PacketBridge
attribute [-instance] _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.orderedLogSubgroup_discrete _root_.OAI.PrimeDegreePackets.orderedLogSubgroup_isZLattice
attribute [-simp] _root_.OAI.PrimeDegreePackets.globalLabels_smul_val _root_.OAI.PrimeDegreePackets.orderedRealPlaces_apply _root_.OAI.PrimeDegreePackets.orderedUnitLog_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Full lattices in the existing packet model

The packet development records a chosen integer basis in its full-lattice
structure. Our finite-generation definition produces that basis. This
conversion preserves the actual submodule and multiplier order.
-/

namespace DukePrimeDegree

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

/-- Equip a full lattice with the basis expected by the packet model. -/
noncomputable def FullLattice.toPacket (M : FullLattice K)
    (hn : Module.finrank ℚ K = n) : PrimeDegreePackets.FullLattice n K where
  carrier := M.toSubmodule
  basis := M.integralBasis.reindex (finCongr hn)
  spans := M.span_eq_top

@[simp] lemma FullLattice.toPacket_carrier (M : FullLattice K)
    (hn : Module.finrank ℚ K = n) : (M.toPacket hn).carrier = M.toSubmodule := rfl

/-- Convert the complex-embedding ordering to the real-embedding ordering
used by the row-lattice packet model. Total reality makes this bijective. -/
noncomputable def EmbeddingOrder.toRealOrder [NumberField.IsTotallyReal K]
    (σ : EmbeddingOrder K n) : PrimeDegreePackets.OrderedEmbeddings n K :=
  Equiv.ofBijective (orderedRealEmbedding σ) (by
    constructor
    · intro i j hij
      apply σ.injective
      apply AlgHom.ext
      intro x
      have h := congrArg (fun f : K →+* ℝ => (f x : ℂ)) hij
      simpa only [orderedRealEmbedding_complex] using h
    · intro τ
      let τc : K →ₐ[ℚ] ℂ := (Complex.ofRealHom.comp τ).toRatAlgHom
      obtain ⟨i, hi⟩ := σ.surjective τc
      refine ⟨i, ?_⟩
      ext x
      apply Complex.ofReal_injective
      rw [orderedRealEmbedding_complex, hi]
      rfl)

@[simp] lemma EmbeddingOrder.toRealOrder_apply [NumberField.IsTotallyReal K]
    (σ : EmbeddingOrder K n) (i : Fin n) : σ.toRealOrder i = orderedRealEmbedding σ i := rfl

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealNorms
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
namespace PrimeDegreePackets

def diagonalOneParameter {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (t : ℝ) : G n :=
  ⟨Matrix.diagonal (fun i => Real.exp (ell i * t)), by
    rw [Matrix.det_diagonal, ← Real.exp_sum, ← Finset.sum_mul, hell, zero_mul,
      Real.exp_zero]⟩



lemma conjugation_entry {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (h : G n) (t : ℝ) (i j : Fin n) :
    (diagonalOneParameter ell hell t * h * diagonalOneParameter ell hell (-t)).1 i j =
      Real.exp ((ell i - ell j) * t) * h.1 i j := by
  change (Matrix.diagonal (fun i => Real.exp (ell i * t)) * h.1 *
    Matrix.diagonal (fun i => Real.exp (ell i * (-t)))) i j = _
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [mul_assoc, mul_comm (h.1 i j), ← mul_assoc, ← Real.exp_add]
  congr 2
  ring



lemma continuous_rightAction_uncurry (n : ℕ) :
    Continuous (fun p : X n × G n => rightAction p.1 p.2) := by
  have hq : IsOpenQuotientMap (Quotient.mk (QuotientGroup.rightRel (integralGroup n))) :=
    ⟨Quotient.mk_surjective, continuous_quotient_mk', (quotient_covering n).isOpenMap⟩
  apply (hq.prodMap IsOpenQuotientMap.id).isQuotientMap.continuous_iff.mpr
  exact continuous_quotient_mk'.comp (continuous_fst.mul continuous_snd)



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ShannonEntropy
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
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
namespace PrimeDegreePackets

 
def finiteShannon {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ a, Real.negMulLog (p a)


def observationEntropy {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) (P : Y → α) : ℝ :=
  finiteShannon (fun a => μ.real {y | P y = a})

end PrimeDegreePackets

open scoped BigOperators Topology ENNReal
namespace PrimeDegreePackets


def orbitName {Y α : Type*} (T : Y → Y) (P : Y → α) (N : ℕ) (y : Y) : Fin N → α :=
  fun j => P (T^[j] y)



def observationEntropyRate {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) (T : Y → Y) (P : Y → α) : ℝ :=
  sInf ((fun N : ℕ => observationEntropy μ (orbitName T P N)/(N:ℝ)) '' Set.Ici 1)



def measureEntropy {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (T : Y → Y) : ℝ≥0∞ :=
  ⨆ k : ℕ, ⨆ P : Y → Fin k, ⨆ (_hP : ∀ a, MeasurableSet {y | P y = a}),
    ENNReal.ofReal (observationEntropyRate μ T P)

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ObservationCovers
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
namespace PrimeDegreePackets



lemma diagonalOneParameter_zero {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) :
    diagonalOneParameter ell hell 0 = 1 := by
  apply Subtype.ext
  ext i j
  simp [diagonalOneParameter]

lemma diagonalOneParameter_add {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (s t : ℝ) : diagonalOneParameter ell hell (s+t) =
      diagonalOneParameter ell hell s * diagonalOneParameter ell hell t := by
  apply Subtype.ext
  change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [mul_add,Real.exp_add]

lemma diagonalOneParameter_neg {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (t : ℝ) : diagonalOneParameter ell hell (-t) = (diagonalOneParameter ell hell t)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← diagonalOneParameter_add,neg_add_cancel,diagonalOneParameter_zero]

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_AtomMass
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


namespace PrimeDegreePackets

 
def regularDiagonalWeights (d : ℕ) (i : Fin (d+1)) : ℝ :=
  (i.val:ℝ) - (∑ j : Fin (d+1), (j.val:ℝ))/(d+1)

lemma regularDiagonalWeights_sum (d : ℕ) : ∑ i, regularDiagonalWeights d i = 0 := by
  simp only [regularDiagonalWeights, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [mul_div_cancel₀ _ (show (d:ℝ)+1 ≠ 0 by positivity), sub_self]

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ErgodicDecomposition
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


namespace PrimeDegreePackets


instance diagonalLogAction (d : ℕ) : MulAction (Multiplicative (LogCoordinates d)) (X (d+1)) where
  smul u x := rightAction x (diagonalFlow u.toAdd)
  one_smul x := by
    change rightAction x (diagonalFlow 0) = x
    rw [diagonalFlow_zero,rightAction_one]
  mul_smul u v x := by
    change rightAction x (diagonalFlow (u.toAdd + v.toAdd)) =
      rightAction (rightAction x (diagonalFlow v.toAdd)) (diagonalFlow u.toAdd)
    rw [rightAction_mul,←diagonalFlow_add,add_comm u.toAdd v.toAdd]

end PrimeDegreePackets


open scoped ENNReal Topology
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootSubgroups
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

lemma diagonal_conjugation_transvection {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) {i j : Fin n} (hij : i ≠ j) (a t : ℝ) :
    diagonalOneParameter ell hell t * Matrix.SpecialLinearGroup.transvection hij a *
      diagonalOneParameter ell hell (-t) =
      Matrix.SpecialLinearGroup.transvection hij (Real.exp ((ell i-ell j)*t)*a) := by
  ext r s
  rw [conjugation_entry]
  simp only [Matrix.SpecialLinearGroup.transvection_coe,Matrix.add_apply]
  by_cases hrs : r = s <;> by_cases hri : r = i <;> by_cases hsj : s = j
  all_goals simp_all [Matrix.single_apply,Matrix.one_apply,eq_comm]

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootRelations
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


def orbitQuotientMap {d : ℕ} (x : X (d+1)) :
    LogCoordinates d ⧸ (periodGroup x).toIntSubmodule.toAddSubgroup → X (d+1) :=
  Quotient.lift (orbitMap x) (by
    intro u v huv
    have hp : v-u ∈ periodGroup x := by
      have H := QuotientAddGroup.leftRel_apply.mp huv
      simpa only [sub_eq_neg_add,AddSubgroup.toIntSubmodule_toAddSubgroup] using H
    have H := orbitMap_add x (v-u) u
    rw [show orbitMap x (v-u) = x from hp] at H
    simpa using H.symm)

@[simp] lemma orbitQuotientMap_mk {d : ℕ} (x : X (d+1)) (u : LogCoordinates d) :
    orbitQuotientMap x (QuotientAddGroup.mk u) = orbitMap x u := rfl

end PrimeDegreePackets

open scoped Topology Classical ENNReal

open scoped Matrix Topology Classical
namespace PrimeDegreePackets

lemma continuous_rootTransvection {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Continuous (fun t : ℝ => Matrix.SpecialLinearGroup.transvection hij t) := by
  apply Continuous.subtype_mk
  change Continuous (fun t : ℝ => (1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.single i j t)
  apply continuous_const.add
  apply continuous_pi
  intro r
  apply continuous_pi
  intro s
  simp only [Matrix.single_apply]
  split_ifs <;> fun_prop

lemma root_mul_entry {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (r s : Fin n) (t : ℝ) :
    (g * Matrix.SpecialLinearGroup.transvection hij t).1 r s =
      g.1 r s + if s = j then g.1 r i * t else 0 := by
  change (g.1 * Matrix.transvection i j t) r s = _
  by_cases h : s = j
  · subst s
    simp [Matrix.mul_transvection_apply_same,mul_comm]
  · simp [Matrix.mul_transvection_apply_of_ne,h]

 
abbrev RootPivot {n : ℕ} (i k : Fin n) := {g : G n // g.1 k i ≠ 0}

 
abbrev RootSlice {n : ℕ} (i j k : Fin n) := {g : G n // g.1 k i ≠ 0 ∧ g.1 k j = 0}

def rootParameter {n : ℕ} (i j k : Fin n) (g : G n) : ℝ := g.1 k j / g.1 k i

lemma continuous_rootParameter {n : ℕ} {i j k : Fin n} :
    Continuous (fun g : RootPivot i k => rootParameter i j k g.val) := by
  have hc : Continuous (fun g : RootPivot i k => (g.val : Matrix (Fin n) (Fin n) ℝ)) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous.comp continuous_subtype_val
  unfold rootParameter
  apply Continuous.div
  · exact (continuous_apply j).comp ((continuous_apply k).comp hc)
  · exact (continuous_apply i).comp ((continuous_apply k).comp hc)
  · exact fun g => g.prop

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootCharts
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

instance rootGroupMeasurableSpace (n : ℕ) : MeasurableSpace (G n) := borel (G n)
instance rootGroupBorelSpace (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩

lemma rootPivot_isOpen {n : ℕ} (i k : Fin n) :
    IsOpen {g : G n | g.1 k i ≠ 0} := by
  have hc : Continuous (fun g : G n => g.1 k i) :=
    (continuous_apply i).comp ((continuous_apply k).comp
      Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous)
  exact isOpen_ne_fun hc continuous_const

lemma exists_rootPivot {n : ℕ} (i : Fin n) (g : G n) :
    ∃ k : Fin n, g.1 k i ≠ 0 := by
  by_contra h
  push Not at h
  have H := Matrix.det_eq_zero_of_column_eq_zero i h
  rw [g.prop] at H
  exact one_ne_zero H

end PrimeDegreePackets


open scoped ENNReal ProbabilityTheory
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_KernelScaling
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
namespace PrimeDegreePackets

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] [T2Space B]

lemma localHomeomorph_collision_free_isOpen {f : A → B} (hf : IsLocalHomeomorph f) :
    IsOpen {p : A × A | f p.1 ≠ f p.2 ∨ p.1 = p.2} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨x,y⟩ (hne | heq)
  · exact mem_of_superset
      ((isOpen_ne_fun (hf.continuous.comp continuous_fst)
        (hf.continuous.comp continuous_snd)).mem_nhds hne)
      (fun _ h => Or.inl h)
  · change x = y at heq
    subst y
    obtain ⟨U,hU,hemb⟩ := isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp hf x
    apply mem_of_superset (prod_mem_nhds hU hU)
    rintro ⟨a,b⟩ ⟨ha,hb⟩
    by_cases h : f a = f b
    · have H : (⟨a,ha⟩ : U) = ⟨b,hb⟩ := hemb.injective h
      exact Or.inr (congrArg Subtype.val H)
    · exact Or.inl h

 

theorem compact_injective_localHomeomorph_neighborhood {f : A → B}
    (hf : IsLocalHomeomorph f) {K : Set A} (hK : IsCompact K) (hi : Set.InjOn f K) :
    ∃ U : Set A, IsOpen U ∧ K ⊆ U ∧ Topology.IsOpenEmbedding (U.domRestrict f) := by
  have hc : K ×ˢ K ⊆ {p : A × A | f p.1 ≠ f p.2 ∨ p.1 = p.2} := by
    rintro ⟨a,b⟩ ⟨ha,hb⟩
    by_cases h : f a = f b
    · exact Or.inr (hi ha hb h)
    · exact Or.inl h
  obtain ⟨U,V,hU,hV,hKU,hKV,hUV⟩ := generalized_tube_lemma hK hK
    (localHomeomorph_collision_free_isOpen hf) hc
  refine ⟨U ∩ V,hU.inter hV,fun _ hx => ⟨hKU hx,hKV hx⟩,?_⟩
  apply (hf.comp (hU.inter hV).isOpenEmbedding_subtypeVal.isLocalHomeomorph).isOpenEmbedding_of_injective
  intro a b hab
  apply Subtype.ext
  have H := hUV (show (a.val,b.val) ∈ U ×ˢ V from ⟨a.prop.1,b.prop.2⟩)
  exact H.resolve_left (fun hne => hne hab)

end PrimeDegreePackets

open Set Filter Topology MeasureTheory

open MeasureTheory Set Filter Topology

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_XiBoundary
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


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

def integerVector (z : d → ℤ) : d → ℝ := fun i => z i

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_CoordinateLattices
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
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

@[simp] lemma schwartzCM_apply (f : 𝓢(d → ℝ,ℂ)) (x : d → ℝ) :
    f.toContinuousMap x = f x := rfl

end PrimeDegreePackets.ThetaConstruction

open scoped BigOperators FourierTransform
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

 

def adjointEquiv (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) :
    EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d where
  toLinearMap := B.toContinuousLinearMap.adjoint.toLinearMap
  invFun := B.symm.toContinuousLinearMap.adjoint
  left_inv x := by
    have H : B.toContinuousLinearMap.comp B.symm.toContinuousLinearMap =
        ContinuousLinearMap.id ℝ _ := by ext y i; simp
    have J := congrArg ContinuousLinearMap.adjoint H
    rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_id] at J
    exact congrArg (fun T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d => T x) J
  right_inv x := by
    have H : B.symm.toContinuousLinearMap.comp B.toContinuousLinearMap =
        ContinuousLinearMap.id ℝ _ := by ext y i; simp
    have J := congrArg ContinuousLinearMap.adjoint H
    rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_id] at J
    exact congrArg (fun T : EuclideanSpace ℝ d →L[ℝ] EuclideanSpace ℝ d => T x) J
  continuous_toFun := B.toContinuousLinearMap.adjoint.continuous
  continuous_invFun := B.symm.toContinuousLinearMap.adjoint.continuous

def euclideanInteger (z : d → ℤ) : EuclideanSpace ℝ d := toLp 2 (integerVector z)

end PrimeDegreePackets.ThetaConstruction

open MeasureTheory Set Filter Topology Module WithLp Asymptotics
namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

abbrev NonzeroIntegerVector (d : Type*) := {z : d → ℤ // z ≠ 0}

def thetaRemainder (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (t : ℝ) : ℂ :=
  ∑' z : NonzeroIntegerVector d, Complex.exp (-(t:ℂ) * ‖B (euclideanInteger z.1)‖^2)

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LatticeTheta
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
namespace PrimeDegreePackets
open ThetaConstruction
variable {n : ℕ} {K : Type*} [Field K] [NumberField K]

def fullLatticeEuclideanBasis (M : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : Module.finrank ℚ K = n) : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (Matrix.toLinearEquiv (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (embeddingMatrix M σ).transpose
    (isUnit_iff_ne_zero.mpr (by simpa only [Matrix.det_transpose] using embeddingMatrix_det_ne_zero M σ hn))).toContinuousLinearEquiv

end PrimeDegreePackets


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

def normalizedThetaTail (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) : ℝ → ℂ :=
  (Set.Ioi 1).indicator (fun t => thetaRemainder B (Real.pi*max t 1))



def thetaMellinXi (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d) (s : ℂ) : ℂ :=
  s*(s-(Fintype.card d:ℂ)/2) *
    (mellin (normalizedThetaTail B) s + ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
      mellin (normalizedThetaTail (adjointEquiv B.symm)) ((Fintype.card d:ℂ)/2-s)) +
    ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ)*s - (s-(Fintype.card d:ℂ)/2)

end PrimeDegreePackets.ThetaConstruction

open Module MeasureTheory
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ThetaTails
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


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

 
def logScaleLinearEquiv (u : d → ℝ) : EuclideanSpace ℝ d ≃ₗ[ℝ] EuclideanSpace ℝ d where
  toFun x := toLp 2 (fun i => Real.exp (u i)*x i)
  invFun x := toLp 2 (fun i => Real.exp (-u i)*x i)
  map_add' x y := by ext i; simp [mul_add]
  map_smul' a x := by ext i; simp [mul_left_comm]
  left_inv x := by
    ext i
    change Real.exp (-u i)*(Real.exp (u i)*x i) = x i
    rw [←mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul]
  right_inv x := by
    ext i
    change Real.exp (u i)*(Real.exp (-u i)*x i) = x i
    rw [←mul_assoc,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul]

def logScale (u : d → ℝ) : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d :=
  (logScaleLinearEquiv u).toContinuousLinearEquiv

@[simp] lemma logScale_apply (u : d → ℝ) (x : EuclideanSpace ℝ d) (i : d) :
    logScale u x i = Real.exp (u i)*x i := rfl

@[simp] lemma logScale_symm_apply (u : d → ℝ) (x : EuclideanSpace ℝ d) (i : d) :
    (logScale u).symm x i = Real.exp (-u i)*x i := rfl


def logScaledLattice (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (u : d → ℝ) := B.trans (logScale u)

end PrimeDegreePackets.ThetaConstruction


namespace PrimeDegreePackets
open ThetaConstruction

 
def restoredLogCoordinates {d : ℕ} (u : LogCoordinates d) : Fin (d+1) → ℝ :=
  Fin.snoc u (-∑ i, u i)



def orderedThetaLogDomain {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) : Set (LogCoordinates d) :=
  ZSpan.fundamentalDomain (Module.Basis.ofZLatticeBasis ℝ (orderedLogSubgroup σ ⊤)
    (Module.Free.chooseBasis ℤ (orderedLogSubgroup σ ⊤)))

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealThetaXi
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
namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

 
def idealThetaXi {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) : ℂ :=
  ∫ u in orderedThetaLogDomain σ,
    thetaMellinXi (logScaledLattice
      (fullLatticeEuclideanBasis (fractionalIdealFullLattice hn I) σ hn)
      (restoredLogCoordinates u)) (((d+1 : ℕ) : ℂ)*s/2)

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction


def classThetaXi {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (s : ℂ) : ℂ :=
  ∑ c : ClassGroup (𝓞 K),
    ((FractionalIdeal.absNorm (classRepresentative K c).val : ℝ) : ℂ)^s *
      idealThetaXi σ hn (classRepresentative K c) s

end PrimeDegreePackets.HeckeMellin

open Set


namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction



def completedThetaXi {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (s : ℂ) : ℂ :=
  ((2 : ℂ)^(d+1)/((d+1 : ℕ) : ℂ)) *
    Complex.exp (s*(Real.log |(NumberField.discr K : ℝ)| : ℂ)/2) * classThetaXi σ hn s

end PrimeDegreePackets.HeckeMellin

open Filter Set Module MeasureTheory
open scoped Topology NumberField

open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_StarkZeros
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform residues from completed-zeta zero separation

The completed zeta function, its functional equation and its convergent
real Hadamard sum give the uniform residue estimate from a uniform zero
gap. Uniqueness of a near-one zero reduces this gap to real-zero exclusion.
-/

open Filter Set MeasureTheory
open scoped Topology

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.HeckeMellin

universe u

/-- Uniform separation of completed-zeta zeros on the discriminant scale. -/
def CompletedXiGap (d : ℕ) : Prop :=
  ∃ c L₀ : ℝ, 0 < c ∧ 4 ≤ L₀ ∧
    ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
      (hn : Module.finrank ℚ K = d + 1) (σ : OrderedEmbeddings (d + 1) K),
      L₀ ≤ Real.log |(NumberField.discr K : ℝ)| →
      ∀ z, completedThetaXi σ hn z = 0 →
        c ^ 2 ≤ (Real.log |(NumberField.discr K : ℝ)| * (1 - z.re)) ^ 2 +
          (Real.log |(NumberField.discr K : ℝ)| * z.im) ^ 2

/-- The real exceptional-zero assertion in Stark's Lemma 8, after
excluding quadratic subfields. -/
def ExceptionalRealZeroExclusion (d : ℕ) : Prop :=
  ∃ a L₀ : ℝ, 0 < a ∧ 4 ≤ L₀ ∧
    ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
      (hn : Module.finrank ℚ K = d + 1) (σ : OrderedEmbeddings (d + 1) K),
      L₀ ≤ Real.log |(NumberField.discr K : ℝ)| →
      ∀ β : ℝ, 1 - a / Real.log |(NumberField.discr K : ℝ)| ≤ β → β < 1 →
        completedThetaXi σ hn β ≠ 0

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_PrimeBlockRationality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rational diagonal stabilizers of actual lattices

The rational coordinate space below is constructed from an actual lattice
matrix. Its diagonal stabilizer is a concrete subalgebra of real coordinate
functions, not a separately assumed field action. The absence of lattice
vectors on coordinate hyperplanes makes this algebra a field of degree
dividing the ambient dimension.
-/

noncomputable section
open Matrix Module Set
open scoped BigOperators Classical

namespace DukePrimeDegree
open PrimeDegreePackets

/-- Coordinate functions constant on each root block, viewed over `ℚ`. -/
def blockCoordinateAlgebra {n : ℕ} (r : Setoid (Fin n)) :
    Subalgebra ℚ (Fin n → ℝ) where
  carrier := {a | ∀ i j, r i j → a i = a j}
  zero_mem' := fun _ _ _ => rfl
  one_mem' := fun _ _ _ => rfl
  add_mem' := by
    intro a b ha hb i j hij
    change a i + b i = a j + b j
    rw [ha i j hij, hb i j hij]
  mul_mem' := by
    intro a b ha hb i j hij
    change a i * b i = a j * b j
    rw [ha i j hij, hb i j hij]
  algebraMap_mem' := fun _ _ _ _ => rfl

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ConjugationOrbit
attribute [-instance] _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace
attribute [-simp] _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.euclideanRowBasis_apply _root_.OAI.PrimeDegreePackets.rowBasis_apply
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

def slMatrixConjugation {n : ℕ} (h : G n) (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := h⁻¹.val * M * h.val

lemma slMatrixConjugation_mul {n : ℕ} (h k : G n) (M : Matrix (Fin n) (Fin n) ℝ) :
    slMatrixConjugation (h * k) M = slMatrixConjugation k (slMatrixConjugation h M) := by
  simp only [slMatrixConjugation, _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul]
  simp only [mul_assoc]

lemma slMatrixConjugation_one {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    slMatrixConjugation (1 : G n) M = M := by
  simp [slMatrixConjugation]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_BlockOrbit
attribute [-instance] _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The standard block group and its finite-volume lattice orbits

The group here is defined by its concrete action on the coordinate
blocks. The split diagonals and all within-block root groups lie in it.
The preceding rationality argument then forces any nontrivial partition
with a finite-volume orbit through a generic prime-degree lattice to be
the universal partition.
-/

noncomputable section
open Matrix Module Set MeasureTheory
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

/-- The determinant-one matrices commuting with every block-scalar
diagonal. This is the usual block-diagonal matrix subgroup. -/
def blockMatrixGroup {n : ℕ} (r : Setoid (Fin n)) : Subgroup (G n) where
  carrier := {g | ∀ c ∈ blockCoordinateAlgebra r,
    slMatrixConjugation g (Matrix.diagonal c) = Matrix.diagonal c}
  one_mem' := by
    intro c _
    exact slMatrixConjugation_one _
  mul_mem' := by
    intro g h hg hh c hc
    rw [slMatrixConjugation_mul, hg c hc, hh c hc]
  inv_mem' := by
    intro g hg c hc
    have he := slMatrixConjugation_mul g g⁻¹ (Matrix.diagonal c)
    rw [mul_inv_cancel, slMatrixConjugation_one, hg c hc] at he
    exact he.symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootCurveExtraction
attribute [-instance] _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Extracting a root from a differentiable curve

A diagonal with a unique maximal root rescales a curve at the identity.
Its limit is the elementary matrix given by that root component of the
velocity. Closedness then puts this actual root element in the subgroup.
This is a direct matrix argument, with no Lie-subgroup classification.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

/-- Entrywise velocity at the identity; the parameter approaches zero
through positive real values, exactly as in the rescaling argument. -/
def HasMatrixVelocity {n : ℕ} (γ : ℝ → G n)
    (V : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ a b, Tendsto (fun t : ℝ => ((γ t).val a b - (1 : Matrix (Fin n) (Fin n) ℝ) a b) / t)
    (𝓝[>] 0) (𝓝 (V a b))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_BlockTransverseElimination
attribute [-instance] _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace
attribute [-simp] _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing block directions by actual invariant roots

This is a sequence-level Gaussian elimination. No Lie-subgroup
classification or membership of the entire block group is assumed.
Every correction is a product of the specified within-block roots.
Pivots are eventually nonzero because the matrices tend to the identity.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def BlockZeroPattern {n : ℕ} (P : Finset (Fin n × Fin n)) (g : G n) : Prop :=
  ∀ p ∈ P, g.val p.1 p.2 = 0

/-- An elimination schedule records only zeros that must be preserved;
nonzero pivots are supplied locally by convergence to the identity. -/
inductive BlockEliminationChain {n : ℕ} (r : Setoid (Fin n)) :
    Finset (Fin n × Fin n) → Type
  | done {P} : BlockEliminationChain r P
  | step {P} (a b : Fin n) (hab : a ≠ b) (hr : r a b)
      (hP : ∀ j, (j, b) ∈ P → (j, a) ∈ P)
      (tail : BlockEliminationChain r (insert (a, b) P)) : BlockEliminationChain r P

namespace BlockEliminationChain

variable {n : ℕ} {r : Setoid (Fin n)} {P : Finset (Fin n × Fin n)}

def finalEntries : {P : Finset (Fin n × Fin n)} →
    BlockEliminationChain r P → Finset (Fin n × Fin n)
  | P, .done => P
  | _, .step _ _ _ _ _ tail => tail.finalEntries

def append : {P : Finset (Fin n × Fin n)} →
    (c : BlockEliminationChain r P) → BlockEliminationChain r c.finalEntries →
      BlockEliminationChain r P
  | _, .done, d => d
  | _, .step a b hab hr hP tail, d => .step a b hab hr hP (tail.append d)

@[simp] lemma finalEntries_append (c : BlockEliminationChain r P)
    (d : BlockEliminationChain r c.finalEntries) :
    (c.append d).finalEntries = d.finalEntries := by
  induction c with
  | done => rfl
  | step a b hab hr hP tail ih => exact ih d

end BlockEliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_MainConditional
attribute [-instance] _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conditional prime-degree packet equidistribution

Complete volume-weighted local-homothety packets converge to Haar
probability and form a tight family under a residue-relative uniform
zeta scale bound and prime-degree positive-entropy rigidity. The
arithmetic and dynamical hypotheses concern the actual homogeneous
lattice space and its diagonal action. A subsequential packet limit
supplies Haar probability.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree

open PrimeDegreePackets

universe u

/-- The published rigidity input, on the actual lattice space and with
actual diagonal ergodicity and measure-theoretic entropy. -/
def EKLPrimeInput (d : ℕ) : Prop :=
  Nat.Prime (d + 1) → 3 ≤ d + 1 →
    ∀ ν : Measure (X (d + 1)), IsProbabilityMeasure ν →
      ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d + 1)) ν →
      0 < measureEntropy ν
        (fun x => rightAction x (diagonalOneParameter (regularDiagonalWeights d)
          (regularDiagonalWeights_sum d) 1)) → IsHaarProbability ν

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZeroSeparation
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


namespace PrimeDegreePackets
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

 

def anchorNormalize (ν : Measure β) (J : Set β) : Measure β := (ν J)⁻¹ • ν

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafNormalization
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

instance rootSliceSecondCountable {n : ℕ} (i j k : Fin n) :
    SecondCountableTopology (RootSlice i j k) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology



end PrimeDegreePackets


namespace PrimeDegreePackets

 
def rootLeafWindow (R : ℝ) (m : ℕ) : Set ℝ := Ioo (-(R+m)) (R+m)

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafSupport
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

 
def centerRealMeasure (ν : Measure ℝ) (t : ℝ) : Measure ℝ :=
  ν.map (Homeomorph.subRight t)



def basedRealMeasure (ν : Measure ℝ) (t : ℝ) : Measure ℝ :=
  anchorNormalize (centerRealMeasure ν t) (Metric.ball 0 1)

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Contraction of root pairs under neutral diagonal flows

The acting root group is the additive real line. If a diagonal direction
expands the corresponding root character, forward right translation
contracts the relative root parameter. This supplies the geometric
hypothesis of the Hopf lemma even when the orbit leaves compact sets.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

/-- The real root group acts on the lattice space by right translation. -/
@[instance_reducible] def rootTranslationAction {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    MulAction (Multiplicative ℝ) (X n) where
  smul t x := rightAction x (Matrix.SpecialLinearGroup.transvection hij t.toAdd)
  one_smul x := by
    change rightAction x (Matrix.SpecialLinearGroup.transvection hij 0) = x
    simp
  mul_smul t u x := by
    change rightAction x (Matrix.SpecialLinearGroup.transvection hij (t.toAdd + u.toAdd)) =
      rightAction (rightAction x (Matrix.SpecialLinearGroup.transvection hij u.toAdd))
        (Matrix.SpecialLinearGroup.transvection hij t.toAdd)
    rw [rightAction_mul, ← Matrix.SpecialLinearGroup.transvection_add, add_comm]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_RootShearing
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

lemma root_left_mul_entry {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (r s : Fin n) (t : ℝ) :
    (Matrix.SpecialLinearGroup.transvection hij t * g).1 r s =
      g.1 r s + if r = i then t * g.1 j s else 0 := by
  change (Matrix.transvection i j t * g.1) r s = _
  by_cases h : r = i
  · subst r
    simp [Matrix.transvection_mul_apply_same]
  · simp [Matrix.transvection_mul_apply_of_ne, h]

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_HorosphereIsolatingFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Isolating a peripheral root of the shearing horosphere

Each noncentral row or column coordinate can be left unchanged by a
trace-zero diagonal flow which contracts all other horospherical
coordinates. The resulting conjugates converge to that single root.
-/

noncomputable section
open Matrix Filter
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

def centerWeights (d : ℕ) (w : Fin (d + 1) → ℝ) (r : Fin (d + 1)) : ℝ :=
  w r - (∑ s, w s) / (d + 1 : ℝ)

lemma centerWeights_sum (d : ℕ) (w : Fin (d + 1) → ℝ) :
    ∑ r, centerWeights d w r = 0 := by
  simp only [centerWeights, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

lemma centerWeights_sub (d : ℕ) (w : Fin (d + 1) → ℝ) (r s : Fin (d + 1)) :
    centerWeights d w r - centerWeights d w s = w r - w s := by
  unfold centerWeights
  ring

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ExtremalRootFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A neutral flow for the shortest remaining positive root

For type A roots in a fixed positive chamber, choose a root of shortest
index distance. Moving its two diagonal weights to their midpoint makes
that root neutral and keeps every other remaining root strictly contracting.
This is the root-removal step in EK2003 Proposition 8.3.
-/

noncomputable section
open Finset
open scoped BigOperators

namespace DukePrimeDegree

/-- Removing a shortest positive root leaves a collection closed under
root addition. This is the ideal needed for the product induction. -/
theorem erase_shortest_root_closed (n : ℕ)
    (S : Finset (Fin n × Fin n))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ a b c : Fin n, (a, b) ∈ S → (b, c) ∈ S → (a, c) ∈ S)
    (p : Fin n × Fin n)
    (hmin : ∀ q ∈ S, p.2.val - p.1.val ≤ q.2.val - q.1.val) :
    ∀ a b c : Fin n, (a, b) ∈ S.erase p → (b, c) ∈ S.erase p → (a, c) ∈ S.erase p := by
  intro a b c hab hbc
  have habS := (Finset.mem_erase.mp hab).2
  have hbcS := (Finset.mem_erase.mp hbc).2
  refine Finset.mem_erase.mpr ⟨?_, hcomp a b c habS hbcS⟩
  intro he
  subst p
  have hsmall := hmin (a, b) habS
  have h₁ := hpos (a, b) habS
  have h₂ := hpos (b, c) hbcS
  change a.val < b.val at h₁
  change b.val < c.val at h₂
  change c.val - a.val ≤ b.val - a.val at hsmall
  omega

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_MatrixVelocitySpace
attribute [-instance] _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual vector space of subgroup velocities

Velocities are derivatives of genuine curves in the subgroup at its
identity. Multiplication adds velocities and a linear reparametrization
scales them. Conjugating the subgroup conjugates this vector space.
No Lie-subgroup or homogeneous-support assertion is assumed here.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def HasIdentityMatrixDerivative {n : ℕ} (γ : ℝ → G n)
    (V : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  γ 0 = 1 ∧ ∀ i j, HasDerivAt (fun t => (γ t).val i j) (V i j) 0

lemma HasIdentityMatrixDerivative.mul {n : ℕ}
    {γ δ : ℝ → G n} {V W : Matrix (Fin n) (Fin n) ℝ}
    (hγ : HasIdentityMatrixDerivative γ V) (hδ : HasIdentityMatrixDerivative δ W) :
    HasIdentityMatrixDerivative (fun t => γ t * δ t) (V + W) := by
  refine ⟨by simp only [hγ.1, hδ.1, mul_one], ?_⟩
  intro i j
  have hd := HasDerivAt.sum (u := Finset.univ) (fun k _ => (hγ.2 i k).mul (hδ.2 k j))
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  all_goals try (apply Subsingleton.elim)
  · funext t
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Finset.sum_apply,
      Pi.mul_apply]
  · simp only [Finset.sum_add_distrib, ← Matrix.mul_apply, hγ.1, hδ.1,
      Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, Matrix.one_mul, Matrix.add_apply]

lemma HasIdentityMatrixDerivative.reparametrize {n : ℕ}
    {γ : ℝ → G n} {V : Matrix (Fin n) (Fin n) ℝ}
    (hγ : HasIdentityMatrixDerivative γ V) (c : ℝ) :
    HasIdentityMatrixDerivative (fun t => γ (c * t)) (c • V) := by
  refine ⟨by simpa only [mul_zero] using hγ.1, ?_⟩
  intro i j
  have hc : HasDerivAt (fun t : ℝ => c * t) c 0 := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id (0 : ℝ)).const_mul c
  have houter : HasDerivAt (fun t => (γ t).val i j) (V i j) (c * 0) := by
    simpa only [mul_zero] using hγ.2 i j
  simpa only [mul_zero, Function.comp_def, Matrix.smul_apply, smul_eq_mul, mul_comm] using
    houter.comp 0 hc

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ReverseRootFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The reverse root flow used by a right-action shearing pair

For points separated on the right by g, sampling both at U(-t) gives
relative displacement U(t) g U(-t). This action has exactly the same
invariant sets as the original root flow, so its ergodicity follows
from full real-root ergodicity, without selecting a discrete time.
-/

noncomputable section
open MeasureTheory Filter Set

namespace DukePrimeDegree
open PrimeDegreePackets

@[instance_reducible] def reverseRootTranslationAction {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) : MulAction (Multiplicative ℝ) (X n) where
  smul t x := rightAction x (Matrix.SpecialLinearGroup.transvection hij (-t.toAdd))
  one_smul x := by
    change rightAction x (Matrix.SpecialLinearGroup.transvection hij (-0)) = x
    simp
  mul_smul t u x := by
    change rightAction x (Matrix.SpecialLinearGroup.transvection hij (-(t.toAdd + u.toAdd))) =
      rightAction (rightAction x (Matrix.SpecialLinearGroup.transvection hij (-u.toAdd)))
        (Matrix.SpecialLinearGroup.transvection hij (-t.toAdd))
    rw [rightAction_mul, ← Matrix.SpecialLinearGroup.transvection_add]
    congr 2
    ring

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_RootCentralizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The root-pair centralizer

The common centralizer of opposite elementary root groups has a scalar
block on their two coordinates. This gives the concrete matrix form
needed to apply the integral scalar-block obstruction to orbit returns.
-/

noncomputable section
open Set Matrix
open scoped Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets

def rootPairCentralizer {n : ℕ} {i j : Fin n} (hij : i ≠ j) : Subgroup (G n) :=
  Subgroup.centralizer {Matrix.SpecialLinearGroup.transvection hij 1,
    Matrix.SpecialLinearGroup.transvection hij.symm 1}

lemma mem_rootPairCentralizer {n : ℕ} {i j : Fin n} (hij : i ≠ j) (g : G n) :
    g ∈ rootPairCentralizer hij ↔
      g * Matrix.SpecialLinearGroup.transvection hij 1 =
        Matrix.SpecialLinearGroup.transvection hij 1 * g ∧
      g * Matrix.SpecialLinearGroup.transvection hij.symm 1 =
        Matrix.SpecialLinearGroup.transvection hij.symm 1 * g := by
  constructor
  · intro h
    have hc := Subgroup.mem_centralizer_iff.mp h
    exact ⟨(hc _ (by simp)).symm, (hc _ (by simp)).symm⟩
  · rintro ⟨h₁, h₂⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro a ha
    rcases (Set.mem_insert_iff.mp ha) with h | h
    · subst a
      exact h₁.symm
    · rw [Set.mem_singleton_iff] at h
      subst a
      exact h₂.symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_EntropyBalance
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Entropy symmetry and the root coefficient balance

The entropy formula in EKL (2006), Proposition 3.1, is a sum of positive
root weights. Equality of the entropy of an invertible map and its inverse
then gives the row/column balance. The finite algebraic implication
uses trace-zero test weights independently of the dynamical entropy formula.
-/

noncomputable section
open scoped BigOperators Classical

namespace DukePrimeDegree

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The finite positive-root expression in the entropy formula. -/
def rootEntropyForm (w : ι → ι → ℝ) (t : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, w i j * max (t i - t j) 0

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_InfiniteLabelEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Infinite future conditioning on positive-mass leaf atoms

Finite conditioned kernels converge to restriction to the whole itinerary
atom. Martingale convergence identifies this limit with conditioning on
the increasing union of the actual transverse-and-label sigma algebras.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    [StandardBorelSpace T] [Nonempty T]

def labelFiber {N : ℕ} (Q : S × T → Fin N) (z : S × T) : Set T :=
  {t | Q (z.1,t)=Q z}

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RegularEntropyTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finitely many regular weights suffice for coefficient balance

For the prime-degree application the balance argument does not need the
entropy formula at singular weights. One regular weight and one small
perturbation for each coordinate suffice, together with their negatives.
All positive gaps in these explicit weights are at least log 4.
-/

noncomputable section
open scoped BigOperators Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def rawEntropyTest (d : ℕ) (a : Option (Fin (d+1))) (i : Fin (d+1)) : ℝ :=
  4 * (i.val : ℝ) + if a = some i then 1 else 0

def regularEntropyTest (d : ℕ) (a : Option (Fin (d+1))) (i : Fin (d+1)) : ℝ :=
  rawEntropyTest d a i - (∑ j, rawEntropyTest d a j) / (d+1)

lemma regularEntropyTest_sum (d : ℕ) (a : Option (Fin (d+1))) :
    ∑ i, regularEntropyTest d a i = 0 := by
  simp only [regularEntropyTest, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (d+1 : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_CountableWeakKernel
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A probability kernel is measurable for the weak topology

A countable family of finite-basis-union evaluations defines a stronger
second-countable topology on probabilities. Kernel evaluations are measurable
for that topology, and the countable Portmanteau criterion makes the map
to the usual weak topology continuous. No global measurable-space
instance on probabilities is changed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped Topology ENNReal

namespace DukePrimeDegree

variable (Y : Type*) [TopologicalSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y]

/-- A separate wrapper retains both probability topologies without
overriding the existing weak topology. -/
structure BasisProbability where
  toProbability : ProbabilityMeasure Y

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PositiveRootPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matrix support of groups generated by positive roots

Transitive positive root sets define matrix patterns preserved by all
products of their root generators. The assertion also holds on the
closure, supplying the concrete support restriction for root induction.
-/

noncomputable section
open Matrix Set
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

/-- Outside the chosen positive roots the matrix equals the identity. -/
def PositiveRootPattern {n : ℕ} (S : Finset (Fin n × Fin n)) (g : G n) : Prop :=
  ∀ r s, (r, s) ∉ S → g.val r s = (1 : Matrix (Fin n) (Fin n) ℝ) r s

lemma positiveRootPattern_one {n : ℕ} (S : Finset (Fin n × Fin n)) :
    PositiveRootPattern S (1 : G n) := by
  intro r s _
  rfl

lemma positiveRootPattern_transvection {n : ℕ} (S : Finset (Fin n × Fin n))
    {i j : Fin n} (hij : i ≠ j) (hijS : (i, j) ∈ S) (t : ℝ) :
    PositiveRootPattern S (Matrix.SpecialLinearGroup.transvection hij t) := by
  intro r s hrs
  have hne : ¬ (r = i ∧ s = j) := by
    rintro ⟨rfl, rfl⟩
    exact hrs hijS
  simp only [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply]
  have hz : Matrix.single i j t r s = 0 := by
    simp only [Matrix.single_apply]
    split_ifs with h
    · exact (hne ⟨h.1.symm, h.2.symm⟩).elim
    · rfl
  rw [hz, add_zero]

lemma positiveRootPattern_mul {n : ℕ} (S : Finset (Fin n × Fin n))
    (htrans : ∀ a b c : Fin n, (a, b) ∈ S → (b, c) ∈ S → (a, c) ∈ S)
    {g h : G n} (hg : PositiveRootPattern S g) (hh : PositiveRootPattern S h) :
    PositiveRootPattern S (g * h) := by
  let M := g.val - 1
  let N := h.val - 1
  have hM (r s : Fin n) (hrs : (r, s) ∉ S) : M r s = 0 := sub_eq_zero.mpr (hg r s hrs)
  have hN (r s : Fin n) (hrs : (r, s) ∉ S) : N r s = 0 := sub_eq_zero.mpr (hh r s hrs)
  have heq : (g * h).val = 1 + M + N + M * N := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, M, N]
    noncomm_ring
  intro r s hrs
  have hMN : (M * N) r s = 0 := by
    change (∑ k, M r k * N k s) = 0
    apply Finset.sum_eq_zero
    intro k _
    by_cases hrk : (r, k) ∈ S
    · have hks : (k, s) ∉ S := fun hks => hrs (htrans r k s hrk hks)
      rw [hN k s hks, mul_zero]
    · rw [hM r k hrk, zero_mul]
  rw [heq]
  change (1 : Matrix (Fin n) (Fin n) ℝ) r s + M r s + N r s + (M * N) r s = _
  rw [hM r s hrs, hN r s hrs, hMN, add_zero, add_zero, add_zero]

/-- The subgroup generated by the root lines in `S`. -/
def positiveRootGeneratedGroup {n : ℕ} (S : Finset (Fin n × Fin n)) : Subgroup (G n) :=
  Subgroup.closure {g | ∃ (i j : Fin n) (hij : i ≠ j) (t : ℝ),
    (i, j) ∈ S ∧ g = Matrix.SpecialLinearGroup.transvection hij t}

lemma positiveRootGeneratedGroup_pattern {n : ℕ} (S : Finset (Fin n × Fin n))
    (htrans : ∀ a b c : Fin n, (a, b) ∈ S → (b, c) ∈ S → (a, c) ∈ S)
    {g : G n} (hg : g ∈ positiveRootGeneratedGroup S) : PositiveRootPattern S g := by
  apply Subgroup.closure_induction'' (p := fun g _ => PositiveRootPattern S g) ?_ ?_ ?_ ?_ hg
  · rintro g ⟨i, j, hij, t, hS, rfl⟩
    exact positiveRootPattern_transvection S hij hS t
  · rintro g ⟨i, j, hij, t, hS, rfl⟩
    rw [Matrix.SpecialLinearGroup.transvection_inv]
    exact positiveRootPattern_transvection S hij hS (-t)
  · exact positiveRootPattern_one S
  · intro g h _ _ hg hh
    exact positiveRootPattern_mul S htrans hg hh

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PositiveRootFactorization
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

lemma positiveRootGeneratedGroup_mono {n : ℕ} {S T : Finset (Fin n × Fin n)}
    (hST : S ⊆ T) : positiveRootGeneratedGroup S ≤ positiveRootGeneratedGroup T := by
  apply Subgroup.closure_mono
  rintro g ⟨i, j, hij, t, hS, rfl⟩
  exact ⟨i, j, hij, t, hST hS, rfl⟩

lemma transvection_mem_positiveRootGeneratedGroup {n : ℕ}
    (S : Finset (Fin n × Fin n)) {i j : Fin n} (hij : i ≠ j)
    (hS : (i, j) ∈ S) (t : ℝ) :
    Matrix.SpecialLinearGroup.transvection hij t ∈ positiveRootGeneratedGroup S :=
  Subgroup.subset_closure ⟨i, j, hij, t, hS, rfl⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PositiveRootCoordinates
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

lemma remaining_root_entry {n : ℕ} (S : Finset (Fin n × Fin n))
    (hpos : ∀ p ∈ S, p.1 < p.2) {a b : Fin n} (hab : a ≠ b)
    (hcomp : ∀ i j k : Fin n, (i, j) ∈ S.erase (a, b) →
      (j, k) ∈ S.erase (a, b) → (i, k) ∈ S.erase (a, b))
    (w : positiveRootGeneratedGroup (S.erase (a, b))) :
    w.val.val a b = 0 ∧ w.val.val b b = 1 := by
  have hw := positiveRootGeneratedGroup_pattern (S.erase (a, b)) hcomp w.prop
  constructor
  · simpa only [Matrix.one_apply, hab, ite_false, if_false] using hw a b (by simp)
  · have hbb : (b, b) ∉ S.erase (a, b) := by
      intro h
      exact lt_irrefl b (hpos (b, b) (Finset.mem_of_mem_erase h))
    simpa using hw b b hbb

lemma root_entry_mul_transvection {n : ℕ} {a b : Fin n} (hab : a ≠ b)
    (t : ℝ) (g : G n) :
    (g * Matrix.SpecialLinearGroup.transvection hab t).val a b =
      g.val a b + g.val a a * t := by
  change (g.val * (1 + Matrix.single a b t)) a b = _
  simp [Matrix.mul_add]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_QuotientNeighborhoods
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small relative lifts on the arithmetic quotient

Open quotient charts provide a neighborhood in which any two points are
related by a matrix in a prescribed identity neighborhood. This is the
local lifting step used with compactly controlled centralizer returns.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

/-- Right translations are a left action of the opposite subgroup. -/
@[instance_reducible] def rightSubgroupAction {n : ℕ} (C : Subgroup (G n)) :
    MulAction (MulOpposite C) (X n) where
  smul c x := rightAction x (c.unop : G n)
  one_smul x := by change rightAction x 1 = x; simp
  mul_smul c d x := by
    change rightAction x ((d.unop : G n) * (c.unop : G n)) =
      rightAction (rightAction x (d.unop : G n)) (c.unop : G n)
    exact (rightAction_mul x _ _).symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralDiagonal
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

def neutralWeightSubgroup {n : ℕ} (i j : Fin n) : AddSubgroup (Fin n → ℝ) where
  carrier := {ell | (∑ r, ell r) = 0 ∧ ell i = ell j}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha, hai⟩ ⟨hb, hbi⟩
    constructor
    · simp only [Pi.add_apply, Finset.sum_add_distrib, ha, hb, add_zero]
    · simp only [Pi.add_apply, hai, hbi]
  neg_mem' := by
    rintro a ⟨ha, hai⟩
    constructor
    · simp only [Pi.neg_apply, Finset.sum_neg_distrib, ha, neg_zero]
    · simp only [Pi.neg_apply, hai]

lemma diagonalOneParameter_add_weights {n : ℕ}
    (a b : Fin n → ℝ) (ha : ∑ r, a r = 0) (hb : ∑ r, b r = 0) (t : ℝ) :
    diagonalOneParameter (a + b)
      (by simp only [Pi.add_apply, Finset.sum_add_distrib, ha, hb, add_zero]) t =
      diagonalOneParameter a ha t * diagonalOneParameter b hb t := by
  apply Subtype.ext
  change Matrix.diagonal (fun r => Real.exp ((a r + b r) * t)) =
    Matrix.diagonal (fun r => Real.exp (a r * t)) * Matrix.diagonal (fun r => Real.exp (b r * t))
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext r
  simp only [add_mul, Real.exp_add]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootInductionStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The extremal-root step of the product argument

For a nonempty closed collection of positive roots, one root can be
removed while preserving closure. Its actual intrinsic leaf measure is
constant along the closed group generated by the remaining roots, off
one common null set. This is the holonomy step in Einsiedler--Katok
(2003), Proposition 8.3.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma erase_neutral_root_closed {n : ℕ}
    (S : Finset (Fin n × Fin n))
    (hcomp : ∀ a b c : Fin n, (a, b) ∈ S → (b, c) ∈ S → (a, c) ∈ S)
    (p : Fin n × Fin n) (ell : Fin n → ℝ) (hneut : ell p.1 = ell p.2)
    (hdecay : ∀ q ∈ S, q ≠ p → ell q.1 < ell q.2) :
    ∀ a b c : Fin n, (a, b) ∈ S.erase p → (b, c) ∈ S.erase p →
      (a, c) ∈ S.erase p := by
  intro a b c hab hbc
  obtain ⟨habp, habS⟩ := Finset.mem_erase.mp hab
  obtain ⟨hbcp, hbcS⟩ := Finset.mem_erase.mp hbc
  refine Finset.mem_erase.mpr ⟨?_, hcomp a b c habS hbcS⟩
  intro he
  have ha := hdecay (a, b) habS habp
  have hb := hdecay (b, c) hbcS hbcp
  have hac : ell a = ell c := by simpa only [← he] using hneut
  exact (ne_of_lt (lt_trans ha hb)) hac

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_EliminationRootChart
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

def ZeroPattern {n : ℕ} (P : Finset (Fin n × Fin n)) (g : G n) : Prop :=
  ∀ p ∈ P, g.val p.1 p.2 = 0

def NonzeroPivots {n : ℕ} (D : Finset (Fin n)) (g : G n) : Prop :=
  ∀ r ∈ D, g.val r r ≠ 0

abbrev EliminationSlice {n : ℕ} (P : Finset (Fin n × Fin n)) (D : Finset (Fin n)) :=
  {g : G n // ZeroPattern P g ∧ NonzeroPivots D g}

theorem zeroPattern_root_translate {n : ℕ} (P : Finset (Fin n × Fin n))
    {a b : Fin n} (hab : a ≠ b)
    (hP : ∀ r, (r, b) ∈ P → (r, a) ∈ P)
    {g : G n} (hg : ZeroPattern P g) (t : ℝ) :
    ZeroPattern P (g * Matrix.SpecialLinearGroup.transvection hab t) := by
  intro p hp
  rw [root_mul_entry, hg p hp]
  by_cases hb : p.2 = b
  · have hs : g.val p.1 a = 0 :=
      hg (p.1, a) (hP p.1 (by simpa only [← hb, Prod.mk.eta] using hp))
    simp only [hb, ite_true, if_true, hs, zero_mul, add_zero]
  · simp only [hb, ite_false, if_false, add_zero]

theorem nonzeroPivots_root_translate {n : ℕ} (D : Finset (Fin n))
    {a b : Fin n} (hab : a ≠ b) (hb : b ∉ D)
    {g : G n} (hg : NonzeroPivots D g) (t : ℝ) :
    NonzeroPivots D (g * Matrix.SpecialLinearGroup.transvection hab t) := by
  intro r hr
  have hrb : r ≠ b := fun h => hb (h ▸ hr)
  simpa only [root_mul_entry, hrb, ite_false, if_false, add_zero] using hg r hr

lemma elimination_pivot_isOpen {n : ℕ} (P : Finset (Fin n × Fin n))
    (D : Finset (Fin n)) (a : Fin n) :
    IsOpen {g : EliminationSlice P D | g.val.val a a ≠ 0} :=
  (rootPivot_isOpen a a).preimage continuous_subtype_val

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_EliminationChain
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

inductive EliminationChain {n : ℕ} :
    Finset (Fin n × Fin n) → Finset (Fin n) → Type
  | done {P D} : EliminationChain P D
  | step {P D} (a b : Fin n) (hab : a ≠ b)
      (hP : ∀ r, (r, b) ∈ P → (r, a) ∈ P) (hb : b ∉ D)
      (tail : EliminationChain (insert (a, b) P) (insert a D)) : EliminationChain P D

namespace EliminationChain

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def finalEntries : {P : Finset (Fin n × Fin n)} → {D : Finset (Fin n)} →
    EliminationChain P D → Finset (Fin n × Fin n)
  | P, _, .done => P
  | _, _, .step _ _ _ _ _ tail => tail.finalEntries

def finalPivots : {P : Finset (Fin n × Fin n)} → {D : Finset (Fin n)} →
    EliminationChain P D → Finset (Fin n)
  | _, D, .done => D
  | _, _, .step _ _ _ _ _ tail => tail.finalPivots

theorem entries_subset_final (c : EliminationChain P D) : P ⊆ c.finalEntries := by
  induction c with
  | done => exact Finset.Subset.refl _
  | step a b hab hP hb tail ih =>
      exact (Finset.subset_insert _ _).trans ih

def Time : {P : Finset (Fin n × Fin n)} → {D : Finset (Fin n)} →
    EliminationChain P D → Type
  | _, _, .done => PUnit
  | _, _, .step _ _ _ _ _ tail => tail.Time × ℝ

instance timeTopology (c : EliminationChain P D) : TopologicalSpace c.Time := by
  induction c with
  | done => exact inferInstanceAs (TopologicalSpace PUnit)
  | step _ _ _ _ _ _ ih => exact @instTopologicalSpaceProd _ _ ih inferInstance

abbrev FinalSlice (c : EliminationChain P D) :=
  EliminationSlice c.finalEntries c.finalPivots

def word : {P : Finset (Fin n × Fin n)} → {D : Finset (Fin n)} →
    (c : EliminationChain P D) → c.Time → G n
  | _, _, .done, _ => 1
  | _, _, .step _ _ hab _ _ tail, t =>
      tail.word t.1 * Matrix.SpecialLinearGroup.transvection hab t.2

def zeroTime : {P : Finset (Fin n × Fin n)} → {D : Finset (Fin n)} →
    (c : EliminationChain P D) → c.Time
  | _, _, .done => PUnit.unit
  | _, _, .step _ _ _ _ _ tail => (tail.zeroTime, 0)

@[simp] theorem word_zeroTime (c : EliminationChain P D) : c.word c.zeroTime = 1 := by
  induction c with
  | done => rfl
  | step a b hab hP hb tail ih =>
      change tail.word tail.zeroTime * Matrix.SpecialLinearGroup.transvection hab 0 = 1
      rw [ih, Matrix.SpecialLinearGroup.transvection_coeff_zero, one_mul]

theorem word_mem_generated (c : EliminationChain P D)
    (S : Finset (Fin n × Fin n)) (hS : c.finalEntries ⊆ S) (t : c.Time) :
    c.word t ∈ positiveRootGeneratedGroup S := by
  induction c with
  | done => exact (positiveRootGeneratedGroup S).one_mem
  | step a b hab hP hb tail ih =>
      apply (positiveRootGeneratedGroup S).mul_mem
      · exact ih hS t.1
      · exact transvection_mem_positiveRootGeneratedGroup S hab
          (hS (tail.entries_subset_final (Finset.mem_insert_self _ _))) t.2

end EliminationChain
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_OrderedEliminationChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Existence of the complete ordered elimination chain

At each step choose the least remaining positive root in row order.
The processed roots form an initial segment, which proves exactly the
zero-preservation and pivot conditions required by the next chart.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def allPositiveRoots (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2)

def InitialRootPattern {n : ℕ} (P : Finset (Fin n × Fin n)) : Prop :=
  ∀ p ∈ P, p ∈ allPositiveRoots n ∧
    ∀ q ∈ allPositiveRoots n, toLex q < toLex p → q ∈ P

def PivotsFromPattern {n : ℕ} (P : Finset (Fin n × Fin n)) (D : Finset (Fin n)) : Prop :=
  ∀ a ∈ D, ∃ b, (a, b) ∈ P

lemma initialRootPattern_stable {n : ℕ} {P : Finset (Fin n × Fin n)}
    (hP : InitialRootPattern P) {a b : Fin n} (hab : a < b) (habP : (a, b) ∉ P) :
    ∀ r, (r, b) ∈ P → (r, a) ∈ P := by
  intro r hr
  have hra : r < a := by
    by_contra hn
    rcases lt_or_eq_of_le (le_of_not_gt hn) with hlt | he
    · exact habP ((hP (r, b) hr).2 (a, b)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩)
        (Prod.Lex.toLex_lt_toLex.mpr (Or.inl hlt)))
    · subst r
      exact habP hr
  exact (hP (r, b) hr).2 (r, a)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hra⟩)
    (Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hab⟩))

lemma initialRootPattern_pivot_notMem {n : ℕ}
    {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    (hP : InitialRootPattern P) (hD : PivotsFromPattern P D)
    {a b : Fin n} (hab : a < b) (habP : (a, b) ∉ P) : b ∉ D := by
  intro hb
  obtain ⟨c, hc⟩ := hD b hb
  exact habP ((hP (b, c) hc).2 (a, b)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩)
    (Prod.Lex.toLex_lt_toLex.mpr (Or.inl hab)))

lemma initialRootPattern_insert_min {n : ℕ} {P : Finset (Fin n × Fin n)}
    (hP : InitialRootPattern P) (p : Fin n × Fin n)
    (hp : p ∈ allPositiveRoots n \ P)
    (hmin : ∀ q ∈ allPositiveRoots n \ P, toLex p ≤ toLex q) :
    InitialRootPattern (insert p P) := by
  intro q hq
  rcases Finset.mem_insert.mp hq with rfl | hq
  · refine ⟨(Finset.mem_sdiff.mp hp).1, ?_⟩
    intro q hq hqp
    by_cases hqP : q ∈ P
    · exact Finset.mem_insert_of_mem hqP
    · exact (not_lt_of_ge (hmin q (Finset.mem_sdiff.mpr ⟨hq, hqP⟩)) hqp).elim
  · exact ⟨(hP q hq).1, fun r hr hrq => Finset.mem_insert_of_mem ((hP q hq).2 r hr hrq)⟩

lemma pivotsFromPattern_insert {n : ℕ} {P : Finset (Fin n × Fin n)}
    {D : Finset (Fin n)} (hD : PivotsFromPattern P D) (a b : Fin n) :
    PivotsFromPattern (insert (a, b) P) (insert a D) := by
  intro r hr
  rcases Finset.mem_insert.mp hr with rfl | hr
  · exact ⟨b, Finset.mem_insert_self _ _⟩
  · obtain ⟨s, hs⟩ := hD r hr
    exact ⟨s, Finset.mem_insert_of_mem hs⟩

theorem exists_complete_elimination_chain (n : ℕ) :
    ∃ c : EliminationChain (∅ : Finset (Fin n × Fin n)) ∅,
      c.finalEntries = allPositiveRoots n := by
  suffices ∀ m : ℕ, ∀ (P : Finset (Fin n × Fin n)) (D : Finset (Fin n)),
      (allPositiveRoots n \ P).card = m → InitialRootPattern P → PivotsFromPattern P D →
      ∃ c : EliminationChain P D, c.finalEntries = allPositiveRoots n by
    exact this _ ∅ ∅ rfl (by intro p hp; simp at hp) (by intro a ha; simp at ha)
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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootChart
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

def completeRootChain (n : ℕ) : EliminationChain (∅ : Finset (Fin n × Fin n)) ∅ :=
  (exists_complete_elimination_chain n).choose

lemma completeRootChain_final (n : ℕ) : (completeRootChain n).finalEntries = allPositiveRoots n :=
  (exists_complete_elimination_chain n).choose_spec

abbrev UpperRootTransverse (n : ℕ) := (completeRootChain n).FinalSlice
abbrev UpperRootTime (n : ℕ) := (completeRootChain n).Time

def emptyEliminationHomeomorph (n : ℕ) :
    EliminationSlice (∅ : Finset (Fin n × Fin n)) ∅ ≃ₜ G n where
  toFun := Subtype.val
  invFun g := ⟨g, by constructor <;> simp [ZeroPattern, NonzeroPivots]⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

lemma upperRootWord_mem (n : ℕ) (t : UpperRootTime n) :
    (completeRootChain n).word t ∈ positiveRootGeneratedGroup (allPositiveRoots n) := by
  apply (completeRootChain n).word_mem_generated
  rw [completeRootChain_final]

def upperRootIdentity (n : ℕ) : UpperRootTransverse n :=
  ⟨1, by
    constructor
    · rw [completeRootChain_final]
      intro p hp
      have hp' := (Finset.mem_filter.mp hp).2
      change (1 : Matrix (Fin n) (Fin n) ℝ) p.1 p.2 = 0
      simp [ne_of_lt hp']
    · intro r _
      change (1 : Matrix (Fin n) (Fin n) ℝ) r r ≠ 0
      simp⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootDisintegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Disintegration in the actual upper-root charts

Both the final Gaussian transversal and the finite product of root times
are standard Borel spaces. The open quotient charts therefore give
finite coordinate measures and genuine conditional probability kernels.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

instance EliminationChain.time_secondCountable {n : ℕ}
    {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)} (c : EliminationChain P D) :
    SecondCountableTopology c.Time := by
  induction c with
  | done => exact inferInstanceAs (SecondCountableTopology PUnit)
  | step a b hab hP hb tail ih =>
      let := ih
      exact inferInstanceAs (SecondCountableTopology (tail.Time × ℝ))

instance EliminationChain.time_polish {n : ℕ}
    {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)} (c : EliminationChain P D) :
    PolishSpace c.Time := by
  induction c with
  | done => exact inferInstanceAs (PolishSpace PUnit)
  | step a b hab hP hb tail ih =>
      let := ih
      exact inferInstanceAs (PolishSpace (tail.Time × ℝ))

instance EliminationChain.time_measurableSpace {n : ℕ}
    {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)} (c : EliminationChain P D) :
    MeasurableSpace c.Time := borel c.Time

instance EliminationChain.time_borelSpace {n : ℕ}
    {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)} (c : EliminationChain P D) :
    BorelSpace c.Time := ⟨rfl⟩

instance EliminationChain.time_standardBorel {n : ℕ}
    {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)} (c : EliminationChain P D) :
    StandardBorelSpace c.Time := by infer_instance

instance EliminationChain.time_nonempty {n : ℕ}
    {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)} (c : EliminationChain P D) :
    Nonempty c.Time := ⟨c.zeroTime⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootLongBoxes
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

lemma allPositiveRoots_closed (n : ℕ) :
    ∀ a b c : Fin n, (a, b) ∈ allPositiveRoots n → (b, c) ∈ allPositiveRoots n →
      (a, c) ∈ allPositiveRoots n := by
  intro a b c hab hbc
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    lt_trans (Finset.mem_filter.mp hab).2 (Finset.mem_filter.mp hbc).2⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootGlobalCoordinates
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

lemma upperRoot_diagonal {n : ℕ} {g : G n}
    (hg : g ∈ positiveRootGeneratedGroup (allPositiveRoots n)) (a : Fin n) :
    g.val a a = 1 := by
  have h := positiveRootGeneratedGroup_pattern (allPositiveRoots n)
    (allPositiveRoots_closed n) hg a a (by simp [allPositiveRoots])
  simpa only [Matrix.one_apply, ite_true, if_true] using h

lemma upperRoot_zeroPattern_eq_one {n : ℕ} {g : G n}
    (hg : g ∈ positiveRootGeneratedGroup (allPositiveRoots n))
    (hz : ZeroPattern (allPositiveRoots n) g) : g = 1 := by
  apply Subtype.ext
  ext a b
  by_cases hab : a < b
  · rw [hz (a, b) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩)]
    simp [ne_of_lt hab]
  · exact positiveRootGeneratedGroup_pattern (allPositiveRoots n)
      (allPositiveRoots_closed n) hg a b (by simpa [allPositiveRoots] using hab)

def upperRootWordMap (n : ℕ) (t : UpperRootTime n) :
    positiveRootGeneratedGroup (allPositiveRoots n) :=
  ⟨(completeRootChain n).word t, upperRootWord_mem n t⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_EliminationRootOrder
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
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def roots : {P : Finset (Fin n × Fin n)} → {D : Finset (Fin n)} →
    EliminationChain P D → List (Fin n × Fin n)
  | _, _, .done => []
  | _, _, .step a b _ _ _ tail => (a, b) :: tail.roots

lemma finalEntries_eq_union_roots (c : EliminationChain P D) :
    c.finalEntries = P ∪ c.roots.toFinset := by
  induction c with
  | done => simp [finalEntries, roots]
  | step a b hab hP hb tail ih =>
      simpa [finalEntries, roots, Finset.union_comm, Finset.union_left_comm,
        Finset.union_assoc] using ih

lemma roots_notMem_initial (c : EliminationChain P D)
    (hpos : ∀ p ∈ c.finalEntries, p.1 < p.2) :
    ∀ p ∈ c.roots, p ∉ P := by
  induction c with
  | done => simp [roots]
  | @step P D a b hab hP hb tail ih =>
      intro p hp
      change p ∈ (a, b) :: tail.roots at hp
      rcases List.mem_cons.mp hp with rfl | hp
      · intro hpP
        have haa := hP a hpP
        exact lt_irrefl a (hpos (a, a)
          (tail.entries_subset_final (Finset.mem_insert_of_mem haa)))
      · exact fun hpP => ih hpos p hp (Finset.mem_insert_of_mem hpP)

lemma roots_nodup (c : EliminationChain P D)
    (hpos : ∀ p ∈ c.finalEntries, p.1 < p.2) : c.roots.Nodup := by
  induction c with
  | done => exact List.nodup_nil
  | step a b hab hP hb tail ih =>
      apply List.nodup_cons.mpr
      exact ⟨fun hp => tail.roots_notMem_initial hpos (a, b) hp
        (Finset.mem_insert_self _ _), ih hpos⟩

end EliminationChain

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootLeafLowerBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Typical root leaves have a linear lower mass bound

The property is expressed at countably many exponential radii. This makes
it measurable and allows transfer through the actual root-box disintegration.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

/-- A finite constant bounds inverse small-ball mass along integer scales. -/
def HasDiscreteLinearLowerBound (ν : Measure ℝ) : Prop :=
  ∃ C N : ℕ, ∀ n : ℕ, N ≤ n →
    ENNReal.ofReal (Real.exp (-(n : ℝ))) ≤
      (C : ℝ≥0∞) * ν (ball 0 (Real.exp (-(n : ℝ))))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_FiniteProjectionFrames
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

def finiteGramDet (v : I → E) (S : Finset I) : ℝ :=
  (Matrix.gram ℝ (fun i : S => v i)).det

end GramFrames

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exhausting upper-root time by compactly contained cubes

The ordered real root coordinates give explicit increasing open cubes,
compact closed cubes, and countable families of long quotient boxes.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

instance specialLinear_secondCountable (n : ℕ) : SecondCountableTopology (G n) := by
  let : SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℝ))
  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology

namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def cube : {P : Finset (Fin n × Fin n)} → {D : Finset (Fin n)} →
    (c : EliminationChain P D) → ℝ → Set c.Time
  | _, _, .done, _ => univ
  | _, _, .step _ _ _ _ _ tail, R => tail.cube R ×ˢ Ioo (-R) R

def closedCube : {P : Finset (Fin n × Fin n)} → {D : Finset (Fin n)} →
    (c : EliminationChain P D) → ℝ → Set c.Time
  | _, _, .done, _ => univ
  | _, _, .step _ _ _ _ _ tail, R => tail.closedCube R ×ˢ Icc (-R) R

lemma cube_open (c : EliminationChain P D) (R : ℝ) : IsOpen (c.cube R) := by
  induction c with
  | done => exact isOpen_univ
  | step a b hab hP hb tail ih => exact ih.prod isOpen_Ioo

lemma closedCube_compact (c : EliminationChain P D) (R : ℝ) : IsCompact (c.closedCube R) := by
  induction c with
  | done => exact (isCompact_univ : IsCompact (Set.univ : Set PUnit))
  | step a b hab hP hb tail ih => exact ih.prod isCompact_Icc

lemma cube_subset_closedCube (c : EliminationChain P D) (R : ℝ) :
    c.cube R ⊆ c.closedCube R := by
  induction c with
  | done => exact subset_rfl
  | step a b hab hP hb tail ih => exact Set.prod_mono ih Ioo_subset_Icc_self

lemma cube_mono (c : EliminationChain P D) : Monotone c.cube := by
  intro R S hRS
  induction c with
  | done => exact subset_rfl
  | step a b hab hP hb tail ih =>
      exact Set.prod_mono ih (Ioo_subset_Ioo (neg_le_neg hRS) hRS)

lemma mem_cube_exists (c : EliminationChain P D) (R : ℝ) (t : c.Time) :
    ∃ m : ℕ, t ∈ c.cube (R + m) := by
  induction c with
  | done => exact ⟨0, mem_univ _⟩
  | step a b hab hP hb tail ih =>
      change tail.Time × ℝ at t
      obtain ⟨m, hm⟩ := ih t.1
      obtain ⟨k, hk⟩ := exists_nat_gt (|t.2| + |R|)
      refine ⟨max m k, ?_, ?_, ?_⟩
      · exact tail.cube_mono (by have h : (m : ℝ) ≤ max m k := Nat.cast_le.mpr (le_max_left _ _); linarith) hm
      · have h₁ := neg_abs_le t.2
        have h₂ := neg_abs_le R
        have h₃ : (k : ℝ) ≤ max m k := Nat.cast_le.mpr (le_max_right _ _)
        linarith
      · have h₁ := le_abs_self t.2
        have h₂ := neg_abs_le R
        have h₃ : (k : ℝ) ≤ max m k := Nat.cast_le.mpr (le_max_right _ _)
        linarith

lemma cubes_cover (c : EliminationChain P D) (R : ℝ) :
    ⋃ m : ℕ, c.cube (R + m) = univ := by
  apply Set.eq_univ_of_forall
  intro t
  exact mem_iUnion.mpr (c.mem_cube_exists R t)

end EliminationChain

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootEuclideanCoordinates
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

def realVectorConsHomeomorph (m : ℕ) : ((Fin m → ℝ) × ℝ) ≃ₜ (Fin (m + 1) → ℝ) where
  toFun p := Fin.cons p.2 p.1
  invFun v := (Fin.tail v, v 0)
  left_inv p := by simp
  right_inv v := Fin.cons_self_tail v
  continuous_toFun := Continuous.finCons (A := fun _ : Fin (m + 1) => ℝ) continuous_snd continuous_fst
  continuous_invFun := (continuous_pi (fun _ => continuous_apply _)).prodMk (continuous_apply 0)

def realCoordinatesReindex {α β : Type*} (e : α ≃ β) : (α → ℝ) ≃ₜ (β → ℝ) where
  toFun f b := f (e.symm b)
  invFun g a := g (e a)
  left_inv f := by funext a; simp
  right_inv g := by funext b; simp
  continuous_toFun := continuous_pi (fun _ => continuous_apply _)
  continuous_invFun := continuous_pi (fun _ => continuous_apply _)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LexicographicRootWeights
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

def lexicographicNeutralRaw {n : ℕ} (a b i : Fin n) : ℝ :=
  if i = a then (b.val : ℝ) else (i.val : ℝ)

lemma lexicographicNeutralRaw_equal {n : ℕ} {a b : Fin n} (hab : a < b) :
    lexicographicNeutralRaw a b a = lexicographicNeutralRaw a b b := by
  simp [lexicographicNeutralRaw, ne_of_gt hab]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_MatrixLogLength
attribute [-instance] _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.integralGroup_discrete _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space
attribute [-simp] _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.euclideanRowBasis_apply _root_.OAI.PrimeDegreePackets.integerRowEquiv_val _root_.OAI.PrimeDegreePackets.pointLattice_mk _root_.OAI.PrimeDegreePackets.rowBasis_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete subadditive length on the real special linear group

The logarithmic matrix length is symmetric under inversion and controls
small matrix displacements. It is used to construct observables with
uniform control along right root translations.
-/

noncomputable section
open Matrix Set Filter
open scoped Matrix.Norms.Operator Topology
namespace DukePrimeDegree
open PrimeDegreePackets

def matrixLogLength {n : ℕ} (g : G n) : ℝ :=
  Real.log (1+‖g.val-1‖) + Real.log (1+‖(g⁻¹).val-1‖)

@[simp] lemma matrixLogLength_one (n : ℕ) : matrixLogLength (1:G n) = 0 := by
  simp [matrixLogLength]

@[simp] lemma matrixLogLength_inv {n : ℕ} (g : G n) : matrixLogLength g⁻¹ = matrixLogLength g := by
  simp only [matrixLogLength,inv_inv,add_comm]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_Dedekind_Basic
attribute [-instance] _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Hilbert ramification theory: Dedekind-domain layer

This file manages the Dedekind-domain part of Hilbert ramification theory in
prime-decomposition theory.

The implementation uses mathlib's ramification/inertia theorems where those
are already the source proof, but the decomposition/inertia/residue-action
interface is proved here: membership criteria, residue-action formula,
normality of inertia in the decomposition group, exactness, and quotient form.
-/

noncomputable section

namespace HilbertRamification
namespace Dedekind

open scoped Pointwise
open Algebra Module

attribute [local instance] Ideal.Quotient.field

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The decomposition and inertia definition:
the decomposition group of a prime ideal. -/
abbrev decompositionGroup
    (P : Ideal B) (G : Type*) [Group G] [MulSemiringAction G B] :
    Subgroup G :=
  MulAction.stabilizer G P

/-- Membership in the decomposition group is exactly stabilization of the prime
ideal. -/
@[simp]
theorem mem_decompositionGroup_iff
    {P : Ideal B} {G : Type*} [Group G] [MulSemiringAction G B] {σ : G} :
    σ ∈ decompositionGroup P G ↔ σ • P = P :=
  Iff.rfl

/-- The inertia-field definition:
the inertia group of a prime ideal. -/
abbrev inertiaGroup
    (P : Ideal B) (G : Type*) [Group G] [MulSemiringAction G B] :
    Subgroup G :=
  P.toAddSubgroup.inertia G

/-- Membership in the inertia group is trivial action on the residue ring. -/
@[simp]
theorem mem_inertiaGroup_iff
    {P : Ideal B} {G : Type*} [Group G] [MulSemiringAction G B] {σ : G} :
    σ ∈ inertiaGroup P G ↔ ∀ x : B, σ • x - x ∈ P :=
  Iff.rfl

/-- prime-decomposition theory:
the residue-field action of the decomposition group. -/
abbrev residueStabilizerHom
    (p : Ideal A) (P : Ideal B) [P.LiesOver p]
    (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B] :
    decompositionGroup P G →* (B ⧸ P) ≃ₐ[A ⧸ p] B ⧸ P :=
  Ideal.Quotient.stabilizerHom P p G

/-- prime-decomposition theory:
the residue action is concretely `a mod P ↦ σ a mod P`. -/
@[simp] theorem residueStabilizerHom_apply
    (p : Ideal A) (P : Ideal B) [P.LiesOver p]
    (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (σ : decompositionGroup P G) (b : B) :
    residueStabilizerHom p P G σ b = ↑(σ • b) :=
  Ideal.Quotient.stabilizerHom_apply P p G σ b

/-- Inertia is normal inside the decomposition group.  The proof is the
intrinsic conjugation argument: if `σ` is trivial mod `P`, then
`τ σ τ⁻¹` is also trivial mod `P` because `τ` stabilizes `P`. -/
instance inertiaSubgroupOfDecomposition_normal
    (P : Ideal B) (G : Type*) [Group G] [MulSemiringAction G B] :
    ((inertiaGroup P G).subgroupOf (decompositionGroup P G)).Normal := by
  refine ⟨?_⟩
  intro σ hσ τ
  rw [Subgroup.mem_subgroupOf] at hσ ⊢
  rw [mem_inertiaGroup_iff] at hσ ⊢
  intro x
  let y : B := (σ : G) • ((τ : G)⁻¹ • x) - ((τ : G)⁻¹ • x)
  have hy : y ∈ P := hσ ((τ : G)⁻¹ • x)
  have hτy : (τ : G) • y ∈ (τ : G) • P :=
    Ideal.smul_mem_pointwise_smul (τ : G) y P hy
  rw [τ.property] at hτy
  simpa [y, smul_sub, mul_smul, inv_smul_smul] using hτy

/-- prime-decomposition theory: in the Galois case the ramification index is
independent of the prime above `p`. -/
theorem dedekindRamification_ramificationIdx_eq
    (p : Ideal A) (P Q : Ideal B)
    [P.IsPrime] [P.LiesOver p] [Q.IsPrime] [Q.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    P.ramificationIdx A = Q.ramificationIdx A := by
  exact Ideal.ramificationIdx_eq_of_isGaloisGroup p P Q G



/-- prime-decomposition theory:
the kernel of the residue action is the inertia group. -/
theorem dedekindRamification_residueAction_ker
    (p : Ideal A) (P : Ideal B) [P.LiesOver p]
    (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B] :
    MonoidHom.ker (residueStabilizerHom p P G) =
      (inertiaGroup P G).subgroupOf (decompositionGroup P G) := by
  exact Ideal.Quotient.ker_stabilizerHom P p G

/-- prime-decomposition theory:
for a finite invariant Galois action, the residue action is surjective. -/
theorem dedekindRamification_residueAction_surjective
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] :
    Function.Surjective (residueStabilizerHom p P G) := by
  exact Ideal.Quotient.stabilizerHom_surjective G p P

/-- The localization and decomposition comparison gives:
the quotient of the decomposition group by inertia is the residue Galois group.
-/
def dedekindRamification_decompositionQuotientInertiaEquivResidueGalois
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] :
    decompositionGroup P G ⧸
        (inertiaGroup P G).subgroupOf (decompositionGroup P G) ≃*
      (B ⧸ P) ≃ₐ[A ⧸ p] B ⧸ P :=
  (QuotientGroup.quotientMulEquivOfEq
      (dedekindRamification_residueAction_ker p P G).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (residueStabilizerHom p P G)
      (dedekindRamification_residueAction_surjective p P G))

/-- prime-decomposition theory, Galois fundamental identity:
`r * e * f = |G|`, with `e` and `f` independent of the chosen prime above `p`.
-/
theorem dedekindRamification_galois_fundamental_identity
    [IsDedekindDomain A] (p : Ideal A) [p.IsMaximal] (_hpb : p ≠ ⊥)
    (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.Finite A B] [IsTorsionFree A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    (p.primesOver B).ncard *
        (Ideal.ramificationIdxIn p B * Ideal.inertiaDegIn p B) =
      Nat.card G := by
  exact Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B G

/-- The prime-decomposition tower identity:
orbit-stabilizer for the action on primes above `p`,
`r * #G_P = #G`. -/
theorem dedekindRamification_ncard_primesOver_mul_decomposition_card
    (p : Ideal A) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    (p.primesOver B).ncard * Nat.card (decompositionGroup P G) =
      Nat.card G := by
  rw [← IsInvariant.orbit_eq_primesOver A B G p P]
  simpa [decompositionGroup] using
    Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)

/-- The prime-decomposition tower identity:
the decomposition group has cardinality `e * f`. -/
theorem dedekindRamification_decomposition_card_eq_ramificationIdxIn_mul_inertiaDegIn
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
    [IsTorsionFree A B]
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    Nat.card (decompositionGroup P G) =
      Ideal.ramificationIdxIn p B * Ideal.inertiaDegIn p B := by
  have hdec :=
    dedekindRamification_ncard_primesOver_mul_decomposition_card
      (A := A) (B := B) p P G
  have hfund :=
    dedekindRamification_galois_fundamental_identity
      (A := A) p hp B G
  exact
    Nat.mul_left_cancel
      (Nat.pos_of_ne_zero (IsDedekindDomain.primesOver_ncard_ne_zero p B))
      (hdec.trans hfund.symm)



/-- Prime-decomposition statement:
the quotient of the decomposition group by inertia has cardinality equal to
the inertia degree. -/
theorem dedekindRamification_decompositionQuotientInertia_card_eq_inertiaDeg
    (p : Ideal A) [p.IsMaximal]
    (P : Ideal B) [P.IsPrime] [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
  Nat.card
        (decompositionGroup P G ⧸
          (inertiaGroup P G).subgroupOf (decompositionGroup P G)) =
      P.inertiaDeg A := by
  have h : IsGalois (A ⧸ p) (B ⧸ P) :=
    isGalois_iff.mpr ⟨inferInstance, Ideal.Quotient.normal (A := A) G p P⟩
  let : Module.Finite (A ⧸ p) (B ⧸ P) := Ideal.Quotient.finite_of_isInvariant G p P
  let : FiniteDimensional (A ⧸ p) (B ⧸ P) := IsGalois.finiteDimensional_of_finite
    (F := A ⧸ p) (E := B ⧸ P)
  calc
    Nat.card
        (decompositionGroup P G ⧸
          (inertiaGroup P G).subgroupOf (decompositionGroup P G)) =
        Nat.card ((B ⧸ P) ≃ₐ[A ⧸ p] B ⧸ P) := by
      exact
        Nat.card_congr
          (dedekindRamification_decompositionQuotientInertiaEquivResidueGalois
            (A := A) (B := B) p P G).toEquiv
    _ = Module.finrank (A ⧸ p) (B ⧸ P) := by
      simpa using (IsGalois.card_aut_eq_finrank (F := A ⧸ p) (E := B ⧸ P))
    _ = P.inertiaDeg A := by
      rw [Ideal.inertiaDeg_eq_of_isMaximal p P]

/-- Prime-decomposition statement:
the quotient cardinality is the Galois-invariant inertia degree `f`. -/
theorem dedekindRamification_decompositionQuotientInertia_card_eq_inertiaDegIn
    (p : Ideal A) [p.IsMaximal]
    (P : Ideal B) [P.IsPrime] [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    Nat.card
        (decompositionGroup P G ⧸
          (inertiaGroup P G).subgroupOf (decompositionGroup P G)) =
      Ideal.inertiaDegIn p B := by
  rw [dedekindRamification_decompositionQuotientInertia_card_eq_inertiaDeg
    (A := A) (B := B) p P G]
  exact (Ideal.inertiaDegIn_eq_inertiaDeg p P G).symm

/-- Prime-decomposition statement:
`#G_P = #(G_P/I_P) * #I_P` for the exact residue sequence. -/
theorem dedekindRamification_decomposition_card_eq_quotient_card_mul_inertia_card
    (P : Ideal B) (G : Type*) [Group G] [MulSemiringAction G B] :
    Nat.card (decompositionGroup P G) =
      Nat.card
          (decompositionGroup P G ⧸
            (inertiaGroup P G).subgroupOf (decompositionGroup P G)) *
        Nat.card (inertiaGroup P G) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((inertiaGroup P G).subgroupOf (decompositionGroup P G))]
  congr 1
  exact
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (Ideal.inertia_le_stabilizer (M := G) P)).toEquiv

/-- Prime-decomposition statement:
`#G_P = #I_P * f`, with `f` the Galois-invariant inertia degree. -/
theorem dedekindRamification_decomposition_card_eq_inertia_card_mul_inertiaDegIn
    (p : Ideal A) [p.IsMaximal]
    (P : Ideal B) [P.IsPrime] [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    Nat.card (decompositionGroup P G) =
      Nat.card (inertiaGroup P G) * Ideal.inertiaDegIn p B := by
  rw [dedekindRamification_decomposition_card_eq_quotient_card_mul_inertia_card
    (B := B) P G,
    dedekindRamification_decompositionQuotientInertia_card_eq_inertiaDegIn
      (A := A) (B := B) p P G,
    mul_comm]


/-- prime-decomposition theory: the inertia subgroup has cardinality equal to the
Galois ramification index. -/
theorem dedekindRamification_inertia_card_eq_ramificationIdxIn
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
    [IsTorsionFree A B]
    (p : Ideal A) (P : Ideal B) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] (hp : p ≠ ⊥) :
    Nat.card (P.toAddSubgroup.inertia G) = Ideal.ramificationIdxIn p B := by
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  let : p.IsMaximal := Ideal.IsMaximal.of_isMaximal_liesOver P p
  have hdecomp_inertia :=
    dedekindRamification_decomposition_card_eq_inertia_card_mul_inertiaDegIn
      (A := A) (B := B) p P G
  have hdecomp_ramification :=
    dedekindRamification_decomposition_card_eq_ramificationIdxIn_mul_inertiaDegIn
      (A := A) (B := B) p hp P G
  have hinertiaDeg_pos : 0 < Ideal.inertiaDegIn p B := by
    rw [Ideal.inertiaDegIn_eq_inertiaDeg p P G]
    exact P.inertiaDeg_pos A
  apply Nat.mul_left_cancel hinertiaDeg_pos
  calc
    Ideal.inertiaDegIn p B * Nat.card (P.toAddSubgroup.inertia G) =
        Nat.card (P.toAddSubgroup.inertia G) * Ideal.inertiaDegIn p B := by
      rw [mul_comm]
    _ = Nat.card (decompositionGroup P G) := hdecomp_inertia.symm
    _ = Ideal.ramificationIdxIn p B * Ideal.inertiaDegIn p B :=
      hdecomp_ramification
    _ = Ideal.inertiaDegIn p B * Ideal.ramificationIdxIn p B := by
      rw [mul_comm]

end Dedekind
end HilbertRamification
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_BigHilbertClassFieldNaturality
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Naturality of the big Hilbert class field

An equivalence of number fields preserves both finite integrality and
positivity at the real infinite places.  Consequently the actual
idele-class transport carries the big-Hilbert norm subgroup exactly onto
the corresponding subgroup of the target field.  This gives canonical
transport on the big-Hilbert reciprocity quotient and on the narrow class
group, with formulas on genuine idele representatives.
-/

open scoped NumberField NumberField.LiesOver Classical TensorProduct

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

variable
    {K M : Type*}
    [Field K] [NumberField K]
    [Field M] [NumberField M]

noncomputable def infinitePlaceCompletionCongrHom
    (e : K ≃ₐ[ℚ] M)
    (W : InfinitePlace M) :
    (W.comap e.toRingHom).Completion →+*
      W.Completion := by
  letI : Algebra K M :=
    e.toRingHom.toAlgebra
  let v :=
    W.comap e.toRingHom
  letI : W.1.LiesOver v.1 :=
    ⟨rfl⟩
  exact
    NumberField.LiesOver.completionMap
      (v := v) (w := W)

theorem infinitePlaceCompletionCongrHom_algebraMap
    (e : K ≃ₐ[ℚ] M)
    (W : InfinitePlace M)
    (x : K) :
    infinitePlaceCompletionCongrHom e W
        (algebraMap K (W.comap e.toRingHom).Completion x) =
      algebraMap M W.Completion (e x) := by
  let : Algebra K M :=
    e.toRingHom.toAlgebra
  let v : InfinitePlace K :=
    W.comap e.toRingHom
  let : W.1.LiesOver v.1 :=
    ⟨rfl⟩
  change
    NumberField.LiesOver.completionMap
        (v := v) (w := W)
        (algebraMap K v.Completion x) =
      algebraMap M W.Completion
        (algebraMap K M x)
  have hx :
      algebraMap K v.Completion x =
        ((WithAbs.toAbs v.1 x : WithAbs v.1) :
          v.Completion) :=
    rfl
  rw [hx,
    NumberField.LiesOver.completionMap_coe
      (v := v) (w := W)]
  apply InfinitePlace.Completion.ext
  rw [
    InfinitePlace.Completion.algebraMap_toCompletion,
    UniformSpace.Completion.algebraMap_def]
  simp only [WithAbs.algebraMap_left_apply,
    WithAbs.algebraMap_right_apply,
    Algebra.algebraMap_self_apply]

theorem
    infinitePlaceCompletionCongrHom_extensionEmbeddingOfIsReal
    (e : K ≃ₐ[ℚ] M)
    (W : InfinitePlace M)
    (hW : W.IsReal)
    (x : (W.comap e.toRingHom).Completion) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal hW
        (infinitePlaceCompletionCongrHom e W x) =
      InfinitePlace.Completion.extensionEmbeddingOfIsReal
        (hW.comap e.toRingHom) x := by
  let : Algebra K M :=
    e.toRingHom.toAlgebra
  let v :=
    W.comap e.toRingHom
  let : W.1.LiesOver v.1 :=
    ⟨rfl⟩
  let :
      NumberField.ComplexEmbedding.LiesOver
        (InfinitePlace.Completion.extensionEmbedding W)
        (InfinitePlace.Completion.extensionEmbedding v) :=
    InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal
      W (hW.comap e.toRingHom)
  have hComplex :
      InfinitePlace.Completion.extensionEmbedding W
          (NumberField.LiesOver.completionMap
            (v := v) (w := W) x) =
        InfinitePlace.Completion.extensionEmbedding v x := by
    exact
      InfinitePlace.Completion.liesOver_extensionEmbedding_apply
        (v := v) (w := W)
  apply Complex.ofReal_injective
  simpa only [
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply,
    infinitePlaceCompletionCongrHom] using hComplex

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_GroupTheory_PowerIndex
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Power indices in commutative groups

Reusable kernel, quotient, product, and additive-transport formulas for
`n`-th powers in commutative groups.  The basic power map and its image and
kernel are mathlib's `powMonoidHom`, `MonoidHom.range`, and `MonoidHom.ker`.
-/

noncomputable section

namespace LocalFieldTheory

open scoped Int

section NthPowers

universe uG uH uU

variable (G : Type uG) (H : Type uH) (U : Type uU)
variable [CommGroup G] [CommGroup H] [CommGroup U]


/-- The identity element is an `n`-th power and hence lies in the range of the power endomorphism.
The identity element is an `n`-th power and hence lies in the range of the power endomorphism. -/
@[simp]
theorem powMonoidHom_range_one_mem (n : ℕ) :
    (1 : G) ∈ (powMonoidHom n : G →* G).range := by
  rw [MonoidHom.mem_range]
  exact ⟨1, one_pow n⟩

end NthPowers

end LocalFieldTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_SUnitPowerQuotient
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
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

/-- One roots-of-unity coordinate together with `r` free coordinates
is the product of `r + 1` copies of `ZMod n`, in multiplicative
notation. -/
noncomputable def multiplicativeZModProductEquivPiSucc
    (n r : ℕ) :
    Multiplicative (ZMod n) ×
        Multiplicative (Fin r → ZMod n) ≃*
      (Fin (r + 1) → Multiplicative (ZMod n)) where
  toFun x i :=
    Fin.cases x.1
      (fun j => Multiplicative.ofAdd (x.2.toAdd j)) i
  invFun f :=
    (f 0,
      Multiplicative.ofAdd
        (fun j => (f j.succ).toAdd))
  left_inv := by
    rintro ⟨a, b⟩
    apply Prod.ext
    · rfl
    · apply Multiplicative.toAdd.injective
      funext j
      rfl
  right_inv := by
    intro f
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  map_mul' := by
    intro x y
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_ValuationSubringUnits_CyclicValueGroup
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Cyclic value groups and normalized uniformizers

This file supplies the ordered-group and rank-one facts used for actual
multiplicative valuation ranges, together with normalized uniformizer results
for `ℤᵐ⁰`-valued valuations.
-/

noncomputable section

universe u x

open WithZero
open scoped NNReal Valued WithZero

namespace LocalFieldTheory.DiscreteValuationField

namespace WithZeroValuation

variable {R : Type u}
variable {Gamma : Type x} [LinearOrderedCommGroupWithZero Gamma]

/-- A nontrivial `ℤᵐ⁰`-valued valuation is rank one via the standard strictly
monotone embedding `ℤᵐ⁰ -> ℝ≥0`.  This is kept as an explicit definition, not
a global instance, so later finite-dimensional closedness arguments can opt in
without changing typeclass search everywhere. -/
@[implicit_reducible]
noncomputable def rankOne
    [Ring R]
    (v : _root_.Valuation R ℤᵐ⁰) [v.IsNontrivial] : v.RankOne where
  hom' :=
    (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0)).comp
      MonoidWithZeroHom.ValueGroup₀.embedding
  strictMono' :=
    (WithZeroMulInt.toNNReal_strictMono
      (by norm_num : (1 : ℝ≥0) < 2)).comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
  exists_val_nontrivial :=
    _root_.Valuation.IsNontrivial.exists_val_nontrivial (v := v)

open LinearOrderedCommGroup


end WithZeroValuation
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_SUnitKummerNormCore
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The full S-unit Kummer norm core

Starting from a prescribed finite set of finite places, we enlarge it by
a fixed idelic support and by a chosen support of the exponent.  For this
enlarged set, a principal idele satisfies the local power conditions exactly
when it is the power of an `S`-unit.  Consequently the associated idele-class
power quotient has the same cardinality as the Galois group of the full
`S`-unit Kummer extension.

These are the two concrete cardinal ingredients in the class-field existence
argument.
-/

open scoped NumberField Classical BigOperators

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain
open KummerTheory

variable {K : Type} [Field K] [NumberField K]

/-- If `K` contains the `n`-th roots of unity and `n > 1`, then either
`n` is even or `K` has no real infinite places.  This is exactly the
archimedean condition needed to place all local `n`-th powers in the
infinite norm subgroup. -/
theorem even_or_no_realInfinitePlace_of_primitiveRoots
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hn : 1 < (n : ℕ)) :
    Even (n : ℕ) ∨
      ∀ w : InfinitePlace K, ¬ w.IsReal := by
  by_cases hnEven : Even (n : ℕ)
  · exact Or.inl hnEven
  · refine Or.inr ?_
    have hnNeTwo : (n : ℕ) ≠ 2 := by
      intro hnTwo
      apply hnEven
      rw [hnTwo]
      exact ⟨1, by omega⟩
    have hnLarge : 2 < (n : ℕ) := by
      omega
    obtain ⟨zeta, hzeta⟩ := hmu
    have hzetaPrimitive :
        IsPrimitiveRoot zeta (n : ℕ) :=
      (mem_primitiveRoots n.pos).mp hzeta
    have hRealZero :
        InfinitePlace.nrRealPlaces K = 0 :=
      InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt
        hnLarge hzetaPrimitive
    intro w hwReal
    have hRealPos :
        0 < InfinitePlace.nrRealPlaces K :=
      Fintype.card_pos_iff.mpr ⟨⟨w, hwReal⟩⟩
    omega

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalPrimeFactorization
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Prime factorization of a nonzero rational number

This file records the elementary rational factorization needed for the
principal-idele calculation over `ℚ`.  At a fixed rational prime `p`, removing
the `p`-power from `x : ℚˣ` leaves the sign of `x` times the finite product of
the powers of all primes different from `p`.

The last declarations package rational `p`-adic units as units of `ℤ_[p]` and
identify the reduction of a natural unit modulo `p ^ k`.
-/

open scoped BigOperators Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

local instance localInst_rda812e_1 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩
/-- The successor of `p` is a `p`-adic unit. -/
theorem padicValRat_rationalPrime_succ
    (p : Nat.Primes) :
    padicValRat p.1 (((p.1 + 1 : ℕ) : ℚ)) = 0 := by
  have hnot :
      ¬ p.1 ∣ p.1 + 1 :=
    p.2.coprime_iff_not_dvd.mp
      (Nat.coprime_self_add_right.mpr
        (Nat.coprime_one_right p.1))
  rw [padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd hnot]
  norm_num

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_Dedekind_OrbitCardinality
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Hilbert ramification theory: prime-decomposition cardinalities

This file records the parts of the prime-decomposition tower identity that are
already available from the Dedekind-domain Galois action and mathlib's
ramification/inertia API.
-/

noncomputable section

namespace HilbertRamification
namespace Dedekind

open scoped Pointwise
open Algebra Module

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The separable-residue cardinality relation:
when the residue extension is separable, the inertia group has cardinality
equal to the ramification index of the chosen prime. -/
theorem inertia_card_eq_ramificationIdx
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
    [IsTorsionFree A B]
    (p : Ideal A) (P : Ideal B) [P.LiesOver p] [P.IsPrime] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] (hp : p ≠ ⊥) :
    Nat.card (inertiaGroup P G) =
      P.ramificationIdx A := by
  rw [dedekindRamification_inertia_card_eq_ramificationIdxIn
    (A := A) (B := B) p P G hp]
  exact Ideal.ramificationIdxIn_eq_ramificationIdx p P G

end Dedekind
end HilbertRamification
end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_Dedekind_CompositumUnramified
attribute [-instance] _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

/-- If a finite family of normal simple intermediate fields generates a
finite Galois number-field extension and the inertia at a prime restricts
trivially to every member of the family, then the inertia of the full
extension is trivial.  This is the finite-radical form of the compositum
argument used for the full `S`-unit Kummer extension. -/
theorem inertiaGroup_eq_bot_of_finset_adjoin_eq_top
    {K M : Type*}
    [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (T : Finset M)
    (Q : Ideal (𝓞 M))
    (hnormal :
      ∀ x : M, x ∈ T →
        Normal K (IntermediateField.adjoin K {x}))
    (hI :
      ∀ (x : M) (_ : x ∈ T),
        inertiaGroup
            (Q.under
              (𝓞 (IntermediateField.adjoin K {x})))
            Gal((IntermediateField.adjoin K {x})/K) =
          ⊥)
    (hadjoin :
      IntermediateField.adjoin K (T : Set M) = ⊤) :
    inertiaGroup Q Gal(M/K) = ⊥ := by
  apply le_antisymm
  · intro sigma hsigma
    have hfix :
        ∀ x : M, x ∈ T → sigma x = x := by
      intro x hx
      let B : IntermediateField K M :=
        IntermediateField.adjoin K {x}
      let : Normal K B := hnormal x hx
      let rB : Gal(M/K) →* Gal(B/K) :=
        AlgEquiv.restrictNormalHom B
      have hsigmaB :
          rB sigma ∈
            inertiaGroup (Q.under (𝓞 B)) Gal(B/K) := by
        rw [mem_inertiaGroup_iff]
        intro y
        change
          algebraMap (𝓞 B) (𝓞 M)
              (rB sigma • y - y) ∈ Q
        rw [map_sub]
        have hcompat :
            algebraMap (𝓞 B) (𝓞 M) (rB sigma • y) =
              sigma • algebraMap (𝓞 B) (𝓞 M) y := by
          apply RingOfIntegers.coe_injective
          change
            algebraMap B M
                (sigma.restrictNormal B y.1) =
              sigma (algebraMap B M y.1)
          exact
            AlgEquiv.restrictNormal_commutes sigma B y.1
        rw [hcompat]
        exact
          (mem_inertiaGroup_iff.mp hsigma)
            (algebraMap (𝓞 B) (𝓞 M) y)
      have hsigmaBone : rB sigma = 1 := by
        rw [← Subgroup.mem_bot, ← hI x hx]
        exact hsigmaB
      have hxB : x ∈ B :=
        IntermediateField.subset_adjoin K {x}
          (Set.mem_singleton x)
      calc
        sigma x =
            algebraMap B M
              ((rB sigma) ⟨x, hxB⟩) := by
          change
            sigma x =
              algebraMap B M
                (sigma.restrictNormal B ⟨x, hxB⟩)
          exact
            (AlgEquiv.restrictNormal_commutes
              sigma B ⟨x, hxB⟩).symm
        _ =
            algebraMap B M
              ((1 : Gal(B/K)) ⟨x, hxB⟩) :=
          congrArg
            (fun tau : Gal(B/K) =>
              algebraMap B M (tau ⟨x, hxB⟩))
            hsigmaBone
        _ = x := rfl
    have hmem :
        sigma ∈
          (IntermediateField.adjoin K
            (T : Set M)).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      induction hx using IntermediateField.adjoin_induction with
      | mem x hx =>
          exact hfix x hx
      | algebraMap a =>
          exact sigma.commutes a
      | add x y hx hy ihx ihy =>
          rw [map_add, ihx, ihy]
      | inv x hx ihx =>
          rw [map_inv₀, ihx]
      | mul x y hx hy ihx ihy =>
          rw [map_mul, ihx, ihy]
    simpa [hadjoin] using hmem
  · exact bot_le

/-- For a finite Galois extension of number fields, ramification index
one at a prime forces the corresponding inertia group to be trivial.
The residue extension is separable because the residue field of a number
field is finite. -/
theorem inertiaGroup_eq_bot_of_ramificationIdx_eq_one
    {K M : Type*}
    [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (p : Ideal (𝓞 K)) (P : Ideal (𝓞 M))
    [p.IsPrime] [P.IsPrime] [P.IsMaximal] [P.LiesOver p]
    (hp0 : p ≠ ⊥)
    (he : P.ramificationIdx (𝓞 K) = 1) :
    inertiaGroup P Gal(M/K) = ⊥ := by
  let : p.IsMaximal :=
    (inferInstance : p.IsPrime).isMaximal hp0
  let : Finite ((𝓞 K) ⧸ p) :=
    Ideal.finiteQuotientOfFreeOfNeBot p hp0
  let : PerfectField ((𝓞 K) ⧸ p) :=
    PerfectField.ofFinite
  let : Algebra.IsSeparable
      ((𝓞 K) ⧸ p) ((𝓞 M) ⧸ P) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  rw [← Subgroup.card_eq_one,
    inertia_card_eq_ramificationIdx
      (A := 𝓞 K) (B := 𝓞 M) p P Gal(M/K) hp0]
  exact he

end HilbertRamification.Dedekind
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitKummerUnramified
attribute [-instance] _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Unramifiedness of the full `S`-unit Kummer extension

This file supplies the ramification input in the existence proof for the
global norm topology.  Every defining root of

`K(√[n]{Kˢ}) / K`

is first rescaled to the root of an actual `S`-unit.  Its simple
intermediate field is then identified with the chosen simple Kummer
extension attached to that unit.  The finite set of such simple fields
generating the full extension is used to kill the full inertia group away
from `S`.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain
open HilbertRamification
open HilbertRamification.Dedekind

noncomputable section

namespace KummerTheory

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
/-- Adjoining an element internally to an intermediate field gives the
same extension as adjoining its ambient value. -/
noncomputable def adjoinSubtypeEquivAmbientAdjoin
    {Omega : Type} [Field Omega] [Algebra K Omega]
    (E : IntermediateField K Omega) (x : E) :
    IntermediateField.adjoin K {x} ≃ₐ[K]
      IntermediateField.adjoin K {(x : Omega)} := by
  exact
    (IntermediateField.equivMap
        (IntermediateField.adjoin K {x}) E.val).trans
      (IntermediateField.equivOfEq
        (by
          rw [IntermediateField.adjoin_map,
            Set.image_singleton]
          rfl))

omit [NumberField K] in
/-- Equality of singleton adjoins in an ambient field descends to equality
of the corresponding singleton adjoins inside an intermediate field. -/
theorem adjoin_subtype_eq_of_adjoin_ambient_eq
    {Omega : Type} [Field Omega] [Algebra K Omega]
    (E : IntermediateField K Omega) (x y : E)
    (h :
      IntermediateField.adjoin K {(x : Omega)} =
        IntermediateField.adjoin K {(y : Omega)}) :
    IntermediateField.adjoin K {x} =
      IntermediateField.adjoin K {y} := by
  apply IntermediateField.map_injective E.val
  calc
    (IntermediateField.adjoin K {x}).map E.val =
        IntermediateField.adjoin K {E.val x} := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]
    _ = IntermediateField.adjoin K {E.val y} := h
    _ = (IntermediateField.adjoin K {y}).map E.val := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_LubinTateApplication_StandardSubgroupIndex
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The canonical standard subgroup index

For the topology-first nonarchimedean local field `K`, the canonical
Lubin--Tate uniformizer and the `(n + 1)`-st principal units generate a
subgroup of `Kˣ` of index

`(Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n`.

The proof passes from field units to integer units, transports the latter
through the canonical packaged local-field equivalence, and then uses the
finite standard Lubin--Tate unit-parameter count.
-/

noncomputable section

open scoped ValuativeRel

namespace LubinTate

open LocalFieldTheory
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A finite-index subgroup contained in another subgroup with the same
index is already equal to it.  The nonzero-index hypothesis excludes the
infinite-index convention `index = 0`. -/
theorem subgroup_eq_of_le_of_index_eq_of_ne_zero
    {G : Type*} [Group G] {H N : Subgroup G}
    (hHN : H ≤ N) (hindex : H.index = N.index)
    (hindex_ne : H.index ≠ 0) :
    H = N := by
  let _ : H.FiniteIndex := ⟨hindex_ne⟩
  apply le_antisymm hHN
  by_contra hNH
  have hne : H ≠ N := by
    intro heq
    apply hNH
    rw [heq]
  have hstrict : H < N := lt_of_le_of_ne hHN hne
  have hi := Subgroup.index_strictAnti hstrict
  rw [hindex] at hi
  exact Nat.lt_irrefl _ hi

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_CyclotomicKummerNormDescent
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Cyclotomic descent for full S-unit Kummer norms

This file implements the roots-of-unity descent in the existence proof of
global class field theory.  Starting from a finite seed of finite places of
`K`, it enlarges the seed just enough that its full inverse image in
`CyclotomicField n K` is a chosen Kummer norm support.  Thus the full
S-unit Kummer extension over the cyclotomic field has its concrete norm
subgroup described by Kummer theory, while the support is still exactly a
full inverse image and hence descends through the cyclotomic norm.

The final normal-closure step turns the resulting finite extension of `K`
into a genuine finite Galois extension without enlarging its norm subgroup.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

variable {K : Type} [Field K] [NumberField K]

local instance cyclotomicKummerNormDescent_neZero
    (n : ℕ+) : NeZero (n : ℕ) :=
  ⟨n.ne_zero⟩

noncomputable local instance
    cyclotomicKummerNormDescent_cyclotomicFiniteDimensional
    (n : ℕ+) :
    FiniteDimensional K (CyclotomicField (n : ℕ) K) :=
  IsCyclotomicExtension.finiteDimensional
    {(n : ℕ)} K (CyclotomicField (n : ℕ) K)

noncomputable local instance
    cyclotomicKummerNormDescent_cyclotomicIsGalois_rda812e_1
    (n : ℕ+) :
    IsGalois K (CyclotomicField (n : ℕ) K) :=
  IsCyclotomicExtension.isGalois
    {(n : ℕ)} K (CyclotomicField (n : ℕ) K)
theorem cyclotomicKummerNormDescent_primitiveRoots_nonempty
    (n : ℕ+) :
    (primitiveRoots (n : ℕ)
      (CyclotomicField (n : ℕ) K)).Nonempty := by
  obtain ⟨ζ, hζ⟩ :=
    (CyclotomicField.isCyclotomicExtension (n : ℕ) K).exists_isPrimitiveRoot
      (Set.mem_singleton (n : ℕ)) n.ne_zero
  exact ⟨ζ, (mem_primitiveRoots n.pos).2 hζ⟩

theorem cyclotomicKummerNormDescent_natCast_ne_zero
    (n : ℕ+) :
    ((n : ℕ) : CyclotomicField (n : ℕ) K) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr n.ne_zero

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_RationalComplexification
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

/-- The complex number `I` is a primitive fourth root of unity. -/
theorem complexI_isPrimitiveRoot_four :
    IsPrimitiveRoot Complex.I 4 := by
  convert Complex.isPrimitiveRoot_exp 4 (by norm_num) using 1
  all_goals try with_reducible_and_instances rfl
  calc
    Complex.I =
        Complex.exp ((Real.pi : ℂ) / 2 * Complex.I) :=
      Complex.exp_pi_div_two_mul_I.symm
    _ = Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I / (4 : ℂ)) := by
      congr 1
      ring

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_InfinitePlaceOverfield
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

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

/-- The field range of a complex embedding is preserved by complex
conjugation when a relative automorphism realizes that conjugation. -/
theorem complexEmbeddingFieldRange_map_complexConjugation
    (φ : L →+* ℂ)
    (σ : L ≃ₐ[K] L)
    (hσ : NumberField.ComplexEmbedding.IsConj φ σ) :
    φ.toRatAlgHom.fieldRange.map
        (Complex.conjAe.restrictScalars ℚ).toAlgHom =
      φ.toRatAlgHom.fieldRange := by
  rw [AlgHom.map_fieldRange]
  apply SetLike.ext
  intro z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨σ x, ?_⟩
    exact hσ.eq x
  · rintro ⟨x, rfl⟩
    refine ⟨σ.symm x, ?_⟩
    calc
      (Complex.conjAe.restrictScalars ℚ)
          (φ (σ.symm x)) =
          φ (σ (σ.symm x)) :=
        (hσ.eq (σ.symm x)).symm
      _ = φ x := by rw [σ.apply_symm_apply]

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_OverextensionArtin
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Artin reciprocity on the ramified infinite-place overextension

This module proves principal-idele triviality, descends the chosen Artin
product to the norm quotient, and identifies it with global reciprocity.
-/

open scoped Classical IsMulCommutative
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

section ComplexConjugationOverextension

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

section

noncomputable def quotientLiftData
    {A B : Type} [CommGroup A] [Group B]
    (N : Subgroup A) (f : A →* B)
    (hN : ∀ x, x ∈ N → f x = 1) :
    {g : A ⧸ N →* B //
      ∀ x, g (QuotientGroup.mk' N x) = f x} := by
  refine ⟨QuotientGroup.lift N f hN, ?_⟩
  intro x
  exact QuotientGroup.lift_mk _ _ _

end

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_GlobalNormResidueNaturality
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Naturality of the global norm-residue symbol

This file records the same-base restriction specialization of abstract
norm-residue naturality in the rational absolute class formation.  All
closed subgroups remain in one fixed separable-closure ambient, so the
statement is directly usable by fixed-field overextension arguments.
-/

open scoped IsMulCommutative

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open GlobalClassFields
open KummerTheory

universe u

/-- Rebundling an element along equality of closed subgroups preserves its
underlying ambient group element. -/
theorem closedSubgroupCongr_apply_val
    {G : Type u} [Group G] [TopologicalSpace G]
    {H H' : ClosedSubgroup G}
    (hH : H = H') (σ : H.toSubgroup) :
    (((MulEquiv.subgroupCongr
        (congrArg ClosedSubgroup.toSubgroup hH)) σ).1 : G) = σ.1 := by
  cases hH
  rfl

/-- Evaluation of the canonical abelianization comparison induced by a
multiplicative equivalence into a commutative group. -/
theorem abelianizationCongrToComm_apply
    {Q R : Type*} [Group Q] [CommGroup R]
    (e : Q ≃* R) (q : Q) :
    MulEquiv.toAdditive
        (e.abelianizationCongr.trans
          (Abelianization.equivOfComm : R ≃* Abelianization R).symm)
        (Additive.ofMul (Abelianization.of q)) =
      Additive.ofMul (e q) := by
  apply Additive.toMul.injective
  change
    (Abelianization.equivOfComm : R ≃* Abelianization R).symm
        (e.abelianizationCongr (Abelianization.of q)) = e q
  rw [abelianizationCongr_of]
  exact
    (Abelianization.equivOfComm : R ≃* Abelianization R).symm_apply_apply _

/-- Evaluation of the canonical quotient from the abelianization of a
commutative group. -/
theorem commutativeAbelianizationEquiv_apply
    {Q R : Type*} [CommGroup Q] [Group R]
    (e : Q ≃* R) (q : Q) :
    MulEquiv.toAdditive
        ((Abelianization.equivOfComm : Q ≃* Abelianization Q).symm.trans e)
        (Additive.ofMul (Abelianization.of q)) =
      Additive.ofMul (e q) := by
  apply Additive.toMul.injective
  change
    e ((Abelianization.equivOfComm : Q ≃* Abelianization Q).symm
      (Abelianization.of q)) = e q
  exact congrArg e
    ((Abelianization.equivOfComm : Q ≃* Abelianization Q).symm_apply_apply q)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_CyclotomicUnramifiedLocalGlobalCompatibility
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Cyclotomic unramified local--global compatibility

For an unramified finite abelian subextension of an abstract rational
fixed field, the actual global norm-residue homomorphism agrees on every
finite one-place idele class with the chosen local Artin homomorphism.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open KummerTheory

@[reducible]
def composeMonoidHom
    {M N P : Type*} [MulOne M] [MulOne N] [MulOne P]
    (f : M →* N) (g : N →* P) : M →* P :=
  g.comp f

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_Padic_ClosedAddSubgroup
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Closed additive subgroups of the p-adic integers

A nonzero closed additive subgroup of `ℤ_[p]` contains a nonzero principal
ideal.  Since every nonzero ideal of `ℤ_[p]` is generated by a power of `p`,
such a subgroup is open.
-/

open scoped Topology

namespace PadicInt

/-- Every additive coset of an open subgroup of the `p`-adic integers
contains the cast of a positive natural number.

The positive natural numbers are dense because they are the translate
by one of the dense image of `ℕ` in `ℤ_[p]`. -/
theorem exists_positive_natCast_sub_mem_of_isOpen_addSubgroup
    (p : ℕ) [Fact p.Prime]
    (H : AddSubgroup ℤ_[p])
    (hopen : IsOpen (H : Set ℤ_[p]))
    (z : ℤ_[p]) :
    ∃ n : ℕ, 0 < n ∧ z - (n : ℤ_[p]) ∈ H := by
  have htranslate :
      Function.Surjective (fun y : ℤ_[p] ↦ y + 1) := by
    intro y
    exact ⟨y - 1, sub_add_cancel y 1⟩
  have hdense :
      DenseRange (fun n : ℕ ↦ (n : ℤ_[p]) + 1) := by
    exact
      htranslate.denseRange.comp
        PadicInt.denseRange_natCast
        (continuous_id.add continuous_const)
  let U : Set ℤ_[p] := {y | z - y ∈ H}
  have hUopen : IsOpen U := by
    exact hopen.preimage (continuous_const.sub continuous_id)
  have hUne : U.Nonempty := by
    refine ⟨z, ?_⟩
    change z - z ∈ H
    simpa only [sub_self] using H.zero_mem
  obtain ⟨n, hn⟩ := hdense.exists_mem_open hUopen hUne
  refine ⟨n + 1, Nat.zero_lt_succ n, ?_⟩
  simpa only [U, Set.mem_ofPred_eq, Nat.cast_add, Nat.cast_one] using hn

/-- A positive integral degree is nontrivial in the multiplicative
copy of the additive group of `ℤ_p`. -/
theorem multiplicative_positiveNatDegree_ne_one
    (p : ℕ) [Fact p.Prime]
    (n : ℕ) (hn : 0 < n) :
    (Multiplicative.ofAdd (1 : ℤ_[p])) ^ n ≠ 1 := by
  intro h
  have h' := congrArg Multiplicative.toAdd h
  change n • (1 : ℤ_[p]) = 0 at h'
  have hn0 : (n : ℤ_[p]) = 0 := by
    simpa only [nsmul_one] using h'
  have : n = 0 := by
    exact_mod_cast hn0
  exact (Nat.ne_of_gt hn) this

end PadicInt
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_SeparableClosurePadicLift
attribute [-instance] _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.matrixSecondCountable
attribute [-simp] _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Separable-closure p-adic lifts for local-global Artin compatibility

This module constructs the finite-place decomposition restriction maps and
the positive p-adic cyclotomic lifts used in the local-global comparison.
-/

open scoped NumberField
open IsDedekindDomain NumberField
open HilbertRamification

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

local instance instFactPrimeValNat_solutions_6 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

/-- The fixed field of the cyclic subgroup generated by one
automorphism of a finite abelian extension.

Passing from `K` to this field is the genuine cyclic reduction used in
the proof of finite-place local--global compatibility: over this field
the given automorphism generates the whole Galois group. -/
noncomputable def automorphismCyclicFixedField
    (σ : Gal(L / K)) :
    IntermediateField K L :=
  IntermediateField.fixedField
    (Subgroup.closure ({σ} : Set (Gal(L / K))))

noncomputable local instance automorphismCyclicFixedFieldNumberField
    (σ : Gal(L / K)) :
    NumberField (automorphismCyclicFixedField σ) :=
  NumberField.of_module_finite K
    (automorphismCyclicFixedField σ)

/-- An automorphism, regarded over the fixed field of the cyclic
subgroup it generates. -/
noncomputable def automorphismOverCyclicFixedField
    (σ : Gal(L / K)) :
    Gal(L / automorphismCyclicFixedField σ) :=
  IntermediateField.fixingSubgroupEquiv
    (automorphismCyclicFixedField σ)
    ⟨σ, by
      rw [automorphismCyclicFixedField,
        IntermediateField.fixingSubgroup_fixedField]
      exact
        Subgroup.subset_closure
          (Set.mem_singleton σ)⟩

omit [NumberField K] [NumberField L] [IsAbelianGalois K L] in
/-- Restricting the automorphism over its cyclic fixed field back to the base
field recovers the original automorphism. -/
@[simp]
theorem automorphismOverCyclicFixedField_restrictScalars
    (σ : Gal(L / K)) :
    (automorphismOverCyclicFixedField σ).restrictScalars K = σ := by
  ext x
  rfl

omit [NumberField K] [NumberField L] [IsAbelianGalois K L] in
/-- The automorphism over its cyclic fixed field genuinely generates
the entire relative Galois group. -/
theorem automorphismOverCyclicFixedField_generates
    (σ : Gal(L / K)) :
    Subgroup.closure
        ({automorphismOverCyclicFixedField σ} :
          Set
            (Gal(L / automorphismCyclicFixedField σ))) =
      ⊤ := by
  let M := automorphismCyclicFixedField σ
  let σM : Gal(L / M) :=
    automorphismOverCyclicFixedField σ
  let e :
      M.fixingSubgroup ≃*
        Gal(L / M) :=
    IntermediateField.fixingSubgroupEquiv M
  have hσ :
      (⟨σ, by
          change
            σ ∈
              (automorphismCyclicFixedField σ).fixingSubgroup
          rw [automorphismCyclicFixedField,
            IntermediateField.fixingSubgroup_fixedField]
          exact
            Subgroup.subset_closure
              (Set.mem_singleton σ)⟩ :
        M.fixingSubgroup) =
        e.symm.toMonoidHom σM := by
    apply Subtype.ext
    rfl
  apply Subgroup.map_injective
    (f := e.symm.toMonoidHom) e.symm.injective
  change
    Subgroup.map e.symm.toMonoidHom
        (Subgroup.closure ({σM} : Set (Gal(L / M)))) =
      Subgroup.map e.symm.toMonoidHom ⊤
  rw [MonoidHom.map_closure, Set.image_singleton,
    ← hσ, Subgroup.map_top_of_surjective
      e.symm.toMonoidHom e.symm.surjective]
  apply Subgroup.map_injective
    (f := M.fixingSubgroup.subtype)
    M.fixingSubgroup.subtype_injective
  rw [MonoidHom.map_closure, Set.image_singleton,
    ← MonoidHom.range_eq_map, M.fixingSubgroup.range_subtype]
  change
    Subgroup.closure ({σ} : Set (Gal(L / K))) =
      (automorphismCyclicFixedField σ).fixingSubgroup
  rw [automorphismCyclicFixedField,
    IntermediateField.fixingSubgroup_fixedField]

/-- A surjective restriction map admits a lift with positive integral
`p`-adic degree whenever the degrees contributed by its kernel form an
open subgroup of `ℤ_[p]`.

The initial lift is corrected inside the genuine restriction kernel.
Density of the positive natural numbers in `ℤ_[p]` supplies the
required correction without changing its prescribed restriction. -/
theorem exists_positivePadicDegree_lift_of_surjective
    {D A : Type} [Group D] [Group A]
    (p : ℕ) [Fact p.Prime]
    (restriction : D →* A)
    (hrestriction : Function.Surjective restriction)
    (degree : D →* Multiplicative ℤ_[p])
    (hdegree :
      IsOpen
        ((((restriction.ker.map degree).toAddSubgroup' :
            AddSubgroup ℤ_[p]) :
          Set ℤ_[p])))
    (σ : A) :
    ∃ τ : D,
      restriction τ = σ ∧
        ∃ n : ℕ, 0 < n ∧
          degree τ =
            (Multiplicative.ofAdd (1 : ℤ_[p])) ^ n := by
  obtain ⟨s, hs⟩ := hrestriction σ
  let H : AddSubgroup ℤ_[p] :=
    (restriction.ker.map degree).toAddSubgroup'
  have hHopen : IsOpen (H : Set ℤ_[p]) := by
    simpa only [H] using hdegree
  obtain ⟨n, hn, hmem⟩ :=
    PadicInt.exists_positive_natCast_sub_mem_of_isOpen_addSubgroup
      p H hHopen (Multiplicative.toAdd (degree s))
  have hcorrection :
      (n : ℤ_[p]) -
          Multiplicative.toAdd (degree s) ∈ H := by
    simpa only [neg_sub] using H.neg_mem hmem
  change
    Multiplicative.ofAdd
        ((n : ℤ_[p]) -
          Multiplicative.toAdd (degree s)) ∈
      restriction.ker.map degree at hcorrection
  obtain ⟨k, hk, hdk⟩ := hcorrection
  refine ⟨s * k, ?_, ⟨n, hn, ?_⟩⟩
  · rw [map_mul, hs]
    change restriction k = 1 at hk
    rw [hk, mul_one]
  · apply Multiplicative.ext
    rw [map_mul]
    change
      Multiplicative.toAdd (degree s) +
          Multiplicative.toAdd (degree k) =
        n • (1 : ℤ_[p])
    have hdk' := congrArg Multiplicative.toAdd hdk
    change
      Multiplicative.toAdd (degree k) =
        (n : ℤ_[p]) -
          Multiplicative.toAdd (degree s) at hdk'
    rw [hdk']
    simp only [nsmul_eq_mul, mul_one]
    abel

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicCyclicData
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite p-adic cyclic data for local-global Artin compatibility

This module packages the simultaneous finite-quotient and cyclotomic
coordinates and the corresponding abstract auxiliary subextension.
-/

open scoped IsMulCommutative NumberField
open NumberField
open HilbertRamification
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

local instance instFactPrimeValNat_solutions_7 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

/-- Inclusion of a subgroup equipped with its subtype topology. -/
def continuousSubgroupSubtype
    {A : Type*} [Group A] [TopologicalSpace A]
    (H : Subgroup A) : H →ₜ* A where
  toMonoidHom := H.subtype
  continuous_toFun := continuous_subtype_val

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_LocalGlobalArtinCompatibility_FinitePadicAuxiliaryField
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The finite p-adic auxiliary field

This module realizes the simultaneous finite/cyclotomic lift as an actual
number field and proves the subgroup and intermediate-field identities
needed by the auxiliary-field argument.
-/

open scoped IsMulCommutative NumberField
open IsDedekindDomain NumberField
open HilbertRamification
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open GlobalClassFields

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

local instance instFactPrimeValNat_solutions_8 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ArithmeticNormalization
attribute [-instance] _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Arithmetic normalization of global reciprocity

The valuation used by the local class-formation implementation is the
logarithm of the multiplicative absolute value.  Consequently its
distinguished element of value `1` is the inverse of a DVR uniformizer.
The resulting field-facing reciprocity map sends a usual uniformizer to
geometric Frobenius.

The arithmetic global norm-residue symbol uses the opposite
normalization: a DVR uniformizer maps to arithmetic Frobenius and a
ramified cyclotomic unit `u` acts by `u⁻¹`.  For an abelian target the two
normalizations differ by the canonical inversion automorphism.  This file
records that normalization explicitly, including its topology and its
local-global compatibility.  Thus no sign convention is hidden in an
unbundled equality.
-/

open scoped IsMulCommutative NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

/-- Inversion as a topological multiplicative automorphism of a
commutative topological group. -/
def commutativeGroupInversionContinuousMulEquiv
    (G : Type*) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    G ≃ₜ* G :=
  { MulEquiv.inv G with
    continuous_toFun := continuous_inv
    continuous_invFun := continuous_inv }

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PeriodicTheta
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


namespace PrimeDegreePackets.ThetaConstruction
variable {d R : Type*} [Fintype d] [CommRing R]


local instance rationalModulusDecidableEq_rda812e_1 : DecidableEq d := Classical.decEq d
def rationalModulusIdeal (R : Type*) [CommRing R] (N : ℕ) : Ideal R :=
  Ideal.span {(N : R)}

end PrimeDegreePackets.ThetaConstruction

open MeasureTheory Module
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_GaussianMellin
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

open MeasureTheory Module WithLp Set


namespace PrimeDegreePackets
open ThetaConstruction
variable {n : ℕ} {K : Type*} [Field K] [NumberField K]

def integralIdealFractionalUnit (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.mpr hI)

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PrincipalUnits
attribute [-simp] _root_.LocalFieldTheory.powMonoidHom_range_one_mem
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
variable {K : Type*} [Field K] [NumberField K]

lemma integralIdealFractionalUnit_top :
    integralIdealFractionalUnit (⊤ : Ideal (𝓞 K)) top_ne_bot = 1 := by
  apply Units.ext
  simp [integralIdealFractionalUnit]

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayCharacter
attribute [-simp] _root_.LocalFieldTheory.powMonoidHom_range_one_mem
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



variable {K : Type*} [Field K] [NumberField K]

 

structure EvenRayCharacter (K : Type*) [Field K] [NumberField K] (N : ℕ) where
  idealHom : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* ℂˣ
  finiteOrder : ∃ e : ℕ, 0 < e ∧ ∀ J, idealHom J ^ e = 1
  residue : MulChar ((𝓞 K) ⧸ rationalModulusIdeal (𝓞 K) N) ℂ
  principalLaw : ∀ (a : 𝓞 K) (ha : a ≠ 0),
    IsCoprime (Ideal.span {a}) (rationalModulusIdeal (𝓞 K) N) →
    (idealHom (integralIdealFractionalUnit (Ideal.span {a})
      (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using ha)) : ℂ) =
        residue (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a)

namespace EvenRayCharacter
variable {N : ℕ} (ψ : EvenRayCharacter K N)

variable [NeZero N]



def conjugate : EvenRayCharacter K N where
  idealHom := (Units.map ((starRingEnd ℂ).toMonoidHom)).comp ψ.idealHom
  finiteOrder := by
    obtain ⟨e,he,H⟩ := ψ.finiteOrder
    refine ⟨e,he,fun J => ?_⟩
    have h := congrArg (Units.map ((starRingEnd ℂ).toMonoidHom)) (H J)
    simpa only [map_pow, map_one, MonoidHom.comp_apply] using h
  residue := star ψ.residue
  principalLaw := by
    intro a ha hcop
    have H := congrArg conj (ψ.principalLaw a ha hcop)
    exact H

omit [NeZero N] in
@[simp] lemma conjugate_idealHom (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (ψ.conjugate.idealHom J : ℂ) = conj ((ψ.idealHom J : ℂ)) := rfl

end EvenRayCharacter
end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayEuler
attribute [-simp] _root_.LocalFieldTheory.powMonoidHom_range_one_mem
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

 
def allCoefficient (I : Ideal (𝓞 K)) : ℂ :=
  if hI : I ≠ ⊥ then
    if IsCoprime I (rationalModulusIdeal (𝓞 K) N) then
      (ψ.idealHom (integralIdealFractionalUnit I hI) : ℂ)
    else 0
  else 0

@[simp] lemma allCoefficient_bot : ψ.allCoefficient ⊥ = 0 := by
  simp [allCoefficient]

@[simp] lemma allCoefficient_zero : ψ.allCoefficient 0 = 0 := ψ.allCoefficient_bot

end EvenRayCharacter
end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayFrobenius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Module Filter
open scoped NumberField nonZeroDivisors BigOperators Classical
namespace PrimeDegreePackets
namespace GaloisIdealCharacter

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

 
def primeAbove (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    Ideal.primesOver P.asIdeal (𝓞 E) := Classical.choice inferInstance

omit [NumberField F] [NumberField E] [FiniteDimensional F E] [IsGalois F E] in
lemma primeAbove_ne_bot (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    (primeAbove F E P).val ≠ ⊥ :=
  Ideal.ne_bot_of_mem_primesOver P.ne_bot (primeAbove F E P).property

 
def primeFrobenius (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : E ≃ₐ[F] E := by
  let Q := primeAbove F E P
  letI : Q.val.IsPrime := Q.property.1
  letI : Q.val.IsMaximal := Q.property.1.isMaximal (primeAbove_ne_bot F E P)
  exact arithFrobAt (𝓞 F) (E ≃ₐ[F] E) Q.val

variable (χ : (E ≃ₐ[F] E) →* ℂˣ)

lemma finite_factor_support (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    Function.HasFiniteMulSupport (fun P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      χ (primeFrobenius F E P) ^ FractionalIdeal.count F P I.val) := by
  have h : {P : IsDedekindDomain.HeightOneSpectrum (𝓞 F) |
      FractionalIdeal.count F P I.val ≠ 0}.Finite := by
    simpa only [Filter.eventually_cofinite] using
      FractionalIdeal.finite_factors I.val
  apply h.subset
  intro P hP
  change (χ (primeFrobenius F E P)) ^ FractionalIdeal.count F P I.val ≠ 1 at hP
  intro hzero
  exact hP (by rw [hzero, zpow_zero])

 

def idealHom : (FractionalIdeal (𝓞 F)⁰ F)ˣ →* ℂˣ where
  toFun I := ∏ᶠ P : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
    χ (primeFrobenius F E P) ^ FractionalIdeal.count F P I.val
  map_one' := by simp only [Units.val_one, FractionalIdeal.count_one, zpow_zero, finprod_one]
  map_mul' I J := by
    simp only [Units.val_mul, FractionalIdeal.count_mul F _ (Units.ne_zero I) (Units.ne_zero J),
      zpow_add]
    exact finprod_mul_distrib (finite_factor_support F E χ I) (finite_factor_support F E χ J)

end GaloisIdealCharacter
end PrimeDegreePackets

end

end OAI
end


