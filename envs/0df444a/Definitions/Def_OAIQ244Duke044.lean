-- Prove2me | Definitions.Def_OAIQ244Duke044
-- name    : OAIQ244Duke044
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:43:29.980578+00:00
-- url     : https://prove2.me/theorems/0f02e2b3-27d7-4208-b915-2f15747d5eb2
-- title:
--   Definitions bundle OAIQ244Duke044 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 195 declarations of OpenAI's Lean: 51 definitions, 2 inductive types or structures, 19 instances and 123 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.infinitePlaceRatComplexificationFactors`, `IdeleGroup.compactIntegralNormOneSet`, `IdeleGroup.compactNormOneClassCover`, `IdeleGroup.normOneIdealClassRepresentative`, `IdeleGroup.normOneIdealClassRepresentativeSet`, `InfiniteIdeleGroup.annulus`, `KummerTheory.fullSUnitKummerExtensionGaloisEquivPiZMod`, `OAI.DukePrimeDegree.PhysicalPrefixWindow.toBox`, `OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleCoordinates`, `OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure`, `OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleRegion`, `OAI.DukePrimeDegree.RootPrefixCoordinates.extend`, `OAI.DukePrimeDegree.RootPrefixCoordinates.extendedRootParam`, `OAI.DukePrimeDegree.RootPrefixCoordinates.originalRectangleCoordinates`, `OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixBox`, `OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure`, `OAI.DukePrimeDegree.RootPrefixCoordinates.physicalWindowFamily`, `OAI.DukePrimeDegree.SmallNeutralPatch`, `OAI.DukePrimeDegree.SmallNeutralPatch.raw`, `OAI.DukePrimeDegree.UpperRootBox`, `OAI.DukePrimeDegree.UpperRootBox.domain`, `OAI.DukePrimeDegree.UpperRootBox.param`, `OAI.DukePrimeDegree.UpperRootBox.range`, `OAI.DukePrimeDegree.UpperRootBox.shrink`, `OAI.DukePrimeDegree.cyclicHeckeFactor`, `OAI.DukePrimeDegree.neutralToPrefix`, `OAI.DukePrimeDegree.neutralTransverseHomeomorph`, `OAI.DukePrimeDegree.neutralUpperRootHomeomorph`, `OAI.DukePrimeDegree.normalizedTransverse`, `OAI.DukePrimeDegree.rootInformationHom`, `OAI.DukePrimeDegree.transverseNeutralCoordinate`, `OAI.DukePrimeDegree.transverseNeutralReconstruct`, `OAI.DukePrimeDegree.transverseUnitCoordinate`, `OAI.PrimeDegreePackets.EvenRayCharacter.classCharacter`, `OAI.PrimeDegreePackets.EvenRayCharacter.classUnitCharacter`, `OAI.PrimeDegreePackets.EvenRayCharacter.nonprincipalContinued`, `OAI.PrimeDegreePackets.EvenRayCharacter.unramifiedContinued`, `RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction`, `RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup`, `RamificationTheory.HilbertRamification.CompleteDVF.residueAction` and 13 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Idele_NormOneCompact`, `AlgebraicNumberTheory_Idele_NormTopology_ArchimedeanNorm`, `AlgebraicNumberTheory_Idele_NormTopology_ExtensionBehavior`, `AlgebraicNumberTheory_RayClass_FullModulus`, `AlgebraicNumberTheory_RayClass_IdealNorm`, `AlgebraicNumberTheory_RayClass_Narrow`, `AlgebraicNumberTheory_RayClass_Rational`, `AlgebraicNumberTheory_RayClass_Topology`, `DukePrimeDegree_Arithmetic_CyclicContinuation`, `DukePrimeDegree_Entropy_RootInformationScale`, `DukePrimeDegree_Geometry_LargePhysicalRectangles`, `DukePrimeDegree_Geometry_NeutralPatchCover`, `DukePrimeDegree_Geometry_NeutralPrefixMap`, `DukePrimeDegree_Geometry_NeutralTransverseCoordinates`, `DukePrimeDegree_Geometry_NeutralUpperRootHomeomorph`, `DukePrimeDegree_Geometry_PhysicalPrefixBox`, `DukePrimeDegree_Geometry_PhysicalPrefixCoordinates`, `DukePrimeDegree_Geometry_PhysicalPrefixMeasure`, `DukePrimeDegree_Geometry_PhysicalPrefixWindows`, `DukePrimeDegree_Geometry_PhysicalRootEmbeddings`, `DukePrimeDegree_Geometry_PhysicalWindowAtlas`, `DukePrimeDegree_Geometry_PrefixExchangeMeasures`, `DukePrimeDegree_Geometry_PrefixExchangeRegions`, `DukePrimeDegree_Geometry_RemainingRootProductBoxes`, `DukePrimeDegree_Geometry_RootPrefixCoordinates`, `DukePrimeDegree_Geometry_RootPrefixFactorChart`, `DukePrimeDegree_Geometry_RootPrefixReorder`, `DukePrimeDegree_Geometry_TransverseDiagonalData`, `DukePrimeDegree_Geometry_UpperRootChart`, `DukePrimeDegree_Geometry_UpperRootDiagonalCharts`, `DukePrimeDegree_Geometry_UpperRootDisintegration`, `DukePrimeDegree_Geometry_UpperRootRestrictions`, `GlobalClassFieldTheory_GlobalClassFields_BigHilbertClassFieldNaturality`, `GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_InfinitePlaceOverfield`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicCharacterRigidity`, `KummerTheory_Concrete_SUnitPreparation_FullSUnitKummerExtension`, `LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedComparison`, `LocalField_DiscreteValuationField_PrincipalUnitPadicAction_AdicProdiscreteComparison`, `LocalField_DiscreteValuationField_PrincipalUnitPadicAction_TopologyModelTypes`, `LocalField_DiscreteValuationField_PrincipalUnits_Core`, `LocalField_DiscreteValuationField_RamificationAddVal`, `LocalField_DiscreteValuationField_RamificationInvariants`, `LocalField_NonarchimedeanLocalField_IdealQuotients`, `LocalField_NonarchimedeanLocalField_NormQuotient`, `LocalField_NonarchimedeanLocalField_NormalizedIntegerValuation`, `LocalField_NonarchimedeanLocalField_UnramifiedFrobenius`, `LubinTate_FormalModule_DegreeStabilization`, `LubinTate_FormalModule_Intertwiner`, `PrimePackets_AmbientLeaves`, `PrimePackets_IntrinsicLeaves`, `PrimePackets_LeafSupport`, `PrimePackets_RayContinuation`, `PrimePackets_RayDescent`, `PrimePackets_RayUnramified`, `PrimePackets_RootCharts`, `PrimePackets_RootLeaves`, `PrimePackets_ScalingCovariance`, `Ramification_HilbertRamification_CompleteDVF`, `Valuation_DiscreteValuationField_AmbientUniformizer`, `Valuation_DiscreteValuationField_Basic`, `Valuation_DiscreteValuationField_FiniteExtension_Degree`, `Valuation_DiscreteValuationField_FiniteExtension_Uniqueness`.
--
--   **Imports.** It imports the published bundle `Def_DukePrimeDegree`; the bundles `OAIQ244Duke026`, `OAIQ244Duke027`, `OAIQ244Duke028`, `OAIQ244Duke029`, `OAIQ244Duke030`, `OAIQ244Duke031`, `OAIQ244Duke033`, `OAIQ244Duke034`, `OAIQ244Duke035` and `OAIQ244Duke036` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke051` and `OAIQ244Duke052`; the statements `OAI.DukePrimeDegree.PhysicalPrefixWindow.centeredConditional_product`, `OAI.DukePrimeDegree.PhysicalPrefixWindow.independent`, `OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_ae_rootKernel`, `OAI.DukePrimeDegree.cyclicHeckeFactor_analytic`, `OAI.DukePrimeDegree.cyclicHeckeFactor_order_conjugation`, `OAI.DukePrimeDegree.cyclic_subfield_order_of_unique_character`, `OAI.PrimeDegreePackets.EvenRayCharacter.nonprincipalContinued_finite_nonnegative_order` and `OAI.PrimeDegreePackets.EvenRayCharacter.unramifiedContinued_eq_dirichlet`; the proofs of `OAI.DukePrimeDegree.EliminationChain.wholeFuture_conditionalInformation_integrable_integral`, `OAI.DukePrimeDegree.PhysicalPrefixWindow.centeredConditional_product`, `OAI.DukePrimeDegree.PhysicalPrefixWindow.independent`, `OAI.DukePrimeDegree.RootPrefixBox.ae_conditionalKernel_eq_dirac_of_atomic_roots`, `OAI.DukePrimeDegree.RootPrefixBox.ae_normalized_uncentered_eq_regularLeaf`, `OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_ae_rootKernel`, `OAI.DukePrimeDegree.all_roots_atomic_of_zero_regular_entropy`, `OAI.DukePrimeDegree.atomic_positive_root_of_zero_entropy`, `OAI.DukePrimeDegree.canonicalRootCoefficient_one_of_invariant`, `OAI.DukePrimeDegree.canonicalRootCoefficient_zero_iff`, `OAI.DukePrimeDegree.cyclicHeckeFactor_analytic`, `OAI.DukePrimeDegree.cyclicHeckeFactor_order_conjugation`, `OAI.DukePrimeDegree.cyclic_subfield_order_of_unique_character`, `OAI.DukePrimeDegree.eklPrimeInput_of_regular_entropy_upper_bounds`, `OAI.DukePrimeDegree.exists_atomic_neutral_future_cover`, `OAI.DukePrimeDegree.exists_compact_equal_leaf_shearing_sequence`, `OAI.DukePrimeDegree.exists_cover_stationary_wholeFutureKernel`, `OAI.DukePrimeDegree.exists_distinct_equal_leaf_horospherical_pair`, `OAI.DukePrimeDegree.exists_equal_leaf_return_sequence_with_windows`, `OAI.DukePrimeDegree.exists_nullset_atomic_root_limit`, `OAI.DukePrimeDegree.exists_nullset_neutral_root_holonomy`, `OAI.DukePrimeDegree.exists_nullset_nonparallel_root_constancy`, `OAI.DukePrimeDegree.exists_real_character_of_simple_zeta`, `OAI.DukePrimeDegree.exists_sparse_upperRoot_comparison`, `OAI.DukePrimeDegree.fixedFieldMultiplicity_le_extension`, `OAI.DukePrimeDegree.negative_diagonal_entropy_le_root_sum_of_small_auxiliary`, `OAI.DukePrimeDegree.no_two_step_positive_roots_of_no_invariant_root`, `OAI.DukePrimeDegree.nonempty_rootPairSelectionData`, `OAI.DukePrimeDegree.positive_root_coefficient_of_positive_diagonal_entropy`, `OAI.DukePrimeDegree.positive_root_sum_le_diagonal_entropy`, `OAI.DukePrimeDegree.rootBox_leaf_separates_fibers_outside_nullset`, `OAI.DukePrimeDegree.rootInvarianceRelation_symmetric_of_regular_tests`, `OAI.DukePrimeDegree.root_invariant_of_adjacent_nonatomic_leaves`, `OAI.PrimeDegreePackets.EvenRayCharacter.nonprincipalContinued_finite_nonnegative_order` and `OAI.PrimeDegreePackets.EvenRayCharacter.unramifiedContinued_eq_dirichlet`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Finsupp.Basic
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
import Mathlib.Algebra.Group.Equiv.TypeTags
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
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.WithZero
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
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.Dynamics.Ergodic.Conservative
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
import Mathlib.FieldTheory.IntermediateField.Basic
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
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Piecewise
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Support
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
import Mathlib.Order.Filter.AtTopBot.Tendsto
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
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Finiteness
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
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Homeomorph.TransferInstance
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Sequences
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.WithTopology
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke026
import Definitions.Def_OAIQ244Duke027
import Definitions.Def_OAIQ244Duke028
import Definitions.Def_OAIQ244Duke029
import Definitions.Def_OAIQ244Duke030
import Definitions.Def_OAIQ244Duke031
import Definitions.Def_OAIQ244Duke033
import Definitions.Def_OAIQ244Duke034
import Definitions.Def_OAIQ244Duke035
import Definitions.Def_OAIQ244Duke036

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_IdealQuotients
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_finite_residue _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-! ### Residue and maximal-ideal successive quotients -/

/-- A successive maximal-ideal quotient over a local field is finite. -/
instance maximalIdealPowSuccQuot_finite
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) :
    Finite (MaximalIdealPowSuccQuot K n) :=
  Finite.of_equiv 𝓀[K] (chosenResidueAddEquivMaximalIdealPowSuccQuot K n)

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormOneCompact
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.CyclicCohomology.permutationSublattice_discreteTopology _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.coordinateLattice_discrete _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralGroup_discrete _root_.OAI.PrimeDegreePackets.logSubgroup_discrete _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.orderedLogSubgroup_discrete _root_.OAI.PrimeDegreePackets.periodGroup_discrete _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.periodSubmodule_discrete _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.SUnitGroup.instDiscreteTopology_fullLogLattice _root_.SUnitGroup.instDiscreteTopology_reducedLogLattice _root_.SUnitGroup.instIsZLattice_reducedLogLattice _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceBaseValued _root_.scaledRelativeIntegerLatticeQuotientFinite
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.Modulus.mem_ideleCongruenceSubgroup_iff _root_.RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff _root_.RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff_local _root_.RayClass.mem_finiteCongruenceSubgroup_iff _root_.RayClass.mem_narrowInfiniteCongruenceSubgroup_iff _root_.RayClass.mem_primeToModulusIdeals_iff _root_.RayClass.primeToModulusIdeal_coe _root_.RayClass.quotientRaySubgroupEquivIdealRayClassGroup_mk _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Compactness of norm-one idele classes

This module combines local compactness, the logarithmic unit lattice, and the
principal-idele norm formula to prove compactness of the norm-one subgroup of
the idele class group.
-/

open scoped Classical NumberField Pointwise RestrictedProduct NNReal
open NumberField IsDedekindDomain
open NumberField.Units.dirichletUnitTheorem

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace InfiniteIdeleGroup

/-- A compact product of local archimedean annuli. -/
def annulus (B : ℝ) : Set (InfiniteIdeleGroup K) :=
  ContinuousMulEquiv.piUnits.symm ''
    Set.univ.pi (fun w : InfinitePlace K ↦ localAnnulus w B)

omit [NumberField K] in
theorem isCompact_annulus (B : ℝ) :
    IsCompact (annulus (K := K) B) := by
  apply IsCompact.image
  · exact isCompact_univ_pi fun w ↦ isCompact_localAnnulus w B
  · exact ContinuousMulEquiv.piUnits.symm.continuous

omit [NumberField K] in
theorem mem_annulus_iff (a : InfiniteIdeleGroup K) (B : ℝ) :
    a ∈ annulus (K := K) B ↔
      ∀ w : InfinitePlace K,
        Real.exp (-B) ≤
            ‖((component w a : w.Completionˣ) : w.Completion)‖ ∧
          ‖((component w a : w.Completionˣ) : w.Completion)‖ ≤
            Real.exp B := by
  constructor
  · rintro ⟨u, hu, rfl⟩ w
    change Real.exp (-B) ≤ ‖(u w : w.Completion)‖ ∧
      ‖(u w : w.Completion)‖ ≤ Real.exp B
    exact hu w (Set.mem_univ w)
  · intro ha
    refine ⟨ContinuousMulEquiv.piUnits a, ?_, ?_⟩
    · intro w _
      exact ha w
    · exact ContinuousMulEquiv.piUnits.symm_apply_apply a

/-- The archimedean norm is continuous. -/
theorem continuous_archimedeanNorm :
    Continuous (archimedeanNorm (K := K)) := by
  classical
  rw [show (archimedeanNorm (K := K) :
      InfiniteIdeleGroup K → ℝ≥0ˣ) =
      fun a ↦ ∏ w : InfinitePlace K,
        nnnormUnitHom w.Completion (component w a) ^ w.mult by
    rfl]
  apply continuous_finsetProd
  intro w _
  apply Continuous.pow
  exact (continuous_nnnorm.units_map _).comp
    ((continuous_apply w).comp
      ContinuousMulEquiv.piUnits.continuous)

theorem norm_infiniteComponent_principalIdele (x : Kˣ)
    (w : InfinitePlace K) :
    ‖((component w (IdeleGroup.principalIdele K x).1 :
        w.Completionˣ) : w.Completion)‖ =
      w (x : K) := by
  change ‖(((WithAbs.equiv w.1).symm (x : K) :
    WithAbs w.1) : w.Completion)‖ = w (x : K)
  rw [NumberField.InfinitePlace.Completion.norm_coe,
    (WithAbs.equiv w.1).apply_symm_apply]

/-- On an algebraic integer unit, the archimedean idele log is exactly
Dirichlet's logarithmic embedding. -/
theorem logNorm_principalRingUnit (u : (𝓞 K)ˣ) :
    logNorm (IdeleGroup.principalIdele K
        (ringUnitToFieldUnit (K := K) u)).1 =
      NumberField.Units.logEmbedding K (Additive.ofMul u) := by
  ext w
  rw [logNorm, logEmbedding_component,
    norm_infiniteComponent_principalIdele]
  rfl

theorem logNorm_component_le {r : ℝ} (a : InfiniteIdeleGroup K)
    (h : ‖logNorm a‖ ≤ r)
    (w : {w : InfinitePlace K //
      w ≠ w₀ (K := K)}) :
    |logNorm a w| ≤ r := by
  simpa only [Real.norm_eq_abs] using
    (norm_le_pi_norm (logNorm a) w).trans h

/-- If the total archimedean norm is one, the omitted logarithmic coordinate
is the negative sum of all the other coordinates. -/
theorem sum_logNorm_eq_neg_distinguished
    (a : InfiniteIdeleGroup K)
    (ha : archimedeanNorm a = 1) :
    ∑ w, logNorm a w =
      -(w₀ (K := K)).mult *
        Real.log
          ‖((component (w₀ (K := K)) a :
              (w₀ (K := K)).Completionˣ) :
            (w₀ (K := K)).Completion)‖ := by
  have hprod :
      ∏ w : InfinitePlace K,
          ‖((component w a : w.Completionˣ) : w.Completion)‖ ^ w.mult =
        1 := by
    have h := congrArg
      (fun z : ℝ≥0ˣ ↦ (((z : ℝ≥0) : ℝ))) ha
    simpa only [archimedeanNorm_apply, Units.coe_prod,
      Units.val_pow_eq_pow_val, nnnormUnitHom_val, NNReal.coe_prod,
      NNReal.coe_pow, coe_nnnorm, Units.val_one, NNReal.coe_one] using h
  have hsum :
      ∑ w : InfinitePlace K,
          w.mult *
            Real.log
              ‖((component w a : w.Completionˣ) :
                w.Completion)‖ = 0 := by
    calc
      ∑ w : InfinitePlace K,
          w.mult *
            Real.log
              ‖((component w a : w.Completionˣ) :
                w.Completion)‖ =
          Real.log
            (∏ w : InfinitePlace K,
              ‖((component w a : w.Completionˣ) :
                w.Completion)‖ ^ w.mult) := by
              rw [Real.log_prod]
              · apply Finset.sum_congr rfl
                intro w _
                rw [Real.log_pow]
              · intro w _
                exact pow_ne_zero _ <|
                  norm_ne_zero_iff.mpr (component w a).ne_zero
      _ = 0 := by rw [hprod, Real.log_one]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (w₀ (K := K))] at hsum
  have hsum' :
      (∑ w : {w : InfinitePlace K // w ≠ w₀ (K := K)},
          w.1.mult *
            Real.log
              ‖((component w.1 a : w.1.Completionˣ) :
                w.1.Completion)‖) =
        -(w₀ (K := K)).mult *
          Real.log
            ‖((component (w₀ (K := K)) a :
                (w₀ (K := K)).Completionˣ) :
              (w₀ (K := K)).Completion)‖ := by
    simpa only [neg_mul] using
      (eq_neg_of_add_eq_zero_right hsum)
  simpa only [logNorm] using hsum'

/-- A norm bound in the logarithmic space bounds every local logarithm.
The harmless factor `#S∞` also covers the omitted coordinate. -/
theorem abs_log_norm_component_le
    {r : ℝ} (hr : 0 ≤ r) (a : InfiniteIdeleGroup K)
    (hlog : ‖logNorm a‖ ≤ r)
    (hnorm : archimedeanNorm a = 1)
    (w : InfinitePlace K) :
    |Real.log
        ‖((component w a : w.Completionˣ) : w.Completion)‖| ≤
      (Fintype.card (InfinitePlace K) : ℝ) * r := by
  have hmult :
      ∀ x : ℝ, 0 ≤ x → x ≤ w.mult * x := by
    intro x hx
    nth_rw 1 [← one_mul x]
    refine mul_le_mul ?_ le_rfl hx ?_
    all_goals
      rw [NumberField.InfinitePlace.mult]
      split_ifs <;> norm_num
  by_cases hw : w = w₀ (K := K)
  · have h := congrArg (‖·‖)
      (sum_logNorm_eq_neg_distinguished a hnorm).symm
    replace h := (le_of_eq h).trans (norm_sum_le _ _)
    simp_rw [norm_mul, norm_neg, Real.norm_eq_abs, Nat.abs_cast] at h
    refine (le_trans ?_ h).trans ?_
    · rw [← hw]
      exact hmult _ (abs_nonneg _)
    · refine (Finset.sum_le_card_nsmul _ _ _
          (fun v _ ↦ logNorm_component_le a hlog v)).trans ?_
      rw [nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ hr
      exact_mod_cast
        (Fintype.card_subtype_le
          (fun w : InfinitePlace K ↦ w ≠ w₀ (K := K)))
  · have h := logNorm_component_le a hlog ⟨w, hw⟩
    rw [logNorm, abs_mul, Nat.abs_cast] at h
    refine (le_trans ?_ h).trans ?_
    · exact hmult _ (abs_nonneg _)
    · nth_rw 1 [← one_mul r]
      exact mul_le_mul
        (Nat.one_le_cast.mpr Fintype.card_pos)
        le_rfl hr (Nat.cast_nonneg _)

/-- Exponentiating the preceding logarithmic estimate gives a compact
annulus containing the idele. -/
theorem mem_annulus_of_logNorm_le
    {r : ℝ} (hr : 0 ≤ r) (a : InfiniteIdeleGroup K)
    (hlog : ‖logNorm a‖ ≤ r)
    (hnorm : archimedeanNorm a = 1) :
    a ∈ annulus (K := K)
      ((Fintype.card (InfinitePlace K) : ℝ) * r) := by
  rw [mem_annulus_iff]
  intro w
  let B := (Fintype.card (InfinitePlace K) : ℝ) * r
  have h :=
    abs_log_norm_component_le hr a hlog hnorm w
  have hnpos :
      0 <
        ‖((component w a : w.Completionˣ) :
          w.Completion)‖ :=
    norm_pos_iff.mpr (component w a).ne_zero
  have habs :
      -B ≤
          Real.log
            ‖((component w a : w.Completionˣ) :
              w.Completion)‖ ∧
        Real.log
            ‖((component w a : w.Completionˣ) :
              w.Completion)‖ ≤ B := by
    simpa only [B] using (abs_le.mp h)
  constructor
  · calc
      Real.exp (-B) ≤
          Real.exp
            (Real.log
              ‖((component w a : w.Completionˣ) :
                w.Completion)‖) :=
        Real.exp_le_exp.mpr habs.1
      _ = ‖((component w a : w.Completionˣ) :
            w.Completion)‖ :=
        Real.exp_log hnpos
  · calc
      ‖((component w a : w.Completionˣ) :
          w.Completion)‖ =
          Real.exp
            (Real.log
              ‖((component w a : w.Completionˣ) :
                w.Completion)‖) :=
        (Real.exp_log hnpos).symm
      _ ≤ Real.exp B := Real.exp_le_exp.mpr habs.2

/-- Every archimedean idele can be multiplied by an algebraic integer unit
so that its logarithmic vector lies in a fixed bounded fundamental
parallelepiped. -/
theorem exists_ringUnit_logNorm_le (a : InfiniteIdeleGroup K) :
    ∃ u : (𝓞 K)ˣ,
      ‖logNorm
          (a * (IdeleGroup.principalIdele K
            (ringUnitToFieldUnit (K := K) u)).1)‖ ≤
        logFundamentalBound (K := K) := by
  let b := unitLatticeRealBasis (K := K)
  let f := ZSpan.floor b (logNorm a)
  have hf :
      (f : logSpace K) ∈ NumberField.Units.unitLattice K := by
    have hspan :
        Submodule.span ℤ (Set.range (b :
          Module.Free.ChooseBasisIndex ℤ
              (NumberField.Units.unitLattice K) →
            logSpace K)) =
          NumberField.Units.unitLattice K := by
      dsimp [b, unitLatticeRealBasis]
      exact (Module.Free.chooseBasis ℤ
        (NumberField.Units.unitLattice K)).ofZLatticeBasis_span
          ℝ (NumberField.Units.unitLattice K)
    exact hspan.le f.property
  change (f : logSpace K) ∈
      Submodule.map
        (NumberField.Units.logEmbedding K).toIntLinearMap ⊤ at hf
  obtain ⟨u, -, hu⟩ := hf
  refine ⟨u.toMul⁻¹, ?_⟩
  have hinv :
      NumberField.Units.logEmbedding K
          (Additive.ofMul u.toMul⁻¹) =
        -(f : logSpace K) := by
    calc
      NumberField.Units.logEmbedding K
          (Additive.ofMul u.toMul⁻¹) =
          -NumberField.Units.logEmbedding K u := by
            rw [← map_neg]
            rfl
      _ = -(f : logSpace K) := congrArg Neg.neg hu
  rw [logNorm_mul, logNorm_principalRingUnit, hinv,
    ← sub_eq_add_neg, ← ZSpan.fract_apply]
  exact ZSpan.norm_fract_le b (logNorm a)

end InfiniteIdeleGroup

namespace IdeleGroup

/-- A principal idele coming from a unit of the ring of integers is integral
at every finite place. -/
theorem principalRingUnit_mem_integralAtFinitePlaces
    (u : (𝓞 K)ˣ) :
    principalIdele K
        (InfiniteIdeleGroup.ringUnitToFieldUnit (K := K) u) ∈
      integralAtFinitePlaces (K := K) := by
  rw [← fractionalIdeal_ker, MonoidHom.mem_ker,
    fractionalIdeal_principalIdele]
  apply Units.ext
  rw [coe_toPrincipalIdeal]
  change
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
        (algebraMap (𝓞 K) K (u : 𝓞 K)) =
      (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
  rw [← FractionalIdeal.coeIdeal_span_singleton,
    Ideal.span_singleton_eq_top.mpr u.isUnit,
    FractionalIdeal.coeIdeal_top]

theorem finite_absoluteNorm_eq_one_of_integral
    (a : FiniteIdeleGroup K)
    (ha : a ∈ FiniteIdeleGroup.integralSubgroup (K := K)) :
    FiniteIdeleGroup.absoluteNorm a = 1 := by
  rw [FiniteIdeleGroup.absoluteNorm_eq_fractionalIdealAbsoluteNorm]
  have hfrac :
      FiniteIdeleGroup.fractionalIdeal a = 1 := by
    rw [← MonoidHom.mem_ker,
      FiniteIdeleGroup.fractionalIdeal_ker]
    exact ha
  rw [hfrac, map_one]

/-- For an idele which is integral at all finite places, the global norm-one
condition is exactly the archimedean norm-one condition. -/
theorem archimedeanNorm_eq_one_of_normOne_integral
    (a : IdeleGroup K)
    (hnorm : a ∈ normOneSubgroup (K := K))
    (hintegral :
      a.2 ∈ FiniteIdeleGroup.integralSubgroup (K := K)) :
    InfiniteIdeleGroup.archimedeanNorm a.1 = 1 := by
  have hfin :=
    finite_absoluteNorm_eq_one_of_integral a.2 hintegral
  change absoluteNorm a = 1 at hnorm
  rw [absoluteNorm_apply, hfin, one_mul] at hnorm
  exact inv_eq_one.mp hnorm

/-- The fixed compact set of norm-one ideles which are integral at every
finite place and logarithmically reduced modulo the ordinary units. -/
def compactIntegralNormOneSet : Set (IdeleGroup K) :=
  (InfiniteIdeleGroup.annulus (K := K)
      ((Fintype.card (InfinitePlace K) : ℝ) *
        InfiniteIdeleGroup.logFundamentalBound (K := K)) ×ˢ
    (FiniteIdeleGroup.integralSubgroup (K := K) :
      Set (FiniteIdeleGroup K))) ∩
  {a | InfiniteIdeleGroup.archimedeanNorm a.1 = 1}

theorem isCompact_compactIntegralNormOneSet :
    IsCompact (compactIntegralNormOneSet (K := K)) := by
  apply IsCompact.inter_right
  · exact
      (InfiniteIdeleGroup.isCompact_annulus
        ((Fintype.card (InfinitePlace K) : ℝ) *
          InfiniteIdeleGroup.logFundamentalBound (K := K))).prod
        (FiniteIdeleGroup.isCompact_integralSubgroup (K := K))
  · exact isClosed_singleton.preimage
      (InfiniteIdeleGroup.continuous_archimedeanNorm.comp continuous_fst)

theorem mem_compactIntegralNormOneSet_iff (a : IdeleGroup K) :
    a ∈ compactIntegralNormOneSet (K := K) ↔
      a.1 ∈ InfiniteIdeleGroup.annulus (K := K)
          ((Fintype.card (InfinitePlace K) : ℝ) *
            InfiniteIdeleGroup.logFundamentalBound (K := K)) ∧
        a.2 ∈ FiniteIdeleGroup.integralSubgroup (K := K) ∧
        InfiniteIdeleGroup.archimedeanNorm a.1 = 1 := by
  change
    ((a.1 ∈ InfiniteIdeleGroup.annulus (K := K)
          ((Fintype.card (InfinitePlace K) : ℝ) *
            InfiniteIdeleGroup.logFundamentalBound (K := K)) ∧
        a.2 ∈ FiniteIdeleGroup.integralSubgroup (K := K)) ∧
      InfiniteIdeleGroup.archimedeanNorm a.1 = 1) ↔ _
  tauto

/-- A norm-one idele integral at every finite place is principal-equivalent
to an element of the fixed compact representative set. -/
theorem exists_compactIntegralNormOneSet_representative
    (a : IdeleGroup K)
    (hnorm : a ∈ normOneSubgroup (K := K))
    (hintegral :
      a.2 ∈ FiniteIdeleGroup.integralSubgroup (K := K)) :
    ∃ b ∈ compactIntegralNormOneSet (K := K),
      QuotientGroup.mk' (principalSubgroup K) b =
        QuotientGroup.mk' (principalSubgroup K) a := by
  obtain ⟨u, hu⟩ :=
    InfiniteIdeleGroup.exists_ringUnit_logNorm_le a.1
  let p : IdeleGroup K :=
    principalIdele K
      (InfiniteIdeleGroup.ringUnitToFieldUnit (K := K) u)
  let b : IdeleGroup K := a * p
  have hpIntegral :
      p ∈ integralAtFinitePlaces (K := K) := by
    exact principalRingUnit_mem_integralAtFinitePlaces u
  have hbIntegral :
      b.2 ∈ FiniteIdeleGroup.integralSubgroup (K := K) := by
    exact (integralAtFinitePlaces (K := K)).mul_mem hintegral
      hpIntegral
  have hpNorm :
      p ∈ normOneSubgroup (K := K) := by
    exact principalSubgroup_le_normOneSubgroup
      ⟨InfiniteIdeleGroup.ringUnitToFieldUnit (K := K) u, rfl⟩
  have hbNorm :
      b ∈ normOneSubgroup (K := K) :=
    (normOneSubgroup (K := K)).mul_mem hnorm hpNorm
  have hbArch :
      InfiniteIdeleGroup.archimedeanNorm b.1 = 1 :=
    archimedeanNorm_eq_one_of_normOne_integral b hbNorm hbIntegral
  have hbLog :
      ‖InfiniteIdeleGroup.logNorm b.1‖ ≤
        InfiniteIdeleGroup.logFundamentalBound (K := K) := by
    exact hu
  have hbAnnulus :
      b.1 ∈ InfiniteIdeleGroup.annulus (K := K)
        ((Fintype.card (InfinitePlace K) : ℝ) *
          InfiniteIdeleGroup.logFundamentalBound (K := K)) :=
    InfiniteIdeleGroup.mem_annulus_of_logNorm_le
      InfiniteIdeleGroup.logFundamentalBound_nonneg b.1 hbLog hbArch
  refine ⟨b,
    (mem_compactIntegralNormOneSet_iff b).mpr
      ⟨hbAnnulus, hbIntegral, hbArch⟩, ?_⟩
  change
    (QuotientGroup.mk' (principalSubgroup K)) (a * p) =
      (QuotientGroup.mk' (principalSubgroup K)) a
  rw [map_mul]
  have hpOne :
      QuotientGroup.mk' (principalSubgroup K) p = 1 := by
    apply (QuotientGroup.eq_one_iff p).mpr
    exact
      ⟨InfiniteIdeleGroup.ringUnitToFieldUnit (K := K) u, rfl⟩
  rw [hpOne]
  exact mul_one
    (QuotientGroup.mk' (principalSubgroup K) a)

/-- For every ordinary ideal class which occurs on a norm-one idele, choose
one such representative; use `1` for the (irrelevant) remaining classes. -/
def normOneIdealClassRepresentative
    (c : ClassGroup (𝓞 K)) : IdeleGroup K :=
  if h : ∃ a : IdeleGroup K,
      a ∈ normOneSubgroup (K := K) ∧ idealClass a = c then
    Classical.choose h
  else
    1

theorem normOneIdealClassRepresentative_mem
    (c : ClassGroup (𝓞 K)) :
    normOneIdealClassRepresentative (K := K) c ∈
      normOneSubgroup (K := K) := by
  rw [normOneIdealClassRepresentative]
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact (normOneSubgroup (K := K)).one_mem

theorem idealClass_normOneIdealClassRepresentative
    (c : ClassGroup (𝓞 K))
    (h : ∃ a : IdeleGroup K,
      a ∈ normOneSubgroup (K := K) ∧ idealClass a = c) :
    idealClass (normOneIdealClassRepresentative (K := K) c) = c := by
  rw [normOneIdealClassRepresentative, dite_eq_left h]
  exact (Classical.choose_spec h).2

/-- The finite set of chosen norm-one representatives of ordinary ideal
classes. -/
def normOneIdealClassRepresentativeSet : Set (IdeleGroup K) :=
  Set.range (normOneIdealClassRepresentative (K := K))

theorem isCompact_normOneIdealClassRepresentativeSet :
    IsCompact (normOneIdealClassRepresentativeSet (K := K)) := by
  apply Set.Finite.isCompact
  exact Set.finite_range _

theorem normOneIdealClassRepresentativeSet_subset_normOne :
    normOneIdealClassRepresentativeSet (K := K) ⊆
      (normOneSubgroup (K := K) : Set (IdeleGroup K)) := by
  rintro _ ⟨c, rfl⟩
  exact normOneIdealClassRepresentative_mem c

/-- Remove the ordinary ideal class of a norm-one idele.  The result is
integral at every finite place, and multiplying back by the chosen
representative recovers the original idele class. -/
theorem exists_integral_normOne_reduction
    (a : IdeleGroup K)
    (ha : a ∈ normOneSubgroup (K := K)) :
    ∃ b : IdeleGroup K,
      b.2 ∈ FiniteIdeleGroup.integralSubgroup (K := K) ∧
      b ∈ normOneSubgroup (K := K) ∧
      QuotientGroup.mk' (principalSubgroup K)
          (b * normOneIdealClassRepresentative
            (K := K) (idealClass a)) =
        QuotientGroup.mk' (principalSubgroup K) a := by
  let r :=
    normOneIdealClassRepresentative (K := K) (idealClass a)
  have hrNorm : r ∈ normOneSubgroup (K := K) :=
    normOneIdealClassRepresentative_mem (idealClass a)
  have hrClass : idealClass r = idealClass a :=
    idealClass_normOneIdealClassRepresentative
      (idealClass a) ⟨a, ha, rfl⟩
  let d : IdeleGroup K := a * r⁻¹
  have hdClass : idealClass d = 1 := by
    dsimp [d]
    rw [map_mul, map_inv, hrClass]
    exact mul_inv_cancel _
  have hdPrincipal :
      fractionalIdeal d ∈
        (toPrincipalIdeal (𝓞 K) K).range := by
    change ClassGroup.mk K (fractionalIdeal d) = 1 at hdClass
    exact (classGroup_mk_eq_one_iff (fractionalIdeal d)).mp hdClass
  obtain ⟨x, hx⟩ := hdPrincipal
  let p : IdeleGroup K := principalIdele K x
  let b : IdeleGroup K := d * p⁻¹
  have hbIntegral :
      b.2 ∈ FiniteIdeleGroup.integralSubgroup (K := K) := by
    change b ∈ integralAtFinitePlaces (K := K)
    rw [← fractionalIdeal_ker, MonoidHom.mem_ker]
    dsimp [b, p]
    rw [map_mul, map_inv, fractionalIdeal_principalIdele,
      hx, mul_inv_cancel]
  have hdNorm :
      d ∈ normOneSubgroup (K := K) :=
    (normOneSubgroup (K := K)).mul_mem ha
      ((normOneSubgroup (K := K)).inv_mem hrNorm)
  have hpNorm :
      p ∈ normOneSubgroup (K := K) :=
    principalSubgroup_le_normOneSubgroup ⟨x, rfl⟩
  have hbNorm :
      b ∈ normOneSubgroup (K := K) :=
    (normOneSubgroup (K := K)).mul_mem hdNorm
      ((normOneSubgroup (K := K)).inv_mem hpNorm)
  refine ⟨b, hbIntegral, hbNorm, ?_⟩
  apply QuotientGroup.eq_iff_div_mem.mpr
  change b * r * a⁻¹ ∈ principalSubgroup K
  refine ⟨x⁻¹, ?_⟩
  dsimp [b, d, p]
  rw [map_inv]
  symm
  calc
    a * r⁻¹ * (principalIdele K x)⁻¹ * r * a⁻¹ =
        (a * a⁻¹) * (r⁻¹ * r) * (principalIdele K x)⁻¹ := by
      ac_rfl
    _ = (principalIdele K x)⁻¹ := by simp

/-- A compact set of ideles meeting every norm-one idele class. -/
def compactNormOneClassCover : Set (IdeleGroup K) :=
  compactIntegralNormOneSet (K := K) *
    normOneIdealClassRepresentativeSet (K := K)

theorem isCompact_compactNormOneClassCover :
    IsCompact (compactNormOneClassCover (K := K)) :=
  by
    simpa [compactNormOneClassCover] using
      (isCompact_compactIntegralNormOneSet (K := K)).mul
        (isCompact_normOneIdealClassRepresentativeSet (K := K))

theorem compactIntegralNormOneSet_subset_normOne :
    compactIntegralNormOneSet (K := K) ⊆
      (normOneSubgroup (K := K) : Set (IdeleGroup K)) := by
  intro a ha
  rw [mem_compactIntegralNormOneSet_iff] at ha
  have hfin :=
    finite_absoluteNorm_eq_one_of_integral a.2 ha.2.1
  change absoluteNorm a = 1
  rw [absoluteNorm_apply, hfin, ha.2.2, inv_one, mul_one]

theorem compactNormOneClassCover_subset_normOne :
    compactNormOneClassCover (K := K) ⊆
      (normOneSubgroup (K := K) : Set (IdeleGroup K)) := by
  rintro z ⟨b, hb, r, hr, rfl⟩
  exact (normOneSubgroup (K := K)).mul_mem
    (compactIntegralNormOneSet_subset_normOne hb)
    (normOneIdealClassRepresentativeSet_subset_normOne hr)

end IdeleGroup

namespace IdeleClassGroup

/-- The image of the compact idele cover is exactly the group of norm-one
idele classes. -/
theorem image_compactNormOneClassCover :
    (QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K)) ''
        IdeleGroup.compactNormOneClassCover (K := K) =
      (normOneSubgroup (K := K) : Set (IdeleClassGroup K)) := by
  ext q
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (mk_mem_normOneSubgroup_iff (K := K) a).mpr
      (IdeleGroup.compactNormOneClassCover_subset_normOne ha)
  · intro hq
    obtain ⟨a, rfl⟩ :=
      QuotientGroup.mk'_surjective
        (IdeleGroup.principalSubgroup K) q
    have ha :
        a ∈ IdeleGroup.normOneSubgroup (K := K) :=
      (mk_mem_normOneSubgroup_iff a).mp hq
    obtain ⟨b, hbIntegral, hbNorm, hbClass⟩ :=
      IdeleGroup.exists_integral_normOne_reduction a ha
    obtain ⟨c, hcCompact, hcClass⟩ :=
      IdeleGroup.exists_compactIntegralNormOneSet_representative
        b hbNorm hbIntegral
    let r : IdeleGroup K :=
      IdeleGroup.normOneIdealClassRepresentative
        (K := K) (IdeleGroup.idealClass a)
    refine ⟨c * r, ?_, ?_⟩
    · exact
        ⟨c, hcCompact, r,
          ⟨IdeleGroup.idealClass a, rfl⟩, rfl⟩
    · calc
        QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
            (c * r) =
            QuotientGroup.mk'
                (IdeleGroup.principalSubgroup K) c *
              QuotientGroup.mk'
                (IdeleGroup.principalSubgroup K) r := by
                  rw [map_mul]
        _ =
            QuotientGroup.mk'
                (IdeleGroup.principalSubgroup K) b *
              QuotientGroup.mk'
                (IdeleGroup.principalSubgroup K) r := by
                  rw [hcClass]
        _ =
            QuotientGroup.mk'
              (IdeleGroup.principalSubgroup K) (b * r) := by
                rw [map_mul]
        _ =
            QuotientGroup.mk'
              (IdeleGroup.principalSubgroup K) a := hbClass

/-- The norm-one idele class group is compact. -/
theorem normOneSubgroup_isCompact :
    IsCompact
      ((normOneSubgroup (K := K) :
        Subgroup (IdeleClassGroup K)) : Set (IdeleClassGroup K)) := by
  rw [← image_compactNormOneClassCover (K := K)]
  exact
    (IdeleGroup.isCompact_compactNormOneClassCover (K := K)).image
      QuotientGroup.continuous_mk

/-- Compact-space form of the compactness theorem for norm-one idele classes. -/
instance normOneSubgroupCompactSpace :
    CompactSpace (normOneSubgroup (K := K)) :=
  isCompact_iff_compactSpace.mp
    (normOneSubgroup_isCompact (K := K))

end IdeleClassGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_FullModulus
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Ray moduli with selected real places

A ray modulus consists of a finite modulus together with the real places at
which positivity is imposed.  This file defines the corresponding idèle and
idèle-class congruence subgroups without fixing an archimedean convention.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

namespace Modulus

instance instBot : Bot (Modulus K) where
  bot := 0

instance instOrderBot : OrderBot (Modulus K) where
  bot_le _ := ⟨bot_le, Finset.empty_subset _⟩

end Modulus

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_Topology
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.quotientRaySubgroupEquivIdealRayClassGroup_mk _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.infinitePlace_mult_smul
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

omit [NumberField K] in
/-- The positive local multiplicative group at an infinite place is
connected. -/
theorem isConnected_infinitePositiveSubgroup
    (v : InfinitePlace K) :
    IsConnected
      ((infinitePositiveSubgroup v : Subgroup v.Completionˣ) :
        Set v.Completionˣ) := by
  rw [isConnected_iff_connectedSpace]
  by_cases hv : v.IsReal
  · let e : v.Completionˣ ≃ₜ* ℝˣ :=
      Units.mapContinuousMulEquiv
        (realCompletionContinuousMulEquiv v hv)
    let f : Set.Ioi (0 : ℝ) → infinitePositiveSubgroup v :=
      fun x ↦
        ⟨e.symm (positiveRealUnit x), by
          apply (mem_infinitePositiveSubgroup_iff v _).2
          intro hv'
          have heq : hv' = hv :=
            Subsingleton.elim _ _
          subst hv'
          change
            0 < ((e (e.symm (positiveRealUnit x)) : ℝˣ) : ℝ)
          rw [e.apply_symm_apply]
          exact x.2⟩
    let : ConnectedSpace (Set.Ioi (0 : ℝ)) :=
      isConnected_iff_connectedSpace.mp isConnected_Ioi
    apply Function.Surjective.connectedSpace (f := f)
    · intro z
      have hzpos :
          0 < ((e z.1 : ℝˣ) : ℝ) := by
        change 0 <
          InfinitePlace.Completion.extensionEmbeddingOfIsReal
            hv (z.1 : v.Completion)
        exact
          ((mem_infinitePositiveSubgroup_iff v z.1).1 z.2 hv)
      let x : Set.Ioi (0 : ℝ) :=
        ⟨((e z.1 : ℝˣ) : ℝ), hzpos⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      change e.symm (positiveRealUnit x) = z.1
      apply e.injective
      simp [x, positiveRealUnit]
    · apply continuous_induced_rng.mpr
      exact e.symm.continuous.comp continuous_positiveRealUnit
  · have hvc : v.IsComplex :=
      InfinitePlace.not_isReal_iff_isComplex.mp hv
    let e : v.Completionˣ ≃ₜ* ℂˣ :=
      Units.mapContinuousMulEquiv
        (complexCompletionContinuousMulEquiv v hvc)
    let f : ℂˣ → infinitePositiveSubgroup v :=
      fun x ↦
        ⟨e.symm x, by
          apply (mem_infinitePositiveSubgroup_iff v _).2
          intro hv'
          exact (hv hv').elim⟩
    apply Function.Surjective.connectedSpace (f := f)
    · intro z
      refine ⟨e z.1, ?_⟩
      apply Subtype.ext
      exact e.symm_apply_apply z.1
    · apply continuous_induced_rng.mpr
      exact e.symm.continuous

omit [NumberField K] in
/-- The narrow archimedean positivity subgroup is connected. -/
theorem isConnected_narrowInfiniteCongruenceSubgroup :
    IsConnected
      ((narrowInfiniteCongruenceSubgroup (K := K) :
        Subgroup (InfiniteIdeleGroup K)) :
          Set (InfiniteIdeleGroup K)) := by
  rw [isConnected_iff_connectedSpace]
  let (v : InfinitePlace K) :
      ConnectedSpace (infinitePositiveSubgroup v) :=
    isConnected_iff_connectedSpace.mp
      (isConnected_infinitePositiveSubgroup v)
  let f :
      (∀ v : InfinitePlace K, infinitePositiveSubgroup v) →
        narrowInfiniteCongruenceSubgroup (K := K) :=
    fun x ↦
      ⟨ContinuousMulEquiv.piUnits.symm
          (fun v ↦ (x v : v.Completionˣ)), by
        apply (mem_narrowInfiniteCongruenceSubgroup_iff _).2
        intro v
        exact (x v).2⟩
  apply Function.Surjective.connectedSpace (f := f)
  · intro a
    let x : ∀ v : InfinitePlace K, infinitePositiveSubgroup v :=
      fun v ↦
        ⟨ContinuousMulEquiv.piUnits a.1 v,
          (mem_narrowInfiniteCongruenceSubgroup_iff a.1).1 a.2 v⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change ContinuousMulEquiv.piUnits.symm
        (fun v ↦ (x v : v.Completionˣ)) = a.1
    apply ContinuousMulEquiv.piUnits.injective
    simp [x]
  · apply continuous_induced_rng.mpr
    apply ContinuousMulEquiv.piUnits.symm.continuous.comp
    exact continuous_pi fun v ↦
      continuous_subtype_val.comp (continuous_apply v)

/-- The image of the connected narrow archimedean positivity subgroup lies in
every open subgroup of the idele class group. -/
theorem narrowInfiniteCongruenceSubgroup_mapsTo_openSubgroup
    (H : Subgroup (IdeleClassGroup K))
    (hH : IsOpen (H : Set (IdeleClassGroup K)))
    {a : InfiniteIdeleGroup K}
    (ha : a ∈ narrowInfiniteCongruenceSubgroup (K := K)) :
    (((a, (1 : FiniteIdeleGroup K)) : IdeleGroup K) :
      IdeleClassGroup K) ∈ H := by
  let : ConnectedSpace
      (narrowInfiniteCongruenceSubgroup (K := K)) :=
    isConnected_iff_connectedSpace.mp
      isConnected_narrowInfiniteCongruenceSubgroup
  let f :
      narrowInfiniteCongruenceSubgroup (K := K) →
        IdeleClassGroup K :=
    fun x ↦
      (((x.1, (1 : FiniteIdeleGroup K)) : IdeleGroup K) :
        IdeleClassGroup K)
  have hf : Continuous f := by
    apply QuotientGroup.continuous_mk.comp
    exact continuous_subtype_val.prodMk continuous_const
  have hf_one : f 1 = 1 := by
    change
      ((QuotientGroup.mk'
        (IdeleGroup.principalSubgroup K))
          ((1 : InfiniteIdeleGroup K),
            (1 : FiniteIdeleGroup K))) = 1
    exact map_one _
  have hinter :
      (Set.range f ∩ (H : Set (IdeleClassGroup K))).Nonempty := by
    refine ⟨1, ?_, H.one_mem⟩
    exact ⟨1, hf_one⟩
  have hsubset : Set.range f ⊆ (H : Set (IdeleClassGroup K)) :=
    (isConnected_range hf).isPreconnected.subset_isClopen
      ⟨H.isClosed_of_isOpen hH, hH⟩ hinter
  exact hsubset ⟨⟨a, ha⟩, rfl⟩

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_NormQuotient
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
# Quotients by local norm subgroups

Constructs `Kˣ/N(Lˣ)`, its universal maps and comparison equivalences, and
relates its finite cardinality to the index of the norm subgroup.
-/

namespace LocalFieldTheory

noncomputable section

universe u v

/-- A map obtained by descending a surjective homomorphism through the norm
quotient is still surjective. -/
theorem normQuotientLift_surjective {K L : Type u} {M : Type v} [Field K] [Field L]
    [Algebra K L] [Group M] (f : Kˣ →* M)
    (h : localNormSubgroup K L ≤ f.ker) (hf : Function.Surjective f) :
    Function.Surjective (normQuotientLift f h) := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨normClass K L x, normQuotientLift_normClass f h x⟩

/-! ### Surjectivity and equality refinements for norm quotients -/

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_Basic
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.CompleteDVF.instIsAdicComplete _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Discretely valued fields

This is the basic one-dimensional API for fields equipped with a chosen
rank-one discrete valuation.
-/

noncomputable section

universe u v

namespace DiscreteValuationField

namespace DVF

variable {K : Type u} [Field K]

/-- Multiplying a uniformizer by a valuation-ring unit does not move it into
the square of the maximal ideal. -/
theorem uniformizer_mul_unit_not_mem_maximalIdeal_sq
    (F : DVF.{u, v} K) {pi u : F.valuationSubring}
    (hpi : F.valuation.IsUniformizer (pi : K)) (hu : IsUnit u) :
    pi * u ∉ F.maximalIdeal ^ 2 := by
  intro hmem
  have hmem' : u * pi ∈ F.maximalIdeal ^ 2 := by
    rw [mul_comm u pi]
    exact hmem
  exact F.uniformizer_not_mem_maximalIdeal_sq hpi
    (((F.maximalIdeal ^ 2).unit_mul_mem_iff_mem hu).1 hmem')

/-! ### Successive quotients of powers of the maximal ideal -/

end DVF
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_FiniteExtension_Degree
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseValuationIsNontrivial _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace ValuationTheory

/-!
# Finite valued extension consequences

This file collects theorem-level consequences around finite valued extensions:
canonical local-Dedekind degree formulas, uniqueness criteria for extended
valuations, and the algebra equivalence identifying an actual integral-closure
valuation ring with mathlib's `integralClosure`.
-/

noncomputable section

universe u v w x y

namespace DiscreteValuationField
namespace ValuedExtension

open ValuationTheory.DiscreteValuationField.Valuation

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

omit [FiniteDimensional K L] in
/-- The residue degree of a finite extension is strictly positive. -/
theorem residueDegree_pos
    [Module.Finite base.valuationSubring target.valuationSubring] :
    0 < (ValuedExtension.residueDegree base.toDVF target.toDVF) := by
  let : target.maximalIdeal.LiesOver base.maximalIdeal :=
    (maximalIdeal_liesOver base target)
  simpa [residueDegree, residueDegree] using
    (target.maximalIdeal.inertiaDeg_pos base.valuationSubring)

omit [FiniteDimensional K L] in
/-- A finite extension of valuation rings induces a finite-dimensional residue
field extension.  This is the source behind using a primitive element for the
residue extension: mathlib's inertia degree is the residue-field `finrank`. -/
theorem residueField_finiteDimensional_of_moduleFinite
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring] :
    FiniteDimensional base.residueField target.residueField := by
  have h := residueDegree_pos base target
  rw [residueDegree_eq_finrank_quotient base target] at h
  exact FiniteDimensional.of_finrank_pos h

omit [FiniteDimensional K L] in
/-- The ramification index of a finite extension is nonzero. -/
theorem ramificationIndex_ne_zero
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring] :
    (ValuedExtension.ramificationIndex base.toDVF target.toDVF) ≠ 0 := by
  let : target.maximalIdeal.LiesOver base.maximalIdeal :=
    (maximalIdeal_liesOver base target)
  simpa [ramificationIndex] using
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
      target.maximalIdeal base.maximalIdeal_ne_bot)

omit [FiniteDimensional K L] in
/-- The actual local-Dedekind fundamental identity for the chosen valuation
rings: in the local case, the mathlib ramification index times the mathlib
inertia degree is the field degree. -/
theorem ramificationIndex_mul_residueDegree_eq_degree
    [Module.Finite base.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    (ValuedExtension.ramificationIndex base.toDVF target.toDVF) *
        ValuedExtension.residueDegree base.toDVF target.toDVF =
      ValuedExtension.degree base.toDVF target.toDVF := by
  simpa [ramificationIndex, residueDegree,
    ramificationIndex, residueDegree, degree] using
    (ideal_ramificationIdx_mul_inertiaDeg_eq_finrank_of_hasExtension
      (K := K) (L := L) base target)

end ValuedExtension
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_FiniteExtension_Uniqueness
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-! Provides the public declarations in the `ValuationTheory.DiscreteValuationField.FiniteExtension.Uniqueness` Lean module. -/

namespace ValuationTheory

noncomputable section

universe u v w x y

namespace DiscreteValuationField
namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- In a finite separable extension of complete DVFs, every extension valuation
is equivalent to the chosen target valuation. -/
theorem valuation_isEquiv_of_finite_separable

    [Algebra.IsSeparable K L]
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma') [base.valuation.HasExtension v'] :
    target.valuation.IsEquiv v' :=
  ((hasUniqueValuationExtension_of_finite_separable base target) :
    HasUniqueValuationExtension.{u, v, w, x, y}
      (base := base) (target := target)) v'

end ValuedExtension
end DiscreteValuationField

end

end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnits_Core
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.representedQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FiniteResidueAbstractExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.DegreeData.FiniteTower.baseQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.topQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteAbstractFieldExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.inertiaSubgroupOfDecomposition_normal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageClassInQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageSubgroup_normal _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false
/-!
Develops quotients of valuation-ring units by higher principal units and compares their first
layer with residue-field units.
-/

namespace LocalFieldTheory

open ValuationTheory

noncomputable section

open scoped BigOperators

universe u v

namespace DiscreteValuationField
namespace CompleteDVF

variable {K : Type u} [Field K]

namespace higherPrincipalUnitGroup

open ValuationTheory.DiscreteValuationField.DVF

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- The type in `Finite (F.valuationSubring ⧸ F.maximalIdeal ^ n)` is finite. -/
noncomputable instance quotientMaximalIdealPowFinite
    [Finite F.residueField] (n : ℕ) :
    Finite (F.valuationSubring ⧸ F.maximalIdeal ^ n) :=
  higherPrincipalUnitGroup.finite_quotient_maximalIdeal_pow_of_finite_residue F n

/-- The type in `Finite (F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n)` is finite. -/
noncomputable instance unitsModHigherPrincipalUnitGroupFinite
    [Finite F.residueField] (n : ℕ) :
    Finite (F.valuationSubringˣ ⧸ higherPrincipalUnitGroup F n) :=
  higherPrincipalUnitGroup.finite_unitsModHigherPrincipalUnitGroup_of_finite_residue
    F n

/--
The type in `Finite (higherPrincipalUnitGroup F m ⧸ (higherPrincipalUnitGroup F n).subgroupOf
(higherPrincipalUnitGroup F m))` is finite.
-/
noncomputable instance principalUnitSubquotientFinite
    [Finite F.residueField] (m n : ℕ) :
    Finite (higherPrincipalUnitGroup F m ⧸
      (higherPrincipalUnitGroup F n).subgroupOf
        (higherPrincipalUnitGroup F m)) :=
  higherPrincipalUnitGroup.finite_principalUnitSubquotient_of_finite_residue
    F m n

/--
The type in `Finite ((higherPrincipalUnitGroup.toPrincipalUnitFiltration
F).principalUnitSubquotient m n)` is finite.
-/
noncomputable instance toPrincipalUnitFiltrationPrincipalUnitSubquotientFinite
    [Finite F.residueField] (m n : ℕ) :
    Finite
      ((higherPrincipalUnitGroup.toPrincipalUnitFiltration F).principalUnitSubquotient
        m n) := by
  let U := higherPrincipalUnitGroup.toPrincipalUnitFiltration F
  exact Finite.of_equiv
    (higherPrincipalUnitGroup F m ⧸
      (higherPrincipalUnitGroup F n).subgroupOf
        (higherPrincipalUnitGroup F m))
    (U.principalUnitSubquotientConcreteEquiv m n).symm.toEquiv

/-! ### Successive principal-unit quotients -/

/-- The type in `Finite (higherPrincipalUnitGroup.principalUnitSuccQuot F n)` is finite. -/
noncomputable instance principalUnitSuccQuotFinite
    [Finite F.residueField] (n : ℕ) :
    Finite (higherPrincipalUnitGroup.principalUnitSuccQuot F n) :=
  Finite.of_equiv
    (higherPrincipalUnitGroup F n ⧸
      (higherPrincipalUnitGroup F (n + 1)).subgroupOf
        (higherPrincipalUnitGroup F n))
    (higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv F n).symm.toEquiv

end higherPrincipalUnitGroup

end CompleteDVF
end DiscreteValuationField

end

end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_NormalizedIntegerValuation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientMaximalIdealPowFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltrationPrincipalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The normalized integer valuation of a local field

The Kummer branch of the local existence theorem uses power-class index
formulas stated for valuations with value group
`WithZero (Multiplicative ℤ)`.  A nonarchimedean local field carries its
canonical valuation in an intrinsic value group.  This file transports that
valuation to the integer model and proves that completeness and the finite
residue field are preserved.
-/

noncomputable section

namespace LocalFieldTheory

open scoped ValuativeRel

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The normalized valuation has the same finite residue field as the
canonical local valuation. -/
noncomputable instance localIntegerValuation_residueFinite :
    Finite
      (IsLocalRing.ResidueField
        (localIntegerValuation K).valuationSubring) := by
  have hfinite : Finite (localCompleteDVF K).residueField := by
    change Finite 𝓀[K]
    infer_instance
  let e := localIntegerValuationSubringEquiv K
  exact Finite.of_equiv (localCompleteDVF K).residueField
    (IsLocalRing.ResidueField.mapEquiv e).symm.toEquiv

end LocalFieldTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_UnramifiedFrobenius
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LocalFieldTheory.localIntegerValuation_residueFinite _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_finite_residue _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.CyclicCohomology.galoisGroupIntegerUnitsModPrincipalUnitsMapEquivOfIsIntegralClosure_mk _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalFieldTheory

/-!
# Actual unramified Frobenius

The arithmetic Frobenius is first defined as finite-field Frobenius on the
residue extension, then lifted to `Gal(L / K)` through the canonical
residue-action isomorphism for a finite unramified extension.
-/

noncomputable section

universe u

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField

/-- Field arithmetic Frobenius acts on residues by raising them to the size of the base residue
field. -/
theorem galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_apply
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (x : 𝓀[L]) :
    galoisGroupResidueAlgEquivOfIsIntegralClosure K L
        (arithmeticFrobeniusOfUnramifiedValuation K L) x =
      x ^ Nat.card 𝓀[K] := by
  rw [galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius]
  exact residueExtensionArithmeticFrobeniusOfValuationExtension_apply K L x

/-- Arithmetic Frobenius sends a primitive root of unity of order prime to the
base residue cardinality to its residue-cardinality power. -/
theorem arithmeticFrobeniusOfUnramifiedValuation_apply_primitiveRoot
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    {n : Nat} {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (hcoprime : (Nat.card 𝓀[K]).Coprime n) :
    arithmeticFrobeniusOfUnramifiedValuation K L ζ =
      ζ ^ Nat.card 𝓀[K] := by
  classical
  let := Fintype.ofFinite 𝓀[K]
  obtain ⟨d, hp, hcard⟩ :=
    FiniteField.card 𝓀[K] (ringChar 𝓀[K])
  have hpCard : ringChar 𝓀[K] ∣ Nat.card 𝓀[K] := by
    rw [Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self (ringChar 𝓀[K]) d.ne_zero
  have hnChar : ¬ringChar 𝓀[K] ∣ n :=
    hp.coprime_iff_not_dvd.mp (hcoprime.coprime_dvd_left hpCard)
  have hnK : (n : 𝓀[K]) ≠ 0 := by
    intro hzero
    exact hnChar ((ringChar.spec 𝓀[K] n).mp hzero)
  have hnL : (n : 𝓀[L]) ≠ 0 := by
    intro hzero
    apply hnK
    apply (algebraMap 𝓀[K] 𝓀[L]).injective
    calc
      algebraMap 𝓀[K] 𝓀[L] (n : 𝓀[K]) = (n : 𝓀[L]) := map_natCast _ n
      _ = 0 := hzero
      _ = algebraMap 𝓀[K] 𝓀[L] 0 := (map_zero _).symm
  have hn : n ≠ 0 := by
    intro hzero
    exact hnK (by simp [hzero])
  have hζIntegral : IsIntegral 𝒪[K] ζ := by
    apply IsIntegral.of_pow (Nat.pos_iff_ne_zero.mpr hn)
    rw [hζ.pow_eq_one]
    exact isIntegral_one
  rcases
      (IsIntegralClosure.isIntegral_iff
        (A := 𝒪[L]) (R := 𝒪[K]) (B := L)).1 hζIntegral with
    ⟨a, ha⟩
  change (a : L) = ζ at ha
  let φ : Gal(L / K) :=
    arithmeticFrobeniusOfUnramifiedValuation K L
  let b : 𝒪[L] :=
    galoisGroupIntegerRingEquivOfIsIntegralClosure K L φ a
  let c : 𝒪[L] := a ^ Nat.card 𝓀[K]
  let f : Polynomial 𝒪[L] := Polynomial.X ^ n - 1
  have haPow : a ^ n = 1 := by
    apply 𝒪[L].subtype_injective
    change (a : L) ^ n = 1
    rw [ha]
    exact hζ.pow_eq_one
  have hbPow : b ^ n = 1 := by
    have hφa : φ (a : L) ^ n = 1 := by
      rw [ha]
      simpa using congrArg φ hζ.pow_eq_one
    apply 𝒪[L].subtype_injective
    simpa [b] using hφa
  have hcPow : c ^ n = 1 := by
    change (a ^ Nat.card 𝓀[K]) ^ n = 1
    rw [← pow_mul, Nat.mul_comm, pow_mul, haPow, one_pow]
  have hbRoot : f.IsRoot b := by
    rw [Polynomial.IsRoot.def]
    simp [f, hbPow]
  have hcRoot : f.IsRoot c := by
    rw [Polynomial.IsRoot.def]
    simp [f, hcPow]
  have hres :
      IsLocalRing.residue 𝒪[L] b =
        IsLocalRing.residue 𝒪[L] c := by
    calc
      IsLocalRing.residue 𝒪[L] b =
          galoisGroupResidueAlgEquivOfIsIntegralClosure K L φ
            (IsLocalRing.residue 𝒪[L] a) := by
        exact
          (galoisGroupResidueFieldEquivOfIsIntegralClosure_residue
            K L φ a).symm
      _ = (IsLocalRing.residue 𝒪[L] a) ^ Nat.card 𝓀[K] := by
        simpa [φ] using
          galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_apply
            K L (IsLocalRing.residue 𝒪[L] a)
      _ = IsLocalRing.residue 𝒪[L] c := by
        simp [c]
  have hnUnit : IsUnit (n : 𝒪[L]) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit (n : 𝒪[L])).1
    simpa using hnL
  have hcUnit : IsUnit c :=
    IsUnit.of_pow_eq_one hcPow hn
  have hderiv : IsUnit (f.derivative.eval c) := by
    simpa [f, Polynomial.derivative_sub, Polynomial.derivative_one,
      Polynomial.derivative_X_pow, Polynomial.eval_mul] using
      hnUnit.mul (hcUnit.pow (n - 1))
  have hbc : b = c :=
    eq_of_simple_roots_of_residue_eq hcRoot hbRoot hres hderiv
  have hval := congrArg (fun x : 𝒪[L] => (x : L)) hbc
  have hval' :
      φ (a : L) = (a : L) ^ Nat.card 𝓀[K] := by
    simpa [b, c] using hval
  change φ ζ = ζ ^ Nat.card 𝓀[K]
  calc
    φ ζ = φ (a : L) := by rw [ha]
    _ = (a : L) ^ Nat.card 𝓀[K] := hval'
    _ = ζ ^ Nat.card 𝓀[K] := by rw [ha]

/-- The order of the actual unramified Galois group is the degree. This is the
cardinality consequence of the normalized Frobenius construction: arithmetic
Frobenius has order `[L : K]` and generates `Gal(L/K)`. -/
theorem galoisGroup_card_eq_finrank_of_unramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Nat.card Gal(L / K) = Module.finrank K L := by
  have hcard :=
    orderOf_eq_card_of_zpowers_eq_top
      (arithmeticFrobeniusOfUnramifiedValuation_zpowers_eq_top K L)
  exact hcard.symm.trans (orderOf_arithmeticFrobeniusOfUnramifiedValuation K L)

end
end LocalFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormTopology_ArchimedeanNorm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Archimedean behavior of idele norms

The positive archimedean norm, and consequently the absolute idele norm, is
preserved by the ordinary norm in a finite number-field extension.
-/

open scoped BigOperators NumberField NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

theorem nnnormUnitHom_map_ringEquiv_of_isometry
    {F E : Type*}
    [NormedField F] [NormedField E]
    (e : F ≃+* E) (he : Isometry e) (x : Fˣ) :
    nnnormUnitHom E
        (Units.mapEquiv e.toMulEquiv x) =
      nnnormUnitHom F x := by
  apply Units.ext
  apply NNReal.eq
  exact
    he.norm_map_of_map_zero (map_zero e) (x : F)


end IdeleGroup

end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_NormTopology_ExtensionBehavior
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Scalar-extension behavior of idele norms

Scalar extension raises the finite, archimedean, and absolute idele norms to
the degree of the number-field extension. The rational relative-idele
base-change realization is included as the endpoint used by cyclotomic
reciprocity.
-/

open scoped BigOperators Classical NumberField NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace IdeleGroup

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

omit [NumberField L] in
/-- Mapping a unit along an infinite-place completion map preserves its
positive norm. -/
theorem nnnormUnitHom_infinitePlaceCompletionMap
    (v₀ : InfinitePlace K)
    (W : InfinitePlace L)
    [W.1.LiesOver v₀.1]
    (x : v₀.Completionˣ) :
    nnnormUnitHom W.Completion
        (Units.map
          (NumberField.LiesOver.completionMap
            (v := v₀) (w := W)) x) =
      nnnormUnitHom v₀.Completion x := by
  apply Units.ext
  change
    ‖NumberField.LiesOver.completionMap
        (v := v₀) (w := W) (x : v₀.Completion)‖₊ =
      ‖(x : v₀.Completion)‖₊
  apply NNReal.eq
  exact
    (infinitePlaceCompletionMap_isometry
      (K := K) (L := L) v₀ W).norm_map_of_map_zero
      (map_zero
        (NumberField.LiesOver.completionMap
          (v := v₀) (w := W)))
      (x : v₀.Completion)


end IdeleGroup

end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_IdealNorm
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Norms of ideals prime to a modulus

For a finite extension `L / K`, the norm of a prime of `L`
above `v` is `v` raised to the inertia degree.  Extending this rule
multiplicatively gives the genuine norm on nonzero fractional ideals.

If `m` is a modulus of `K`, a modulus upstairs is chosen deeply enough
at every prime above `m` that local norms preserve the prescribed
higher-unit conditions.  The norm therefore restricts to the groups of
fractional ideals prime to these moduli.  Its image, together with the
principal ray ideals, is the norm-defined ideal group
`N_{L/K} J_L^m P_K^m`.
-/

open scoped BigOperators Classical NumberField Topology
open NumberField IsDedekindDomain

noncomputable section

namespace RayClass

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

theorem factorizationEquiv_symm_toAdd
    (I : FractionalIdealGroup L) :
    ((FractionalIdealGroup.factorizationEquiv
      (K := L)).symm I).toAdd =
        FractionalIdealGroup.countVector I := by
  ext W
  have h := FractionalIdealGroup.count_factorization
    ((FractionalIdealGroup.factorizationEquiv
      (K := L)).symm I) W
  have hfac :=
    (FractionalIdealGroup.factorizationEquiv
      (K := L)).apply_symm_apply I
  change
    FractionalIdealGroup.factorization
      ((FractionalIdealGroup.factorizationEquiv
        (K := L)).symm I) = I at hfac
  rw [hfac] at h
  exact h.symm.trans (FractionalIdealGroup.countVector_apply I W).symm

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_Narrow
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.IdeleClassGroup.normOneSubgroupCompactSpace _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.ideleGroupLocallyCompactSpace _root_.infiniteIdeleGroupLocallyCompactSpace
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.FiniteIdeleGroup.absoluteNorm_apply _root_.IdeleClassGroup.absoluteNorm_mk _root_.IdeleClassGroup.mk_mem_normOneSubgroup_iff _root_.IdeleGroup.absoluteNorm_apply _root_.IdeleGroup.absoluteNorm_principalIdele _root_.InfiniteIdeleGroup.archimedeanNorm_apply _root_.InfiniteIdeleGroup.logNorm_mul _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.quotientRaySubgroupEquivIdealRayClassGroup_mk _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Narrow ideal classes

This file proves the exact sequence from
global unit signs through the narrow and ordinary class groups.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

theorem finiteCongruenceSubgroup_zero :
    finiteCongruenceSubgroup (0 : FiniteModulus K) =
      FiniteIdeleGroup.integralSubgroup (K := K) := by
  ext a
  simp only [mem_finiteCongruenceSubgroup_iff,
    Finsupp.zero_apply, localHigherUnitGroup_zero,
    FiniteIdeleGroup.mem_integralSubgroup_iff]

/-- The subgroup generated by the zero-modulus congruence subgroup and
the principal ideles; its quotient is the narrow class group. -/
def narrowDenominator :
    Subgroup (IdeleGroup K) :=
  (Modulus.narrowOfFinite (0 : FiniteModulus K)).ideleCongruenceSubgroup ⊔
    IdeleGroup.principalSubgroup K

/-- The narrow class group realized as an idele quotient. -/
abbrev NarrowClassGroup
    (K : Type*) [Field K] [NumberField K] :=
  IdeleGroup K ⧸ narrowDenominator (K := K)

/-- The quotient of infinite ideles by the positive congruence
subgroup. -/
abbrev realSignGroup
    (K : Type*) [Field K] [NumberField K] :=
  InfiniteIdeleGroup K ⧸ narrowInfiniteCongruenceSubgroup (K := K)

/-- Embed an infinite idele as an idele with trivial finite component. -/
def infiniteToIdele :
    InfiniteIdeleGroup K →* IdeleGroup K where
  toFun a := (a, 1)
  map_one' := rfl
  map_mul' _ _ := by simp

/-- Map an infinite idele to its narrow ideal class. -/
def infiniteToNarrow :
    InfiniteIdeleGroup K →* NarrowClassGroup K :=
  (QuotientGroup.mk' (narrowDenominator (K := K))).comp
    (infiniteToIdele (K := K))

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_RayClass_Rational
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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

attribute [local instance] RayClass.rationalRingOfIntegersIsPrincipalIdealRing
local instance rationalNatGeneratorPrimeFact_raa7634_1
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.natGenerator v)) :=
  ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
local instance rationalPrimesEquivPrimeFact_raa7634_1
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Fact
      (Nat.Prime
        ((Rat.HeightOneSpectrum.primesEquiv
          (R := 𝓞 ℚ) v : Nat.Primes) : ℕ)) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv
    (R := 𝓞 ℚ) v).property⟩
/-- The finite part of the modulus `(m)` of `ℚ`.  At the prime over `p` it has
exponent `m.factorization p`. The later equivalences use the hypothesis
`0 < m`; the definition itself is harmless at `m = 0`.
-/
noncomputable def rationalFiniteModulus (m : ℕ) : FiniteModulus ℚ :=
  Finsupp.comapDomain
    Rat.HeightOneSpectrum.natGenerator
    m.factorization
    rational_natGenerator_injective.injOn

@[simp]
theorem rationalFiniteModulus_apply
    (m : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    rationalFiniteModulus m v =
      m.factorization (Rat.HeightOneSpectrum.natGenerator v) := by
  rw [rationalFiniteModulus, Finsupp.comapDomain_apply]

/-- The fractional ideal underlying a rational fractional-ideal unit. -/
abbrev rationalFractionalIdeal (I : FractionalIdealGroup ℚ) :
    FractionalIdeal (nonZeroDivisors (𝓞 ℚ)) ℚ :=
  I

/-- An arbitrary principal generator of a nonzero rational fractional
ideal, before choosing its sign. -/
noncomputable def rawRationalIdealGenerator
    (I : FractionalIdealGroup ℚ) : ℚ :=
  Submodule.IsPrincipal.generator
    ((rationalFractionalIdeal I : FractionalIdeal
      (nonZeroDivisors (𝓞 ℚ)) ℚ) : Submodule (𝓞 ℚ) ℚ)

theorem rawRationalIdealGenerator_ne_zero
    (I : FractionalIdealGroup ℚ) :
    rawRationalIdealGenerator I ≠ 0 := by
  apply mt
    (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero
      ((rationalFractionalIdeal I : FractionalIdeal
        (nonZeroDivisors (𝓞 ℚ)) ℚ) : Submodule (𝓞 ℚ) ℚ)).2
  exact FractionalIdeal.coeToSubmodule_ne_bot.mpr (Units.ne_zero I)

/-- The unique positive generator of a nonzero rational fractional ideal. -/
noncomputable def positiveRationalIdealGenerator
    (I : FractionalIdealGroup ℚ) : ℚ :=
  if 0 < rawRationalIdealGenerator I then
    rawRationalIdealGenerator I
  else
    -rawRationalIdealGenerator I

theorem positiveRationalIdealGenerator_pos
    (I : FractionalIdealGroup ℚ) :
    0 < positiveRationalIdealGenerator I := by
  rw [positiveRationalIdealGenerator]
  split_ifs with h
  · exact h
  · exact neg_pos.mpr
      (lt_of_le_of_ne (not_lt.mp h)
        (rawRationalIdealGenerator_ne_zero I))

theorem rationalFractionalIdeal_eq_span_positiveGenerator
    (I : FractionalIdealGroup ℚ) :
    rationalFractionalIdeal I =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ℚ))
        (positiveRationalIdealGenerator I) := by
  calc
    rationalFractionalIdeal I =
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ℚ))
          (rawRationalIdealGenerator I) :=
      FractionalIdeal.eq_spanSingleton_of_principal _
    _ = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ℚ))
          (positiveRationalIdealGenerator I) := by
      rw [positiveRationalIdealGenerator]
      split_ifs with h
      · rfl
      · apply
          (FractionalIdeal.spanSingleton_eq_spanSingleton
            (S := nonZeroDivisors (𝓞 ℚ))).2
        refine ⟨-1, ?_⟩
        simp

@[simp]
theorem positiveRationalIdealGenerator_one :
    positiveRationalIdealGenerator (1 : FractionalIdealGroup ℚ) = 1 := by
  apply eq_of_spanSingleton_eq_of_pos
    (positiveRationalIdealGenerator_pos 1) zero_lt_one
  rw [← rationalFractionalIdeal_eq_span_positiveGenerator]
  exact FractionalIdeal.spanSingleton_one.symm

theorem positiveRationalIdealGenerator_mul
    (I J : FractionalIdealGroup ℚ) :
    positiveRationalIdealGenerator (I * J) =
      positiveRationalIdealGenerator I *
        positiveRationalIdealGenerator J := by
  apply eq_of_spanSingleton_eq_of_pos
    (positiveRationalIdealGenerator_pos (I * J))
    (mul_pos (positiveRationalIdealGenerator_pos I)
      (positiveRationalIdealGenerator_pos J))
  rw [← rationalFractionalIdeal_eq_span_positiveGenerator,
    ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    ← rationalFractionalIdeal_eq_span_positiveGenerator,
    ← rationalFractionalIdeal_eq_span_positiveGenerator]
  rfl

/-- The positive generator, regarded as a nonzero rational number. -/
noncomputable def positiveRationalIdealGeneratorUnit
    (I : FractionalIdealGroup ℚ) : ℚˣ :=
  Units.mk0 (positiveRationalIdealGenerator I)
    (ne_of_gt (positiveRationalIdealGenerator_pos I))

@[simp]
theorem positiveRationalIdealGeneratorUnit_val
    (I : FractionalIdealGroup ℚ) :
    (positiveRationalIdealGeneratorUnit I : ℚ) =
      positiveRationalIdealGenerator I :=
  rfl

theorem toPrincipalIdeal_positiveRationalIdealGeneratorUnit
    (I : FractionalIdealGroup ℚ) :
    toPrincipalIdeal (𝓞 ℚ) ℚ
        (positiveRationalIdealGeneratorUnit I) = I := by
  apply Units.ext
  rw [coe_toPrincipalIdeal]
  change
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ℚ))
        (positiveRationalIdealGenerator I) =
      rationalFractionalIdeal I
  exact (rationalFractionalIdeal_eq_span_positiveGenerator I).symm

@[simp]
theorem positiveRationalIdealGeneratorUnit_one :
    positiveRationalIdealGeneratorUnit
      (1 : FractionalIdealGroup ℚ) = 1 := by
  apply Units.ext
  exact positiveRationalIdealGenerator_one

/-- The numerator of a rational number as a residue-class unit. -/
def rationalNumeratorResidueUnit
    (m : ℕ) (q : ℚ) (hq : Nat.Coprime q.num.natAbs m) :
    (ZMod m)ˣ :=
  ZMod.unitOfIsCoprime q.num <| by
    simpa [Int.isCoprime_iff_nat_coprime] using hq

/-- The denominator of a rational number as a residue-class unit. -/
def rationalDenominatorResidueUnit
    (m : ℕ) (q : ℚ) (hq : Nat.Coprime q.den m) :
    (ZMod m)ˣ :=
  ZMod.unitOfIsCoprime (q.den : ℤ) <| by
    simpa [Int.isCoprime_iff_nat_coprime] using hq

/-- Reduction of a rational number whose numerator and denominator are
both prime to `m`. -/
def rationalResidueUnit
    (m : ℕ) (q : ℚ)
    (hnum : Nat.Coprime q.num.natAbs m)
    (hden : Nat.Coprime q.den m) :
    (ZMod m)ˣ :=
  rationalNumeratorResidueUnit m q hnum *
    (rationalDenominatorResidueUnit m q hden)⁻¹

/-- Rational residue units are independent of the chosen equality proof. -/
theorem rationalResidueUnit_congr
    (m : ℕ) {q r : ℚ} (hqr : q = r)
    (hqnum : Nat.Coprime q.num.natAbs m)
    (hqden : Nat.Coprime q.den m)
    (hrnum : Nat.Coprime r.num.natAbs m)
    (hrden : Nat.Coprime r.den m) :
    rationalResidueUnit m q hqnum hqden =
      rationalResidueUnit m r hrnum hrden := by
  subst r
  rfl

/-- Reduction of rational numbers prime to a modulus is multiplicative. -/
theorem rationalResidueUnit_mul
    (m : ℕ) (q r : ℚ)
    (hqnum : Nat.Coprime q.num.natAbs m)
    (hqden : Nat.Coprime q.den m)
    (hrnum : Nat.Coprime r.num.natAbs m)
    (hrden : Nat.Coprime r.den m)
    (hqrnum : Nat.Coprime (q * r).num.natAbs m)
    (hqrden : Nat.Coprime (q * r).den m) :
    rationalResidueUnit m (q * r) hqrnum hqrden =
      rationalResidueUnit m q hqnum hqden *
        rationalResidueUnit m r hrnum hrden := by
  let Nq := rationalNumeratorResidueUnit m q hqnum
  let Dq := rationalDenominatorResidueUnit m q hqden
  let Nr := rationalNumeratorResidueUnit m r hrnum
  let Dr := rationalDenominatorResidueUnit m r hrden
  let Nqr := rationalNumeratorResidueUnit m (q * r) hqrnum
  let Dqr := rationalDenominatorResidueUnit m (q * r) hqrden
  have hcross : Nqr * Dq * Dr = Nq * Nr * Dqr := by
    apply Units.ext
    have h :=
      congrArg (Int.castRingHom (ZMod m)) (Rat.mul_num_den' q r)
    simpa [Nq, Dq, Nr, Dr, Nqr, Dqr,
      rationalNumeratorResidueUnit,
      rationalDenominatorResidueUnit, map_mul] using h
  change Nqr * Dqr⁻¹ = (Nq * Dq⁻¹) * (Nr * Dr⁻¹)
  calc
    Nqr * Dqr⁻¹ =
        (Nqr * Dq * Dr) * (Dq⁻¹ * Dr⁻¹ * Dqr⁻¹) := by
      simp [mul_comm, mul_left_comm, mul_assoc]
    _ = (Nq * Nr * Dqr) * (Dq⁻¹ * Dr⁻¹ * Dqr⁻¹) := by
      rw [hcross]
    _ = (Nq * Dq⁻¹) * (Nr * Dr⁻¹) := by
      simp [mul_comm, mul_left_comm, mul_assoc]

/-- The rational residue unit of one is one. -/
theorem rationalResidueUnit_one (m : ℕ) :
    rationalResidueUnit m 1 (by simp) (by simp) = 1 := by
  apply Units.ext
  simp [rationalResidueUnit, rationalNumeratorResidueUnit,
    rationalDenominatorResidueUnit]

/-! ### The local congruence condition over `ℚ` -/

end RayClass
end
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootCharts
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.overlapMeasure_finite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_sFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_sFinite _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}



theorem diagonal_coordinateMeasure (B : RootBox hij k) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) (μ : Measure (X n))
    (hinv : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ) :
    (B.diagonal ell hell t).coordinateMeasure μ =
      (B.coordinateMeasure μ).map (rootDiagonalCoordinates ell hell t) := by
  let E := rootDiagonalCoordinates (i := i) (j := j) (k := k) ell hell t
  let H := rightActionHomeomorph (diagonalOneParameter ell hell t)
  have hμ (S : Set (X n)) : μ (H '' S) = μ S := by
    calc
      μ (H '' S) = (μ.map H) (H '' S) := congrArg (fun ν => ν (H '' S)) hinv.symm
      _ = μ S := by rw [H.isOpenEmbedding.measurableEmbedding.map_apply,
        H.injective.preimage_image]
  ext S hS
  rw [Measure.map_apply E.continuous.measurable hS,
    coordinateMeasure_apply _ μ hS,
    coordinateMeasure_apply _ μ (E.continuous.measurable hS),diagonal_domain]
  rw [←hμ (rootQuotientParametrization hij '' (E ⁻¹' S ∩ B.domain))]
  congr 1
  ext x
  constructor
  · rintro ⟨z,⟨hzS,w,hw,rfl⟩,rfl⟩
    refine ⟨rootQuotientParametrization hij w,⟨w,⟨hzS,hw⟩,rfl⟩,?_⟩
    exact (rootDiagonalCoordinates_param hij ell hell t w).symm
  · rintro ⟨_,⟨w,⟨hwS,hw⟩,rfl⟩,rfl⟩
    exact ⟨E w,⟨hwS,⟨w,hw,rfl⟩⟩,rootDiagonalCoordinates_param hij ell hell t w⟩

 

theorem diagonal_conditionalKernel (B : RootBox hij k) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hinv : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ) :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
      (B.diagonal ell hell t).conditionalKernel μ (rootSliceDiagonal ell hell t s) =
        (B.conditionalKernel μ s).map (rootTimeScaling ell i j t) := by
  simp only [conditionalKernel,diagonal_coordinateMeasure B ell hell t μ hinv]
  exact root_conditional_scaling ell hell t (B.coordinateMeasure μ)

end RootBox
end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayDescent
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

variable [NeZero N]



lemma idealHom_eq_classValue (hψ : ψ.residue = 1)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (hc : IsCoprime I (rationalModulusIdeal (𝓞 K) N)) :
    ψ.idealHom (integralIdealFractionalUnit I hI) =
      ψ.classValue (ClassGroup.mk K (integralIdealFractionalUnit I hI)) := by
  apply ψ.idealHom_eq_of_coprime_class hψ I _ hI _ hc (classIdeal_coprime _)
  exact (classIdeal_class _).symm

lemma classValue_one (hψ : ψ.residue = 1) : ψ.classValue 1 = 1 := by
  have hc : IsCoprime (⊤ : Ideal (𝓞 K)) (rationalModulusIdeal (𝓞 K) N) := by
    rw [← Ideal.one_eq_top]
    exact isCoprime_one_left
  have H := ψ.idealHom_eq_classValue hψ ⊤ top_ne_bot hc
  simpa only [integralIdealFractionalUnit_top, map_one] using H.symm

lemma classValue_mul (hψ : ψ.residue = 1) (c e : ClassGroup (𝓞 K)) :
    ψ.classValue (c*e) = ψ.classValue c * ψ.classValue e := by
  let I := (classIdeal K N c).val
  let J := (classIdeal K N e).val
  have hI : I ≠ ⊥ := classIdeal_ne_bot c
  have hJ : J ≠ ⊥ := classIdeal_ne_bot e
  have hc : IsCoprime (I*J) (rationalModulusIdeal (𝓞 K) N) :=
    IsCoprime.mul_left_iff.mpr ⟨classIdeal_coprime c, classIdeal_coprime e⟩
  have H := ψ.idealHom_eq_classValue hψ (I*J) (mul_ne_zero hI hJ) hc
  rw [integralUnit_mul I J hI hJ, map_mul, map_mul] at H
  have HI : ClassGroup.mk K (integralIdealFractionalUnit I hI) = c := classIdeal_class c
  have HJ : ClassGroup.mk K (integralIdealFractionalUnit J hJ) = e := classIdeal_class e
  rw [HI, HJ] at H
  exact H.symm

 
def classCharacter (hψ : ψ.residue = 1) : ClassGroup (𝓞 K) →* ℂ where
  toFun c := (ψ.classValue c : ℂ)
  map_one' := by rw [ψ.classValue_one hψ]; rfl
  map_mul' c e := by rw [ψ.classValue_mul hψ]; rfl


def classUnitCharacter (hψ : ψ.residue = 1) : ClassGroup (𝓞 K) →* ℂˣ where
  toFun := ψ.classValue
  map_one' := ψ.classValue_one hψ
  map_mul' := ψ.classValue_mul hψ

end EvenRayCharacter

end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayUnramified
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

variable [NeZero N]



def unramifiedContinued {d : ℕ} [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hψ : ψ.residue = 1) (s : ℂ) : ℂ :=
  idealClassLFunction σ hn (ψ.classCharacter hψ) s *
    badEulerCorrection (ψ.classUnitCharacter hψ) N s

end EvenRayCharacter
end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RayContinuation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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



variable [NeZero N]



def nonprincipalContinued {d : ℕ} [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1) : ℂ → ℂ :=
  if hr : ψ.residue = 1 then ψ.unramifiedContinued σ hn hr else ψ.continued σ

end EvenRayCharacter
end PrimeDegreePackets

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_CyclicContinuation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Continued cyclic Artin factorizations

After realizing the nonprincipal cyclic characters as even ray
characters, the actual Artin factorization continues away from zero and
one. Its zero-order relation has nonnegative finite summands.
-/

noncomputable section

open Filter Set Module
open scoped NumberField BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter
  PrimeDegreePackets.HeckeMellin

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [NumberField.IsTotallyReal F] [NumberField.IsTotallyReal E]
variable {d e N : ℕ} [NeZero N]

/-- The principal factor is the incomplete Dedekind zeta function; the
other factors are the entire continuations of the realized characters. -/
def cyclicHeckeFactor (σ : OrderedEmbeddings (d + 1) F)
    (hn : finrank ℚ F = d + 1)
    (ψ : ((E ≃ₐ[F] E) →* ℂˣ) → EvenRayCharacter F N)
    (χ : (E ≃ₐ[F] E) →* ℂˣ) : ℂ → ℂ :=
  if χ = 1 then cosetMeromorphic σ hn N else (ψ χ).nonprincipalContinued σ hn

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_RootLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.overlapMeasure_finite _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_sFinite _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_sFinite _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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



lemma diagonal_marginal (A : RootBox hij k) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) (μ : Measure (X n))
    (hinv : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ) :
    ((A.diagonal ell hell t).coordinateMeasure μ).fst =
      (A.coordinateMeasure μ).fst.map (rootSliceDiagonalHomeomorph ell hell t) := by
  rw [A.diagonal_coordinateMeasure ell hell t μ hinv]
  exact fst_map_measurableEquiv (A.coordinateMeasure μ)
    (rootSliceDiagonalHomeomorph ell hell t).toMeasurableEquiv
    (rootTimeScaling ell i j t).toMeasurableEquiv

 

theorem ae_leafMeasure_diagonal (A : RootBox hij k) (R S : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ)
    (hAS : (A.diagonal ell hell t).time ⊆ rootLeafWindow S 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (hinv : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      (A.diagonal ell hell t).leafMeasure S μ (rootSliceDiagonal ell hell t s) =
        (A.leafMeasure R μ s).map (rootTimeScaling ell i j t) := by
  let C := rootLongBoxFamily hij k R
  let (m : ℕ) : Countable (C m) := (rootLongBoxFamily_countable hij k R m).to_subtype
  let e := rootSliceDiagonalHomeomorph (i := i) (j := j) (k := k) ell hell t
  let f := rootTimeScaling ell i j t
  let AD := A.diagonal ell hell t
  have hT (m : ℕ) (B : C m) : B.val.time = rootLeafWindow R m :=
    rootLongBoxFamily_time hij k R m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAR.trans (rootLeafWindow_mono R (Nat.zero_le m))
  have hincD (m : ℕ) (B : C m) : AD.time ⊆ (B.val.diagonal ell hell t).time :=
    image_mono (hinc m B)
  have hcov : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ (m : ℕ) (B : C m),
      s ∈ B.val.transverse →
      (B.val.diagonal ell hell t).conditionalKernel μ (e s) =
        (B.val.conditionalKernel μ s).map f := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    exact base_ae_of_ae A B.val (hinc m B) μ
      (B.val.diagonal_conditionalKernel ell hell t μ hinv)
  have hD : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ (m : ℕ) (B : C m),
      s ∈ B.val.transverse →
      (AD.leafMeasure S μ (e s)).restrict (f '' B.val.time) =
        (anchorNormalize ((B.val.diagonal ell hell t).conditionalKernel μ (e s))
          (f '' A.time)).restrict (f '' B.val.time) := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    have H := AD.ae_leafMeasure_restrict S hAS μ hfree
      (B.val.diagonal ell hell t) (hincD m B)
    rw [A.diagonal_marginal ell hell t μ hinv] at H
    have H' := e.toMeasurableEquiv.measurableEmbedding.ae_map_iff.mp H
    filter_upwards [H'] with s hs
    intro hsB
    exact (hs (mem_image_of_mem e hsB)).2
  filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree,
    A.ae_injective_root_slice_of_ae_free μ hfree,hcov,hD] with s hs hi hc hd
  apply measure_eq_of_restrictionChain (fun m => f '' rootLeafWindow R m)
    (fun a b hab => image_mono (rootLeafWindow_mono R hab))
    (by rw [←image_iUnion,rootLeafWindow_cover,image_univ,f.surjective.range_eq])
  intro m
  obtain ⟨B,hBC,hsB⟩ := rootLongBoxFamily_covers hij k R m s hi
  let B' : C m := ⟨B,hBC⟩
  have H := hd m B' hsB
  rw [hc m B' hsB] at H
  have ha : anchorNormalize ((B.conditionalKernel μ s).map f) (f '' A.time) =
      (anchorNormalize (B.conditionalKernel μ s) A.time).map f :=
    anchorNormalize_map_equiv (B.conditionalKernel μ s) f.toMeasurableEquiv A.time
  change (AD.leafMeasure S μ (e s)).restrict (f '' B.time) =
    (anchorNormalize ((B.conditionalKernel μ s).map f) (f '' A.time)).restrict (f '' B.time) at H
  rw [ha] at H
  change (AD.leafMeasure S μ (e s)).restrict (f '' rootLeafWindow R m) =
    ((A.leafMeasure R μ s).map f).restrict (f '' rootLeafWindow R m)
  have hmap (ν : Measure ℝ) (J : Set ℝ) :
      (ν.map f).restrict (f '' J) = (ν.restrict J).map f := by
    exact (f.toMeasurableEquiv.restrict_map ν (f '' J)).trans
      (congrArg (fun T : Set ℝ => (ν.restrict T).map f) (f.injective.preimage_image J))
  rw [hmap,hs.2.2.2 m B hBC hsB]
  rw [hmap] at H
  simpa only [rootLongBoxFamily_time hij k R m B hBC] using H

end RootBox
end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LeafSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.overlapMeasure_finite _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_sFinite _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

 

theorem ae_mem_leafMeasure_support (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ z ∂A.coordinateMeasure μ, z.2 ∈ (A.leafMeasure R μ z.1).support := by
  let κ := A.leafKernel R hAR μ hfree
  have hK : ∀ᵐ z ∂A.coordinateMeasure μ, z.2 ∈ (κ z.1).support := by
    have H : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ᵐ t ∂A.conditionalKernel μ s,
        t ∈ (κ s).support := by
      filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree,A.ae_leafKernel_eq R hAR μ hfree] with s hs he
      have hle : A.conditionalKernel μ s ≤ κ s := by
        rw [he,←hs.2.2.1]
        exact Measure.restrict_le_self
      filter_upwards [(A.conditionalKernel μ s).support_mem_ae] with t ht
      exact (Measure.support_mono hle) ht
    have H' := Measure.ae_compProd_of_ae_ae (measurableSet_kernel_support κ) H
    simpa only [conditionalKernel,Measure.disintegrate] using H'
  have he : ∀ᵐ z ∂A.coordinateMeasure μ, κ z.1 = A.leafMeasure R μ z.1 :=
    ae_of_ae_map measurable_fst.aemeasurable (A.ae_leafKernel_eq R hAR μ hfree)
  filter_upwards [hK,he] with z hz hez
  rwa [←hez]

 

theorem ae_leafMeasure_ball_pos (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ z ∂A.coordinateMeasure μ, ∀ r : ℝ, 0 < r →
      0 < A.leafMeasure R μ z.1 (Metric.ball z.2 r) := by
  filter_upwards [A.ae_mem_leafMeasure_support R hAR μ hfree] with z hz
  intro r hr
  exact ((A.leafMeasure R μ z.1).mem_support_iff_forall z.2).mp hz _ (Metric.ball_mem_nhds _ hr)

end RootBox
end PrimeDegreePackets


namespace PrimeDegreePackets



namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}


instance regularLeafKernel_locallyFinite (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (s : RootSlice i j k) : IsLocallyFiniteMeasure (A.regularLeafKernel R hAR μ hfree s) :=
  locallyFiniteRealVersion_locallyFinite _ _

end RootBox
end PrimeDegreePackets


namespace PrimeDegreePackets


namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}



theorem ae_basedLeaf_spec (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ z ∂A.coordinateMeasure μ,
      IsLocallyFiniteMeasure (A.basedLeaf R μ z) ∧
        A.basedLeaf R μ z (Metric.ball 0 1) = 1 := by
  have hlf : ∀ᵐ z ∂A.coordinateMeasure μ, IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) :=
    ae_of_ae_map measurable_fst.aemeasurable
      ((A.ae_leafMeasure_spec R hAR μ hfree).mono fun s hs => hs.1)
  filter_upwards [hlf,A.ae_leafMeasure_ball_pos R hAR μ hfree] with z hz hp
  let : IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) := hz
  exact ⟨basedRealMeasure_locallyFinite _ _ (hp 1 zero_lt_one),
    basedRealMeasure_ball_one _ _ (hp 1 zero_lt_one)⟩

end RootBox
end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IntrinsicLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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



lemma ae_intrinsicRootLeaf_spec_restrict (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ x ∂μ.restrict A.range, IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) ∧
      intrinsicRootLeaf hij μ x (Metric.ball 0 1) = 1 := by
  apply A.ae_of_coordinate μ
  filter_upwards [A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree,
    A.ae_basedLeaf_spec R hAR μ hfree] with z he hz
  rwa [he]

end RootBox



theorem ae_intrinsicRootLeaf_spec (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ x ∂μ, IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) ∧
      intrinsicRootLeaf hij μ x (Metric.ball 0 1) = 1 := by
  let : Countable (boundedRootAtlas hij) := (boundedRootAtlas_countable hij).to_subtype
  have H := (ae_restrict_iUnion_iff (μ := μ) (fun B : boundedRootAtlas hij => B.val.box.range)
    (fun x => IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) ∧
      intrinsicRootLeaf hij μ x (Metric.ball 0 1) = 1)).mpr
    (fun B => B.val.box.ae_intrinsicRootLeaf_spec_restrict B.val.radius B.val.time_bound μ hfree)
  simpa only [boundedRootAtlas_iUnion,Measure.restrict_univ] using H



instance intrinsicRootKernel_locallyFinite (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) (x : X n) :
    IsLocallyFiniteMeasure (intrinsicRootKernel hij μ hfree x) :=
  locallyFiniteRealVersion_locallyFinite _ _

end PrimeDegreePackets


namespace PrimeDegreePackets
namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

lemma ae_basedLeaf_diagonal (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (hinv : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ) :
    ∀ᵐ z ∂A.coordinateMeasure μ,
      (A.diagonal ell hell t).basedLeaf (Real.exp ((ell j-ell i)*t)*R) μ
          (rootDiagonalCoordinates ell hell t z) =
        anchorNormalize ((A.basedLeaf R μ z).map (rootTimeScaling ell i j t)) (Metric.ball 0 1) := by
  have H := ae_of_ae_map measurable_fst.aemeasurable
    (A.ae_leafMeasure_diagonal R (Real.exp ((ell j-ell i)*t)*R) hAR ell hell t
      (A.diagonal_time_bound R hAR ell hell t) μ hfree hinv)
  have Hlf := ae_of_ae_map measurable_fst.aemeasurable
    ((A.ae_leafMeasure_spec R hAR μ hfree).mono fun s hs => hs.1)
  filter_upwards [H,Hlf,A.ae_leafMeasure_ball_pos R hAR μ hfree] with z hz hlf hp
  let : IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) := hlf
  change basedRealMeasure ((A.diagonal ell hell t).leafMeasure _ μ
    (rootSliceDiagonal ell hell t z.1)) (Real.exp ((ell j-ell i)*t)*z.2) = _
  rw [hz]
  exact basedRealMeasure_scaling (A.leafMeasure R μ z.1)
    (Real.exp ((ell j-ell i)*t)) z.2 (Real.exp_ne_zero _) (hp 1 zero_lt_one)

lemma ae_intrinsicRootLeaf_diagonal_restrict (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (hinv : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ) :
    ∀ᵐ x ∂μ.restrict A.range,
      intrinsicRootLeaf hij μ (rightAction x (diagonalOneParameter ell hell t)) =
        anchorNormalize ((intrinsicRootLeaf hij μ x).map (rootTimeScaling ell i j t)) (Metric.ball 0 1) := by
  apply A.ae_of_coordinate μ
  have HD := (A.diagonal ell hell t).ae_intrinsicRootLeaf_coordinates
    (Real.exp ((ell j-ell i)*t)*R) (A.diagonal_time_bound R hAR ell hell t) μ hfree
  rw [A.diagonal_coordinateMeasure ell hell t μ hinv] at HD
  have HD' := ae_of_ae_map (rootDiagonalCoordinates ell hell t).measurable.aemeasurable HD
  filter_upwards [HD',A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree,
    A.ae_basedLeaf_diagonal R hAR ell hell t μ hfree hinv] with z hd ha hc
  rw [rootDiagonalCoordinates_param] at hd
  rw [hd,ha,hc]

end RootBox

 

theorem ae_intrinsicRootLeaf_diagonal {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (hinv : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ) :
    ∀ᵐ x ∂μ,
      intrinsicRootLeaf hij μ (rightAction x (diagonalOneParameter ell hell t)) =
        anchorNormalize ((intrinsicRootLeaf hij μ x).map (rootTimeScaling ell i j t)) (Metric.ball 0 1) := by
  let : Countable (boundedRootAtlas hij) := (boundedRootAtlas_countable hij).to_subtype
  have H := (ae_restrict_iUnion_iff (μ := μ) (fun B : boundedRootAtlas hij => B.val.box.range) _).mpr
    (fun B => B.val.box.ae_intrinsicRootLeaf_diagonal_restrict B.val.radius B.val.time_bound
      ell hell t μ hfree hinv)
  simpa only [boundedRootAtlas_iUnion,Measure.restrict_univ] using H

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_AmbientLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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



theorem ae_intrinsicRootLeaf_ball_pos {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < intrinsicRootLeaf hij μ x (Metric.ball 0 r) := by
  let : Countable (boundedRootAtlas hij) := (boundedRootAtlas_countable hij).to_subtype
  have H (B : boundedRootAtlas hij) : ∀ᵐ x ∂μ.restrict B.val.box.range,
      ∀ r : ℝ, 0 < r → 0 < intrinsicRootLeaf hij μ x (Metric.ball 0 r) := by
    apply B.val.box.ae_of_coordinate μ
    have Hlf := ae_of_ae_map measurable_fst.aemeasurable
      ((B.val.box.ae_leafMeasure_spec B.val.radius B.val.time_bound μ hfree).mono fun _ h => h.1)
    filter_upwards [B.val.box.ae_intrinsicRootLeaf_coordinates B.val.radius B.val.time_bound μ hfree,
      B.val.box.ae_leafMeasure_ball_pos B.val.radius B.val.time_bound μ hfree,Hlf] with z he hp hf
    let : IsLocallyFiniteMeasure (B.val.box.leafMeasure B.val.radius μ z.1) := hf
    intro r hr
    rw [he]
    exact basedRealMeasure_ball_pos _ _ _ (hp r hr)
  have HH := (ae_restrict_iUnion_iff (μ := μ) (fun B : boundedRootAtlas hij => B.val.box.range) _).mpr H
  simpa only [boundedRootAtlas_iUnion,Measure.restrict_univ] using HH



end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ScalingCovariance
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
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


theorem ae_intrinsicRootLeaf_canonical (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) (t : ℝ) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ (rightAction x (rootCanonicalFlow d j t)) =
      anchorNormalize ((intrinsicRootLeaf hij μ x).map
        (Homeomorph.mulLeft₀ (Real.exp t) (Real.exp_ne_zero t))) (Metric.ball 0 1) := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  have H := ae_intrinsicRootLeaf_diagonal hij (rootCanonicalWeights d j)
    (rootCanonicalWeights_sum d j) t μ hfree (rootCanonicalFlow_preserving d j t μ hA).map_eq
  have he : rootTimeScaling (rootCanonicalWeights d j) i j t =
      Homeomorph.mulLeft₀ (Real.exp t) (Real.exp_ne_zero t) := by
    apply Homeomorph.ext
    intro v
    simp only [rootTimeScaling,Homeomorph.coe_mulLeft₀,rootCanonicalWeights_difference d hij,one_mul]
  simpa only [rootCanonicalFlow,he] using H

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma aemeasurable_rootInformation (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) (t : ℝ) :
    AEMeasurable (rootInformation hij μ t) μ := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  exact ((Measure.measurable_coe (Metric.isOpen_ball (x := (0:ℝ))
    (ε := Real.exp (-t))).measurableSet).comp_aemeasurable
    (aemeasurable_intrinsicRootLeaf hij μ hfree)).ennreal_toReal.log.neg

lemma ae_rootInformation_nonneg (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ x ∂μ, 0 ≤ rootInformation hij μ t x := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  filter_upwards [ae_intrinsicRootLeaf_spec hij μ hfree] with x hx
  have hle : intrinsicRootLeaf hij μ x (Metric.ball 0 (Real.exp (-t))) ≤ 1 := by
    rw [←hx.2]
    exact measure_mono (Metric.ball_subset_ball
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)))
  exact neg_nonneg.mpr (Real.log_nonpos ENNReal.toReal_nonneg
    (by simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hle))


theorem ae_intrinsicRootLeaf_ball_cocycle (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) (s t : ℝ) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x (Metric.ball 0 (Real.exp (-(s+t)))) =
      intrinsicRootLeaf hij μ x (Metric.ball 0 (Real.exp (-t))) *
      intrinsicRootLeaf hij μ (rightAction x (rootCanonicalFlow d j t))
        (Metric.ball 0 (Real.exp (-s))) := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  filter_upwards [ae_intrinsicRootLeaf_canonical d hij μ hA t,
    ae_intrinsicRootLeaf_spec hij μ hfree,ae_intrinsicRootLeaf_ball_pos hij μ hfree] with x he hs hp
  let : IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) := hs.1
  rw [he,normalized_realScaling_ball _ _ _ (Real.exp_pos _)]
  have h1 : 1/Real.exp t = Real.exp (-t) := by simp [Real.exp_neg,one_div]
  have h2 : Real.exp (-s)/Real.exp t = Real.exp (-(s+t)) := by
    rw [←Real.exp_sub]
    congr 1
    ring
  rw [h1,h2,←mul_assoc,ENNReal.mul_inv_cancel
    (hp _ (Real.exp_pos _)).ne' measure_ball_lt_top.ne,one_mul]

 

theorem ae_rootInformation_cocycle (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) (s t : ℝ) :
    ∀ᵐ x ∂μ, rootInformation hij μ (s+t) x = rootInformation hij μ t x +
      rootInformation hij μ s (rightAction x (rootCanonicalFlow d j t)) := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  have hs := ae_intrinsicRootLeaf_spec hij μ hfree
  have hp := ae_intrinsicRootLeaf_ball_pos hij μ hfree
  have hT := rootCanonicalFlow_preserving d j t μ hA
  have hST : ∀ᵐ x ∂μ, IsLocallyFiniteMeasure
      (intrinsicRootLeaf hij μ (rightAction x (rootCanonicalFlow d j t))) := by
    have H : ∀ᵐ y ∂μ.map (fun x => rightAction x (rootCanonicalFlow d j t)),
        IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ y) := by
      rw [hT.map_eq]
      exact hs.mono fun _ h => h.1
    exact ae_of_ae_map hT.measurable.aemeasurable H
  have hPT : ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 <
      intrinsicRootLeaf hij μ (rightAction x (rootCanonicalFlow d j t)) (Metric.ball 0 r) := by
    have H : ∀ᵐ y ∂μ.map (fun x => rightAction x (rootCanonicalFlow d j t)),
        ∀ r : ℝ, 0 < r → 0 < intrinsicRootLeaf hij μ y (Metric.ball 0 r) := by
      rw [hT.map_eq]
      exact hp
    exact ae_of_ae_map hT.measurable.aemeasurable H
  filter_upwards [ae_intrinsicRootLeaf_ball_cocycle d hij μ hA s t,hs,hp,hST,hPT]
    with x he hs hp hst hpt
  let : IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) := hs.1
  let : IsLocallyFiniteMeasure
      (intrinsicRootLeaf hij μ (rightAction x (rootCanonicalFlow d j t))) := hst
  have h0 : (intrinsicRootLeaf hij μ x (Metric.ball 0 (Real.exp (-t)))).toReal ≠ 0 :=
    (ENNReal.toReal_pos (hp _ (Real.exp_pos _)).ne' measure_ball_lt_top.ne).ne'
  have h0T : (intrinsicRootLeaf hij μ (rightAction x (rootCanonicalFlow d j t))
      (Metric.ball 0 (Real.exp (-s)))).toReal ≠ 0 :=
    (ENNReal.toReal_pos (hpt _ (Real.exp_pos _)).ne' measure_ball_lt_top.ne).ne'
  dsimp only [rootInformation]
  rw [he,ENNReal.toReal_mul,Real.log_mul h0 h0T]
  ring

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma rootInformationMean_add (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    rootInformationMean hij μ (s+t) = rootInformationMean hij μ s + rootInformationMean hij μ t := by
  have hT := rootCanonicalFlow_preserving d j t μ hA
  have hps : ∀ᵐ x ∂μ, 0 ≤ rootInformation hij μ s (rightAction x (rootCanonicalFlow d j t)) := by
    have H : ∀ᵐ y ∂μ.map (fun x => rightAction x (rootCanonicalFlow d j t)),
        0 ≤ rootInformation hij μ s y := by
      rw [hT.map_eq]
      exact ae_rootInformation_nonneg d hij μ hA hs
    exact ae_of_ae_map hT.measurable.aemeasurable H
  have he : (fun x => ENNReal.ofReal (rootInformation hij μ (s+t) x)) =ᵐ[μ]
      (fun x => ENNReal.ofReal (rootInformation hij μ t x) +
        ENNReal.ofReal (rootInformation hij μ s (rightAction x (rootCanonicalFlow d j t)))) := by
    filter_upwards [ae_rootInformation_cocycle d hij μ hA s t,
      ae_rootInformation_nonneg d hij μ hA ht,hps] with x he hpt hps
    rw [he,ENNReal.ofReal_add hpt hps]
  have hms := (aemeasurable_rootInformation d hij μ hA s).ennreal_ofReal
  have hmt := (aemeasurable_rootInformation d hij μ hA t).ennreal_ofReal
  have hmap : ∫⁻ x, ENNReal.ofReal (rootInformation hij μ s
      (rightAction x (rootCanonicalFlow d j t))) ∂μ = rootInformationMean hij μ s := by
    have H : AEMeasurable (fun x => ENNReal.ofReal (rootInformation hij μ s x))
        (μ.map (fun x => rightAction x (rootCanonicalFlow d j t))) := hT.map_eq.symm ▸ hms
    rw [←lintegral_map' H hT.measurable.aemeasurable,hT.map_eq]
    rfl
  rw [rootInformationMean,lintegral_congr_ae he,lintegral_add_left' hmt,hmap,add_comm]
  rfl

lemma rootInformationMean_zero_time (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    rootInformationMean hij μ 0 = 0 := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_intrinsicRootLeaf_spec hij μ hfree] with x hx
  simp [rootInformation,hx.2]

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_RootInformationScale
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact scaling of the mean root information

The actual normalized leaf information is additive under the canonical
flow. Monotonicity and rational approximation promote its integer-time
scaling law to every nonnegative real time, including infinite means.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
  (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
  (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)

include hA

def rootInformationHom : ℝ≥0 →+ ℝ≥0∞ where
  toFun t := rootInformationMean hij μ t
  map_zero' := rootInformationMean_zero_time d hij μ hA
  map_add' s t := rootInformationMean_add d hij μ hA s.property t.property

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootChart
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.time_borelSpace _root_.OAI.DukePrimeDegree.EliminationChain.time_polish _root_.OAI.DukePrimeDegree.EliminationChain.time_secondCountable _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

structure UpperRootBox (n : ℕ) (g : G n) where
  transverse : Set (UpperRootTransverse n)
  time : Set (UpperRootTime n)
  transverse_open : IsOpen transverse
  time_open : IsOpen time
  embedding : Topology.IsOpenEmbedding
    ((transverse ×ˢ time).domRestrict (upperRootQuotientParam n g))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootDisintegration
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

namespace UpperRootBox
variable {n : ℕ} {g : G n}

abbrev domain (B : UpperRootBox n g) := B.transverse ×ˢ B.time
abbrev param (B : UpperRootBox n g) := B.domain.domRestrict (upperRootQuotientParam n g)
def range (B : UpperRootBox n g) := Set.range B.param

end UpperRootBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootRestrictions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compatible restrictions of full upper-root conditionals

Shrinking an actual upper-root quotient box restricts its coordinate
measure. The disintegrated kernels therefore agree projectively on
intersections, with the normalization fixed by a common smaller box.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets
namespace UpperRootBox
variable {n : ℕ} {g : G n}



def shrink (B : UpperRootBox n g)
    (U : Set (UpperRootTransverse n)) (V : Set (UpperRootTime n)) (hU : IsOpen U) (hV : IsOpen V)
    (hUB : U ⊆ B.transverse) (hVB : V ⊆ B.time) : UpperRootBox n g :=
  ⟨U,V,hU,hV,B.embedding.comp (Topology.IsOpenEmbedding.inclusion
    (Set.prod_mono hUB hVB) ((hU.prod hV).preimage continuous_subtype_val))⟩



end UpperRootBox
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

namespace RootPrefixCoordinates
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {T : Type*} [TopologicalSpace T]

def extend (C : RootPrefixCoordinates n P T) (hP : InitialRootPattern P)
    (p : Fin n × Fin n) (hp : p ∈ allPositiveRoots n \ P)
    (hmin : ∀ q ∈ allPositiveRoots n \ P, toLex p ≤ toLex q) :
    RootPrefixCoordinates n (insert p P) (T × ℝ) := by
  let S := allPositiveRoots n \ P
  have hpos : ∀ q ∈ S, q.1 < q.2 :=
    fun _ hq => (Finset.mem_filter.mp (Finset.mem_sdiff.mp hq).1).2
  have hab : p.1 ≠ p.2 := ne_of_lt (hpos p hp)
  have hclosed := initialRemaining_roots_closed P hP
  have herase : ∀ a b c : Fin n, (a,b) ∈ S.erase p →
      (b,c) ∈ S.erase p → (a,c) ∈ S.erase p := by
    rw [initialRemaining_erase]
    exact initialRemaining_roots_closed (insert p P) (initialRootPattern_insert_min hP p hp hmin)
  let e : positiveRootGeneratedGroup (allPositiveRoots n \ insert p P) ≃ₜ
      positiveRootGeneratedGroup (S.erase p) :=
    Homeomorph.setCongr (by rw [show S.erase p = allPositiveRoots n \ insert p P from
      initialRemaining_erase P p])
  let F := positiveRootFactorHomeomorph S hpos hclosed hab hp herase
  let H := ((Homeomorph.refl ℝ).prodCongr e).trans F
  refine {
    base := fun z => C.base z.1 * Matrix.SpecialLinearGroup.transvection hab z.2
    equiv := (Homeomorph.prodAssoc T ℝ _).trans
      (((Homeomorph.refl T).prodCongr H).trans C.equiv)
    param_eq_mul := ?_ }
  intro z w
  change (C.equiv (z.1, F (z.2, e w))).val = _
  rw [C.param_eq_mul]
  change C.base z.1 * (Matrix.SpecialLinearGroup.transvection hab z.2 * w.val) = _
  exact (mul_assoc _ _ _).symm

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixFactorChart
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space
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

theorem factorParam_isOpenEmbedding : Topology.IsOpenEmbedding (C.factorParam s g) := by
  have herase : ∀ a b c : Fin n, (a,b) ∈ s.remaining.erase s.root →
      (b,c) ∈ s.remaining.erase s.root → (a,c) ∈ s.remaining.erase s.root := by
    dsimp only [InitialRootStep.remaining]
    rw [initialRemaining_erase]
    exact initialRemaining_roots_closed _ (initialRootPattern_insert_min s.initial s.root
      s.mem_remaining s.least)
  let F := positiveRootRightFactorHomeomorph s.remaining s.remaining_positive s.remaining_closed
    s.distinct s.mem_remaining herase
  let E := (Homeomorph.prodAssoc (UpperRootTransverse n × T) _ ℝ).trans
    (((Homeomorph.refl (UpperRootTransverse n × T)).prodCongr F).trans
      (Homeomorph.prodAssoc (UpperRootTransverse n) T _))
  have H := (Homeomorph.mulLeft g).isOpenEmbedding.comp (C.groupParam_isOpenEmbedding.comp E.isOpenEmbedding)
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  change C.factorBase s g z.1 * Matrix.SpecialLinearGroup.transvection s.distinct z.2 =
    g * C.groupParam (z.1.1.1,(z.1.1.2,F (z.1.2,z.2)))
  rw [C.groupParam_eq_mul]
  change (g * (z.1.1.1.val * (C.base z.1.1.2 * z.1.2.val))) *
    Matrix.SpecialLinearGroup.transvection s.distinct z.2 =
      g * (z.1.1.1.val * (C.base z.1.1.2 *
        (z.1.2.val * Matrix.SpecialLinearGroup.transvection s.distinct z.2)))
  simp only [mul_assoc]

lemma continuous_factorBase : Continuous (C.factorBase s g) := by
  have H := (C.factorParam_isOpenEmbedding s g).continuous.comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : FactorTransverse s (T := T) => (0:ℝ))))
  simpa only [Function.comp_def, id_eq, factorParam, Matrix.SpecialLinearGroup.transvection_coeff_zero,
    mul_one] using H

lemma factorPivotDomain_open (k : Fin n) : IsOpen (C.factorPivotDomain s g k) :=
  (rootPivot_isOpen s.root.1 k).preimage (C.continuous_factorBase s g)

theorem factorSlice_isOpenEmbedding (k : Fin n) :
    Topology.IsOpenEmbedding (C.factorSlice s g k) := by
  have hf : Continuous (C.factorPivot s g k) :=
    ((C.continuous_factorBase s g).comp continuous_subtype_val).subtype_mk _
  apply root_transversal_isOpenEmbedding s.distinct _ hf
  let f := fun z : C.factorPivotDomain s g k × ℝ =>
    rootPivotTranslate s.distinct (C.factorPivot s g k z.1) z.2
  have H := (C.factorParam_isOpenEmbedding s g).comp
    ((C.factorPivotDomain_open s g k).isOpenEmbedding_subtypeVal.prodMap
      (Topology.IsOpenEmbedding.id (X := ℝ)))
  exact Topology.IsOpenEmbedding.of_comp f (rootPivot_isOpen s.root.1 k).isOpenEmbedding_subtypeVal H

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingRootProductBoxes
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

namespace RootPrefixCoordinates
variable {n : ℕ} (q : InitialRootStep n) {T : Type*} [TopologicalSpace T]
  (C : RootPrefixCoordinates n q.processed T) (g : G n) (k : Fin n)

lemma continuous_factorTime : Continuous (C.factorTime q g k) := by
  have hp : Continuous (C.factorPivot q g k) :=
    ((C.continuous_factorBase q g).comp continuous_subtype_val).subtype_mk _
  exact continuous_rootParameter.comp hp

lemma rectangleSlice_isOpenEmbedding (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) :
    Topology.IsOpenEmbedding (C.rectangleSlice q g k Q) :=
  (C.factorSlice_isOpenEmbedding q g k).comp
    (Q.inclusion_isOpenEmbedding (C.factorPivotDomain_open q g k))

lemma continuous_rectangleTime (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) :
    Continuous (C.rectangleTime q g k Q) :=
  (C.continuous_factorTime q g k).comp
    (Q.inclusion_isOpenEmbedding (C.factorPivotDomain_open q g k)).continuous

end RootPrefixCoordinates

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PhysicalRootEmbeddings
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quotient embeddings of physical root rectangles -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

variable {T B : Type*} [MeasurableSpace T] [MeasurableSpace B]
  [TopologicalSpace T] [TopologicalSpace B]

namespace RootPrefixCoordinates
variable {n : ℕ} (q : InitialRootStep n) {S : Type*} [TopologicalSpace S]
  (C : RootPrefixCoordinates n q.processed S) (g : G n) (k : Fin n)

theorem rectangle_param_isOpenEmbedding
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k)
    (hA : A.transverse = Set.range (C.rectangleSlice q g k Q))
    (J : Set ℝ) (hJ : IsOpen J)
    (hwindow : ∀ w : Q.first × Q.second,
      (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time) :
    Topology.IsOpenEmbedding ((univ ×ˢ (univ ×ˢ J)).domRestrict
      (physicalRootParam q.distinct (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q))) :=
  physicalRootParam_isOpenEmbedding q.distinct A _ (C.rectangleSlice_isOpenEmbedding q g k Q)
    _ (C.continuous_rectangleTime q g k Q) _ (isOpen_univ.prod (isOpen_univ.prod hJ))
    (C.rectangle_coordinates_inside q g k Q A hA J hwindow)

end RootPrefixCoordinates

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPrefixReorder
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1))

def extendedRootParam
    (z : (UpperRootTransverse (d+1) × T) ×
      (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)) : X (d+1) :=
  (C.extend q.initial q.root q.mem_remaining q.least).quotientParam g
    (z.1.1,((z.1.2,z.2.2),q.nextGroupCast (q.nextConjugation d z.2.2 z.2.1)))

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PrefixExchangeRegions
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Injective open regions in the exchanged prefix chart -/

noncomputable section
open Matrix MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain (insert q.root q.processed) D)
    (hfinal : c.finalEntries = allPositiveRoots (d+1))

lemma fullRectangleCoordinates_isOpenEmbedding
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) :
    Topology.IsOpenEmbedding (C.fullRectangleCoordinates q g k Q) :=
  Q.first_open.isOpenEmbedding_subtypeVal.prodMap
    (Q.second_open.isOpenEmbedding_subtypeVal.prodMap (Topology.IsOpenEmbedding.id (X := ℝ)))

def exchangedRectangleCoordinates (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) :
    Q.first × (Q.second × ℝ) → (UpperRootTransverse (d+1) × (T × ℝ)) × c.Time :=
  (prefixTimeExchange (T := T) q c hfinal) ∘ C.fullRectangleCoordinates q g k Q

def exchangedRectangleRegion (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (J : Set ℝ) : Set ((UpperRootTransverse (d+1) × (T × ℝ)) × c.Time) :=
  C.exchangedRectangleCoordinates q g k c hfinal Q '' (univ ×ˢ (univ ×ˢ J))

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PrefixExchangeMeasures
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual prefix-box measures inside an exchanged independent rectangle -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*}
    [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain (insert q.root q.processed) D)
    (hfinal : c.finalEntries = allPositiveRoots (d+1))

def exchangedRectangleMeasure
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k) (J : Set ℝ) (μ : Measure (X (d+1))) :
    Measure ((UpperRootTransverse (d+1) × (T × ℝ)) × c.Time) :=
  ((shiftedRootFactorPullback q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)).restrict (univ ×ˢ (univ ×ˢ J))).map
      (C.exchangedRectangleCoordinates q g k c hfinal Q)

instance exchangedRectangleMeasure_finite
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k) (J : Set ℝ) (μ : Measure (X (d+1))) [IsFiniteMeasure μ] :
    IsFiniteMeasure (C.exchangedRectangleMeasure q g k c hfinal Q A J μ) := by
  let := shiftedRootFactorPullback_finite q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
    (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
  unfold exchangedRectangleMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PhysicalPrefixMeasure
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent physical rectangles in the full prefix coordinates -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*}
    [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))

def physicalPrefixMeasure (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k) (J : Set ℝ) (μ : Measure (X (d+1))) :
    Measure ((UpperRootTransverse (d+1) × T) ×
      (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)) :=
  ((shiftedRootFactorPullback q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)).restrict
      (univ ×ˢ (univ ×ˢ J))).map (C.fullRectangleCoordinates q g k Q)

instance physicalPrefixMeasure_finite
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k) (J : Set ℝ) (μ : Measure (X (d+1))) [IsFiniteMeasure μ] :
    IsFiniteMeasure (C.physicalPrefixMeasure q g k Q A J μ) := by
  let := shiftedRootFactorPullback_finite q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
    (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
  unfold physicalPrefixMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PhysicalPrefixCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical rectangles in the original remaining-subgroup time chart -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain q.processed D)
    (hf : c.finalEntries = allPositiveRoots (d+1))

variable {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))

def originalRectangleCoordinates
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) :
    Q.first × (Q.second × ℝ) → (UpperRootTransverse (d+1) × T) × c.Time :=
  (physicalPrefixCoordinates (T := T) q c hf) ∘ C.fullRectangleCoordinates q g k Q

lemma originalRectangleCoordinates_openEmbedding
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) :
    Topology.IsOpenEmbedding (C.originalRectangleCoordinates q c hf g k Q) :=
  (physicalPrefixCoordinates (T := T) q c hf).isOpenEmbedding.comp
    (C.fullRectangleCoordinates_isOpenEmbedding q g k Q)

lemma originalRectangleCoordinates_param
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (z : Q.first × (Q.second × ℝ)) :
    C.timeParam c q.initial hf g (C.originalRectangleCoordinates q c hf g k Q z) =
      physicalRootParam q.distinct (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q) z := by
  rw [originalRectangleCoordinates,Function.comp_apply,physicalPrefixCoordinates_param]
  exact C.rectangle_includedFiberPoint q g k Q z

lemma originalRectangleCoordinates_image
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) (J : Set ℝ) :
    C.originalRectangleCoordinates q c hf g k Q '' (univ ×ˢ (univ ×ˢ J)) =
      Q.first ×ˢ (remainingFactorTime q c hf '' (Q.second ×ˢ J)) := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w.1.prop,(w.2.1.val,w.2.2),⟨w.2.1.prop,hw.2.2⟩,rfl⟩
  · rintro ⟨hs,w,hw,he⟩
    refine ⟨(⟨z.1,hs⟩,(⟨w.1,hw.1⟩,w.2)),⟨mem_univ _,mem_univ _,hw.2⟩,?_⟩
    exact Prod.ext rfl he

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PhysicalPrefixBox
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual prefix boxes obtained from physical independent rectangles -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain q.processed D)
    (hf : c.finalEntries = allPositiveRoots (d+1))
    {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))

def physicalPrefixBox
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k) (hA : A.transverse = range (C.rectangleSlice q g k Q))
    (J : Set ℝ) (hJ : IsOpen J)
    (hwindow : ∀ w : Q.first × Q.second,
      (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time) :
    RootPrefixBox C c q.initial hf g where
  transverse := Q.first
  time := remainingFactorTime q c hf '' (Q.second ×ˢ J)
  transverse_open := Q.first_open
  time_open := (remainingFactorTime q c hf).isOpenMap _ (Q.second_open.prod hJ)
  embedding := by
    have H : Topology.IsOpenEmbedding
        ((C.originalRectangleCoordinates q c hf g k Q '' (univ ×ˢ (univ ×ˢ J))).domRestrict
          (C.timeParam c q.initial hf g)) := by
      apply openEmbedding_on_coordinate_image
        (C.originalRectangleCoordinates q c hf g k Q) (C.timeParam c q.initial hf g)
        (univ ×ˢ (univ ×ˢ J)) (C.originalRectangleCoordinates_openEmbedding q c hf g k Q)
        (C.timeParam_localHomeomorph c q.initial hf g) (isOpen_univ.prod (isOpen_univ.prod hJ))
      have he : (univ ×ˢ (univ ×ˢ J)).domRestrict
          (C.timeParam c q.initial hf g ∘ C.originalRectangleCoordinates q c hf g k Q) =
          (univ ×ˢ (univ ×ˢ J)).domRestrict
            (physicalRootParam q.distinct (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)) := by
        funext z
        exact C.originalRectangleCoordinates_param q c hf g k Q z.val
      rw [he]
      exact C.rectangle_param_isOpenEmbedding q g k Q A hA J hJ hwindow
    erw [C.originalRectangleCoordinates_image q c hf g k Q J] at H
    exact H

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_LargePhysicalRectangles
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded independent physical rectangles covering arbitrary compact fibers -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))

theorem exists_large_physical_rectangle (s : UpperRootTransverse (d+1) × T)
    (hs : ((g*s.1.val)*C.base s.2).val k q.root.1 ≠ 0)
    (hfree : ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction (Quotient.mk _ ((g*s.1.val)*C.base s.2)) v =
        Quotient.mk _ ((g*s.1.val)*C.base s.2) → v = 1)
    (K : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))) (hK : IsCompact K)
    (I : Set ℝ) (hI : IsCompact I) (hne : I.Nonempty) :
    ∃ (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
      (A : RootBox q.distinct k) (R : ℝ) (J : Set ℝ)
      (K' : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))) (I' : Set ℝ),
      IsOpen J ∧ s ∈ Q.first ∧ K ⊆ Q.second ∧ I ⊆ J ∧
      IsCompact K' ∧ Q.second ⊆ K' ∧ IsCompact I' ∧ J ⊆ I' ∧
      A.transverse = range (C.rectangleSlice q g k Q) ∧
      A.time ⊆ rootLeafWindow R 0 ∧
      ∀ w : Q.first × Q.second,
        (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time := by
  let E := q.nextGroupCoordinates
  obtain ⟨r,hr⟩ := (hK.image E.continuous).isBounded.subset_ball 0
  let V := E ⁻¹' Metric.ball 0 r
  let K' := E.symm '' Metric.closedBall 0 r
  have hV : IsOpen V := Metric.isOpen_ball.preimage E.continuous
  have hKV : K ⊆ V := fun w hw => hr ⟨w,hw,rfl⟩
  have hK' : IsCompact K' := (isCompact_closedBall 0 r).image E.symm.continuous
  have hVK' : V ⊆ K' := by
    intro w hw
    exact ⟨E w,Metric.mem_closedBall.mpr (Metric.mem_ball.mp hw).le,E.symm_apply_apply w⟩
  obtain ⟨rI,hrI⟩ := hI.isBounded.subset_ball 0
  obtain ⟨Q,A,R,J,hJ,hsQ,hKQ,hIJ,hQV,hJI,hA,hAR,hw⟩ :=
    exists_shifted_root_rectangle_covering_compact (C.factorPivotDomain_open q g k)
      q.distinct (C.factorSlice q g k) (C.factorSlice_isOpenEmbedding q g k)
      (C.factorTime q g k) (C.continuous_factorTime q g k) s
      (C.factorPivotDomain_cylinder q g k s hs)
      (C.factorSlice_fiber_injective_of_free q g k s hfree)
      K hK I hI hne V hV hKV (Metric.ball 0 rI) Metric.isOpen_ball hrI
  exact ⟨Q,A,R,J,K',Metric.closedBall 0 rI,hJ,hsQ,hKQ,hIJ,hK',
    hQV.trans hVK',isCompact_closedBall 0 rI,hJI.trans Metric.ball_subset_closedBall,
    hA,hAR,hw⟩

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_UpperRootDiagonalCharts
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The diagonal action on actual full upper-root quotient boxes -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma upperRootTransverseDiagonal_add {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t u : ℝ) (s : UpperRootTransverse n) :
    upperRootTransverseDiagonal ell hell (t + u) s =
      upperRootTransverseDiagonal ell hell u (upperRootTransverseDiagonal ell hell t s) := by
  apply Subtype.ext
  exact congrArg (s.val * ·) (diagonalOneParameter_add ell hell t u) |>.trans
    (mul_assoc _ _ _).symm

lemma upperRootTransverseDiagonal_zero {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (s : UpperRootTransverse n) :
    upperRootTransverseDiagonal ell hell 0 s = s := by
  apply Subtype.ext
  simp only [upperRootTransverseDiagonal, diagonalOneParameter_zero, mul_one]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_TransverseDiagonalData
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

lemma continuous_transverseLogDiagonal (n : ℕ) :
    Continuous (@transverseLogDiagonal n) := by
  apply continuous_pi
  intro i
  have hentry : Continuous (fun s : UpperRootTransverse n => s.val.val i i) := by
    fun_prop
  exact hentry.abs.log (fun s => abs_ne_zero.mpr (upperRootTransverse_diagonal_ne_zero s i))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralTransverseCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

lemma transverseLogDiagonal_sum {n : ℕ} (s : PositiveTransverse n) :
    ∑ i, transverseLogDiagonal s.val i=0 := by
  simp only [transverseLogDiagonal,abs_of_pos (s.prop _)]
  rw [←Real.log_prod (fun i _ => (s.prop i).ne'),
    upperRootTransverse_diagonal_prod,Real.log_one]

def transverseNeutralCoordinate {n : ℕ} (s : PositiveTransverse n) :
    transverseNeutralSpace n :=
  ⟨transverseLogDiagonal s.val,transverseLogDiagonal_sum s⟩

def normalizedTransverse {n : ℕ} (s : PositiveTransverse n) : UpperRootTransverse n :=
  upperRootTransverseDiagonal (transverseNeutralCoordinate s).val
    (transverseNeutralCoordinate s).prop (-1) s.val

lemma normalizedTransverse_entry {n : ℕ} (s : PositiveTransverse n) (i j : Fin n) :
    (normalizedTransverse s).val.val i j=transverseColumnRatios s.val i j := by
  change (s.val.val*diagonalOneParameter _ _ (-1)).val i j=_
  rw [mul_diagonalOneParameter_entry]
  change s.val.val.val i j * Real.exp (Real.log |s.val.val.val j j| * (-1)) = _
  rw [abs_of_pos (s.prop j),mul_neg_one,Real.exp_neg,Real.exp_log (s.prop j)]
  rfl

lemma normalizedTransverse_diagonal {n : ℕ} (s : PositiveTransverse n) (i : Fin n) :
    (normalizedTransverse s).val.val i i=1 := by
  rw [normalizedTransverse_entry]
  exact div_self (s.prop i).ne'

def transverseUnitCoordinate {n : ℕ} (s : PositiveTransverse n) :
    UnitDiagonalTransverse n :=
  ⟨normalizedTransverse s,normalizedTransverse_diagonal s⟩

def transverseNeutralReconstruct {n : ℕ}
    (z : UnitDiagonalTransverse n × transverseNeutralSpace n) : PositiveTransverse n :=
  ⟨upperRootTransverseDiagonal z.2.val z.2.prop 1 z.1.val,by
    intro i
    change (z.1.val.val*diagonalOneParameter z.2.val z.2.prop 1).val i i > 0
    rw [mul_diagonalOneParameter_entry,z.1.prop i,one_mul]
    exact Real.exp_pos _⟩

lemma transverseNeutralReconstruct_coordinates {n : ℕ} (s : PositiveTransverse n) :
    transverseNeutralReconstruct (transverseUnitCoordinate s,transverseNeutralCoordinate s)=s := by
  apply Subtype.ext
  change upperRootTransverseDiagonal (transverseNeutralCoordinate s).val
    (transverseNeutralCoordinate s).prop 1
    (upperRootTransverseDiagonal (transverseNeutralCoordinate s).val
      (transverseNeutralCoordinate s).prop (-1) s.val)=s.val
  rw [←upperRootTransverseDiagonal_add,neg_add_cancel,upperRootTransverseDiagonal_zero]

lemma transverseNeutralCoordinate_reconstruct {n : ℕ}
    (z : UnitDiagonalTransverse n × transverseNeutralSpace n) :
    transverseNeutralCoordinate (transverseNeutralReconstruct z)=z.2 := by
  apply Subtype.ext
  funext i
  change Real.log |(z.1.val.val*diagonalOneParameter z.2.val z.2.prop 1).val i i|=z.2.val i
  rw [mul_diagonalOneParameter_entry,z.1.prop i,one_mul,mul_one,
    abs_of_pos (Real.exp_pos _),Real.log_exp]

lemma transverseUnitCoordinate_reconstruct {n : ℕ}
    (z : UnitDiagonalTransverse n × transverseNeutralSpace n) :
    transverseUnitCoordinate (transverseNeutralReconstruct z)=z.1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext i j
  change (normalizedTransverse (transverseNeutralReconstruct z)).val.val i j =
    z.1.val.val.val i j
  rw [normalizedTransverse_entry]
  change (z.1.val.val*diagonalOneParameter z.2.val z.2.prop 1).val i j /
    (z.1.val.val*diagonalOneParameter z.2.val z.2.prop 1).val j j = z.1.val.val.val i j
  rw [mul_diagonalOneParameter_entry,mul_diagonalOneParameter_entry,
    z.1.prop j,one_mul,mul_div_cancel_right₀ _ (Real.exp_ne_zero _)]

lemma continuous_transverseNeutralCoordinate (n : ℕ) :
    Continuous (@transverseNeutralCoordinate n) :=
  ((continuous_transverseLogDiagonal n).comp continuous_subtype_val).subtype_mk _

lemma continuous_transverseUnitCoordinate (n : ℕ) :
    Continuous (@transverseUnitCoordinate n) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  change Continuous (fun s : PositiveTransverse n => (normalizedTransverse s).val.val)
  have he : (fun s : PositiveTransverse n => (normalizedTransverse s).val.val)=
      fun s => transverseColumnRatios s.val := by
    funext s i j
    exact normalizedTransverse_entry s i j
  rw [he]
  exact (continuous_transverseColumnRatios n).comp continuous_subtype_val

lemma continuous_transverseNeutralReconstruct (n : ℕ) :
    Continuous (@transverseNeutralReconstruct n) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun z : UnitDiagonalTransverse n × transverseNeutralSpace n =>
    (z.1.val.val*diagonalOneParameter z.2.val z.2.prop 1).val i j)
  simp only [mul_diagonalOneParameter_entry,mul_one]
  have h₁ : Continuous (fun z : UnitDiagonalTransverse n × transverseNeutralSpace n =>
      z.1.val) := continuous_subtype_val.comp continuous_fst
  have h₂ : Continuous (fun z : UnitDiagonalTransverse n × transverseNeutralSpace n =>
      z.1.val.val) := continuous_subtype_val.comp h₁
  have hm : Continuous (fun z : UnitDiagonalTransverse n × transverseNeutralSpace n =>
      z.1.val.val.val) := continuous_subtype_val.comp h₂
  have he : Continuous (fun z : UnitDiagonalTransverse n × transverseNeutralSpace n =>
      z.2.val j) := (continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)
  exact ((continuous_apply j).comp ((continuous_apply i).comp hm)).mul
    (Real.continuous_exp.comp he)

def neutralTransverseHomeomorph (n : ℕ) :
    PositiveTransverse n ≃ₜ UnitDiagonalTransverse n × transverseNeutralSpace n where
  toFun s := (transverseUnitCoordinate s,transverseNeutralCoordinate s)
  invFun := transverseNeutralReconstruct
  left_inv := transverseNeutralReconstruct_coordinates
  right_inv z := Prod.ext (transverseUnitCoordinate_reconstruct z)
    (transverseNeutralCoordinate_reconstruct z)
  continuous_toFun := (continuous_transverseUnitCoordinate n).prodMk
    (continuous_transverseNeutralCoordinate n)
  continuous_invFun := continuous_transverseNeutralReconstruct n

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralUpperRootHomeomorph
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

def neutralUpperRootHomeomorph (n : ℕ) :
    UnitDiagonalTransverse n × (UpperRootTime n × transverseNeutralSpace n) ≃ₜ
      PositiveTransverse n × UpperRootTime n :=
  ((Homeomorph.refl (UnitDiagonalTransverse n)).prodCongr
    (Homeomorph.prodComm (UpperRootTime n) (transverseNeutralSpace n))).trans
    ((Homeomorph.prodAssoc _ _ _).symm.trans
      ((neutralRootSkewHomeomorph n).trans
        ((neutralTransverseHomeomorph n).symm.prodCongr
          (Homeomorph.refl (UpperRootTime n)))))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralPrefixMap
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual change from neutral coordinates to full-root prefix coordinates -/

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

def neutralToPrefix (n : ℕ) (z : NeutralCoordinateBase n × transverseNeutralSpace n) :
    (UpperRootTransverse n × PUnit.{1}) × UpperRootTime n :=
  (((transverseNeutralReconstruct (z.1.1,z.2)).val,PUnit.unit),
    (completeRootChain n).rootDilation z.2.val (-1) z.1.2)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PhysicalPrefixWindows
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical product windows covering compact prefix-time sets -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

namespace PhysicalPrefixWindow
variable {d : ℕ} {q : InitialRootStep (d+1)} {T : Type*} [TopologicalSpace T]
    {C : RootPrefixCoordinates (d+1) q.processed T} {g : G (d+1)}

def toBox (B : PhysicalPrefixWindow q C g)
    {D : Finset (Fin (d+1))} (c : EliminationChain q.processed D)
    (hf : c.finalEntries = allPositiveRoots (d+1)) : RootPrefixBox C c q.initial hf g :=
  C.physicalPrefixBox q c hf g B.pivot B.rectangle B.box B.transverse_eq
    B.interval B.interval_open B.window

end PhysicalPrefixWindow

namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain q.processed D)
    (hf : c.finalEntries = allPositiveRoots (d+1))

theorem exists_physicalPrefixWindow_covering (s : UpperRootTransverse (d+1) × T)
    (hfree : ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction (Quotient.mk _ ((g*s.1.val)*C.base s.2)) v =
        Quotient.mk _ ((g*s.1.val)*C.base s.2) → v = 1)
    (K : Set c.Time) (hK : IsCompact K) :
    ∃ B : PhysicalPrefixWindow q C g,
      s ∈ B.rectangle.first ∧ K ⊆ (B.toBox c hf).time := by
  let E := remainingFactorTime q c hf
  let P := E.symm '' K
  have hP : IsCompact P := hK.image E.symm.continuous
  let V := (Prod.fst '' P) ∪ {1}
  let I := (Prod.snd '' P) ∪ {0}
  have hV : IsCompact V := (hP.image continuous_fst).union isCompact_singleton
  have hI : IsCompact I := (hP.image continuous_snd).union isCompact_singleton
  obtain ⟨k,hk⟩ := exists_rootPivot q.root.1 ((g*s.1.val)*C.base s.2)
  obtain ⟨Q,A,R,J,V',I',hJ,hsQ,hVQ,hIJ,hV',hQV',hI',hJI',hA,hAR,hw⟩ :=
    C.exists_large_physical_rectangle q g k s hk hfree V hV I hI ⟨0,Or.inr rfl⟩
  let B : PhysicalPrefixWindow q C g :=
    ⟨k,Q,⟨1,hVQ (Or.inr rfl)⟩,A,hA,J,hJ,R,hAR,V',hV',hQV',I',hI',hJI',hw⟩
  refine ⟨B,hsQ,?_⟩
  intro t ht
  refine ⟨E.symm t,⟨hVQ (Or.inl ?_),hIJ (Or.inl ?_)⟩,E.apply_symm_apply t⟩
  · exact ⟨E.symm t,⟨t,ht,rfl⟩,rfl⟩
  · exact ⟨E.symm t,⟨t,ht,rfl⟩,rfl⟩

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PhysicalWindowAtlas
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countable compact-covering atlases of physical product windows -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set TopologicalSpace
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*}
    [TopologicalSpace T] [SecondCountableTopology T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain q.processed D)
    (hf : c.finalEntries = allPositiveRoots (d+1))

theorem exists_countable_physical_windows (K : Set c.Time) (hK : IsCompact K) :
    ∃ F : Set (PhysicalPrefixWindow q C g), F.Countable ∧
      (∀ B ∈ F, K ⊆ (B.toBox c hf).time) ∧
      ∀ s : UpperRootTransverse (d+1) × T,
        (∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
          rightAction (Quotient.mk _ ((g*s.1.val)*C.base s.2)) v =
            Quotient.mk _ ((g*s.1.val)*C.base s.2) → v = 1) →
        ∃ B ∈ F, s ∈ B.rectangle.first := by
  let Good := {B : PhysicalPrefixWindow q C g | K ⊆ (B.toBox c hf).time}
  obtain ⟨F,hFG,hFc,hF⟩ := isOpen_biUnion_countable Good
    (fun B : PhysicalPrefixWindow q C g => B.rectangle.first)
    (fun B _ => B.rectangle.first_open)
  refine ⟨F,hFc,fun B hB => hFG hB,?_⟩
  intro s hs
  obtain ⟨B,hsB,hKB⟩ := C.exists_physicalPrefixWindow_covering q g c hf s hs K hK
  have H : s ∈ ⋃ B ∈ Good, B.rectangle.first :=
    mem_iUnion.mpr ⟨B,mem_iUnion.mpr ⟨hKB,hsB⟩⟩
  rw [←hF] at H
  simpa only [mem_iUnion,exists_prop] using H

def physicalWindowFamily (R : ℝ) (m : ℕ) : Set (PhysicalPrefixWindow q C g) :=
  (C.exists_countable_physical_windows q g c hf (c.closedCube (R+m))
    (c.closedCube_compact (R+m))).choose

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralPatchCover
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A countable cover by actual small neutral rectangles -/

noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

structure SmallNeutralPatch (n : ℕ) (ε : ℝ) where
  center : G n
  box : RootPrefixBox (neutralEmptyPrefix n) (completeRootChain n)
    (emptyRootPattern n) (completeRootChain_final n) center
  bound : ℝ
  base : Set (NeutralCoordinateBase n)
  neutral : Set (transverseNeutralSpace n)
  base_open : IsOpen base
  neutral_open : IsOpen neutral
  neutral_nonempty : neutral.Nonempty
  time_bound : box.time ⊆ (completeRootChain n).remainingWindow bound 0
  in_box : ∀ z ∈ base ×ˢ neutral, neutralToPrefix n z ∈ box.domain
  small : ∀ z ∈ base ×ˢ neutral, ∀ w ∈ base ×ˢ neutral,
    (neutralProductParam n z)⁻¹*neutralProductParam n w ∈ matrixBall n ε

def SmallNeutralPatch.raw {n : ℕ} {ε : ℝ} (P : SmallNeutralPatch n ε) : Set (X n) :=
  neutralQuotientParam n P.center '' (P.base ×ˢ P.neutral)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_BigHilbertClassFieldNaturality
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
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

theorem
    infinitePlaceCompletionCongrHom_mem_infinitePositiveSubgroup_iff
    (e : K ≃ₐ[ℚ] M)
    (W : InfinitePlace M)
    (x : (W.comap e.toRingHom).Completionˣ) :
    Units.map
          (infinitePlaceCompletionCongrHom e W).toMonoidHom x ∈
        RayClass.infinitePositiveSubgroup W ↔
      x ∈
        RayClass.infinitePositiveSubgroup
          (W.comap e.toRingHom) := by
  rw [RayClass.mem_infinitePositiveSubgroup_iff,
    RayClass.mem_infinitePositiveSubgroup_iff]
  constructor
  · intro h hv
    have hW :
        W.IsReal :=
      (InfinitePlace.isReal_comap_iff
        e.toRingEquiv).1 hv
    have hpos :=
      h hW
    change
      0 <
        InfinitePlace.Completion.extensionEmbeddingOfIsReal hW
          (infinitePlaceCompletionCongrHom e W
            (x : (W.comap e.toRingHom).Completion)) at hpos
    rw [
      infinitePlaceCompletionCongrHom_extensionEmbeddingOfIsReal
        e W hW] at hpos
    simpa only using hpos
  · intro h hW
    have hv :
        (W.comap e.toRingHom).IsReal :=
      hW.comap e.toRingHom
    have hpos :=
      h hv
    change
      0 <
        InfinitePlace.Completion.extensionEmbeddingOfIsReal hW
          (infinitePlaceCompletionCongrHom e W
            (x : (W.comap e.toRingHom).Completion))
    rw [
      infinitePlaceCompletionCongrHom_extensionEmbeddingOfIsReal
        e W hW]
    simpa only using hpos

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_RamificationInvariants
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientMaximalIdealPowFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltrationPrincipalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Canonical ramification invariants

The ramification index and residue degree are the ideal-theoretic invariants of
the chosen valuation rings.  Every theorem below is stated directly in the
ambient valued-extension context; there are no compatibility aliases or
extension-marker arguments.
-/

noncomputable section

universe u v w x

namespace LocalFieldTheory.DiscreteValuationField

open ValuationTheory.DiscreteValuationField

namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- The local fundamental identity for a finite extension of valuation rings. -/
theorem degree_eq_ramificationIndex_mul_residueDegree
    [Module.Finite base.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    ValuationTheory.DiscreteValuationField.ValuedExtension.degree
        base.toDVF target.toDVF =
      ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
          base.toDVF target.toDVF *
        ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
          base.toDVF target.toDVF :=
  (ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_mul_residueDegree_eq_degree
    base target).symm

/--
Establishes the inequality
`ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex base.toDVF target.toDVF
≠ 0`.
-/
theorem ramificationIndex_ne_zero
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring] :
    ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
      base.toDVF target.toDVF ≠ 0 :=
  ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_ne_zero
    base target

/--
Establishes the strict bound `0 <
ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex base.toDVF target.toDVF`.
-/
theorem ramificationIndex_pos
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring] :
    0 < ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
      base.toDVF target.toDVF :=
  Nat.pos_of_ne_zero (ramificationIndex_ne_zero base target)

/--
Establishes the identity `ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
base.toDVF target.toDVF = ValuationTheory.DiscreteValuationField.ValuedExtension.degree base.toDVF
target.toDVF`.
-/
theorem ramificationIndex_eq_degree_of_residueDegree_eq_one
    [Module.Finite base.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    (h :
      ValuationTheory.DiscreteValuationField.ValuedExtension.residueDegree
        base.toDVF target.toDVF = 1) :
    ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
        base.toDVF target.toDVF =
      ValuationTheory.DiscreteValuationField.ValuedExtension.degree
        base.toDVF target.toDVF := by
  rw [degree_eq_ramificationIndex_mul_residueDegree base target, h, mul_one]

end ValuedExtension
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Abstract and concrete unramified Frobenius

This module compares the residue-degree construction on a fixed separable
closure with the ordinary unramified valuation extension and its arithmetic
Frobenius.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open RamificationTheory.HilbertRamification.ValuationSubring


section

variable (K L : Type)
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K)
    (ValuativeRel.valuation L)]

noncomputable instance comparisonIntegerRingIsIntegralClosure :
    IsIntegralClosure 𝒪[L] 𝒪[K] L :=
  localCompleteDVF_integerRing_isIntegralClosure K L

/-! ## Comparison of unramifiedness -/

/-! ## Frobenius normalization -/

end

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_RamificationAddVal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientMaximalIdealPowFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltrationPrincipalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupFinite _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseValuationIsNontrivial _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Additive valuations in finite complete-DVF extensions

The normalized additive valuation on the target valuation ring restricts to
the ramification index times the normalized additive valuation on the base
valuation ring.  The proof is characteristic-independent and follows from the
ideal identity
`m_K · O_L = m_L ^ e`.
-/

noncomputable section

universe u v w x

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace ValuedExtension
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- The target normalized additive valuation of an element from the base
valuation ring is its base additive valuation multiplied by the ramification
index.  This includes the zero element, whose additive valuation is `⊤`. -/
theorem addVal_integerMap_eq_ramificationIndex_nsmul
    (a : base.valuationSubring) :
    IsDiscreteValuationRing.addVal target.valuationSubring
        (integerMap base.toDVF target.toDVF a) =
      ramificationIndex base.toDVF target.toDVF •
        IsDiscreteValuationRing.addVal base.valuationSubring a := by
  let e := ramificationIndex base.toDVF target.toDVF
  have he_ne : e ≠ 0 := by
    intro he
    have hle :=
      maximalIdeal_map_integerMap_le base.toDVF target.toDVF
    have hmap :=
      maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndex
        base target
    rw [show ramificationIndex base.toDVF target.toDVF = e from rfl,
      he, pow_zero] at hmap
    rw [hmap] at hle
    have hle_top :
        (⊤ : Ideal target.valuationSubring) ≤
          IsLocalRing.maximalIdeal target.valuationSubring := by
      simpa only [Ideal.one_eq_top] using hle
    exact
      (IsLocalRing.maximalIdeal.isMaximal
        target.valuationSubring).ne_top (top_unique hle_top)
  by_cases ha : a = 0
  · subst a
    have he_coe_ne : (e : ℕ∞) ≠ 0 := by
      exact_mod_cast he_ne
    rw [map_zero, IsDiscreteValuationRing.addVal_zero,
      IsDiscreteValuationRing.addVal_zero, nsmul_eq_mul,
      ENat.mul_top he_coe_ne]
  obtain ⟨pi, hpi⟩ :=
    IsDiscreteValuationRing.exists_irreducible base.valuationSubring
  obtain ⟨varpi, hvarpi⟩ :=
    IsDiscreteValuationRing.exists_irreducible target.valuationSubring
  obtain ⟨m, unit, ha_decomp⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hpi
  have hspan :
      Ideal.span
          ({integerMap base.toDVF target.toDVF pi} :
            Set target.valuationSubring) =
        Ideal.span ({varpi ^ e} : Set target.valuationSubring) := by
    calc
      Ideal.span
          ({integerMap base.toDVF target.toDVF pi} :
            Set target.valuationSubring) =
          Ideal.map (integerMap base.toDVF target.toDVF)
            (Ideal.span ({pi} : Set base.valuationSubring)) := by
              rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.map (integerMap base.toDVF target.toDVF)
          base.maximalIdeal := by
            rw [show base.maximalIdeal =
                IsLocalRing.maximalIdeal base.valuationSubring from rfl,
              hpi.maximalIdeal_eq]
      _ = target.maximalIdeal ^ e := by
            exact
              maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndex
                base target
      _ = Ideal.span ({varpi ^ e} : Set target.valuationSubring) := by
            rw [show target.maximalIdeal =
                IsLocalRing.maximalIdeal target.valuationSubring from rfl,
              hvarpi.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hmap_uniformizer :
      IsDiscreteValuationRing.addVal target.valuationSubring
          (integerMap base.toDVF target.toDVF pi) =
        (e : ℕ∞) := by
    calc
      IsDiscreteValuationRing.addVal target.valuationSubring
          (integerMap base.toDVF target.toDVF pi) =
          IsDiscreteValuationRing.addVal target.valuationSubring
            (varpi ^ e) :=
        (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).2
          (Ideal.span_singleton_eq_span_singleton.mp hspan)
      _ = (e : ℕ∞) := hvarpi.addVal_pow e
  rw [ha_decomp, map_mul, map_pow,
    IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_pow, hmap_uniformizer,
    IsDiscreteValuationRing.addVal_def
      ((unit : base.valuationSubring) * pi ^ m)
      unit hpi m rfl]
  have hmap_unit :
      IsDiscreteValuationRing.addVal target.valuationSubring
          (integerMap base.toDVF target.toDVF
            (unit : base.valuationSubring)) = 0 := by
    exact
      IsDiscreteValuationRing.addVal_eq_zero_iff.mpr
        ((unit.isUnit : IsUnit (unit : base.valuationSubring)).map
          (integerMap base.toDVF target.toDVF))
  rw [hmap_unit, zero_add]
  simp [e, nsmul_eq_mul, mul_comm]

/-- The target additive valuation of the image of a base uniformizer is the
ramification index. -/
theorem addVal_integerMap_eq_ramificationIndex_of_irreducible
    {a : base.valuationSubring} (ha : Irreducible a) :
    IsDiscreteValuationRing.addVal target.valuationSubring
        (integerMap base.toDVF target.toDVF a) =
      (ramificationIndex base.toDVF target.toDVF : ℕ∞) := by
  rw [addVal_integerMap_eq_ramificationIndex_nsmul base target a,
    IsDiscreteValuationRing.addVal_uniformizer ha, nsmul_eq_mul, mul_one]

/-- If a base uniformizer remains a uniformizer after applying the
valuation-ring map, then the relative ramification index is one. -/
theorem ramificationIndex_eq_one_of_integerMap_uniformizer
    (a : base.valuationSubring)
    (ha : base.valuation.IsUniformizer (a : K))
    (hmap :
      target.valuation.IsUniformizer
        ((integerMap base.toDVF target.toDVF a :
          target.valuationSubring) : L)) :
    ramificationIndex base.toDVF target.toDVF = 1 := by
  have haIrreducible : Irreducible a :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer a).2
      (base.maximalIdeal_eq_span_uniformizer ha)
  have hmapIrreducible :
      Irreducible (integerMap base.toDVF target.toDVF a) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer
      (integerMap base.toDVF target.toDVF a)).2
      (target.maximalIdeal_eq_span_uniformizer hmap)
  have hadd :=
    addVal_integerMap_eq_ramificationIndex_nsmul base target a
  rw [IsDiscreteValuationRing.addVal_uniformizer hmapIrreducible,
    IsDiscreteValuationRing.addVal_uniformizer haIrreducible,
    nsmul_eq_mul, mul_one] at hadd
  have hcoe :
      (ramificationIndex base.toDVF target.toDVF : ℕ∞) = 1 :=
    hadd.symm
  exact_mod_cast hcoe

end ValuedExtension
end LocalFieldTheory.DiscreteValuationField

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_Intertwiner
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientMaximalIdealPowFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltrationPrincipalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Intertwining equations for Lubin--Tate series

For two Lubin--Tate series with the same prescribed linear coefficient, this
module defines the multivariable intertwining equation and its additive defect.
-/

noncomputable section

universe u v

namespace LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type*}

/-- Each variable itself intertwines a Lubin--Tate series with itself. -/
theorem intertwines_X [Finite σ]
    (e : LubinTateSeries F π) (i : σ) :
    Intertwines e e (MvPowerSeries.X i) := by
  rw [Intertwines,
    MvPowerSeries.subst_X (inVariable_hasSubst e)]
  rfl

end SameUniformizer
end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_FormalModule_DegreeStabilization
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientMaximalIdealPowFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltrationPrincipalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastToQpadicClosureSubfield_apply _root_.LocalFieldTheory.DiscreteValuationField.LocalField.ratCastWithValToQpadicClosureSubfield_apply _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.degree_eq_finrank _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integerMap_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureRingEquivTargetValuationSubringOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureToTargetValuationSubringOfHasExtension_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_apply_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_residueMap _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueFieldEquivOfSurjective_symm_apply_target_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residue _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueMap_residueFieldEquivOfSurjective_symm_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.residueUnitsEquivOfResidueMapSurjective_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.targetValuationSubringToIntegralClosureOfModuleFinite_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.unitMap_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-degree stabilization for Lubin--Tate intertwining defects

The coefficient of an intertwining defect in total degree at most `m`
depends only on the coefficients of the proposed intertwiner in total degree
at most `m`.  This is the finite-degree continuity statement needed to pass
from recursively corrected finite approximations to one full multivariable
power series.

The proof uses total-degree truncation.  On the left side of the
intertwining equation, truncation commutes with substituting a series with
zero constant coefficient into the fixed Lubin--Tate series.  On the right
side, truncation of multivariable substitution depends only on the same
truncation of the outer series.
-/

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

universe u v w

namespace LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

omit [Fintype σ] in
theorem coeff_subst_lubinTateSeries_add_monomial_of_degree_le
    (e : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (q d : σ →₀ ℕ) (hq : q.degree ≤ d.degree)
    (hd : 1 ≤ d.degree) (c : F.valuationSubring) :
    MvPowerSeries.coeff q
        (PowerSeries.subst
          (H + MvPowerSeries.monomial d c)
          e.toPowerSeries) =
      MvPowerSeries.coeff q
          (PowerSeries.subst H e.toPowerSeries) +
        π * (if q = d then c else 0) := by
  have hd0 : d ≠ 0 := by
    intro h
    subst d
    simp at hd
  have hMconstant :
      MvPowerSeries.constantCoeff
          (MvPowerSeries.monomial d c) = 0 :=
    constantCoeff_monomial_eq_zero_stabilization hd0 c
  have hnewSubst :
      PowerSeries.HasSubst
        (H + MvPowerSeries.monomial d c) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by
      simp [hH, hMconstant])
  have hHsubst : PowerSeries.HasSubst H :=
    PowerSeries.HasSubst.of_constantCoeff_zero hH
  let oldTerm : ℕ → F.valuationSubring := fun n =>
    PowerSeries.coeff n e.toPowerSeries •
      MvPowerSeries.coeff q (H ^ n)
  let deltaTerm : ℕ → F.valuationSubring := fun n =>
    PowerSeries.coeff n e.toPowerSeries •
      if n = 1 then (if q = d then c else 0) else 0
  have hold : Function.HasFiniteSupport oldTerm := by
    simpa only [oldTerm] using
      PowerSeries.coeff_subst_finite hHsubst e.toPowerSeries q
  have hdelta : Function.HasFiniteSupport deltaTerm := by
    rw [Function.HasFiniteSupport]
    refine (Set.finite_singleton 1).subset ?_
    intro n hn
    simp only [Function.mem_support] at hn
    simp only [Set.mem_singleton_iff]
    by_contra hne
    apply hn
    simp [deltaTerm, hne]
  rw [
    PowerSeries.coeff_subst hnewSubst e.toPowerSeries q,
    PowerSeries.coeff_subst hHsubst e.toPowerSeries q]
  calc
    ∑ᶠ n : ℕ,
        PowerSeries.coeff n e.toPowerSeries •
          MvPowerSeries.coeff q
            ((H + MvPowerSeries.monomial d c) ^ n) =
        (∑ᶠ n : ℕ, (oldTerm n + deltaTerm n)) := by
      apply finsum_congr
      intro n
      rw [coeff_pow_add_monomial_of_degree_le
        hH q d hq hd c n, smul_add]
    _ = (∑ᶠ n : ℕ, oldTerm n) +
        ∑ᶠ n : ℕ, deltaTerm n :=
      finsum_add_distrib hold hdelta
    _ = (∑ᶠ n : ℕ, oldTerm n) +
        PowerSeries.coeff 1 e.toPowerSeries *
          (if q = d then c else 0) := by
      congr 1
      rw [finsum_eq_single _ 1]
      · simp [deltaTerm, smul_eq_mul]
      · intro n hn
        simp [deltaTerm, hn]
    _ = (∑ᶠ n : ℕ, oldTerm n) +
        π * (if q = d then c else 0) := by
      rw [LubinTateSeries.coeff_one_eq_uniformizer]

end SameUniformizer
end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.Ramification_HilbertRamification_CompleteDVF
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientMaximalIdealPowFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltrationPrincipalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.ProCGroups.InducedFunctions.inducedMulDistribMulAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.decompositionSubgroupMulSemiringAction _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsInvariant _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instSMulCommClass _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.toDecompositionGroupOfEqTop_coe _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroupResidueAction_residue _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroupQuotientRamificationEquivInertiaAutQuotient_mk _root_.RamificationTheory.HilbertRamification.ValuationSubring.mem_ramificationGroupInInertiaAut_iff _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Decomposition and inertia for finite extensions of complete DVFs

For a finite separable extension of complete discretely valued fields, the
extension of the base valuation is unique.  Consequently every
base-field automorphism stabilizes the chosen target valuation ring and the
full Galois group is the decomposition group.  Reduction then gives the
finite Galois exact sequence

`1 -> I(L/K) -> Gal(L/K) -> Gal(k_L/k_K) -> 1`.

The valuation-subring definitions and their ordinary exactness are reused
from `HilbertRamification.ValuationSubring`; this file only supplies the
complete-DVF specialization and the finite-Galois surjectivity theorem.
-/

noncomputable section

open scoped Pointwise

universe u v w x

namespace RamificationTheory.HilbertRamification.CompleteDVF

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

section ValuationUniqueness

variable [FiniteDimensional K L]

include base target

theorem inv_smul_valuationSubring_eq
    [Algebra.IsSeparable K L]
    (sigma : L ≃ₐ[K] L) :
    sigma⁻¹ • target.valuation.valuationSubring =
      target.valuation.valuationSubring := by
  let pulledBack := target.valuation.comap (sigma : L →+* L)
  let : base.valuation.HasExtension pulledBack :=
    comapValuation_hasExtension (base := base) (target := target) sigma
  have hEquiv : target.valuation.IsEquiv pulledBack :=
    (hasUniqueValuationExtension_of_finite_separable base target :
      ValuedExtension.HasUniqueValuationExtension.{u, v, w, x, x}
        (base := base) (target := target)) pulledBack
  have hSubring :
      target.valuation.valuationSubring = pulledBack.valuationSubring :=
    (_root_.Valuation.isEquiv_iff_valuationSubring
      target.valuation pulledBack).1 hEquiv
  have hComap :
      pulledBack.valuationSubring =
        sigma⁻¹ • target.valuation.valuationSubring := by
    ext z
    change target.valuation (sigma z) ≤ 1 ↔
      z ∈ sigma⁻¹ • target.valuation.valuationSubring
    rw [_root_.ValuationSubring.mem_inv_pointwise_smul_iff]
    simp [AlgEquiv.smul_def, _root_.Valuation.mem_valuationSubring_iff]
  exact hComap.symm.trans hSubring.symm

/-- Every automorphism of a finite separable extension of complete DVFs
stabilizes the target valuation ring. -/
theorem automorphism_stabilizes_valuationSubring
    [Algebra.IsSeparable K L]
    (sigma : L ≃ₐ[K] L) :
    sigma • target.valuation.valuationSubring =
      target.valuation.valuationSubring := by
  have hinv := inv_smul_valuationSubring_eq
    (base := base) (target := target) sigma
  calc
    sigma • target.valuation.valuationSubring =
        sigma • (sigma⁻¹ • target.valuation.valuationSubring) := by rw [hinv]
    _ = target.valuation.valuationSubring := by simp [smul_smul]

/-- For a finite separable extension of complete DVFs, the full automorphism
group is canonically the decomposition group of the target valuation ring. -/
def galEquivDecompositionGroup
    [Algebra.IsSeparable K L] :
    (L ≃ₐ[K] L) ≃*
      ValuationSubring.decompositionGroup K
        target.valuation.valuationSubring where
  toFun sigma := ⟨sigma, by
    change sigma • target.valuation.valuationSubring =
      target.valuation.valuationSubring
    exact automorphism_stabilizes_valuationSubring
      (base := base) (target := target) sigma⟩
  invFun sigma := (sigma : L ≃ₐ[K] L)
  left_inv _ := rfl
  right_inv _ := by apply Subtype.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; rfl

/-- States the theorem `galEquivDecompositionGroup_coe`. -/
@[simp]
theorem galEquivDecompositionGroup_coe
    [Algebra.IsSeparable K L]
    (sigma : L ≃ₐ[K] L) :
    ((galEquivDecompositionGroup (base := base) (target := target) sigma :
        ValuationSubring.decompositionGroup K
      target.valuation.valuationSubring) : L ≃ₐ[K] L) = sigma :=
  rfl

end ValuationUniqueness

/-- Reduction of the decomposition-group action, as automorphisms over the
base residue field. -/
def decompositionResidueAction :
    ValuationSubring.decompositionGroup K
        target.valuation.valuationSubring →*
      (target.residueField ≃ₐ[base.residueField] target.residueField) where
  toFun sigma :=
    { ValuationSubring.residueAction K target.valuation.valuationSubring sigma with
      commutes' := by
        intro z
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
        change
          ValuationSubring.residueAction K target.valuation.valuationSubring sigma
              (IsLocalRing.residue target.valuationSubring
                (algebraMap base.valuationSubring target.valuationSubring a)) =
            IsLocalRing.residue target.valuationSubring
              (algebraMap base.valuationSubring target.valuationSubring a)
        change
          sigma •
              (IsLocalRing.residue target.valuationSubring
                (algebraMap base.valuationSubring target.valuationSubring a)) =
            IsLocalRing.residue target.valuationSubring
              (algebraMap base.valuationSubring target.valuationSubring a)
        change
          IsLocalRing.residue target.valuationSubring
              (sigma •
                algebraMap base.valuationSubring target.valuationSubring a) =
            IsLocalRing.residue target.valuationSubring
              (algebraMap base.valuationSubring target.valuationSubring a)
        congr 1
        apply Subtype.ext
        change
          (sigma : L ≃ₐ[K] L) (algebraMap K L (a : K)) =
            algebraMap K L (a : K)
        exact (sigma : L ≃ₐ[K] L).commutes (a : K) }
  map_one' := by
    apply AlgEquiv.ext
    intro z
    change
      ValuationSubring.residueAction K target.valuation.valuationSubring 1 z =
        (1 : target.residueField ≃ₐ[base.residueField] target.residueField) z
    rw [MonoidHom.map_one]
    exact AlgEquiv.one_apply (R := base.residueField) (A₁ := target.residueField) z
  map_mul' := by
    intro sigma tau
    apply AlgEquiv.ext
    intro z
    change
      ValuationSubring.residueAction K target.valuation.valuationSubring
          (sigma * tau) z =
        (ValuationSubring.residueAction K target.valuation.valuationSubring sigma *
          ValuationSubring.residueAction K target.valuation.valuationSubring tau) z
    rw [MonoidHom.map_mul]

/-- States the theorem `decompositionResidueAction_apply`. -/
@[simp]
theorem decompositionResidueAction_apply
    (sigma : ValuationSubring.decompositionGroup K
      target.valuation.valuationSubring)
    (z : target.residueField) :
    decompositionResidueAction (K := K) (base := base) (target := target) sigma z =
      ValuationSubring.residueAction K
        target.valuation.valuationSubring sigma z :=
  rfl

/-- States the theorem `decompositionResidueAction_algebraMap`. -/
@[simp]
theorem decompositionResidueAction_algebraMap
    (sigma : ValuationSubring.decompositionGroup K
      target.valuation.valuationSubring)
    (z : base.residueField) :
    decompositionResidueAction (K := K) (base := base) (target := target) sigma
        (algebraMap base.residueField target.residueField z) =
      algebraMap base.residueField target.residueField z :=
  (decompositionResidueAction
    (K := K) (base := base) (target := target) sigma).commutes z

section FullGaloisGroup

variable [FiniteDimensional K L]

include base target

/-- The residue action of the full automorphism group, transported through
the canonical identification with the decomposition group. -/
def residueAction
    [Algebra.IsSeparable K L] :
    (L ≃ₐ[K] L) →*
      (target.residueField ≃ₐ[base.residueField] target.residueField) :=
  (decompositionResidueAction
    (K := K) (base := base) (target := target)).comp
    (galEquivDecompositionGroup
      (base := base) (target := target)).toMonoidHom

/-- States the theorem `residueAction_apply`. -/
@[simp]
theorem residueAction_apply
    [Algebra.IsSeparable K L]
    (sigma : L ≃ₐ[K] L) :
    residueAction (K := K) (base := base) (target := target) sigma =
      decompositionResidueAction
        (K := K) (base := base) (target := target)
        (galEquivDecompositionGroup
          (base := base) (target := target) sigma) :=
  rfl

end FullGaloisGroup

end RamificationTheory.HilbertRamification.CompleteDVF

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnitPadicAction_TopologyModelTypes
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Type-level topology models for principal units

Adic principal units, discrete finite quotients, and the prodiscrete inverse limit are
represented by distinct wrapper types so that their topologies cannot be confused by instance
selection.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace CompleteDVF
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
namespace higherPrincipalUnitGroup

open LubinTate
open LubinTate.Valuations

variable {K : Type u} [Field K]

open Internal

/-! ## Topology is part of the type

The algebraic quotient and inverse-limit types above deliberately carry no
preferred topology.  The following models distinguish the topologies used in
the p-adic action at the type level.  In particular, no theorem below can
silently reinterpret the same quotient as both a quotient-topological and a
discrete space.
-/

namespace DiscretePrincipalUnitQuotient

/--
Equips the target with its canonical `TopologicalSpace` structure, namely `TopologicalSpace
(DiscretePrincipalUnitQuotient F n)`.
-/
instance instTopologicalSpace (F : CompleteDVF.{u, v} K) (n : ℕ) :
    TopologicalSpace (DiscretePrincipalUnitQuotient F n) := ⊥

/--
Equips the target with its canonical `DiscreteTopology` structure, namely `DiscreteTopology
(DiscretePrincipalUnitQuotient F n)`.
-/
instance instDiscreteTopology (F : CompleteDVF.{u, v} K) (n : ℕ) :
    DiscreteTopology (DiscretePrincipalUnitQuotient F n) :=
  ⟨rfl⟩

end DiscretePrincipalUnitQuotient

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PrincipalUnitPadicAction_AdicProdiscreteComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageClassInQuotient_normal _root_.LocalFieldTheory.DiscreteValuationField.ValuedNorm.filtrationPreimageSubgroup_normal _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Adic and prodiscrete principal-unit models

The adic topology on first principal units agrees with the prodiscrete topology carried
by the inverse limit of finite quotient coordinates.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace CompleteDVF
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
namespace higherPrincipalUnitGroup

open LubinTate
open LubinTate.Valuations

variable {K : Type u} [Field K]

open Internal

/-- The prodiscrete principal-unit limit is Hausdorff. -/
noncomputable instance principalUnitProdiscreteLimitT2Space
    (F : CompleteDVF.{u, v} K) :
    T2Space (PrincipalUnitProdiscreteLimit F) := by
  let : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => ⊥
  let : (n : ℕ) → DiscreteTopology (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => ⟨rfl⟩
  let : (n : ℕ) → T2Space (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => DiscreteTopology.toT2Space
  let : T2Space (Internal.principalUnitInverseLimitCarrier F) := by
    infer_instance
  let : T2Space (Additive (Internal.principalUnitInverseLimitCarrier F)) := by
    change T2Space (Internal.principalUnitInverseLimitCarrier F)
    infer_instance
  exact T2Space.of_injective_continuous
    (Internal.principalUnitProdiscreteLimitHomeomorphUnderlying F).injective
    (Internal.principalUnitProdiscreteLimitHomeomorphUnderlying F).continuous

/-- The topology on the type in `T2Space (AdicPrincipalUnits F)` is Hausdorff. -/
noncomputable instance adicPrincipalUnitsT2Space
    (F : CompleteDVF.{u, v} K) : T2Space (AdicPrincipalUnits F) :=
  (adicPrincipalUnitsHomeomorphProdiscreteLimit F).symm.t2Space

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.Valuation_DiscreteValuationField_AmbientUniformizer
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientMaximalIdealPowFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltrationPrincipalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupFinite _root_.LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_isRankOneDiscrete _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.Valuations.exponentialValuationSubringIsLocalRing _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.maximalIdealPowSuccQuotAddEquivPrincipalUnitSuccQuot_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.mem_iff _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_coord _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidueOfUniformizer_symm_residue _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotConcreteEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotLift_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuotAdd_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_map_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotOfMaximalIdealPowSuccQuot_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerLift_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.rootsPrincipalUnitUniformizerMulHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.toPrincipalUnitFiltration_subgroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModOneEquivResidueFieldUnits_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModPrincipalUnitEquivOfPreserves_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitEquivOfPreserves_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.zero_eq_top _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.localIntegerValuationSubringEquiv_apply_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup_coe _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.ValuationTheory.DiscreteValuationField.ValuedExtension.Henselian.integralClosureValuationSubringIntegerMapOfMemOrInv_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Uniformizers detected in an ambient complete discrete valuation field

An embedding into an ambient complete DVF can make a uniformizer easier to
recognize.  For a finite separable extension, uniqueness of the extended
valuation transports that recognition back to the chosen valuation.
-/

namespace ValuationTheory

noncomputable section

universe u v w x y z

namespace DiscreteValuationField
namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- Let `L / K` be finite separable with a chosen complete discrete valuation
extending the one on `K`.  If a field embedding of `L` into another complete
DVF sends `π` to an ambient uniformizer, and the pulled-back ambient valuation
also extends the base valuation, then `π` is a uniformizer for the chosen
valuation on `L`.

The proof first uses uniqueness of valuation extension to compare the chosen
valuation with the ambient comap valuation.  It then pulls divisibility by the
ambient uniformizer back through the field embedding, proving that `π`
generates the chosen maximal ideal. -/
theorem isUniformizer_of_ambient_image_isUniformizer
    {M : Type y} [Field M]
    (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
    (ambient : CompleteDVF.{y, z} M)
    [base.valuation.HasExtension target.valuation]
    (ι : L →+* M)
    [base.valuation.HasExtension (ambient.valuation.comap ι)]
    {π : L} (hπ : ambient.valuation.IsUniformizer (ι π)) :
    target.valuation.IsUniformizer π := by
  have hEquiv :
      target.valuation.IsEquiv (ambient.valuation.comap ι) :=
    valuation_isEquiv_of_finite_separable base target
      (ambient.valuation.comap ι)
  have hπ_target_lt : target.valuation π < 1 := by
    have hπ_comap_lt :
        (ambient.valuation.comap ι) π <
          (ambient.valuation.comap ι) 1 := by
      simpa using hπ.val_lt_one
    simpa using
      (hEquiv.lt_iff_lt (x := π) (y := (1 : L))).2 hπ_comap_lt
  let πtarget : target.valuationSubring :=
    ⟨π, hπ_target_lt.le⟩
  have hmaximal :
      target.maximalIdeal =
        Ideal.span ({πtarget} : Set target.valuationSubring) := by
    apply le_antisymm
    · intro a ha
      have ha_target_lt : target.valuation (a : L) < 1 :=
        (_root_.Valuation.mem_maximalIdeal_iff
          (v := target.valuation)).1 ha
      have ha_ambient_lt : ambient.valuation (ι (a : L)) < 1 := by
        have ha_comap_lt :
            (ambient.valuation.comap ι) (a : L) <
              (ambient.valuation.comap ι) 1 :=
          (hEquiv.lt_iff_lt (x := (a : L)) (y := (1 : L))).1
            (by simpa using ha_target_lt)
        simpa using ha_comap_lt
      let aambient : ambient.valuationSubring :=
        ⟨ι (a : L), ha_ambient_lt.le⟩
      let πambient : ambient.valuationSubring :=
        ⟨ι π, hπ.val_lt_one.le⟩
      have ha_ambient_maximal :
          aambient ∈ ambient.maximalIdeal :=
        (_root_.Valuation.mem_maximalIdeal_iff
          (v := ambient.valuation)).2 ha_ambient_lt
      have hπambient :
          ambient.valuation.IsUniformizer (πambient : M) := by
        simpa [πambient] using hπ
      rw [ambient.maximalIdeal_eq_span_uniformizer hπambient,
        Ideal.mem_span_singleton] at ha_ambient_maximal
      obtain ⟨c, hc⟩ := ha_ambient_maximal
      have hc_field :
          ι (a : L) = ι π * (c : M) := by
        simpa [aambient, πambient] using
          congrArg
            (fun t : ambient.valuationSubring => (t : M)) hc
      have hπ_ne : π ≠ 0 := by
        intro hzero
        apply hπ.ne_zero
        simp [hzero]
      have hc_eq :
          (c : M) = ι (π⁻¹ * (a : L)) := by
        apply mul_left_cancel₀ hπ.ne_zero
        calc
          ι π * (c : M) = ι (a : L) := hc_field.symm
          _ = ι (π * (π⁻¹ * (a : L))) := by
            congr 1
            rw [← mul_assoc, mul_inv_cancel₀ hπ_ne, one_mul]
          _ = ι π * ι (π⁻¹ * (a : L)) := by
            rw [map_mul]
      have hquotient_comap :
          (ambient.valuation.comap ι) (π⁻¹ * (a : L)) ≤
            (ambient.valuation.comap ι) 1 := by
        have hquotient_ambient :
            ambient.valuation (ι (π⁻¹ * (a : L))) ≤ 1 := by
          rw [← hc_eq]
          exact c.property
        simpa using hquotient_ambient
      have hquotient_target :
          target.valuation (π⁻¹ * (a : L)) ≤ 1 := by
        have hle :=
          (hEquiv.le_iff_le
            (x := π⁻¹ * (a : L)) (y := (1 : L))).2
            hquotient_comap
        simpa using hle
      let quotient : target.valuationSubring :=
        ⟨π⁻¹ * (a : L), hquotient_target⟩
      rw [Ideal.mem_span_singleton]
      refine ⟨quotient, ?_⟩
      apply Subtype.ext
      change (a : L) = π * (π⁻¹ * (a : L))
      rw [← mul_assoc, mul_inv_cancel₀ hπ_ne, one_mul]
    · rw [Ideal.span_le]
      intro a ha
      have ha_eq : a = πtarget := by
        simpa using ha
      subst a
      exact
        (_root_.Valuation.mem_maximalIdeal_iff
          (v := target.valuation)).2
          (by simpa [πtarget] using hπ_target_lt)
  have hπtarget :
      target.valuation.IsUniformizer (πtarget : L) :=
    target.valuation.isUniformizer_of_maximalIdeal_eq_span hmaximal
  simpa [πtarget] using hπtarget

end ValuedExtension
end DiscreteValuationField
end
end ValuationTheory
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicCharacterRigidity
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isAbelianGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isIntegral _root_.KummerTheory.rationalCyclotomicTorsionFixedField_normal _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueCharacteristic.fact_prime _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Rigidity of the rational cyclotomic character

The actual rational cyclotomic character is detected by all of its
prime-power reductions.  In particular, if every reduction of every
`p`-adic character coordinate has square one, then the underlying
automorphism of the full rational cyclotomic field has square one.
-/

open scoped Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

local instance localInst_raa7634_1 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩
/-- An automorphism of the full rational cyclotomic field has square one
as soon as every prime-power reduction of its genuine cyclotomic
character has square one. -/
theorem rationalCyclotomicAutomorphism_sq_eq_one_of_character_reductions
    (σ :
      KummerTheory.rationalCyclotomicField ≃ₐ[ℚ]
        KummerTheory.rationalCyclotomicField)
    (h :
      ∀ (p : Nat.Primes) (k : ℕ),
        Units.map (PadicInt.toZModPow k).toMonoidHom
              (KummerTheory.rationalCyclotomicCharacterPrimeProduct
                σ p) ^ 2 =
          1) :
    σ ^ 2 = 1 := by
  apply
    KummerTheory.rationalCyclotomicCharacterPrimeProduct_injective
  rw [map_pow, map_one]
  funext p
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro k
  let u : ℤ_[p.1]ˣ :=
    KummerTheory.rationalCyclotomicCharacterPrimeProduct σ p
  let f : ℤ_[p.1] →* ZMod (p.1 ^ k) :=
    (PadicInt.toZModPow k).toMonoidHom
  have hk : Units.map f (u ^ 2) = 1 := by
    change
      Units.map (PadicInt.toZModPow k).toMonoidHom
          (KummerTheory.rationalCyclotomicCharacterPrimeProduct σ p ^ 2) =
        1
    rw [map_pow]
    exact h p k
  simp only [Pi.pow_apply, Pi.one_apply]
  calc
    (PadicInt.toZModPow k)
          ↑(KummerTheory.rationalCyclotomicCharacterPrimeProduct σ p ^ 2) =
        f ↑(u ^ 2) := rfl
    _ = ↑(Units.map f (u ^ 2)) :=
      (Units.coe_map f (u ^ 2)).symm
    _ = ↑(1 : (ZMod (p.1 ^ k))ˣ) :=
      congrArg Units.val hk
    _ = f ↑(1 : ℤ_[p.1]ˣ) := (map_one f).symm
    _ = (PadicInt.toZModPow k) ↑(1 : ℤ_[p.1]ˣ) := rfl

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_ComplexificationArtin_InfinitePlaceOverfield
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
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
noncomputable def infinitePlaceRatComplexificationFactors
    (v : InfinitePlace K) :
    IntermediateField ℚ
      (infinitePlaceComplexificationOverfield
        (K := K) (L := L) v) :=
  (infinitePlaceEmbeddedExtensionField
      (K := K) (L := L) v ⊔
    infinitePlaceBaseFourthRootField
      (K := K) (L := L) v).restrictScalars ℚ

end ComplexConjugationOverextension

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_FullSUnitKummerExtension
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The full S-unit Kummer extension

Construction, finite generation, Galois structure, cardinality, and coordinates for the Kummer extension generated by all `S`-unit roots.
-/

open scoped NumberField Classical IsMulCommutative NNReal ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace KummerTheory

variable {K : Type*} [Field K]
    [numberFieldK : NumberField K]

/-- The Galois group of the full `S`-unit Kummer extension, with one
coordinate for every finite place in `S` and every infinite place.
This chosen coordinate form is consumed by the global norm-index
theorem. -/
noncomputable def fullSUnitKummerExtensionGaloisEquivPiZMod
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Gal(fullSUnitKummerExtension
        (K := K) (Omega := Omega) n S/K) ≃*
      (Fin (totalPlaceCard (K := K) S) →
        Multiplicative (ZMod (n : ℕ))) := by
  let r := SUnitGroup.logRank (K := K) S
  let eFin : Fin (r + 1) ≃
      Fin (totalPlaceCard (K := K) S) :=
    finCongr
      (totalPlaceCard_eq_sUnitLogRank_add_one
        (K := K) S).symm
  let eReindex :
      (Fin (r + 1) → Multiplicative (ZMod (n : ℕ))) ≃*
        (Fin (totalPlaceCard (K := K) S) →
          Multiplicative (ZMod (n : ℕ))) :=
    { toFun := fun f i => f (eFin.symm i)
      invFun := fun f i => f (eFin i)
      left_inv := by
        intro f
        funext i
        simp only [Equiv.symm_apply_apply]
      right_inv := by
        intro f
        funext i
        simp only [Equiv.apply_symm_apply]
      map_mul' := by
        intro f g
        rfl }
  exact
    (fullSUnitKummerExtensionGaloisCoordinates
      (K := K) (Omega := Omega) n hn hmu S).trans <|
      (multiplicativeZModProductEquivPiSucc
        (n : ℕ) r).trans eReindex

end KummerTheory
end
end


