-- Prove2me | Definitions.Def_OAIQ244Duke070
-- name    : OAIQ244Duke070
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T22:47:12.9704+00:00
-- url     : https://prove2.me/theorems/b3fa6dbe-18df-492d-aa8f-b26d42e8da14
-- title:
--   Definitions bundle OAIQ244Duke070 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 83 declarations of OpenAI's Lean: 16 definitions, 1 instance and 66 theorems. The definitions and types are `GlobalClassFieldTheory.ClassFieldAxiom.everywhereLocalFieldNormSubgroup`, `GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal`, `GlobalClassFieldTheory.ClassFieldAxiom.sUnitLocalUnitPowerMap`, `GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.fullConductor`, `GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards`, `GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq`, `GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient`, `LocalClassFieldTheory.abstractBaseFrobeniusLift`, `LocalClassFieldTheory.concreteNormResidueSymbolOfEmbedding`, `LocalClassFieldTheory.embeddedBaseNormClass`, `LocalClassFieldTheory.finiteExtensionDecompositionResidueFintype`, `LocalClassFieldTheory.finiteGaloisNormConjugationOfEmbeddings`, `LocalClassFieldTheory.finiteGaloisResidueEmbeddingOfEmbedding`, `LocalClassFieldTheory.intrinsicBaseContinuousEquivAmbientEmbeddedField`, `LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField`, `LocalClassFieldTheory.towerEmbeddedBaseNormClass`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_ClassFieldAxiom_CyclicIdeleClassNormIndex`, `GlobalClassFieldTheory_ClassFieldAxiom_HasseNormPrinciple`, `GlobalClassFieldTheory_ClassFieldAxiom_IdelePowerLocalUnitNormContainment`, `GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_RestrictionKernel`, `GlobalClassFieldTheory_ClassFieldAxiom_SUnitLocalPowerMap`, `GlobalClassFieldTheory_GlobalClassFields_ConductorInfinitePart`, `GlobalClassFieldTheory_GlobalClassFields_ConductorLattice`, `GlobalClassFieldTheory_GlobalClassFields_ConductorLocalComparison`, `GlobalClassFieldTheory_GlobalClassFields_ConductorRayClassMaximality`, `GlobalClassFieldTheory_GlobalClassFields_NormConductor`, `GlobalClassFieldTheory_Reciprocity_InfinitePlaceArtin`, `KummerTheory_Concrete_SUnitPreparation_EnlargedSUnitRestriction`, `LocalClassFieldTheory_Finite_LocalReciprocity_ConcreteReciprocityCanonical`, `LocalClassFieldTheory_Finite_LocalReciprocity_ConcreteReciprocityTransport`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientPrimeNormTransport`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_BaseComparison_IntrinsicBaseEquivalence`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_EmbeddedFrobeniusTransport`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldLocalData`, `LocalClassFieldTheory_Finite_LocalReciprocity_GeneralTowerNaturality`, `LocalClassFieldTheory_Finite_LocalReciprocity_IntermediateFieldNormResidueNaturality`, `LocalClassFieldTheory_Finite_LocalReciprocity_Main`, `LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedComparison`, `LocalField_DiscreteValuationField_FieldUnitPowerIndexFormulas`, `LocalField_DiscreteValuationField_PadicValuationComparison`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke062`, `OAIQ244Duke063`, `OAIQ244Duke064`, `OAIQ244Duke065` and `OAIQ244Duke066` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke074`, `OAIQ244Duke075`, `OAIQ244Duke076`, `OAIQ244Duke077`, `OAIQ244Duke078` and `OAIQ244Duke079`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
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
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Group.Cyclic
import Mathlib.Algebra.Order.Hom.Units
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
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
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
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
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.ProductFormula
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
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic
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
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
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
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Homeomorph.TransferInstance
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Mathlib.Topology.WithTopology
import Definitions.Def_OAIQ244Duke062
import Definitions.Def_OAIQ244Duke063
import Definitions.Def_OAIQ244Duke064
import Definitions.Def_OAIQ244Duke065
import Definitions.Def_OAIQ244Duke066

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_ConcreteReciprocityTransport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.realComplexNormQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory
open RamificationTheory KummerTheory CyclicCohomology

open LocalFieldTheory

open ClassFormation

/-!
# Finite local reciprocity: transport of abstract reciprocity to a field extension

This file contains the final comparison step in the proof of the local
reciprocity law.  Once the actual absolute-Galois datum, henselian valuation,
and class-field axiom have been constructed, the abstract reciprocity theorem is transported
through the concrete finite Galois realization in a separable closure and
through the actual field norm.

The coefficient module remains `(SeparableClosure K)ˣ`; this is essential in
imperfect positive characteristic.
-/

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Transport relative to an explicit embedding -/

/-- Norm-residue symbol obtained from an explicit separable-closure
realization. -/
def concreteNormResidueSymbolOfEmbedding
    (i : L →ₐ[K] SeparableClosure K)
    (D : DegreeData (G_p1 K)) (v : ValuationData D (A_p0 K))
    (hcf : SatisfiesClassFieldAxiom (A_p0 K)) :
    Kˣ →* Abelianization Gal(L / K) :=
  (concreteReciprocityEquivOfEmbedding K L i D v hcf).symm.toMonoidHom.comp
    (normClass K L)

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_ConcreteReciprocityCanonical
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.realComplexNormQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientMaximalIdealPowFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeEquiv_unramifiedFrobenius _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeHom_mk _root_.ClassFormation.DegreeData.finiteUnramifiedRestriction_frobenius _root_.ClassFormation.DegreeData.finiteUnramifiedRestriction_mk _root_.ClassFormation.DegreeData.maximalUnramifiedExtensionRestriction_mk _root_.ClassFormation.DegreeData.maximalUnramifiedFrobeniusPower_one _root_.ClassFormation.DegreeData.maximalUnramifiedRestriction_frobenius _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteAbelianSubextension.normSubgroupMap_val _root_.ClassFormation.FiniteGaloisSubextension.classFieldCandidate_field _root_.ClassFormation.FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe_field _root_.ClassFormation.ValuationData.maximalUnramifiedNormResidue_degree _root_.ClassFormation.mem_normFilterBasis_iff _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.abstractFixedFieldCosetToAlgHom_mk _root_.LocalClassFieldTheory.abstractFixedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.abstractRelativeFixedFieldUnitsEquivGaloisFixed_coe _root_.LocalClassFieldTheory.abstractRelativeUnitsEquiv_extensionUnitsEquiv _root_.LocalClassFieldTheory.baseFieldUnitsEquiv_val _root_.LocalClassFieldTheory.baseFixingCosetToAlgHom_mk _root_.LocalClassFieldTheory.intrinsicBaseEquivAmbientFixedField_apply_val _root_.LocalClassFieldTheory.localBaseValuation_baseFieldUnitsEquiv _root_.LocalClassFieldTheory.normQuotientMapOfRingEquiv_normClass _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory
open RamificationTheory CyclicCohomology KummerTheory

open LocalFieldTheory

open ClassFormation

/-!
# Finite local reciprocity: canonicity of local reciprocity

The construction of local reciprocity realizes a finite Galois extension in
a fixed separable closure.  This file proves that the transported reciprocity
isomorphism is independent of that realization.  Two embeddings are extended
to an automorphism of the separable closure, and
the abstract reciprocity naturality theorem supplies the required naturality.
-/

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Conjugating two realizations -/

/-- The finite quotient attached to an explicit finite Galois realization. -/
noncomputable instance
    finiteGaloisAbstractExtensionOfEmbedding_bundle_finite
    (i : L →ₐ[K] SeparableClosure K) :
    Finite ((B_p0 K).toSubgroup ⧸
      extensionSubgroup (B_p0 K)
        (finiteGaloisAbstractExtensionOfEmbedding K L i).field
        (finiteGaloisAbstractExtensionOfEmbedding K L i).below) :=
  (finiteGaloisAbstractExtensionOfEmbedding K L i).finite

/-! ## The two vertical maps of the abstract reciprocity naturality theorem -/

/-- Equality transport of both sides of the norm-residue symbol.  This is
the dependent-type form of replacing equal abstract fields in the abstract
reciprocity naturality theorem. -/
theorem normResidueSymbol_congr
    {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    (D : DegreeData Γ) (A : Rep ℤ Γ) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ]
    [TotallyDisconnectedSpace Γ]
    (K L K' L' : ClosedSubgroup Γ)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    [hNormal : (extensionSubgroup K L hLK).Normal]
    [hNormal' : (extensionSubgroup K' L' hL'K').Normal]
    [hFinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hFinite' : Finite (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K')]
    [hAbsolute : Finite ((baseField Γ).toSubgroup ⧸
      extensionSubgroup (baseField Γ) K (le_baseField K))]
    [hAbsolute' : Finite ((baseField Γ).toSubgroup ⧸
      extensionSubgroup (baseField Γ) K' (le_baseField K'))]
    (hK : K = K') (hL : L = L') :
    let E : FiniteGaloisSubextension K :=
      ⟨L, hLK, hNormal, hFinite⟩
    let E' : FiniteGaloisSubextension K' :=
      ⟨L', hL'K', hNormal', hFinite'⟩
    let KF : FiniteAbstractField Γ := ⟨K, hAbsolute⟩
    let K'F : FiniteAbstractField Γ := ⟨K', hAbsolute'⟩
    let q := MulEquiv.toAdditive
      ((extensionQuotientCongr hLK hL'K' hK hL).abelianizationCongr)
    let b := finiteNormQuotientCongr A
      (hFinite := hFinite) (hFinite' := hFinite')
      hLK hL'K' hK hL
    q.toAddMonoidHom.comp
        (D.normResidueSymbol A v hcf KF E).toAddMonoidHom =
      (D.normResidueSymbol A v hcf K'F E').toAddMonoidHom.comp
        b.toAddMonoidHom := by
  subst K'
  subst L'
  have hp : hLK = hL'K' := Subsingleton.elim _ _
  subst hL'K'
  have hn : hNormal = hNormal' := Subsingleton.elim _ _
  subst hNormal'
  have hf : hFinite = hFinite' := Subsingleton.elim _ _
  subst hFinite'
  have ha : hAbsolute = hAbsolute' := Subsingleton.elim _ _
  subst hAbsolute'
  simp [extensionQuotientCongr, finiteNormQuotientCongr]
  apply AddMonoidHom.ext
  intro x
  rfl

section EmbeddingConjugation

attribute [local instance] finiteGaloisEmbeddingConjugate_normal

theorem finiteGaloisConjugationOfEmbeddings_apply_factor
    (i j : L →ₐ[K] SeparableClosure K)
    (z : (finiteGaloisAbstractExtensionOfEmbedding K L i).extensionQuotient) :
    let hLK := fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L i)
    let s := (finiteGaloisEmbeddingConjugator K L i j)⁻¹
    let hB := finiteGaloisBase_conjugator K s
    let hH := finiteGaloisClosedFixingSubgroup_conjugator K L i j
    finiteGaloisConjugationOfEmbeddings K L i j z =
      extensionQuotientCongr
        (conjugateClosedSubgroup_mono hLK s)
        (fixingSubgroupLeBase K (SeparableClosure K)
          (finiteGaloisFieldRangeOfEmbedding K L j)) hB hH
        (finiteReciprocityNaturalityConjugation (B_p0 K)
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) hLK s z) := by
  dsimp only
  unfold finiteGaloisConjugationOfEmbeddings
  rfl

theorem finiteGaloisConjugationOfEmbeddings_abelianization_factor
    (i j : L →ₐ[K] SeparableClosure K)
    (z : Abelianization
      (finiteGaloisAbstractExtensionOfEmbedding K L i).extensionQuotient) :
    let hLK := fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L i)
    let s := (finiteGaloisEmbeddingConjugator K L i j)⁻¹
    let hB := finiteGaloisBase_conjugator K s
    let hH := finiteGaloisClosedFixingSubgroup_conjugator K L i j
    (finiteGaloisConjugationOfEmbeddings K L i j).abelianizationCongr z =
      (extensionQuotientCongr
        (conjugateClosedSubgroup_mono hLK s)
        (fixingSubgroupLeBase K (SeparableClosure K)
          (finiteGaloisFieldRangeOfEmbedding K L j)) hB hH).abelianizationCongr
        ((finiteReciprocityNaturalityConjugation (B_p0 K)
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
          hLK s).abelianizationCongr z) := by
  dsimp only
  let hLK : (finiteGaloisClosedFixingSubgroupOfEmbedding K L i).toSubgroup ≤
      (B_p0 K).toSubgroup :=
    fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L i)
  let hLjK : (finiteGaloisClosedFixingSubgroupOfEmbedding K L j).toSubgroup ≤
      (B_p0 K).toSubgroup :=
    fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L j)
  let s := (finiteGaloisEmbeddingConjugator K L i j)⁻¹
  let e := finiteReciprocityNaturalityConjugation (B_p0 K)
    (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) hLK s
  let c := extensionQuotientCongr
    (K := conjugateClosedSubgroup (B_p0 K) s)
    (L := conjugateClosedSubgroup
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) s)
    (K' := B_p0 K) (L' := finiteGaloisClosedFixingSubgroupOfEmbedding K L j)
    (conjugateClosedSubgroup_mono hLK s) hLjK
    (finiteGaloisBase_conjugator K s)
    (finiteGaloisClosedFixingSubgroup_conjugator K L i j)
  refine QuotientGroup.induction_on z ?_
  intro x
  change
    (finiteGaloisConjugationOfEmbeddings K L i j).abelianizationCongr
        (Abelianization.of x) =
      c.abelianizationCongr (e.abelianizationCongr (Abelianization.of x))
  exact (abelianizationCongr_of
      (finiteGaloisConjugationOfEmbeddings K L i j) x).trans
    ((congrArg Abelianization.of
      (finiteGaloisConjugationOfEmbeddings_apply_factor K L i j x)).trans
      ((abelianizationCongr_of c (e x)).symm.trans
        (congrArg c.abelianizationCongr (abelianizationCongr_of e x).symm)))

section EmbeddingNormConjugation

attribute [local instance] finiteGaloisEmbeddingNormAddZeroClass

/-- Conjugation on the finite norm quotients, rewritten so that both its
source and target use the fixed concrete base subgroup. -/
def finiteGaloisNormConjugationOfEmbeddings
    (i j : L →ₐ[K] SeparableClosure K) :
    FiniteNormQuotient (AG K) (B_p0 K)
        (finiteGaloisAbstractExtensionOfEmbedding K L i).field
        (finiteGaloisAbstractExtensionOfEmbedding K L i).below →+
      FiniteNormQuotient (AG K) (B_p0 K)
        (finiteGaloisAbstractExtensionOfEmbedding K L j).field
        (finiteGaloisAbstractExtensionOfEmbedding K L j).below := by
  let hLK : (finiteGaloisClosedFixingSubgroupOfEmbedding K L i).toSubgroup ≤
      (B_p0 K).toSubgroup :=
    fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L i)
  let s := (finiteGaloisEmbeddingConjugator K L i j)⁻¹
  have hB := finiteGaloisBase_conjugator K
    (finiteGaloisEmbeddingConjugator K L i j)⁻¹
  have hH := finiteGaloisClosedFixingSubgroup_conjugator K L i j
  let e := finiteReciprocityNaturalityConjugationNormMap (AG K) (B_p0 K)
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
      hLK s
  letI := finite_conjugateExtension (B_p0 K)
    (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) hLK s
  let c := finiteNormQuotientCongr (AG K)
    (K := conjugateClosedSubgroup (B_p0 K) s)
    (L := conjugateClosedSubgroup
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) s)
    (K' := B_p0 K) (L' := finiteGaloisClosedFixingSubgroupOfEmbedding K L j)
    (hFinite := finite_conjugateExtension (B_p0 K)
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) hLK s)
    (hFinite' := finiteGaloisExtensionQuotientOfEmbedding_finite K L j)
    (conjugateClosedSubgroup_mono hLK s)
    (fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L j)) hB hH
  have hi :
      (finiteGaloisAbstractExtensionOfEmbedding K L i).field =
        finiteGaloisClosedFixingSubgroupOfEmbedding K L i := rfl
  have hj :
      finiteGaloisClosedFixingSubgroupOfEmbedding K L j =
        (finiteGaloisAbstractExtensionOfEmbedding K L j).field := rfl
  let pre := finiteNormQuotientCongr (AG K)
    (hFinite :=
      finiteGaloisAbstractExtensionOfEmbedding_bundle_finite K L i)
    (hFinite' := finiteGaloisExtensionQuotientOfEmbedding_finite K L i)
    (finiteGaloisAbstractExtensionOfEmbedding K L i).below hLK rfl hi
  let post := finiteNormQuotientCongr (AG K)
    (hFinite := finiteGaloisExtensionQuotientOfEmbedding_finite K L j)
    (hFinite' :=
      finiteGaloisAbstractExtensionOfEmbedding_bundle_finite K L j)
    (fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L j))
    (finiteGaloisAbstractExtensionOfEmbedding K L j).below rfl hj
  exact post.toAddMonoidHom.comp
    (c.toAddMonoidHom.comp (e.comp pre.toAddMonoidHom))

end EmbeddingNormConjugation

theorem finiteGaloisNormConjugationOfEmbeddings_apply_factor
    (i j : L →ₐ[K] SeparableClosure K)
    (a : FiniteNormQuotient (AG K) (B_p0 K)
      (finiteGaloisAbstractExtensionOfEmbedding K L i).field
      (finiteGaloisAbstractExtensionOfEmbedding K L i).below) :
    let hLK := fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L i)
    let s := (finiteGaloisEmbeddingConjugator K L i j)⁻¹
    let hB := finiteGaloisBase_conjugator K s
    let hH := finiteGaloisClosedFixingSubgroup_conjugator K L i j
    finiteGaloisNormConjugationOfEmbeddings K L i j a =
      finiteNormQuotientCongr (AG K)
        (hFinite := finite_conjugateExtension (B_p0 K)
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) hLK s)
        (hFinite' := finiteGaloisExtensionQuotientOfEmbedding_finite K L j)
        (conjugateClosedSubgroup_mono hLK s)
        (fixingSubgroupLeBase K (SeparableClosure K)
          (finiteGaloisFieldRangeOfEmbedding K L j)) hB hH
        (finiteReciprocityNaturalityConjugationNormMap (AG K) (B_p0 K)
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) hLK s a) := by
  dsimp only
  unfold finiteGaloisNormConjugationOfEmbeddings
  rfl

/-! ## Concrete comparison on representatives -/

/-- On a base unit, conjugation of finite norm classes is the identity after
the target base subgroup is identified with the original base subgroup. -/
@[simp]
theorem finiteGaloisNormConjugationOfEmbeddings_finiteNormClass_baseUnit
    (i j : L →ₐ[K] SeparableClosure K) (x : Kˣ) :
    finiteGaloisNormConjugationOfEmbeddings K L i j
        (finiteNormClass (AG K) (B_p0 K)
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
          (fixingSubgroupLeBase K (SeparableClosure K)
            (finiteGaloisFieldRangeOfEmbedding K L i))
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
            (Additive.ofMul x))) =
      finiteNormClass (AG K) (B_p0 K)
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L j)
        (fixingSubgroupLeBase K (SeparableClosure K)
          (finiteGaloisFieldRangeOfEmbedding K L j))
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
          (Additive.ofMul x)) := by
  let hLK := fixingSubgroupLeBase K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)
  let s := (finiteGaloisEmbeddingConjugator K L i j)⁻¹
  have hB := finiteGaloisBase_conjugator K s
  have hH : conjugateClosedSubgroup
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) s =
      finiteGaloisClosedFixingSubgroupOfEmbedding K L j :=
    finiteGaloisClosedFixingSubgroup_conjugator K L i j
  let hConjFinite := finite_conjugateExtension (B_p0 K)
    (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) hLK s
  let a := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
    (Additive.ofMul x)
  have ha :
      AddEquiv.addSubgroupCongr
          (congrArg (ambientFixedAddSubgroup (AG K)) hB)
          (conjugateFixedElement (AG K) (B_p0 K) s a) =
      baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
        (Additive.ofMul x) := by
    apply Subtype.ext
    rw [AddEquiv.addSubgroupCongr_apply,
      conjugateFixedElement_coe]
    apply Additive.ext
    apply Units.ext
    change finiteGaloisEmbeddingConjugator K L i j
        (algebraMap K (SeparableClosure K) (x : K)) =
      algebraMap K (SeparableClosure K) (x : K)
    exact (finiteGaloisEmbeddingConjugator K L i j).commutes (x : K)
  let hLjK : (finiteGaloisClosedFixingSubgroupOfEmbedding K L j).toSubgroup ≤
      (B_p0 K).toSubgroup :=
    fixingSubgroupLeBase K (SeparableClosure K)
      (finiteGaloisFieldRangeOfEmbedding K L j)
  let c := finiteNormQuotientCongr (AG K)
    (K := conjugateClosedSubgroup (B_p0 K) s)
    (L := conjugateClosedSubgroup
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) s)
    (K' := B_p0 K) (L' := finiteGaloisClosedFixingSubgroupOfEmbedding K L j)
    (hFinite := hConjFinite)
    (hFinite' := finiteGaloisExtensionQuotientOfEmbedding_finite K L j)
    (conjugateClosedSubgroup_mono hLK s) hLjK hB hH
  have hfactor := finiteGaloisNormConjugationOfEmbeddings_apply_factor K L i j
    (finiteNormClass (AG K) (B_p0 K)
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) hLK a)
  have hnorm := finiteReciprocityNaturalityConjugationNormMap_finiteNormClass
    (AG K) (B_p0 K) (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) hLK s a
  have hclass := finiteNormQuotientCongr_finiteNormClass (AG K)
    (K := conjugateClosedSubgroup (B_p0 K) s)
    (L := conjugateClosedSubgroup
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) s)
    (K' := B_p0 K) (L' := finiteGaloisClosedFixingSubgroupOfEmbedding K L j)
    (hFinite := hConjFinite)
    (hFinite' := finiteGaloisExtensionQuotientOfEmbedding_finite K L j)
    (conjugateClosedSubgroup_mono hLK s) hLjK hB hH
    (conjugateFixedElement (AG K) (B_p0 K) s a)
  exact hfactor.trans ((congrArg c hnorm).trans
    (hclass.trans (congrArg (finiteNormClass (AG K) (B_p0 K)
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L j) hLjK) ha)))

/-! ## The two outer comparison squares -/

/-- The concrete quotient identification is unchanged by conjugating the
chosen realization. -/
theorem finiteGaloisAbstractQuotientEquivGaloisGroup_conjugation
    (i j : L →ₐ[K] SeparableClosure K)
    (z : Abelianization
      (finiteGaloisAbstractExtensionOfEmbedding K L i).extensionQuotient) :
    (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L j).abelianizationCongr
        ((finiteGaloisConjugationOfEmbeddings K L i j).abelianizationCongr z) =
      (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i).abelianizationCongr z := by
  refine QuotientGroup.induction_on z ?_
  intro q
  have hraw :
      finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L j
          (finiteGaloisConjugationOfEmbeddings K L i j q) =
        finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i q := by
    refine QuotientGroup.induction_on q ?_
    intro τ
    rw [finiteGaloisConjugationOfEmbeddings_mk]
    apply AlgEquiv.ext
    intro x
    apply j.injective
    let σ := finiteGaloisEmbeddingConjugator K L i j
    calc
      j ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L j
          (QuotientGroup.mk
            (finiteGaloisConjugateBaseElement K L i j τ))) x) =
          (finiteGaloisConjugateBaseElement K L i j τ).1 (j x) :=
        finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
          K L j (finiteGaloisConjugateBaseElement K L i j τ) x
      _ = σ (τ.1 (i x)) := by
        have hinv : σ⁻¹ (j x) = i x := by
          apply σ.injective
          simp [σ]
        simp [finiteGaloisConjugateBaseElement, σ, hinv]
      _ = σ (i ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
          (QuotientGroup.mk τ)) x)) := by
        exact congrArg σ
          (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
            K L i τ x).symm
      _ = j ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
          (QuotientGroup.mk τ)) x) :=
        finiteGaloisEmbeddingConjugator_apply K L i j _
  calc
    (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L j).abelianizationCongr
        ((finiteGaloisConjugationOfEmbeddings K L i j).abelianizationCongr
          (Abelianization.of q)) =
      (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L j).abelianizationCongr
        (Abelianization.of
          (finiteGaloisConjugationOfEmbeddings K L i j q)) :=
      congrArg
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L j).abelianizationCongr
        (abelianizationCongr_of
          (finiteGaloisConjugationOfEmbeddings K L i j) q)
    _ = Abelianization.of
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L j
          (finiteGaloisConjugationOfEmbeddings K L i j q)) :=
      abelianizationCongr_of
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L j) _
    _ = Abelianization.of
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i q) :=
      congrArg Abelianization.of hraw
    _ = (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i).abelianizationCongr
        (Abelianization.of q) :=
      (abelianizationCongr_of
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i) q).symm

/-- Additive form of the preceding source comparison. -/
theorem finiteGaloisAbstractQuotientEquivGaloisGroup_conjugation_additive
    (i j : L →ₐ[K] SeparableClosure K)
    (z : Additive (Abelianization
      (finiteGaloisAbstractExtensionOfEmbedding K L i).extensionQuotient)) :
    MulEquiv.toAdditive
        ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L j).abelianizationCongr)
        (MulEquiv.toAdditive
          ((finiteGaloisConjugationOfEmbeddings K L i j).abelianizationCongr) z) =
      MulEquiv.toAdditive
        ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i).abelianizationCongr) z := by
  apply Additive.toMul.injective
  exact finiteGaloisAbstractQuotientEquivGaloisGroup_conjugation
    K L i j z.toMul

/-- The concrete norm-quotient identification is unchanged by conjugating
the chosen realization. -/
theorem finiteNormQuotientEquivEmbeddedNormQuotient_conjugation
    (i j : L →ₐ[K] SeparableClosure K)
    (a : FiniteNormQuotient (AG K) (B_p0 K)
      (finiteGaloisAbstractExtensionOfEmbedding K L i).field
      (finiteGaloisAbstractExtensionOfEmbedding K L i).below) :
    finiteNormQuotientEquivEmbeddedNormQuotient
        K (SeparableClosure K) L j
        (finiteGaloisNormConjugationOfEmbeddings K L i j a) =
      finiteNormQuotientEquivEmbeddedNormQuotient
        K (SeparableClosure K) L i a := by
  refine FiniteNormQuotient.induction_on (AG K) (B_p0 K)
    (finiteGaloisAbstractExtensionOfEmbedding K L i).field
    (finiteGaloisAbstractExtensionOfEmbedding K L i).below a ?_
  intro a₀
  let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
  let x : Additive Kˣ := e.symm a₀
  have hx : e x = a₀ := e.apply_symm_apply a₀
  rw [← hx]
  cases x with
  | ofMul x =>
      change finiteNormQuotientEquivEmbeddedNormQuotient
          K (SeparableClosure K) L j
          (finiteGaloisNormConjugationOfEmbeddings K L i j
            (finiteNormClass (AG K) (B_p0 K)
              (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
              (fixingSubgroupLeBase K (SeparableClosure K)
                (finiteGaloisFieldRangeOfEmbedding K L i))
              (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
                (Additive.ofMul x)))) =
        finiteNormQuotientEquivEmbeddedNormQuotient
          K (SeparableClosure K) L i
          (finiteNormClass (AG K) (B_p0 K)
            (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
            (fixingSubgroupLeBase K (SeparableClosure K)
              (finiteGaloisFieldRangeOfEmbedding K L i))
            (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
              (Additive.ofMul x)))
      rw [finiteGaloisNormConjugationOfEmbeddings_finiteNormClass_baseUnit,
        finiteNormQuotientEquivEmbeddedNormQuotient_finiteNormClass_baseUnit,
        finiteNormQuotientEquivEmbeddedNormQuotient_finiteNormClass_baseUnit]

/-! ## The abstract reciprocity naturality theorem and embedding independence -/

/-- The additive transported reciprocity equivalence is independent of the
embedding into the fixed separable closure. -/
theorem concreteReciprocityAddEquivOfEmbedding_eq
    (i j : L →ₐ[K] SeparableClosure K)
    (D : DegreeData (G_p0 K)) (v : ValuationData D (AG K))
    (hcf : SatisfiesClassFieldAxiom (AG K)) :
    concreteReciprocityAddEquivOfEmbedding K L i D v hcf =
      concreteReciprocityAddEquivOfEmbedding K L j D v hcf := by
  let Ei := finiteGaloisAbstractExtensionOfEmbedding K L i
  let Ej := finiteGaloisAbstractExtensionOfEmbedding K L j
  let hBAbsolute : Finite ((baseField (G_p0 K)).toSubgroup ⧸
      extensionSubgroup (baseField (G_p0 K)) (B_p0 K) (le_baseField (B_p0 K))) := by
    exact (intrinsicFiniteAbstractBase K).finite
  let hEiNormal :
      (extensionSubgroup
        (intrinsicFiniteAbstractBase K).field Ei.field Ei.below).Normal :=
    Ei.normal
  let hEjNormal :
      (extensionSubgroup
        (intrinsicFiniteAbstractBase K).field Ej.field Ej.below).Normal :=
    Ej.normal
  let q := MulEquiv.toAdditive
    ((finiteGaloisConjugationOfEmbeddings K L i j).abelianizationCongr)
  let b := finiteGaloisNormConjugationOfEmbeddings K L i j
  let ri := D.abstractReciprocityEquiv
    (AG K) v hcf (intrinsicFiniteAbstractBase K) Ei
  let rj := D.abstractReciprocityEquiv
    (AG K) v hcf (intrinsicFiniteAbstractBase K) Ej
  let ni := finiteNormQuotientEquivEmbeddedNormQuotient
    K (SeparableClosure K) L i
  let nj := finiteNormQuotientEquivEmbeddedNormQuotient
    K (SeparableClosure K) L j
  let si := MulEquiv.toAdditive
    ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i).abelianizationCongr)
  let sj := MulEquiv.toAdditive
    ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L j).abelianizationCongr)
  have hsource (z : Additive (Abelianization Ei.extensionQuotient)) :
      sj (q z) = si z := by
    exact finiteGaloisAbstractQuotientEquivGaloisGroup_conjugation_additive
      K L i j z
  have hnorm (a : FiniteNormQuotient (AG K) (B_p0 K) Ei.field Ei.below) :
      nj (b a) = ni a := by
    exact finiteNormQuotientEquivEmbeddedNormQuotient_conjugation
      K L i j a
  have hinv :
      q.toAddMonoidHom.comp
          (D.normResidueSymbol (AG K) v hcf
            (intrinsicFiniteAbstractBase K) Ei).toAddMonoidHom =
        (D.normResidueSymbol (AG K) v hcf
          (intrinsicFiniteAbstractBase K) Ej).toAddMonoidHom.comp b := by
    let σ := finiteGaloisEmbeddingConjugator K L i j
    let Hi := finiteGaloisClosedFixingSubgroupOfEmbedding K L i
    let Hj := finiteGaloisClosedFixingSubgroupOfEmbedding K L j
    let hLK : Hi.toSubgroup ≤ (B_p0 K).toSubgroup :=
      fixingSubgroupLeBase K (SeparableClosure K)
        (finiteGaloisFieldRangeOfEmbedding K L i)
    let hLjK : Hj.toSubgroup ≤ (B_p0 K).toSubgroup :=
      fixingSubgroupLeBase K (SeparableClosure K)
        (finiteGaloisFieldRangeOfEmbedding K L j)
    let s := σ⁻¹
    have hB := finiteGaloisBase_conjugator K σ⁻¹
    have hH := finiteGaloisClosedFixingSubgroup_conjugator K L i j
    let hConj := conjugateClosedSubgroup_mono hLK s
    let hHiNormal :
        (extensionSubgroup
          (intrinsicFiniteAbstractBase K).field Hi hLK).Normal := by
      exact (finiteGaloisAbstractExtensionOfEmbedding K L i).normal
    let hHiFinite : Finite
        ((intrinsicFiniteAbstractBase K).field.toSubgroup ⧸
          extensionSubgroup (intrinsicFiniteAbstractBase K).field Hi hLK) := by
      exact finiteGaloisExtensionQuotientOfEmbedding_finite K L i
    let hConjNormal :
        (extensionSubgroup ((intrinsicFiniteAbstractBase K).conjugate s).field
          (conjugateClosedSubgroup Hi s) hConj).Normal := by
      exact finiteGaloisEmbeddingConjugate_normal K L i s
    let hConjFinite := finite_conjugateExtension (B_p0 K) Hi hLK s
    let hConjAbsolute : Finite ((baseField (G_p0 K)).toSubgroup ⧸
        extensionSubgroup (baseField (G_p0 K))
          (conjugateClosedSubgroup (B_p0 K) s)
          (le_baseField (conjugateClosedSubgroup (B_p0 K) s))) :=
      Finite.of_equiv
        ((baseField (G_p0 K)).toSubgroup ⧸
          extensionSubgroup (baseField (G_p0 K)) (B_p0 K) (le_baseField (B_p0 K)))
        (by
          simpa [baseField] using
            (absoluteConjugateCosetEquiv (B_p0 K) s).symm)
    let q₀ := MonoidHom.toAdditive
      (normResidueNaturalityAbelianizedConjugation (B_p0 K) Hi hLK s).toMonoidHom
    let b₀ := finiteReciprocityNaturalityConjugationNormMap (AG K) (B_p0 K) Hi hLK s
    let qt := MulEquiv.toAdditive
      ((extensionQuotientCongr hConj hLjK hB hH).abelianizationCongr)
    let bt := finiteNormQuotientCongr (AG K)
      (hFinite := hConjFinite)
      (hFinite' := finiteGaloisExtensionQuotientOfEmbedding_finite K L j)
      hConj hLjK hB hH
    have hraw := D.normResidueNaturality_conjugation (AG K) v hcf
      (intrinsicFiniteAbstractBase K) Hi hLK s
    have htransport := normResidueSymbol_congr D (AG K) v hcf
      (conjugateClosedSubgroup (B_p0 K) s)
      (conjugateClosedSubgroup Hi s) (B_p0 K) Hj hConj hLjK hB hH
    apply AddMonoidHom.ext
    intro a
    have hrawa := DFunLike.congr_fun hraw a
    have htransporta := DFunLike.congr_fun htransport (b₀ a)
    have hcombined :
        qt (q₀ (D.normResidueSymbol (AG K) v hcf
          (intrinsicFiniteAbstractBase K) Ei a)) =
          D.normResidueSymbol (AG K) v hcf
            (intrinsicFiniteAbstractBase K) Ej (bt (b₀ a)) := by
      exact (congrArg qt hrawa).trans htransporta
    have hqfactor :
        q (D.normResidueSymbol (AG K) v hcf
          (intrinsicFiniteAbstractBase K) Ei a) =
          qt (q₀ (D.normResidueSymbol (AG K) v hcf
            (intrinsicFiniteAbstractBase K) Ei a)) := by
      change Additive.ofMul
          ((finiteGaloisConjugationOfEmbeddings K L i j).abelianizationCongr
            (D.normResidueSymbol (AG K) v hcf
              (intrinsicFiniteAbstractBase K) Ei a).toMul) =
        Additive.ofMul
          ((extensionQuotientCongr hConj hLjK hB hH).abelianizationCongr
            ((finiteReciprocityNaturalityConjugation (B_p0 K) Hi hLK s).abelianizationCongr
              (D.normResidueSymbol (AG K) v hcf
                (intrinsicFiniteAbstractBase K) Ei a).toMul))
      exact congrArg Additive.ofMul
        (finiteGaloisConjugationOfEmbeddings_abelianization_factor
          K L i j
          (D.normResidueSymbol (AG K) v hcf
            (intrinsicFiniteAbstractBase K) Ei a).toMul)
    have hbfactor : b a = bt (b₀ a) := by
      exact finiteGaloisNormConjugationOfEmbeddings_apply_factor K L i j a
    change q (D.normResidueSymbol (AG K) v hcf
      (intrinsicFiniteAbstractBase K) Ei a) =
      D.normResidueSymbol (AG K) v hcf
        (intrinsicFiniteAbstractBase K) Ej (b a)
    exact hqfactor.trans (hcombined.trans
      (congrArg (D.normResidueSymbol (AG K) v hcf
        (intrinsicFiniteAbstractBase K) Ej) hbfactor.symm))
  have hforward (z : Additive (Abelianization Ei.extensionQuotient)) :
      b (ri z) = rj (q z) := by
    have hz := DFunLike.congr_fun hinv (ri z)
    change q (ri.symm (ri z)) = rj.symm (b (ri z)) at hz
    calc
      b (ri z) = rj (rj.symm (b (ri z))) :=
        (rj.apply_symm_apply (b (ri z))).symm
      _ = rj (q (ri.symm (ri z))) := congrArg rj hz.symm
      _ = rj (q z) := by rw [ri.symm_apply_apply]
  apply AddEquiv.ext
  intro x
  change ni (ri (si.symm x)) = nj (rj (sj.symm x))
  exact reciprocityTransport_pointwise q b ri.toEquiv rj.toEquiv ni nj
    si.toEquiv sj.toEquiv hsource hnorm hforward x

end EmbeddingConjugation

/-- Public multiplicative form of embedding independence. -/
theorem concreteReciprocityEquivOfEmbedding_eq
    (i j : L →ₐ[K] SeparableClosure K)
    (D : DegreeData (G_p0 K)) (v : ValuationData D (AG K))
    (hcf : SatisfiesClassFieldAxiom (AG K)) :
    concreteReciprocityEquivOfEmbedding K L i D v hcf =
      concreteReciprocityEquivOfEmbedding K L j D v hcf := by
  apply MulEquiv.ext
  intro x
  have h := DFunLike.congr_fun
    (concreteReciprocityAddEquivOfEmbedding_eq K L i j D v hcf)
    (Additive.ofMul x)
  exact congrArg Additive.toMul h

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_Main
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.realComplexNormQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.normQuotientMapOfRingEquiv_normClass _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

namespace LocalClassFieldTheory

open LocalFieldTheory

/-!
# Finite local reciprocity: the local reciprocity law

The residue Frobenius datum, the normalized henselian valuation, and the
class-field axiom constructed over the fixed separable closure are inserted
into the abstract reciprocity theorem.  The resulting isomorphism is independent of the
embedding used to realize the finite Galois extension in that closure.
-/

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsGalois K L]

/-- The isomorphism in the finite local reciprocity construction is independent of the embedding used to
realize `L/K` inside the fixed separable closure. -/
theorem abelianizationEquivNormQuotient_eq_of_embedding
    (i : L →ₐ[K] SeparableClosure K) :
    abelianizationEquivNormQuotient K L =
      concreteReciprocityEquivOfEmbedding K L i
        (localResidueDatum K)
        (localHenselianValuation K)
        (separableClosureUnits_isClassFormation K) := by
  simpa [abelianizationEquivNormQuotient, concreteReciprocityEquiv] using
    (concreteReciprocityEquivOfEmbedding_eq K L
      (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L) i
      (localResidueDatum K)
      (localHenselianValuation K)
      (separableClosureUnits_isClassFormation K))

end
end LocalClassFieldTheory
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_FieldUnitPowerIndexFormulas
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.representedQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FiniteResidueAbstractExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.DegreeData.FiniteTower.baseQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.topQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.FiniteAbstractField.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractFieldExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instCommGroupSubtypeUnitsMemSubgroup _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable _root_.LocalClassFieldTheory.finiteGaloisExtensionQuotientOfEmbedding_finite _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteGaloisAbstractExtensionOfEmbedding_bundle_finite _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Power indices in local-field unit groups

The index formulas below use the actual principal-unit structures from
the field-unit structure theorem.  Both the natural-cardinality form and the literal rational
form involving the normalized local absolute value are recorded.
-/

noncomputable section

universe u

namespace LocalFieldTheory.DiscreteValuationField
namespace LocalField

variable {K : Type u} [Field K]

/-- The local-field power-index formula in mixed characteristic, in natural-cardinality form for
the valuation-ring unit group.  Its finite kernel is written as the canonical
field root group `μ_n(K)`. -/
theorem mixed_unitIndex
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    {n : ℕ} [NeZero n]
    [Finite
      ((CompleteDVF.higherPrincipalUnitGroup
        (ofWithZeroValuation v).toCompleteDVF) 1 ⧸
        (powMonoidHom n : ((CompleteDVF.higherPrincipalUnitGroup
            (ofWithZeroValuation v).toCompleteDVF) 1) →* ((CompleteDVF.higherPrincipalUnitGroup
            (ofWithZeroValuation v).toCompleteDVF) 1)).range)] :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    letI : MixedWithZeroValuationContext v :=
      mixedWithZeroValuationContext v
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    let d := Module.finrank ℚ_[F.residueCharacteristic] K
    Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) =
      Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) *
        F.residueCharacteristic ^
          (d * padicValNat F.residueCharacteristic n) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let d := Module.finrank ℚ_[F.residueCharacteristic] K
  let hex :=
    WithZeroValuation.exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective
      v hv
  let π := Classical.choose hex
  have hπval : v (π : K) = WithZero.exp (-1 : ℤ) :=
    Classical.choose_spec hex
  have hπ : v.IsUniformizer (π : K) :=
    WithZeroValuation.isUniformizer_of_valuation_eq_exp_neg_one
      v (π : K) hπval
  obtain ⟨a, e⟩ :=
    chosenMixed_firstPrincipalUnitStructure_ofWithZeroValuation
      v hv
  exact
    card_units_nthPowerQuotient_of_mixedPrincipalUnitStructure_fieldKernel
      (p := F.residueCharacteristic) (F := F.toCompleteDVF) hπ
      (ZMod (F.residueCharacteristic ^ a)) d e.symm.toMulEquiv

/-- In mixed characteristic, an exponent prime to the residue characteristic
has no principal-unit defect.  Thus the valuation-ring unit power index is
the cardinality of the canonical field root group `μ_n(K)`.  Finiteness of
the principal-unit quotient is obtained internally from the mixed
principal-unit structure. -/
theorem mixed_unitIndex_of_coprime
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v)
    {n : ℕ} [NeZero n]
    [Fact
      (Nat.Coprime n
        (ofWithZeroValuation v).residueCharacteristic)] :
    let F : LocalField.{u, 0} K := ofWithZeroValuation v
    Nat.card (F.valuationSubringˣ ⧸
        (powMonoidHom n : F.valuationSubringˣ →* F.valuationSubringˣ).range) =
      Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) := by
  let F : LocalField.{u, 0} K := ofWithZeroValuation v
  let : MixedWithZeroValuationContext v :=
    mixedWithZeroValuationContext v
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let d := Module.finrank ℚ_[F.residueCharacteristic] K
  obtain ⟨a, e⟩ :=
    chosenMixed_firstPrincipalUnitStructure_ofWithZeroValuation
      v hv
  let U :=
    CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1
  let A :=
    ZMod (F.residueCharacteristic ^ a) ×
      (Fin d → ℤ_[F.residueCharacteristic])
  let : NeZero (F.residueCharacteristic ^ a) :=
    ⟨pow_ne_zero _ F.residueCharacteristic_prime.ne_zero⟩
  let : Finite
      (A ⧸ LocalFieldTheory.nsmulAddSubgroup A n) := by
    infer_instance
  let : Finite
      (U ⧸ (powMonoidHom n : U →* U).range) :=
    LocalFieldTheory.finite_nthPowerQuotient_of_mulEquiv
      U (Multiplicative A) n e.symm.toMulEquiv
  have hpnd : ¬ F.residueCharacteristic ∣ n :=
    F.residueCharacteristic_prime.coprime_iff_not_dvd.mp
      (Fact.out : Nat.Coprime n F.residueCharacteristic).symm
  have hpadic :
      padicValNat F.residueCharacteristic n = 0 :=
    padicValNat.eq_zero_of_not_dvd hpnd
  simpa only [F, hpadic, Nat.mul_zero, pow_zero, Nat.mul_one] using
    (mixed_unitIndex v hv (n := n))

end LocalField
end LocalFieldTheory.DiscreteValuationField
end
end

section
-- module Solutions.OAIQ244_DUKE.KummerTheory_Concrete_SUnitPreparation_EnlargedSUnitRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option synthInstance.maxHeartbeats 400000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Restriction from an enlarged S-unit Kummer extension

The concrete embedding and Galois restriction map, its fixing subgroup, and the cyclic fixed fields attached to kernel elements.
-/

open scoped NumberField Classical IsMulCommutative NNReal ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace KummerTheory

variable {K : Type*} [Field K]
    [numberFieldK : NumberField K]

/-- The kernel of restriction is precisely the subgroup fixing the
concrete embedded copy of `E` in `N`. -/
theorem enlargedSUnitKummerRestrictionHom_ker_eq_fixingSubgroup
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (enlargedSUnitKummerRestrictionHom
      (K := K) (Omega := Omega) E n hmu hexponent S).ker =
      (enlargedSUnitKummerEmbeddedExtension
        (K := K) (Omega := Omega) E n hmu
        hexponent S).fixingSubgroup := by
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  let _ : Algebra E N :=
    enlargedSUnitKummerAlgebra
      (K := K) (Omega := Omega) E n hmu hexponent S
  let _ : IsScalarTower K E N := by infer_instance
  let M : IntermediateField K N :=
    (IsScalarTower.toAlgHom K E N).fieldRange
  change
    (AlgEquiv.restrictNormalHom
      (F := K) (K₁ := N) (E := E)).ker =
        M.fixingSubgroup
  ext sigma
  rw [MonoidHom.mem_ker,
    IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hsigma y hy
    rcases hy with ⟨x, rfl⟩
    have hx :
        sigma.restrictNormal E x = x := by
      change
        (AlgEquiv.restrictNormalHom
          (F := K) (K₁ := N) (E := E) sigma) x =
            (1 : Gal(E/K)) x
      rw [hsigma]
    calc
      sigma (algebraMap E N x) =
          algebraMap E N (sigma.restrictNormal E x) :=
        (AlgEquiv.restrictNormal_commutes sigma E x).symm
      _ = algebraMap E N x :=
        congrArg (algebraMap E N) hx
  · intro hsigma
    apply AlgEquiv.ext
    intro x
    apply (algebraMap E N).injective
    change
      algebraMap E N (sigma.restrictNormal E x) =
        algebraMap E N x
    exact
      (AlgEquiv.restrictNormal_commutes sigma E x).trans
        (hsigma (algebraMap E N x) ⟨x, rfl⟩)

/-- The field fixed by the concrete restriction kernel is exactly the
embedded copy of `E`. -/
theorem fixedField_enlargedSUnitKummerRestrictionHom_ker
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IntermediateField.fixedField
        (enlargedSUnitKummerRestrictionHom
          (K := K) (Omega := Omega) E n hmu
          hexponent S).ker =
      enlargedSUnitKummerEmbeddedExtension
        (K := K) (Omega := Omega) E n hmu
        hexponent S := by
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  let : FiniteDimensional K N :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n hnK hmu S'
  rw [
    enlargedSUnitKummerRestrictionHom_ker_eq_fixingSubgroup
      (K := K) (Omega := Omega) E n hmu
      hexponent S]
  exact
    IsGalois.fixedField_fixingSubgroup
      (enlargedSUnitKummerEmbeddedExtension
        (K := K) (Omega := Omega) E n hmu
        hexponent S)

/-- The embedded extension `E` lies in every cyclic fixed field attached
to an element of `Gal(N/E)`. -/
theorem enlargedSUnitKummerEmbeddedExtension_le_cyclicFixedField
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (sigma :
      (enlargedSUnitKummerRestrictionHom
        (K := K) (Omega := Omega) E n hmu
        hexponent S).ker) :
    enlargedSUnitKummerEmbeddedExtension
        (K := K) (Omega := Omega) E n hmu
        hexponent S ≤
      enlargedSUnitKummerCyclicFixedField
        (K := K) (Omega := Omega) E n hmu
        hexponent S sigma := by
  apply (IntermediateField.le_iff_le _ _).2
  rw [
    ← enlargedSUnitKummerRestrictionHom_ker_eq_fixingSubgroup
      (K := K) (Omega := Omega) E n hmu
      hexponent S]
  exact Subgroup.zpowers_le.mpr sigma.2

end KummerTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_SUnitKummerPrimeSelection_RestrictionKernel
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Restriction kernels of S-unit Kummer extensions

This file specializes the chosen restriction-kernel coordinates of an
enlarged S-unit Kummer extension to coordinate generators, their required
number, and their cyclic fixed fields.
-/

open scoped NumberField Classical IsMulCommutative
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

section GeneralKummer

variable {K : Type*} [Field K]
    [NumberField K]

/-- The standard coordinate generators span the actual restriction kernel
`Gal(N / E)`. -/
theorem iSup_zpowers_sUnitKummerKernelGenerator_eq_top
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (⨆ i :
        Fin
          (sUnitKummerPrimeCount
            (K := K) E n hmu r S),
      Subgroup.zpowers
        (sUnitKummerKernelGenerator
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i)) =
      ⊤ := by
  let e :=
    chosenEnlargedSUnitKummerRestrictionKernelEquivPiZMod
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S
  let P :
      Subgroup
        (enlargedSUnitKummerRestrictionHom
          (K := K) (Omega := Omega) E n hmu
          (galois_pow_eq_one_of_equiv_pi_zmod
            (K := K) E n r eG) S).ker :=
    ⨆ i,
      Subgroup.zpowers
        (sUnitKummerKernelGenerator
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i)
  change P = ⊤
  apply top_unique
  intro sigma _
  have hsingle
      (i :
        Fin
          (sUnitKummerPrimeCount
            (K := K) E n hmu r S))
      (z : Multiplicative (ZMod (n : ℕ))) :
      e.symm (Pi.mulSingle i z) ∈ P := by
    obtain ⟨m, hm⟩ :=
      ZMod.natCast_zmod_surjective z.toAdd
    have hz :
        z =
          (Multiplicative.ofAdd
            (1 : ZMod (n : ℕ))) ^ m := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow]
      simpa using hm.symm
    have hpower : e.symm (Pi.mulSingle i z) =
        (sUnitKummerKernelGenerator
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i) ^ m :=
      (congrArg (fun t : Multiplicative (ZMod (n : ℕ)) =>
        e.symm (Pi.mulSingle i t)) hz).trans
        ((congrArg e.symm
          (Pi.mulSingle_pow i (Multiplicative.ofAdd (1 : ZMod (n : ℕ))) m)).trans
          (map_pow e.symm
            (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod (n : ℕ)))) m))
    have hmem :=
      P.pow_mem
        ((le_iSup
          (fun i =>
            Subgroup.zpowers
              (sUnitKummerKernelGenerator
                (K := K) (Omega := Omega) E n hmu
                p v hp hv hn r eG S i)) i)
          (Subgroup.mem_zpowers
            (sUnitKummerKernelGenerator
              (K := K) (Omega := Omega) E n hmu
              p v hp hv hn r eG S i)))
        m
    exact hpower.symm ▸ hmem
  have hesigma :
      e sigma ∈ P.map e.toMonoidHom := by
    apply Subgroup.pi_mem_of_mulSingle_mem (e sigma)
    intro i
    refine
      ⟨e.symm (Pi.mulSingle i (e sigma i)),
        hsingle i (e sigma i), ?_⟩
    exact e.apply_symm_apply _
  obtain ⟨tau, htau, htauSigma⟩ := hesigma
  have htauEq : tau = sigma :=
    e.injective htauSigma
  exact show sigma ∈ (P : Set _) from htauEq ▸ htau

end GeneralKummer

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_SUnitLocalPowerMap
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# S-unit localization modulo local powers

This module constructs the localization map from an S-unit group to the
finite product of local unit power classes and proves its kernel and
surjectivity properties for the Kummer prime set.
-/

open scoped NumberField Classical NNReal IsMulCommutative
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open KummerTheory
open LocalFieldTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- The unit-valued localization map
`Kˢ → ∏ v ∈ T, U_v / U_vⁿ`.  Disjointness makes every `S`-unit an
integral unit at the places in `T`. -/
def sUnitLocalUnitPowerMap
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hST : Disjoint S T) :
    SUnitGroup (K := K) S →*
      ∀ v : T,
        (v.1.adicCompletionIntegers K)ˣ ⧸
          (powMonoidHom (n : ℕ) :
            (v.1.adicCompletionIntegers K)ˣ →*
              (v.1.adicCompletionIntegers K)ˣ).range :=
  MonoidHom.pi fun v =>
    let localPrincipal :
        SUnitGroup (K := K) S →* (v.1.adicCompletion K)ˣ :=
      ((IdeleGroup.finiteComponent v.1).comp
        (IdeleGroup.principalIdele K)).comp
          (SUnitGroup (K := K) S).subtype
    let localPrincipalUnit :
        SUnitGroup (K := K) S →*
          (v.1.adicCompletionIntegers K).units :=
      localPrincipal.codRestrict
        (v.1.adicCompletionIntegers K).units
        (fun x => by
          have hvS : v.1 ∉ S := by
            intro hvS
            exact (Finset.disjoint_left.mp hST) hvS v.2
          rw [
            HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
          change
            Valued.v
                (((IdeleGroup.finiteComponent v.1
                    (IdeleGroup.principalIdele K (x : Kˣ)) :
                      (v.1.adicCompletion K)ˣ) :
                  v.1.adicCompletion K)) =
              1
          rw [IdeleGroup.finiteComponent_principalIdele,
            HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
          exact
            (mem_SUnitGroup_iff (K := K) S x).mp
              x.2 v.1 hvS)
    (QuotientGroup.mk'
        (powMonoidHom (n : ℕ) :
          (v.1.adicCompletionIntegers K)ˣ →*
            (v.1.adicCompletionIntegers K)ˣ).range).comp
      ((v.1.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.toMonoidHom.comp
        localPrincipalUnit)

/-- The unit-valued localization map and the field-valued localization map
defining `Δ` have the same kernel. -/
theorem sUnitLocalUnitPowerMap_ker
    (n : ℕ+)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hST : Disjoint S T) :
    (sUnitLocalUnitPowerMap (K := K) n S T hST).ker =
      sUnitLocalPowerKernel (K := K) n S T := by
  ext x
  let localUnit (v : T) :
      (v.1.adicCompletionIntegers K)ˣ :=
    (v.1.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType
      ⟨IdeleGroup.finiteComponent v.1
          (IdeleGroup.principalIdele K (x : Kˣ)), by
        have hvS : v.1 ∉ S := by
          intro hvS
          exact (Finset.disjoint_left.mp hST) hvS v.2
        rw [
          HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
        rw [IdeleGroup.finiteComponent_principalIdele,
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
        exact
          (mem_SUnitGroup_iff (K := K) S x).mp
            x.2 v.1 hvS⟩
  have localUnit_toField (v : T) :
      Units.map
          (algebraMap (v.1.adicCompletionIntegers K)
            (v.1.adicCompletion K)).toMonoidHom (localUnit v) =
        Units.map
          (algebraMap K (v.1.adicCompletion K)).toMonoidHom
          (x : Kˣ) := by
    apply Units.ext
    rfl
  rw [mem_sUnitLocalPowerKernel_iff, MonoidHom.mem_ker]
  constructor
  · intro hx v
    have hv := congrFun hx v
    rw [Pi.one_apply] at hv
    change QuotientGroup.mk' _ (localUnit v) = 1 at hv
    have hvInteger :=
      (QuotientGroup.eq_one_iff (localUnit v)).mp hv
    have hvField :=
      (mem_powMonoidHom_range_adicCompletionIntegers_iff
        v.1 n (localUnit v)).mp hvInteger
    rw [localUnit_toField v] at hvField
    exact hvField
  · intro hx
    funext v
    rw [Pi.one_apply]
    change QuotientGroup.mk' _ (localUnit v) = 1
    apply (QuotientGroup.eq_one_iff (localUnit v)).mpr
    apply
      (mem_powMonoidHom_range_adicCompletionIntegers_iff
        v.1 n (localUnit v)).mpr
    rw [localUnit_toField v]
    exact hx v

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_IdelePowerLocalUnitNormContainment
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Norm containment for idele power-local-unit subgroups

This module packages the finite-place local norm conditions and proves the
global norm containment and principal-intersection identity used in the
idele-class norm-index argument.
-/

open scoped NumberField Classical NNReal IsMulCommutative
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open KummerTheory
open LocalFieldTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type*} [Field K] [NumberField K]

/-- Every global relative-idele norm satisfies all of the actual
finite-place local norm conditions. -/
theorem relativeIdeleNorm_range_le_allFinitePlaceLocalNormCondition
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    (RelativeIdeleGroup.norm K L).range ≤
      allFinitePlaceLocalNormCondition
        (K := K) (L := L) := by
  rintro a ⟨b, rfl⟩
  rw [allFinitePlaceLocalNormCondition]
  apply Subgroup.mem_iInf.mpr
  intro v
  exact
    _root_.relativeIdeleNorm_finiteComponent_mem_chosenLocalNormSubgroup
      (K := K) (L := L) v b


end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_CyclicIdeleClassNormIndex
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The global class-field axiom

This file proves the cyclic idele-class norm-index formula.  The first
input is the `H⁻¹` calculation for the principal-idele term in

`1 → Lˣ → I_L → C_L → 1`.

For a cyclic extension this term vanishes by Hilbert 90.  The result below
is transported through the actual low-degree Tate comparison and then
through the equivariant identification of `Lˣ` with the subgroup of
principal relative ideles.
-/

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

section NormQuotientCommutativity

section IntermediateNormQuotientCommutativity

attribute [local instance] GlobalClassFieldTheory.ClassFieldAxiom.cyclicNormBase_isMulCommutative
local instance cyclicNormRelative_isMulCommutative_r593d99_1
    (A B : Type) [Field A] [NumberField A] [Field B] [Algebra A B] :
    IsMulCommutative (RelativeIdeleGroup.ClassGroup A B) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
/-- Cardinal consequence with the actual `N/M` norm quotient as
target. -/
theorem ideleClassNormQuotient_card_le_actualPushout
    (K M L N : Type)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Field N] [NumberField N]
    [Algebra K M] [Algebra K L]
    [Algebra M N] [Algebra L N] [Algebra K N]
    [IsScalarTower K M N] [IsScalarTower K L N]
    [Algebra.IsPushout K M L N]
    [FiniteDimensional K M] [FiniteDimensional K L]
    [FiniteDimensional M N] [FiniteDimensional L N]
    [IsGalois K L] [IsGalois K M]
    [Finite (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M N)]
    (hcoprime :
      (Module.finrank K M).Coprime
        (Module.finrank K L)) :
    Nat.card (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K L) ≤
      Nat.card (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M N) :=
  Nat.card_le_card_of_injective
    (actualPushoutNormQuotientMap K M L N)
    (actualPushoutNormQuotientMap_injective_of_coprime
      K M L N hcoprime)

/-- Actual tower form of the cardinal bound:

`#(C_K / N_{L/K}C_L) ≤
  #(C_M / N_{L/M}C_L) · #(C_K / N_{M/K}C_M)`. -/
theorem ideleClassNormQuotient_card_le_actual_tower_mul
    (K M L : Type)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]
    [IsGalois K M]
    [Finite (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M L)]
    [Finite (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K M)] :
    Nat.card (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K L) ≤
      Nat.card (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M L) *
        Nat.card (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K M) := by
  let : Finite (RelativeIdeleGroup.ClassNormQuotient M L) := by
    change
      Finite
        (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient M L)
    infer_instance
  let : Finite (RelativeIdeleGroup.ClassNormQuotient K M) := by
    change
      Finite
        (RelativeIdeleGroup.Cohomology.IdeleClassNormQuotient K M)
    infer_instance
  change
    Nat.card (RelativeIdeleGroup.ClassNormQuotient K L) ≤
      Nat.card (RelativeIdeleGroup.ClassNormQuotient M L) *
        Nat.card (RelativeIdeleGroup.ClassNormQuotient K M)
  let e :=
    intermediateClassNormQuotientBaseChangeMulEquiv
      K M L
  let :
      Finite
        (IntermediateClassNormQuotient K M L) :=
    Finite.of_injective e e.injective
  calc
    Nat.card (RelativeIdeleGroup.ClassNormQuotient K L) ≤
        Nat.card
            (IntermediateClassNormQuotient K M L) *
          Nat.card
            (RelativeIdeleGroup.ClassNormQuotient K M) :=
      ideleClassNormQuotient_card_le_mul K M L
    _ =
        Nat.card (RelativeIdeleGroup.ClassNormQuotient M L) *
          Nat.card
            (RelativeIdeleGroup.ClassNormQuotient K M) := by
      rw [Nat.card_congr e.toEquiv]

end IntermediateNormQuotientCommutativity

end NormQuotientCommutativity

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_ClassFieldAxiom_HasseNormPrinciple
attribute [-instance] _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
attribute [-simp] _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.IdeleGroup.finitePlaceIdele_finiteComponent_of_ne _root_.IdeleGroup.finitePlaceIdele_finiteComponent_same _root_.IdeleGroup.finitePlaceIdele_infiniteComponent _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IdeleGroup.infinitePlaceIdeleContinuous_apply _root_.IdeleGroup.infinitePlaceIdele_finiteComponent _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne _root_.IdeleGroup.infinitePlaceIdele_infiniteComponent_same _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The Hasse norm principle: the concrete local-global map

This file proves the Hasse norm principle on the actual idele and field norm
maps.  The local condition is expressed canonically:
at a place `v` it is the image of the determinant norm on
`K_v ⊗[K] L`.  At finite places this is the chosen completion norm
subgroup by
`_root_.finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup`.

The resulting homomorphism

`Kˣ / N(Lˣ) ⟶ I_K / I_K,loc-norm`

is the concrete diagonal local-norm map.  Its injectivity is exactly the
Hasse norm principle.  The global-to-local inclusion and this equivalence
are independent of the global class-field axiom; the reverse inclusion
follows from degree-minus-one Tate-cohomology vanishing.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

open CategoryTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand

/-- Every global relative-idele norm is a local determinant norm at every
place. -/
theorem relativeIdeleNorm_range_le_allPlaceLocalNormCondition
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    (RelativeIdeleGroup.norm K L).range ≤
      allPlaceLocalNormCondition (K := K) (L := L) := by
  intro a ha
  refine ⟨relativeIdeleNorm_range_le_allFinitePlaceLocalNormCondition
      (K := K) (L := L) ha, ?_⟩
  rcases ha with ⟨b, rfl⟩
  rw [allInfinitePlaceLocalNormCondition]
  apply Subgroup.mem_iInf.mpr
  intro v
  exact
    ⟨RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) v b,
      (RelativeIdeleGroup.infiniteComponent_norm
        (K := K) (L := L) v b).symm⟩

/-- Base-field units that are determinant norms at every completion. -/
def everywhereLocalFieldNormSubgroup
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Subgroup Kˣ :=
  (allPlaceLocalNormCondition (K := K) (L := L)).comap
    (IdeleGroup.principalIdele K)

/-- A global field norm is a local norm at every place.  This is the
unconditional direction of the Hasse norm principle. -/
theorem globalFieldNormSubgroup_le_everywhereLocalFieldNormSubgroup
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    globalFieldNormSubgroup K L ≤
      everywhereLocalFieldNormSubgroup K L := by
  rintro x ⟨y, rfl⟩
  show
    IdeleGroup.principalIdele K
        (Units.map
          (Algebra.norm K : L →* K) y) ∈
      allPlaceLocalNormCondition (K := K) (L := L)
  rw [← RelativeIdeleGroup.norm_principalIdele K L y]
  exact
    relativeIdeleNorm_range_le_allPlaceLocalNormCondition
      (K := K) (L := L) ⟨_, rfl⟩

/-- The concrete diagonal local-norm map.  Its source is the global norm
quotient, while its target kills precisely those ideles satisfying every
local norm condition. -/
noncomputable def hasseNormDiagonal
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Kˣ ⧸ globalFieldNormSubgroup K L →*
      IdeleGroup K ⧸ allPlaceLocalNormCondition (K := K) (L := L) :=
  QuotientGroup.map
    (globalFieldNormSubgroup K L)
    (allPlaceLocalNormCondition (K := K) (L := L))
    (IdeleGroup.principalIdele K)
    globalFieldNormSubgroup_le_everywhereLocalFieldNormSubgroup

/-- The Hasse norm diagonal sends the class of a field unit to the class
of its principal idele. -/
@[simp]
theorem hasseNormDiagonal_mk
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (x : Kˣ) :
    hasseNormDiagonal K L
        (QuotientGroup.mk' (globalFieldNormSubgroup K L) x) =
      QuotientGroup.mk'
        (allPlaceLocalNormCondition (K := K) (L := L))
        (IdeleGroup.principalIdele K x) :=
  rfl

end GlobalClassFieldTheory.ClassFieldAxiom
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ConductorLocalComparison
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteAbstractConjugate_normal _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteResidueConjugate_normal _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.abelianIntermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.IdeleGroup.extension_finiteComponent _root_.IdeleGroup.extension_principalIdele _root_.IdeleGroup.extension_self _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IdeleGroup.norm_principalIdele _root_.IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.rationalFiniteModulus_apply _root_.RayClass.rationalModulus_finitePart_apply _root_.RayClass.signToNarrow_mk _root_.IdeleGroup.idealClass_classRepresentative _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_ideleClassNorm _root_.ideleClassCongr_mk _root_.ideleClassCongr_refl _root_.ideleClassExtension_mk _root_.ideleClassExtension_self _root_.ideleClassNorm_mk _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.infinitePlace_mult_smul _root_.intermediateClassNormQuotientBaseChangeMulEquiv_mk _root_.ordinaryIdeleClassNormQuotientCongrOfAlgEquiv_mk _root_.ordinaryIdeleClassNorm_relativeIdeleClassBaseChange _root_.principalLocalNormQuotientMap_apply _root_.relativeFiniteIdeleMulEquiv_apply _root_.relativeFiniteIdeleToFiniteIdele_apply _root_.relativeIdeleBaseChangeMulEquiv_finite _root_.relativeIdeleBaseChangeMulEquiv_infinite _root_.relativeIdeleBaseChangeMulEquiv_principalIdele _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv _root_.relativeIdeleClassBaseChangeMulEquiv_mk _root_.relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleCongr_norm _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Narrow finite and local conductor exponents

The narrow finite conductor is the finite component of the conductor in
the all-real-positive convention.  We formulate its local condition
directly inside the idele class group: insert a higher unit at one finite
place and `1` at every other place, then pass to the idele class group.

The proof is constructive.  One inequality follows by restricting any
global defining modulus to one place.  For the reverse inequality, replace
one exponent of a fixed defining modulus by the local minimum and split an
idele into its one-place component and the remaining defining-modulus
component.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

namespace ConductorialSubgroup

/-- The exponent of the narrow finite conductor at every finite place is
its finite local conductor exponent. -/
theorem narrowFiniteConductor_apply_eq_narrowFiniteLocalConductorExponent
    (H : ConductorialSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    H.narrowFiniteConductor v =
      H.narrowFiniteLocalConductorExponent v := by
  rw [H.narrowFiniteConductor_apply,
    H.narrowFiniteConductorExponent_eq_narrowFiniteLocalConductorExponent v]

/-- A defining modulus can be chosen to agree with the narrow finite
conductor on any prescribed finite set of finite places and with the
fixed bounding modulus away from that set. -/
theorem exists_definingModulus_finitePart_agrees_on_finset
    (H : ConductorialSubgroup K)
    (s : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ m : RayClass.Modulus K,
      IsDefiningModulus H.1 m ∧
        (∀ v ∈ s, m.finitePart v = H.narrowFiniteConductor v) ∧
        (∀ v ∉ s, m.finitePart v = H.narrowFiniteConductorBoundingModulus v) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine
        ⟨H.chosenDefiningModulus,
          H.chosenDefiningModulus_spec, ?_, ?_⟩
      · intro v hv
        simp at hv
      · intro v _hv
        rfl
  | @insert v s hv ih =>
      obtain ⟨m, hm, hmOn, hmOff⟩ := ih
      let m' : RayClass.Modulus K :=
        m.replaceFinitePart
          (m.finitePart.update v (H.narrowFiniteConductor v))
      have hlocal :
          RayClass.localHigherUnitClassSubgroup v
              (H.narrowFiniteConductor v) ≤ H.1 := by
        rw [H.narrowFiniteConductor_apply,
          H.narrowFiniteConductorExponent_eq_narrowFiniteLocalConductorExponent v]
        exact H.narrowFiniteLocalConductorExponent_spec v
      have hm' : IsDefiningModulus H.1 m' :=
        replaceFiniteExponent_definingModulus H.1 m hm v
          (H.narrowFiniteConductor v) hlocal
      refine ⟨m', hm', ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hws
        · simp [m', RayClass.Modulus.replaceFinitePart]
        · by_cases hwv : w = v
          · subst w
            simp [m', RayClass.Modulus.replaceFinitePart]
          · simpa [m', RayClass.Modulus.replaceFinitePart, hwv] using hmOn w hws
      · intro w hw
        have hwv : w ≠ v := by
          intro hwv
          subst w
          exact hw (Finset.mem_insert_self v s)
        have hws : w ∉ s := by
          intro hws
          exact hw (Finset.mem_insert_of_mem hws)
        simpa [m', RayClass.Modulus.replaceFinitePart, hwv] using hmOff w hws

/-- A defining full modulus can be chosen whose finite part is exactly the
narrow finite conductor. -/
theorem exists_definingModulus_finitePart_eq_narrowFiniteConductor
    (H : ConductorialSubgroup K) :
    ∃ m : RayClass.Modulus K,
      IsDefiningModulus H.1 m ∧
        m.finitePart = H.narrowFiniteConductor := by
  classical
  obtain ⟨m, hm, hmOn, hmOff⟩ :=
    H.exists_definingModulus_finitePart_agrees_on_finset
      H.narrowFiniteConductorBoundingModulus.support
  refine ⟨m, hm, ?_⟩
  ext v
  by_cases hv : v ∈ H.narrowFiniteConductorBoundingModulus.support
  · exact hmOn v hv
  · have hbound : H.narrowFiniteConductorBoundingModulus v = 0 := by
      exact Finsupp.notMem_support_iff.mp hv
    have hmzero : m.finitePart v = 0 :=
      (hmOff v hv).trans hbound
    have hfinite_le :
        H.narrowFiniteConductor v ≤
          H.narrowFiniteConductorBoundingModulus v := by
      simpa only [ConductorialSubgroup.narrowFiniteConductorBoundingModulus] using
        H.narrowFiniteConductor_le H.chosenDefiningModulus_spec v
    rw [hbound] at hfinite_le
    have hfinite_zero : H.narrowFiniteConductor v = 0 :=
      Nat.eq_zero_of_le_zero hfinite_le
    exact hmzero.trans hfinite_zero.symm

end ConductorialSubgroup

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ConductorInfinitePart
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteAbstractConjugate_normal _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteResidueConjugate_normal _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.abelianIntermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.IdeleGroup.extension_finiteComponent _root_.IdeleGroup.extension_principalIdele _root_.IdeleGroup.extension_self _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IdeleGroup.norm_principalIdele _root_.IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.rationalModulus_finitePart_apply _root_.RayClass.signToNarrow_mk _root_.IdeleGroup.idealClass_classRepresentative _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_ideleClassNorm _root_.ideleClassCongr_mk _root_.ideleClassCongr_refl _root_.ideleClassExtension_mk _root_.ideleClassExtension_self _root_.ideleClassNorm_mk _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.infinitePlace_mult_smul _root_.intermediateClassNormQuotientBaseChangeMulEquiv_mk _root_.ordinaryIdeleClassNormQuotientCongrOfAlgEquiv_mk _root_.ordinaryIdeleClassNorm_relativeIdeleClassBaseChange _root_.principalLocalNormQuotientMap_apply _root_.relativeFiniteIdeleMulEquiv_apply _root_.relativeFiniteIdeleToFiniteIdele_apply _root_.relativeIdeleBaseChangeMulEquiv_finite _root_.relativeIdeleBaseChangeMulEquiv_infinite _root_.relativeIdeleBaseChangeMulEquiv_principalIdele _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv _root_.relativeIdeleClassBaseChangeMulEquiv_mk _root_.relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleCongr_norm _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Removing one real place from a defining modulus

This file gives the one-place archimedean step toward the full conductor.
Removing the positivity condition at a real place preserves the defining
property exactly when the whole one-place idèle-class image is already
contained in the target subgroup.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

namespace ConductorialSubgroup

/-- Membership in the infinite part of the full conductor is the failure of
the corresponding one-place idèle-class image to lie in the target subgroup. -/
@[simp]
theorem mem_fullConductorInfinitePart_iff
    (H : ConductorialSubgroup K) (v : RayClass.RealPlace K) :
    v ∈ H.fullConductorInfinitePart ↔
      ¬ (IdeleGroup.infinitePlaceIdeleClass v.1).range ≤ H.1 := by
  simp only [fullConductorInfinitePart, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- The full conductor, with the narrow finite conductor as finite part and
exactly the required real places as infinite part. -/
noncomputable def fullConductor
    (H : ConductorialSubgroup K) : RayClass.Modulus K where
  finitePart := H.narrowFiniteConductor
  infinitePart := H.fullConductorInfinitePart

end ConductorialSubgroup

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ConductorLattice
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteAbstractConjugate_normal _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteResidueConjugate_normal _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.abelianIntermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.nthRootsSubgroupFintype _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Lattice operations on narrow finite conductors

Increasing a modulus decreases its ray congruence subgroup.  This
contravariance makes the narrow finite conductor of an intersection of
norm subgroups the pointwise maximum of their narrow finite conductors.
Under class-field correspondence, this is the finite-part lcm formula
for a compositum.  For a generated subgroup one obtains the
complementary divisibility by the pointwise minimum.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-- Idèle congruence subgroups are contravariant in the modulus. -/
theorem rayClassIdeleCongruenceSubgroup_antitone
    {m n : RayClass.Modulus K} (hmn : m ≤ n) :
    n.ideleCongruenceSubgroup ≤
      m.ideleCongruenceSubgroup := by
  rintro a ⟨haInfinite, haFinite⟩
  exact
    ⟨rayClassInfiniteCongruenceSubgroup_antitone
        (K := K) hmn haInfinite,
      rayClassFiniteCongruenceSubgroup_antitone
        (K := K) hmn.1 haFinite⟩

/-- Ray congruence subgroups in the idèle class group are
contravariant in the modulus. -/
theorem rayClassCongruenceSubgroup_antitone
    {m n : RayClass.Modulus K} (hmn : m ≤ n) :
    n.congruenceSubgroup ≤
      m.congruenceSubgroup := by
  unfold RayClass.Modulus.congruenceSubgroup
  apply Subgroup.map_mono
  exact
    sup_le
      ((rayClassIdeleCongruenceSubgroup_antitone
        (K := K) hmn).trans le_sup_left)
      le_sup_right

/-- Once a modulus defines a subgroup, every larger modulus also
defines it. -/
theorem isDefiningModulus_mono
    (H : Subgroup (IdeleClassGroup K))
    {m n : RayClass.Modulus K}
    (hm : IsDefiningModulus H m)
    (hmn : m ≤ n) :
    IsDefiningModulus H n :=
  (rayClassCongruenceSubgroup_antitone
    (K := K) hmn).trans hm

namespace ConductorialSubgroup

/-- The exact narrow finite conductor, interpreted as a full modulus with
positivity at every real place, is a defining modulus. -/
theorem narrowFiniteConductor_isDefiningModulus
    (H : ConductorialSubgroup K) :
    IsDefiningModulus H.1
      (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) := by
  obtain ⟨m, hm, hfinite⟩ :=
    H.exists_definingModulus_finitePart_eq_narrowFiniteConductor
  apply isDefiningModulus_mono H.1 hm
  exact ⟨hfinite.le, Finset.subset_univ _⟩

end ConductorialSubgroup

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_ConductorRayClassMaximality
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAbstractExtension.ramificationQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.representedQuotientFinite _root_.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FiniteResidueAbstractExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.DegreeData.FiniteTower.baseQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.topQuotientFinite _root_.ClassFormation.DegreeData.FiniteTower.totalQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteAbstractConjugate_normal _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteResidueConjugate_normal _root_.ClassFormation.FiniteAbstractField.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteAbstractFieldExtension.instFiniteQuotientSubtypeMemSubgroupFieldBaseExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.abelianIntermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupBaseFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instFiniteQuotientSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionQuotientOfEmbedding_finite _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSubquotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.quotientMaximalIdealPowFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.unitsModHigherPrincipalUnitGroupFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.finiteGaloisAbstractExtensionOfEmbedding_bundle_finite _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.IdeleGroup.extension_finiteComponent _root_.IdeleGroup.extension_principalIdele _root_.IdeleGroup.extension_self _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IdeleGroup.norm_principalIdele _root_.IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.rationalFiniteModulus_apply _root_.RayClass.rationalModulus_finitePart_apply _root_.RayClass.signToNarrow_mk _root_.IdeleGroup.idealClass_classRepresentative _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleClassCongr_ideleClassNorm _root_.ideleClassCongr_mk _root_.ideleClassCongr_refl _root_.ideleClassExtension_mk _root_.ideleClassExtension_self _root_.ideleClassNorm_mk _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe _root_.infinitePlace_mult_smul _root_.intermediateClassNormQuotientBaseChangeMulEquiv_mk _root_.ordinaryIdeleClassNormQuotientCongrOfAlgEquiv_mk _root_.ordinaryIdeleClassNorm_relativeIdeleClassBaseChange _root_.principalLocalNormQuotientMap_apply _root_.relativeFiniteIdeleMulEquiv_apply _root_.relativeFiniteIdeleToFiniteIdele_apply _root_.relativeIdeleBaseChangeMulEquiv_finite _root_.relativeIdeleBaseChangeMulEquiv_infinite _root_.relativeIdeleBaseChangeMulEquiv_principalIdele _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv _root_.relativeIdeleClassBaseChangeMulEquiv_mk _root_.relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleCongr_norm _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Exact narrow finite conductor ray-class presentations

For a conductorial subgroup `H` of the idèle class group, the ray class
group at its exact narrow finite conductor maps canonically onto `C_K / H`.
This file characterizes injectivity of that map by equality of the two
finite orders and proves uniqueness of subgroups whose exact narrow finite
conductor ray-class presentations are maximal.
-/

open scoped IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

variable {K : Type} [Field K] [NumberField K]

namespace ConductorialSubgroup

attribute [local instance] GlobalClassFieldTheory.GlobalClassFields.conductorRayClassMaximality_ideleClassGroupIsMulCommutative
/-- The canonical quotient map from the ray class group at the exact
narrow finite conductor of `H` onto `C_K / H`. -/
noncomputable def narrowFiniteConductorRayClassGroupToQuotient
    (H : ConductorialSubgroup K) :
    RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) →*
      IdeleClassGroup K ⧸ H.1 :=
  QuotientGroup.map
    (RayClass.Modulus.congruenceSubgroup
      (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor))
    H.1
    (MonoidHom.id _)
    (show
      RayClass.Modulus.congruenceSubgroup
          (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) ≤
        Subgroup.comap (MonoidHom.id _) H.1 from by
      intro x hx
      change x ∈ H.1
      exact H.narrowFiniteConductor_isDefiningModulus hx)

/-- The exact narrow finite conductor quotient map preserves every
idèle-class representative. -/
@[simp]
theorem narrowFiniteConductorRayClassGroupToQuotient_mk
    (H : ConductorialSubgroup K)
    (c : IdeleClassGroup K) :
    H.narrowFiniteConductorRayClassGroupToQuotient
      (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup
            (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) c) =
      QuotientGroup.mk' H.1 c :=
  rfl

/-- The exact narrow finite conductor ray-class map onto `C_K / H` is
surjective. -/
theorem narrowFiniteConductorRayClassGroupToQuotient_surjective
    (H : ConductorialSubgroup K) :
    Function.Surjective H.narrowFiniteConductorRayClassGroupToQuotient := by
  intro q
  obtain ⟨c, rfl⟩ :=
    QuotientGroup.mk'_surjective H.1 q
  exact
    ⟨QuotientGroup.mk'
        (RayClass.Modulus.congruenceSubgroup
          (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) c,
      rfl⟩

/-- The exact narrow finite conductor ray-class map is injective exactly
when its finite source and target have the same order. -/
theorem narrowFiniteConductorRayClassGroupToQuotient_injective_iff_card_eq
    (H : ConductorialSubgroup K) :
    Function.Injective H.narrowFiniteConductorRayClassGroupToQuotient ↔
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1) := by
  let f := H.narrowFiniteConductorRayClassGroupToQuotient
  have hfSurjective : Function.Surjective f :=
    H.narrowFiniteConductorRayClassGroupToQuotient_surjective
  constructor
  · intro hfInjective
    exact
      Nat.card_congr
        (Equiv.ofBijective f
          ⟨hfInjective, hfSurjective⟩)
  · intro hcard
    exact
      (hfSurjective.bijective_of_nat_card_le hcard.le).1

/-- When the exact narrow finite conductor ray class group and `C_K / H`
have the same order, the canonical quotient map is a multiplicative
equivalence. -/
noncomputable def narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq
    (H : ConductorialSubgroup K)
    (hcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1)) :
    RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) ≃*
      IdeleClassGroup K ⧸ H.1 :=
  MulEquiv.ofBijective
    H.narrowFiniteConductorRayClassGroupToQuotient
    ⟨H.narrowFiniteConductorRayClassGroupToQuotient_injective_iff_card_eq.2
        hcard,
      H.narrowFiniteConductorRayClassGroupToQuotient_surjective⟩

/-- The maximal exact narrow finite conductor equivalence preserves every
idèle-class representative. -/
@[simp]
theorem narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk
    (H : ConductorialSubgroup K)
    (hcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1))
    (c : IdeleClassGroup K) :
    H.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq
        hcard
      (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup
            (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) c) =
      QuotientGroup.mk' H.1 c :=
  rfl

/-- A conductorial subgroup is exactly the congruence subgroup at its
narrow finite conductor precisely when its quotient has the full exact
narrow finite conductor ray class number. -/
theorem
    subgroup_eq_narrowFiniteConductorCongruenceSubgroup_iff_rayClassGroup_card_eq_quotient_card
    (H : ConductorialSubgroup K) :
    H.1 = RayClass.Modulus.congruenceSubgroup
      (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) ↔
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1) := by
  constructor
  · intro hH
    calc
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
          (RayClass.Modulus.congruenceSubgroup
            (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)).index :=
        (Subgroup.index_eq_card _).symm
      _ = H.1.index := by
        rw [← hH]
      _ = Nat.card (IdeleClassGroup K ⧸ H.1) :=
        Subgroup.index_eq_card H.1
  · intro hcard
    let f := H.narrowFiniteConductorRayClassGroupToQuotient
    have hfInjective : Function.Injective f :=
      H.narrowFiniteConductorRayClassGroupToQuotient_injective_iff_card_eq.2
        hcard
    apply le_antisymm
    · intro c hc
      have hfc :
          f
              (QuotientGroup.mk'
                (RayClass.Modulus.congruenceSubgroup
                  (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) c) =
            1 := by
        change QuotientGroup.mk' H.1 c = 1
        exact (QuotientGroup.eq_one_iff _).2 hc
      have hcOne :
          QuotientGroup.mk'
              (RayClass.Modulus.congruenceSubgroup
                (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) c =
            1 :=
        hfInjective (hfc.trans (map_one f).symm)
      exact (QuotientGroup.eq_one_iff _).1 hcOne
    · exact H.narrowFiniteConductor_isDefiningModulus

/-- Conductorial subgroups with the same exact narrow finite conductor
and maximal exact-conductor ray-class presentations have equal underlying
subgroups. -/
theorem
    subgroups_eq_of_narrowFiniteConductors_eq_of_rayClassGroup_cards_eq_quotient_cards
    (H J : ConductorialSubgroup K)
    (hconductor : H.narrowFiniteConductor = J.narrowFiniteConductor)
    (hHcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1))
    (hJcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite J.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ J.1)) :
    H.1 = J.1 := by
  calc
    H.1 = RayClass.Modulus.congruenceSubgroup
      (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor) :=
      H.subgroup_eq_narrowFiniteConductorCongruenceSubgroup_iff_rayClassGroup_card_eq_quotient_card.2
        hHcard
    _ = RayClass.Modulus.congruenceSubgroup
      (RayClass.Modulus.narrowOfFinite J.narrowFiniteConductor) :=
      congrArg
        (fun f => RayClass.Modulus.congruenceSubgroup
          (RayClass.Modulus.narrowOfFinite f))
        hconductor
    _ = J.1 :=
      (J.subgroup_eq_narrowFiniteConductorCongruenceSubgroup_iff_rayClassGroup_card_eq_quotient_card.2
        hJcard).symm

/-- The quotients by two maximal exact narrow finite conductor subgroups
with the same conductor are canonically equivalent. -/
def ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards
    (H J : ConductorialSubgroup K)
    (hconductor : H.narrowFiniteConductor = J.narrowFiniteConductor)
    (hHcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1))
    (hJcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite J.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ J.1)) :
    (IdeleClassGroup K ⧸ H.1) ≃*
      (IdeleClassGroup K ⧸ J.1) :=
  QuotientGroup.quotientMulEquivOfEq
    (H.subgroups_eq_of_narrowFiniteConductors_eq_of_rayClassGroup_cards_eq_quotient_cards
      J hconductor hHcard hJcard)

/-- The canonical equivalence between maximal exact narrow finite
conductor quotients preserves every idèle-class representative. -/
@[simp]
theorem
    ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk
    (H J : ConductorialSubgroup K)
    (hconductor : H.narrowFiniteConductor = J.narrowFiniteConductor)
    (hHcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite H.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ H.1))
    (hJcard :
      Nat.card (RayClass.RayClassGroup
        (RayClass.Modulus.narrowOfFinite J.narrowFiniteConductor)) =
        Nat.card (IdeleClassGroup K ⧸ J.1))
    (c : IdeleClassGroup K) :
    H.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards
        J hconductor hHcard hJcard
        (QuotientGroup.mk' H.1 c) =
      QuotientGroup.mk' J.1 c :=
  rfl

end ConductorialSubgroup

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_NormConductor
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Narrow finite conductors of actual idele-class norm subgroups

For a finite Galois extension of number fields, the image of the
idele-class norm contains an explicitly constructed ray congruence
subgroup.  At a ramified finite place we choose a sufficiently deep
higher-unit group inside the open local norm subgroup.  Outside the
finite ramification set, the full local unit group already consists of
norms.  The archimedean positive subgroup is always contained in the
corresponding tensor-norm image.

This produces a defining modulus directly from the actual extension.  In
particular, the idele-class norm range is open, closed, and of finite
index.  Its narrow finite conductor can only be supported at ramified
finite places.  The full conductor, including an archimedean component,
is deliberately not defined here.
-/

open scoped NumberField Classical IsMulCommutative

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain Topology

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Fix the canonical commutative idèle-class structure used by the norm
quotients in this module. -/
local instance normConductorIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_InfinitePlaceArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIsGalois
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.IdeleGroup.extension_finiteComponent _root_.IdeleGroup.extension_principalIdele _root_.IdeleGroup.extension_self _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.IdeleGroup.idealClass_classRepresentative _root_.doubleCosetExtension_mk _root_.extendAbsoluteValueExtensionFromIntermediate_apply _root_.ideleClassCongr_ideleClassNorm _root_.ideleClassCongr_mk _root_.ideleClassCongr_refl _root_.ideleClassExtension_mk _root_.ideleClassExtension_self _root_.ideleCongr_finiteComponent _root_.ideleCongr_principalIdele _root_.intermediateClassNormQuotientBaseChangeMulEquiv_mk _root_.ordinaryIdeleClassNormQuotientCongrOfAlgEquiv_mk _root_.ordinaryIdeleClassNorm_relativeIdeleClassBaseChange _root_.relativeIdeleClassBaseChangeMulEquiv_classInclusion _root_.relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv _root_.relativeIdeleClassBaseChangeMulEquiv_mk _root_.relativeIdeleClassCongrOfAlgEquiv_ideleClassNorm _root_.relativeIdeleClassCongr_ideleClassNorm _root_.relativeIdeleCongr_norm _root_.restrictAbsoluteValueExtensionToIntermediate_apply _root_.towerRelativeIdeleViaOrdinaryMulEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Archimedean Artin homomorphisms

At a ramified infinite place, the local extension is complex over
real.  Its Artin homomorphism sends the sign of a real unit to the
corresponding complex-conjugation element of the decomposition group.
At an unramified infinite place the decomposition group, and hence the
local homomorphism, is trivial.
-/

open scoped BigOperators Classical IsMulCommutative NumberField
  NumberField.LiesOver
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open HilbertRamification
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]

variable [IsAbelianGalois K L]

omit [NumberField L] in
/-- The archimedean Artin product after an idele norm is the product,
over all infinite places upstairs, of the base local Artin maps applied
to the corresponding local field norms. -/
theorem infinitePlaceGlobalArtinMonoidHom_norm_eq_prod
    {M : Type}
    [Field M] [NumberField M] [Algebra K M]
    (a : IdeleGroup M) :
    letI : ∀ W : InfinitePlace M,
        W.1.LiesOver
          (infinitePlaceBelow (K := K) W).1 :=
      fun _ => ⟨rfl⟩
    infinitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)
        (IdeleGroup.norm K M a) =
      ∏ W : InfinitePlace M,
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L)
          (infinitePlaceBelow (K := K) W)
          (LocalFieldTheory.normUnits
            (infinitePlaceBelow
              (K := K) W).Completion
            W.Completion
            (IdeleGroup.infiniteComponent W a)) := by
  classical
  let : ∀ W : InfinitePlace M,
      W.1.LiesOver
        (infinitePlaceBelow (K := K) W).1 :=
    fun _ => ⟨rfl⟩
  let factor : InfinitePlace M → (L ≃ₐ[K] L) :=
    fun W =>
      chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L)
        (infinitePlaceBelow (K := K) W)
        (LocalFieldTheory.normUnits
          (infinitePlaceBelow
            (K := K) W).Completion
          W.Completion
          (IdeleGroup.infiniteComponent W a))
  unfold infinitePlaceGlobalArtinMonoidHom
  rw [MonoidHom.finsetProd_apply]
  change
    (∏ v : InfinitePlace K,
      chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v
        (IdeleGroup.infiniteComponent v
          (IdeleGroup.norm K M a))) =
      ∏ W : InfinitePlace M, factor W
  calc
    (∏ v : InfinitePlace K,
        chosenInfinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (IdeleGroup.infiniteComponent v
            (IdeleGroup.norm K M a))) =
        ∏ v : InfinitePlace K,
          ∏ W ∈ Finset.univ with
              infinitePlaceBelow (K := K) W = v,
            factor W := by
      apply Finset.prod_congr rfl
      intro v _
      let vK := v.1
      let hvK : vK.IsNontrivial := v.isNontrivial
      let eAbove :=
        infinitePlaceAboveEquivExtension
          (K := K) (L := M) v
      let :=
        AlgebraicNumberTheory.Valuations.completionTensorDecomposition_extensionFintype
          (K := K) (L := M) vK hvK
      let : Fintype {W : InfinitePlace M //
          infinitePlaceBelow (K := K) W = v} :=
        Fintype.ofEquiv
          (AlgebraicNumberTheory.Valuations.AbsoluteValueExtension vK M)
          eAbove.symm
      let : ∀ W : {W : InfinitePlace M //
          infinitePlaceBelow (K := K) W = v},
          W.1.1.LiesOver v.1 :=
        fun W =>
          ⟨congrArg (fun q : InfinitePlace K => q.1) W.2⟩
      rw [IdeleGroup.infiniteComponent_norm_eq_prod]
      rw [map_prod]
      symm
      rw [Finset.prod_subtype
        (p := fun W : InfinitePlace M =>
          infinitePlaceBelow (K := K) W = v)
        (s := Finset.univ.filter fun W : InfinitePlace M =>
          infinitePlaceBelow (K := K) W = v)
        (by intro W; simp)]
      apply Finset.prod_congr rfl
      intro W _
      rcases W with ⟨W, rfl⟩
      rfl
    _ = ∏ W : InfinitePlace M, factor W :=
      Finset.prod_fiberwise
        Finset.univ
        (infinitePlaceBelow (K := K))
        factor

omit [NumberField L] in
/-- The archimedean part of the Artin norm--restriction field diamond.
Restriction of the upper infinite Artin product is the lower infinite Artin
product after the ordinary idele norm. -/
theorem infinitePlaceGlobalArtinMonoidHom_norm_restriction
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L'] :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (infinitePlaceGlobalArtinMonoidHom
          (K := K') (L := L')) =
      (infinitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)).comp
        (IdeleGroup.norm K K') := by
  apply MonoidHom.ext
  intro a
  let : ∀ W : InfinitePlace K',
      W.1.LiesOver
        (infinitePlaceBelow
          (K := K) W).1 :=
    fun _ => ⟨rfl⟩
  change
    ((AlgEquiv.restrictNormalHom L).comp
      (AlgEquiv.restrictScalarsHom K))
      (infinitePlaceGlobalArtinMonoidHom
        (K := K') (L := L') a) =
      infinitePlaceGlobalArtinMonoidHom
        (K := K) (L := L)
        (IdeleGroup.norm K K' a)
  rw [infinitePlaceGlobalArtinMonoidHom_norm_eq_prod]
  unfold infinitePlaceGlobalArtinMonoidHom
  rw [MonoidHom.finsetProd_apply]
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro W _
  exact
    DFunLike.congr_fun
      (chosenInfinitePlaceArtinMonoidHom_norm_restriction
        (K := K) (L := L) W)
      (IdeleGroup.infiniteComponent W a)

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedComparison
attribute [-instance] _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_mk _root_.LocalClassFieldTheory.principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_apply _root_.LocalClassFieldTheory.principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_mk _root_.LocalClassFieldTheory.principalUnitsSuccQuotTraceOfUnramifiedValuation_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
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


section BaseFrobeniusLift

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The chosen degree-one lift used in the abstract unramified Frobenius. -/
noncomputable def abstractBaseFrobeniusLift :
    (abstractBase_p1 K).toSubgroup :=
  Classical.choose
    ((localResidueDatum K).normalizedDegree_surjective
      (finiteResidueAbstractBase K)
      (Multiplicative.ofAdd (1 : ZHat)))

end BaseFrobeniusLift

section

variable (K L : Type)
  [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K)
    (ValuativeRel.valuation L)]

variable
  [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]

variable (i : L →ₐ[K] SeparableClosure K)

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] in
/-- Reduction of an embedded finite extension into the selected residue
algebraic closure used by `localResidueDatum`. -/
noncomputable def finiteGaloisResidueEmbeddingOfEmbedding :
    𝓀[L] →+*
      selectedResidueField (localSeparableValuationSubring K) := by
  letI : Algebra L (SeparableClosure K) := i.toRingHom.toAlgebra
  have h := congrArg ValuationSubring.toSubring
    (localSeparableValuationSubring_comap_embedding K L i)
  change ((localSeparableValuationSubring K).comap i.toRingHom).toSubring =
    (ValuativeRel.valuation L).integer at h
  letI : IsLocalRing ((localSeparableValuationSubring K).comap i.toRingHom).toSubring := by
    change IsLocalRing ((localSeparableValuationSubring K).comap i.toRingHom)
    infer_instance
  let e : (ValuativeRel.valuation L).integer ≃+*
      ((localSeparableValuationSubring K).comap i.toRingHom).toSubring :=
    RingEquiv.subringCongr h.symm
  exact (valuationSubringComapResidueMap
      (F := L) (localSeparableValuationSubring K)).comp
    (IsLocalRing.ResidueField.mapEquiv e).toRingHom

omit [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] in
/-- The residue embedding is reduction of the original field embedding. -/
@[simp] theorem finiteGaloisResidueEmbeddingOfEmbedding_residue
    (x : 𝒪[L]) :
    finiteGaloisResidueEmbeddingOfEmbedding K L i
        (IsLocalRing.residue 𝒪[L] x) =
      IsLocalRing.residue (localSeparableValuationSubring K)
        (⟨i (x : L), by
          have hx : (x : L) ∈
              (localSeparableValuationSubring K).comap i.toRingHom := by
            rw [localSeparableValuationSubring_comap_embedding K L i]
            exact x.property
          exact hx⟩ : localSeparableValuationSubring K) := by
  simp only [finiteGaloisResidueEmbeddingOfEmbedding]
  rfl

/-! ## Comparison of unramifiedness -/

/-! ## Frobenius normalization -/

section AbstractUnramifiedFrobenius

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] in
theorem finiteGaloisResidueBaseExtension_normal :
    (extensionSubgroup (finiteResidueAbstractBase K).field
      (finiteGaloisAbstractExtensionOfEmbedding K L i).field
      (finiteGaloisAbstractExtensionOfEmbedding K L i).below).Normal :=
  (finiteGaloisAbstractExtensionOfEmbedding K L i).normal

attribute [local instance] finiteGaloisResidueBaseExtension_normal

end AbstractUnramifiedFrobenius

end

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldLocalData
attribute [-instance] _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instDiscreteTopology _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instAddCommGroup _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.instTopologicalSpace _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitT2Space _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.residueField_charP_residueCharacteristic _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_finite_residue _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeDegreeIntermediate_top_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.primeOrderFixedField_isGalois _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.scaledRelativeIntegerLatticeQuotientFinite
attribute [-simp] _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeEquiv_unramifiedFrobenius _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeHom_mk _root_.ClassFormation.DegreeData.finiteUnramifiedRestriction_frobenius _root_.ClassFormation.DegreeData.finiteUnramifiedRestriction_mk _root_.ClassFormation.DegreeData.maximalUnramifiedExtensionRestriction_mk _root_.ClassFormation.DegreeData.maximalUnramifiedFrobeniusPower_one _root_.ClassFormation.DegreeData.maximalUnramifiedRestriction_frobenius _root_.ClassFormation.ValuationData.maximalUnramifiedNormResidue_degree _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalClassFieldTheory.abstractFixedFieldCosetToAlgHom_mk _root_.LocalClassFieldTheory.intrinsicBaseEquivAmbientFixedField_apply_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.coeffHom_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_C _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.EqualCharacteristicLaurent.powerSeriesEvalSubringHom_X _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_mul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit_one _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.AdicPrincipalUnits.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.DiscretePrincipalUnitQuotient.val_transition _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.adicPrincipalUnitsHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.iwasawaGlobalInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddEquivInverseLimitCarrier_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitAddHomeomorphInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierEval_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadic_smul_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitMulEquivInverseLimitCarrier_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitPadic_smul_carrier_coordinate _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicScalar_eq_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierToFull_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierTransition_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.uniformizerHigherUnitQuotientEquiv_mk _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.addEquiv_symm_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.coordinate_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.of_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.PrincipalUnitProdiscreteLimit.val_of _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAddEquivUnderlyingOfWithZeroValuation_map_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaDegreeTerm_zero _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaGn_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaPartialProduct_zero_input _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedAtLevel_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeedIdeal_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.iwasawaSeed_val _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_natCast_smul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_nsmul_eq_pow _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadic_smul_def _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotAddEquivResidue_iwasawaSeed _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict_apply _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.multiplicativeIntegerValuationOfUniformizer_val _root_.LocalFieldTheory.DiscreteValuationField.LocalField.higherPrincipalUnitAddToFirst_smul _root_.LocalFieldTheory.DiscreteValuationField.LocalField.laurentSeriesEquivLaurentImageSubfield_apply_coe _root_.LocalFieldTheory.DiscreteValuationField.LocalField.padicIntToValuationSubring_coe _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomOfPrincipalUnitHom_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_principal _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_root _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitDecompositionLogHomWithUniformizerValue_uniformizer _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomOfPrincipalUnitHom_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.fieldUnitLogHomWithUniformizerValue_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHomOfMaximalIdealPow_apply _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeriesHom_apply_ofAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_maximalIdealPow_val_ofWithZeroValuationScaled _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_mul_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_val_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitExpSeries_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogPartialSum_zero_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHomOfWithZeroValuationScaled_apply_toAdd _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeriesHom_apply_toAdd_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitLogSeries_one_ofWithZeroValuation _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.principalUnitSubOne_one_ofWithZeroValuation _root_.LocalFieldTheory.Padic.integerRingEquivPadicDVRValuationSubring_coe _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LubinTate.LubinTateSeries.standardLubinTateSeries_toPowerSeries _root_.LubinTate.SameUniformizer.coeff_recursiveIntertwiner _root_.LubinTate.SameUniformizer.constantCoeff_inVariable _root_.LubinTate.SameUniformizer.intertwinerApproximation_zero _root_.LubinTate.SameUniformizer.standardLubinTateEndomorphism_coeff_one _root_.LubinTate.padicValuationSubringToCompletedUnramifiedWittRing_uniformizer _root_.LubinTate.standardLubinTateBaseUniformizerUnit_coe _root_.LubinTate.standardLubinTateChangedUniformizerUnit_coe _root_.LubinTate.standardLubinTateEndomorphismEvalAt_one _root_.LubinTate.standardLubinTateEndomorphismEvalAt_zero _root_.LubinTate.standardLubinTateEndomorphismValue_one _root_.LubinTate.standardLubinTateEndomorphismValue_zero _root_.LubinTate.standardLubinTateLevelCoefficientHom_apply _root_.LubinTate.standardLubinTateLevelGenerator_coe _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_C _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_X _root_.LubinTate.standardLubinTateLevelPowerSeriesEval_coe _root_.LubinTate.standardLubinTatePolynomialIterateOverSeparableClosure_eval _root_.LubinTate.standardLubinTatePolynomialIterate_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_eval_zero _root_.LubinTate.standardLubinTatePolynomialIterate_zero _root_.LubinTate.standardLubinTatePolynomial_derivative_eval_zero _root_.LubinTate.standardLubinTatePolynomial_eval _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries _root_.LubinTate.standardLubinTatePolynomial_toPowerSeries_eq_series _root_.LubinTate.standardLubinTatePrimitiveLevelAction_coe _root_.LubinTate.standardLubinTatePrimitivePointIntegerAction_one _root_.LubinTate.standardLubinTatePrimitivePointInteger_coe _root_.LubinTate.standardLubinTatePrimitivePointIterateInteger_zero _root_.LubinTate.standardLubinTatePrimitivePolynomialOverField_coeff_zero _root_.LubinTate.standardLubinTatePrimitivePolynomial_coeff_zero _root_.LubinTate.standardLubinTatePrimitiveRootAction_one _root_.LubinTate.standardLubinTateUnitFactorFieldUnit_coe _root_.LubinTate.standardLubinTateUnitParameterAlgEquiv_apply_gen _root_.LubinTate.standardLubinTateUnitParameterAlgHom_apply_gen _root_.LubinTate.standardLubinTateUnitParameterChosenRepresentative_spec _root_.LubinTate.standardLubinTateUnitParameterEquivGal_apply _root_.LubinTate.standardLubinTateUnitParameterEquivGal_inv_class_apply_gen _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_coe _root_.LubinTate.standardLubinTateUnitParameterLevelRoot_one _root_.LubinTate.standardLubinTateUnitParameterRoot_class _root_.LubinTate.standardLubinTateUnitParameterToGalHom_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_algebraMap _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionResidueAction_apply _root_.RamificationTheory.HilbertRamification.CompleteDVF.galEquivDecompositionGroup_coe _root_.RamificationTheory.HilbertRamification.CompleteDVF.residueAction_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit_mul_uniformizer _root_.RamificationTheory.HilbertRamification.Higher.dvfUniformizerRepresentativeHom_apply _root_.RamificationTheory.HilbertRamification.Higher.dvfValuationSubringUnitAut_apply _root_.RamificationTheory.HilbertRamification.Higher.intrinsicRamificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup_neg_one _root_.RamificationTheory.HilbertRamification.Higher.mem_dvfHigherPrincipalUnitGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_lowerRamificationGroup_iff _root_.RamificationTheory.HilbertRamification.Higher.mem_valuationSubringDisplacementSubalgebraOfUniqueExtension_iff _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberDepthOfUniqueExtension_depth _root_.RamificationTheory.HilbertRamification.Higher.ramificationNumberOfUniqueExtension_one _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_nat _root_.RamificationTheory.HilbertRamification.Higher.realRamificationIdeal_neg_one _root_.RamificationTheory.HilbertRamification.Higher.uniformizerGradedHom_mk _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_coe _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_apply_inv_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_mul_apply _root_.RamificationTheory.HilbertRamification.Higher.valuationSubringAutOfUniqueExtension_one_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.LubinTate.standardLubinTateLevelAutomorphismIntegerRingEquiv_apply _root_.infinitePlace_mult_smul
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Canonical local data on finite fixed fields

This file compares the normalized valuation induced on a finite abstract
field by the local class formation with the ordinary normalized valuation
of its concrete fixed field.  The concrete field is equipped with the
canonical spectral extension of the topology on the original local field.
-/

noncomputable section

namespace LocalClassFieldTheory

open scoped NNReal Pointwise ValuativeRel
open ClassFormation LocalFieldTheory RamificationTheory CyclicCohomology
open RamificationTheory.HilbertRamification.ValuationSubring

attribute [local instance] LocalClassFieldTheory.finiteFixedFieldSeparableClosureAlgebra
/-- On a finite fixed field, the normalized valuation induced by the local
class formation is the ordinary normalized local-field valuation. -/
theorem localHenselianValuation_valuationAt_abstractFixedField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField (Gal(SeparableClosure K / K)))
    (x : (abstractFixedField K (SeparableClosure K) H.field)ˣ) :
    letI : FiniteDimensional K
        (abstractFixedField K (SeparableClosure K) H.field) :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) H.field H.finite
    letI : NontriviallyNormedField
        (abstractFixedField K (SeparableClosure K) H.field) :=
      finiteExtensionSpectralNormedField K
        (abstractFixedField K (SeparableClosure K) H.field)
    letI : ValuativeRel
        (abstractFixedField K (SeparableClosure K) H.field) :=
      finiteExtensionSpectralValuativeRel K
        (abstractFixedField K (SeparableClosure K) H.field)
    letI : IsNonarchimedeanLocalField
        (abstractFixedField K (SeparableClosure K) H.field) :=
      finiteExtensionSpectralIsNonarchimedeanLocalField K
        (abstractFixedField K (SeparableClosure K) H.field)
    ((((localHenselianValuation K).valuationAt H
          (abstractFixedFieldUnitsEquivGaloisFixed
            K (SeparableClosure K) H.field (Additive.ofMul x))) :
        (localHenselianValuation K).valueGroup) : ZHat) =
      Int.castRingHom ZHat
        (IsNonarchimedeanLocalField.valuationMap
          (abstractFixedField K (SeparableClosure K) H.field)
          (Additive.ofMul x)) := by
  let F := abstractFixedField K (SeparableClosure K) H.field
  let : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H.field H.finite
  let : NontriviallyNormedField F :=
    finiteExtensionSpectralNormedField K F
  let : ValuativeRel F := finiteExtensionSpectralValuativeRel K F
  let : IsNonarchimedeanLocalField F :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K F
  let : Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation F) :=
    finiteExtensionSpectralValuation_hasExtension K F
  let hIntegralClosure : IsIntegralClosure 𝒪[F] 𝒪[K] F :=
    localCompleteDVF_integerRing_isIntegralClosure K F
  let a :=
    abstractFixedFieldUnitsEquivGaloisFixed
      K (SeparableClosure K) H.field (Additive.ofMul x)
  let f := Module.finrank 𝓀[K] 𝓀[F]
  let z :=
    Int.castRingHom ZHat
      (IsNonarchimedeanLocalField.valuationMap F (Additive.ofMul x))
  have hdegree :
      (H.residueDegree (localResidueDatum K) : ℕ) = f := by
    have hdegreeRaw :=
      localResidueDatum_residueDegree_eq_residueFinrank K H
    exact hdegreeRaw.trans (by
        apply Nat.pow_right_injective
          (Finite.one_lt_card : 2 ≤ Nat.card 𝓀[K])
        calc
          _ = Nat.card 𝓀[F] := by
            symm
            refine @Module.natCard_eq_pow_finrank 𝓀[K] 𝓀[F] _ _ ?_ ?_
            refine @Module.Finite.of_finite 𝓀[K] 𝓀[F] _ _ ?_ ?_
            infer_instance
          _ = Nat.card 𝓀[F] := rfl
          _ = _ := by
            dsimp only [f]
            refine @Module.natCard_eq_pow_finrank 𝓀[K] 𝓀[F] _ _ ?_ ?_
            refine @Module.Finite.of_finite 𝓀[K] 𝓀[F] _ _ ?_ ?_
            infer_instance)
  have hnorm :
      (localHenselianValuation K).normCompositeAt H a =
        f • z := by
    change localBaseValuation K
        (normToBase
          (galoisAmbientUnitsRep K (SeparableClosure K)) H.field a) =
      f • z
    rw [show a =
      abstractFixedFieldUnitsEquivGaloisFixed
        K (SeparableClosure K) H.field (Additive.ofMul x) from rfl]
    rw [localBaseValuation_normToBase_abstractFixedFieldUnit]
    change Int.castRingHom ZHat
        (IsNonarchimedeanLocalField.valuationMap K
          (Additive.ofMul (normUnits K F x))) =
      f • Int.castRingHom ZHat
        (IsNonarchimedeanLocalField.valuationMap F
          (Additive.ofMul x))
    have hnormInt :=
      @v_normUnits_eq_residue_finrank_mul_of_isSeparable
        K F _ _ _ _ _ _ _ _ _ _ _ _ hIntegralClosure x
    have hnormInt' : IsNonarchimedeanLocalField.valuationMap K
        (Additive.ofMul (normUnits K F x)) =
      (f : Int) *
        IsNonarchimedeanLocalField.valuationMap F
          (Additive.ofMul x) := by
      convert hnormInt using 3
      all_goals try rfl
      all_goals (simp only [f]; congr!)
      all_goals first
        | exact residueAlgebra_eq
        | exact residueModule_eq
        | (rw [residueAlgebra_eq]; exact residueModule_eq)
        | (simp only [residueAlgebra_eq]; exact residueModule_eq)
        | (convert residueModule_eq using 2; exact residueAlgebra_eq)
    rw [hnormInt', ← map_nsmul]
    rfl
  have hnorm' :
      (localHenselianValuation K).normCompositeAt H a =
        (H.residueDegree (localResidueDatum K) : ℕ) • z := by
    rw [hdegree]
    exact hnorm
  rw [(localHenselianValuation K).valuationAt_coe]
  change zHatDivide (H.residueDegree (localResidueDatum K) : ℕ)
      (H.residueDegree (localResidueDatum K)).pos
      ((localHenselianValuation K).normCompositeAtInResidueImage H a) = z
  have hsub :
      (localHenselianValuation K).normCompositeAtInResidueImage H a =
        ⟨zHatMulNat (H.residueDegree (localResidueDatum K) : ℕ) z,
          ⟨z, rfl⟩⟩ := by
    apply Subtype.ext
    change (localHenselianValuation K).normCompositeAt H a =
      zHatMulNat (H.residueDegree (localResidueDatum K) : ℕ) z
    simpa only [zHatMulNat_apply] using hnorm'
  exact (congrArg (zHatDivide (H.residueDegree (localResidueDatum K) : ℕ)
      (H.residueDegree (localResidueDatum K)).pos) hsub).trans
    (zHatDivide_zHatMulNat (H.residueDegree (localResidueDatum K) : ℕ)
      (H.residueDegree (localResidueDatum K)).pos z)

/-- A separable-closure equivalence extending an embedding of a finite
separable local extension identifies the two uniquely extended local
valuation rings. -/
theorem localSeparableValuationSubring_eq_comap_finiteExtensionEquiv
    (K F : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    (i : F →ₐ[K] SeparableClosure K) :
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    letI : Algebra.IsSeparable F (SeparableClosure K) :=
      Algebra.isSeparable_tower_top_of_isSeparable
        K F (SeparableClosure K)
    letI : IsSepClosure F (SeparableClosure K) :=
      ⟨inferInstance, inferInstance⟩
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      localSeparableValuationSubring F =
        (localSeparableValuationSubring K).comap e.toRingHom := by
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  let : Algebra.IsSeparable F (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      K F (SeparableClosure K)
  let : IsSepClosure F (SeparableClosure K) :=
    ⟨inferInstance, inferInstance⟩
  intro e
  let A := localSeparableValuationSubring K
  let B := A.comap e.toRingHom
  have hcomap :
      A.comap i.toRingHom =
        (ValuativeRel.valuation F).valuationSubring :=
    localSeparableValuationSubring_comap_embedding K F i
  have hBext :
      (localCompleteDVF F).valuation.HasExtension B.valuation := by
    apply
      ValuationTheory.DiscreteValuationField.Valuation.hasExtension_valuation_of_valuationSubring_pullback
    intro x
    change e (algebraMap F (SeparableClosure F) x) ∈ A ↔
      x ∈ (localCompleteDVF F).valuation.valuationSubring
    rw [e.commutes]
    change x ∈ A.comap i.toRingHom ↔
      x ∈ (ValuativeRel.valuation F).valuationSubring
    rw [hcomap]
  let : (localCompleteDVF F).valuation.HasExtension B.valuation :=
    hBext
  exact localSeparableValuationSubring_eq_of_hasExtension F B

/-- After identifying separable closures over a finite separable local
extension, the ambient selected valuation ring is stabilized by the whole
absolute Galois group of the extension field. -/
theorem localSeparableDecompositionGroup_eq_top_finiteExtensionEquiv
    (K F : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    (i : F →ₐ[K] SeparableClosure K) :
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    letI : Algebra.IsSeparable F (SeparableClosure K) :=
      Algebra.isSeparable_tower_top_of_isSeparable
        K F (SeparableClosure K)
    letI : IsSepClosure F (SeparableClosure K) :=
      ⟨inferInstance, inferInstance⟩
    ∀ _e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      decompositionGroup F (localSeparableValuationSubring K) = ⊤ := by
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  let : Algebra.IsSeparable F (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      K F (SeparableClosure K)
  let : IsSepClosure F (SeparableClosure K) :=
    ⟨inferInstance, inferInstance⟩
  intro e
  let A := localSeparableValuationSubring K
  let AF := localSeparableValuationSubring F
  have hAF :
      AF = A.comap e.toRingHom :=
    localSeparableValuationSubring_eq_comap_finiteExtensionEquiv
      K F i e
  have hAFtop :
      decompositionGroup F AF = ⊤ :=
    localSeparableDecompositionGroup_eq_top F
  apply top_unique
  intro sigma _hsigma
  let sigmaF : Gal(SeparableClosure F / F) :=
    AlgEquiv.autCongr e.symm sigma
  have hsigmaF :
      sigmaF • AF = AF := by
    have :
        sigmaF ∈ decompositionGroup F AF := by
      rw [hAFtop]
      trivial
    change sigmaF • AF = AF at this
    exact this
  change sigma • A = A
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have hmem (z : SeparableClosure K) :
      e.symm z ∈ AF ↔ z ∈ A := by
    rw [hAF]
    change e (e.symm z) ∈ A ↔ z ∈ A
    rw [e.apply_symm_apply]
  rw [← hmem (sigma⁻¹ • x), ← hmem x]
  have hx :=
    congrArg
      (fun B : ValuationSubring (SeparableClosure F) =>
        e.symm x ∈ B)
      hsigmaF
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hx
  simpa [sigmaF, AlgEquiv.autCongr_apply] using hx.to_iff

@[implicit_reducible]
noncomputable def finiteExtensionDecompositionResidueFintype
    (K F : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    (i : F →ₐ[K] SeparableClosure K) :
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    letI : Algebra.IsSeparable F (SeparableClosure K) :=
      Algebra.isSeparable_tower_top_of_isSeparable
        K F (SeparableClosure K)
    letI : IsSepClosure F (SeparableClosure K) :=
      ⟨inferInstance, inferInstance⟩
    ∀ _e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      Fintype (decompositionResidueField F
        (localSeparableValuationSubring K)) := by
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  letI : Algebra.IsSeparable F (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      K F (SeparableClosure K)
  letI : IsSepClosure F (SeparableClosure K) :=
    ⟨inferInstance, inferInstance⟩
  intro _e
  let A := localSeparableValuationSubring K
  let C := (ValuativeRel.valuation F).valuationSubring
  have hcomap :
      A.comap (algebraMap F (SeparableClosure K)) = C := by
    change A.comap i.toRingHom =
      (ValuativeRel.valuation F).valuationSubring
    exact localSeparableValuationSubring_comap_embedding K F i
  have htop : decompositionGroup F A = ⊤ :=
    localSeparableDecompositionGroup_eq_top_finiteExtensionEquiv
      K F i _e
  let residueEquiv :
      IsLocalRing.ResidueField C ≃+*
        decompositionResidueField F A :=
    residueFieldEquivDecompositionResidueOfEqTop A C hcomap htop
  letI : Finite (IsLocalRing.ResidueField C) := by
    change Finite 𝓀[F]
    infer_instance
  letI : Fintype (IsLocalRing.ResidueField C) :=
    Fintype.ofFinite _
  exact Fintype.ofEquiv _ residueEquiv.toEquiv

/-- The intrinsic residue degree of a finite separable local extension is
unchanged after moving its separable closure into the ambient separable
closure of the base field. -/
theorem
    localResidueDegree_eq_residueAbsoluteDegreeIn_finiteExtensionEquiv
    (K F : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    (i : F →ₐ[K] SeparableClosure K) :
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    letI : Algebra.IsSeparable F (SeparableClosure K) :=
      Algebra.isSeparable_tower_top_of_isSeparable
        K F (SeparableClosure K)
    letI : IsSepClosure F (SeparableClosure K) :=
      ⟨inferInstance, inferInstance⟩
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (sigma : Gal(SeparableClosure F / F)),
      letI : Fintype (decompositionResidueField F
          (localSeparableValuationSubring K)) :=
        finiteExtensionDecompositionResidueFintype K F i e
      localResidueDegree F sigma =
        residueAbsoluteDegreeIn
          (decompositionResidueField F
            (localSeparableValuationSubring K))
          (selectedResidueField
            (localSeparableValuationSubring K))
          (residueAlgActionOfEqTop F
            (localSeparableValuationSubring K)
            (localSeparableDecompositionGroup_eq_top_finiteExtensionEquiv
              K F i e)
            (AlgEquiv.autCongr e sigma)) := by
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  let : Algebra.IsSeparable F (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      K F (SeparableClosure K)
  let : IsSepClosure F (SeparableClosure K) :=
    ⟨inferInstance, inferInstance⟩
  intro e sigma
  let : Fintype (decompositionResidueField F
      (localSeparableValuationSubring K)) :=
    finiteExtensionDecompositionResidueFintype K F i e
  let A := localSeparableValuationSubring K
  let AF := localSeparableValuationSubring F
  let C := (ValuativeRel.valuation F).valuationSubring
  let kF := IsLocalRing.ResidueField C
  let kA := decompositionResidueField F A
  let kAF := decompositionResidueField F AF
  let OmegaA := selectedResidueField A
  let OmegaF := selectedResidueField AF
  have hAcomap :
      A.comap (algebraMap F (SeparableClosure K)) = C := by
    change A.comap i.toRingHom =
      (ValuativeRel.valuation F).valuationSubring
    exact localSeparableValuationSubring_comap_embedding K F i
  have hAFcomap :
      AF.comap (algebraMap F (SeparableClosure F)) = C := by
    ext x
    exact localSeparableValuationSubring_pullback F x
  have hAtop :
      decompositionGroup F A = ⊤ :=
    localSeparableDecompositionGroup_eq_top_finiteExtensionEquiv
      K F i e
  have hAFtop :
      decompositionGroup F AF = ⊤ :=
    localSeparableDecompositionGroup_eq_top F
  let eA : kF ≃+* kA :=
    residueFieldEquivDecompositionResidueOfEqTop
      A C hAcomap hAtop
  let eAF : kF ≃+* kAF :=
    residueFieldEquivDecompositionResidueOfEqTop
      AF C hAFcomap hAFtop
  let tau : kAF ≃+* kA :=
    eAF.symm.trans eA
  have hAF :
      AF = A.comap e.toRingHom :=
    localSeparableValuationSubring_eq_comap_finiteExtensionEquiv
      K F i e
  let r : AF ≃+* A :=
    valuationSubringEquivOfComapEq A AF e.toRingEquiv hAF
  let eResidue : OmegaF ≃+* OmegaA :=
    IsLocalRing.ResidueField.mapEquiv r
  have hr (x : AF) :
      ((r x : A) : SeparableClosure K) =
        e (x : SeparableClosure F) := by
    rfl
  have heResidue (x : kAF) :
      eResidue (algebraMap kAF OmegaF x) =
        algebraMap kA OmegaA (tau x) := by
    obtain ⟨y, rfl⟩ := eAF.surjective x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    rw [residueFieldEquivDecompositionResidueOfEqTop_algebraMap]
    have htau :
        tau (eAF (IsLocalRing.residue C a)) =
          eA (IsLocalRing.residue C a) := by
      simp [tau]
    rw [htau]
    change IsLocalRing.ResidueField.map r
        (IsLocalRing.residue AF _) =
      algebraMap kA OmegaA
        (eA (IsLocalRing.residue C a))
    rw [IsLocalRing.ResidueField.map_residue,
      residueFieldEquivDecompositionResidueOfEqTop_algebraMap]
    congr 1
    apply Subtype.ext
    exact (hr _).trans (e.commutes (a : F))
  let rhoF : OmegaF ≃ₐ[kAF] OmegaF :=
    localSeparableResidueAlgAction F sigma
  let rhoA : OmegaA ≃ₐ[kA] OmegaA :=
    residueAlgActionOfEqTop F A hAtop
      (AlgEquiv.autCongr e sigma)
  let conjugate : OmegaA ≃ₐ[kA] OmegaA :=
    { eResidue.symm.trans (rhoF.toRingEquiv.trans eResidue) with
      commutes' := fun x => by
        change eResidue
            (rhoF (eResidue.symm (algebraMap kA OmegaA x))) =
          algebraMap kA OmegaA x
        have hpre :
            eResidue.symm (algebraMap kA OmegaA x) =
              algebraMap kAF OmegaF (tau.symm x) := by
          apply eResidue.injective
          rw [eResidue.apply_symm_apply, heResidue,
            tau.apply_symm_apply]
        rw [hpre, rhoF.commutes, heResidue,
          tau.apply_symm_apply] }
  have hconjugate : conjugate = rhoA := by
    apply AlgEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := eResidue.surjective x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    change eResidue
        (rhoF (eResidue.symm
          (eResidue (IsLocalRing.residue AF a)))) =
      rhoA (eResidue (IsLocalRing.residue AF a))
    rw [eResidue.symm_apply_apply]
    change IsLocalRing.ResidueField.map r
        (residueAlgActionOfEqTop F AF hAFtop sigma
          (IsLocalRing.residue AF a)) =
      residueAlgActionOfEqTop F A hAtop
        (AlgEquiv.autCongr e sigma)
        (IsLocalRing.ResidueField.map r
          (IsLocalRing.residue AF a))
    dsimp only [residueAlgActionOfEqTop]
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
      decompositionGroupResidueAction_residue,
      IsLocalRing.ResidueField.map_residue,
      IsLocalRing.ResidueField.map_residue,
      decompositionGroupResidueAction_residue]
    congr 1
    apply Subtype.ext
    change e (sigma (a : SeparableClosure F)) =
      AlgEquiv.autCongr e sigma (e (a : SeparableClosure F))
    simp [AlgEquiv.autCongr_apply]
  change residueAbsoluteDegreeIn kAF OmegaF rhoF =
    residueAbsoluteDegreeIn kA OmegaA rhoA
  rw [← hconjugate]
  exact
    (residueAbsoluteDegreeIn_semilinear_conjugation
      kAF OmegaF tau eResidue heResidue rhoF).symm

/-- Local residue degree is invariant under a semilinear equivalence of
local fields and separable closures that carries the selected extension
valuation ring to the selected extension valuation ring. -/
theorem localResidueDegree_semilinear_conjugation
    (K F : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (phi : K ≃+* F)
    (e : SeparableClosure K ≃+* SeparableClosure F)
    (he : ∀ x : K,
      e (algebraMap K (SeparableClosure K) x) =
        algebraMap F (SeparableClosure F) (phi x))
    (hvaluation :
      localSeparableValuationSubring K =
        (localSeparableValuationSubring F).comap e.toRingHom)
    (sigma : Gal(SeparableClosure K / K)) :
    let sigmaF : Gal(SeparableClosure F / F) :=
      { e.symm.trans (sigma.toRingEquiv.trans e) with
        commutes' := fun x => by
          change e (sigma (e.symm
            (algebraMap F (SeparableClosure F) x))) =
              algebraMap F (SeparableClosure F) x
          have hpre :
              e.symm (algebraMap F (SeparableClosure F) x) =
                algebraMap K (SeparableClosure K) (phi.symm x) := by
            apply e.injective
            rw [e.apply_symm_apply, he, phi.apply_symm_apply]
          rw [hpre, sigma.commutes, he, phi.apply_symm_apply] }
    localResidueDegree F sigmaF =
      localResidueDegree K sigma := by
  dsimp only
  let AK := localSeparableValuationSubring K
  let AF := localSeparableValuationSubring F
  let CK := (localCompleteDVF K).valuation.valuationSubring
  let CF := (localCompleteDVF F).valuation.valuationSubring
  let kK := IsLocalRing.ResidueField CK
  let kF := IsLocalRing.ResidueField CF
  let kAK := decompositionResidueField K AK
  let kAF := decompositionResidueField F AF
  let OmegaK := selectedResidueField AK
  let OmegaF := selectedResidueField AF
  have hbase (x : K) :
      x ∈ CK ↔ phi x ∈ CF := by
    change
      x ∈ (localCompleteDVF K).valuation.valuationSubring ↔
        phi x ∈ (localCompleteDVF F).valuation.valuationSubring
    rw [← localSeparableValuationSubring_pullback K x,
      ← localSeparableValuationSubring_pullback F (phi x)]
    rw [hvaluation]
    change
      e (algebraMap K (SeparableClosure K) x) ∈ AF ↔
        algebraMap F (SeparableClosure F) (phi x) ∈ AF
    rw [he]
  let rBase : CK ≃+* CF := {
    toFun := fun x =>
      ⟨phi (x : K), (hbase (x : K)).1 x.property⟩
    invFun := fun y =>
      ⟨phi.symm (y : F), (hbase (phi.symm (y : F))).2 (by
        simpa only [phi.apply_symm_apply] using y.property)⟩
    left_inv := fun x => by
      ext
      simp
    right_inv := fun y => by
      ext
      simp
    map_mul' := fun x y => by
      ext
      simp
    map_add' := fun x y => by
      ext
      simp }
  let eBaseResidue : kK ≃+* kF :=
    IsLocalRing.ResidueField.mapEquiv rBase
  let r : AK ≃+* AF :=
    valuationSubringEquivOfComapEq AF AK e hvaluation
  let eResidue : OmegaK ≃+* OmegaF :=
    IsLocalRing.ResidueField.mapEquiv r
  have hr (x : AK) :
      ((r x : AF) : SeparableClosure F) =
        e (x : SeparableClosure K) := by
    rfl
  let bK : kK ≃+* kAK :=
    localBaseResidueEquivDecompositionResidue K
  let bF : kF ≃+* kAF :=
    localBaseResidueEquivDecompositionResidue F
  let tau : kAK ≃+* kAF :=
    bK.symm.trans (eBaseResidue.trans bF)
  have heResidue (x : kAK) :
      eResidue (algebraMap kAK OmegaK x) =
        algebraMap kAF OmegaF (tau x) := by
    obtain ⟨y, rfl⟩ := bK.surjective x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    rw [localBaseResidueEquivDecompositionResidue_algebraMap]
    have htau :
        tau (bK (IsLocalRing.residue CK a)) =
          bF (eBaseResidue (IsLocalRing.residue CK a)) := by
      simp [tau]
    rw [htau]
    change IsLocalRing.ResidueField.map r
        (IsLocalRing.residue AK _) =
      algebraMap kAF OmegaF
        (bF (IsLocalRing.ResidueField.map rBase
          (IsLocalRing.residue CK a)))
    rw [IsLocalRing.ResidueField.map_residue,
      IsLocalRing.ResidueField.map_residue,
      localBaseResidueEquivDecompositionResidue_algebraMap]
    congr 1
    apply Subtype.ext
    exact (hr _).trans (he (a : K))
  let sigmaF : Gal(SeparableClosure F / F) :=
    { e.symm.trans (sigma.toRingEquiv.trans e) with
      commutes' := fun x => by
        change e (sigma (e.symm
          (algebraMap F (SeparableClosure F) x))) =
            algebraMap F (SeparableClosure F) x
        have hpre :
            e.symm (algebraMap F (SeparableClosure F) x) =
              algebraMap K (SeparableClosure K) (phi.symm x) := by
          apply e.injective
          rw [e.apply_symm_apply, he, phi.apply_symm_apply]
        rw [hpre, sigma.commutes, he, phi.apply_symm_apply] }
  let rhoK : OmegaK ≃ₐ[kAK] OmegaK :=
    localSeparableResidueAlgAction K sigma
  let rhoF : OmegaF ≃ₐ[kAF] OmegaF :=
    localSeparableResidueAlgAction F sigmaF
  let conjugate : OmegaF ≃ₐ[kAF] OmegaF :=
    { eResidue.symm.trans (rhoK.toRingEquiv.trans eResidue) with
      commutes' := fun x => by
        change eResidue
            (rhoK (eResidue.symm (algebraMap kAF OmegaF x))) =
          algebraMap kAF OmegaF x
        have hpre :
            eResidue.symm (algebraMap kAF OmegaF x) =
              algebraMap kAK OmegaK (tau.symm x) := by
          apply eResidue.injective
          rw [eResidue.apply_symm_apply, heResidue,
            tau.apply_symm_apply]
        rw [hpre, rhoK.commutes, heResidue,
          tau.apply_symm_apply] }
  have hconjugate : conjugate = rhoF := by
    apply AlgEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := eResidue.surjective x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    change eResidue
        (rhoK (eResidue.symm
          (eResidue (IsLocalRing.residue AK a)))) =
      rhoF (eResidue (IsLocalRing.residue AK a))
    rw [eResidue.symm_apply_apply]
    change IsLocalRing.ResidueField.map r
        (residueAlgActionOfEqTop K AK
          (localSeparableDecompositionGroup_eq_top K) sigma
          (IsLocalRing.residue AK a)) =
      residueAlgActionOfEqTop F AF
        (localSeparableDecompositionGroup_eq_top F) sigmaF
        (IsLocalRing.ResidueField.map r
          (IsLocalRing.residue AK a))
    dsimp only [residueAlgActionOfEqTop]
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
      decompositionGroupResidueAction_residue,
      IsLocalRing.ResidueField.map_residue,
      IsLocalRing.ResidueField.map_residue,
      decompositionGroupResidueAction_residue]
    congr 1
    apply Subtype.ext
    change e (sigma (a : SeparableClosure K)) =
      sigmaF (e (a : SeparableClosure K))
    simp [sigmaF]
  change residueAbsoluteDegreeIn kAF OmegaF rhoF =
    residueAbsoluteDegreeIn kAK OmegaK rhoK
  rw [← hconjugate]
  exact
    residueAbsoluteDegreeIn_semilinear_conjugation
      kAK OmegaK tau eResidue heResidue rhoK

/-- Every `F`-algebra equivalence from the standard separable closure of a
finite fixed field `F` to the original ambient separable closure identifies
the two uniquely extended local valuation rings. -/
theorem localSeparableValuationSubring_eq_comap_abstractFixedFieldEquiv
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField (Gal(SeparableClosure K / K)))
    (e : SeparableClosure (finiteFixedField K H) ≃ₐ[
          finiteFixedField K H] SeparableClosure K) :
    letI : FiniteDimensional K
        (finiteFixedField K H) :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) H.field H.finite
    letI : NontriviallyNormedField
        (finiteFixedField K H) :=
      finiteExtensionSpectralNormedField K
        (finiteFixedField K H)
    letI : ValuativeRel
        (finiteFixedField K H) :=
      finiteExtensionSpectralValuativeRel K
        (finiteFixedField K H)
    letI : IsNonarchimedeanLocalField
        (finiteFixedField K H) :=
      finiteExtensionSpectralIsNonarchimedeanLocalField K
        (finiteFixedField K H)
    localSeparableValuationSubring (finiteFixedField K H) =
        (localSeparableValuationSubring K).comap e.toRingHom := by
  let F := abstractFixedField K (SeparableClosure K) H.field
  let : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  let : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H.field H.finite
  let : NontriviallyNormedField F :=
    finiteExtensionSpectralNormedField K F
  let : ValuativeRel F :=
    finiteExtensionSpectralValuativeRel K F
  let : IsNonarchimedeanLocalField F :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K F
  let : Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation F) :=
    finiteExtensionSpectralValuation_hasExtension K F
  let A := localSeparableValuationSubring K
  let B := A.comap e.toRingHom
  have hcomap :
      A.comap
          (abstractFixedField K (SeparableClosure K) H.field).val.toRingHom =
        (ValuativeRel.valuation F).valuationSubring := by
    exact localSeparableValuationSubring_comap_embedding K F
      (abstractFixedField K (SeparableClosure K) H.field).val
  have hBext :
      (localCompleteDVF F).valuation.HasExtension B.valuation := by
    apply
      ValuationTheory.DiscreteValuationField.Valuation.hasExtension_valuation_of_valuationSubring_pullback
    intro x
    change e (algebraMap F (SeparableClosure F) x) ∈ A ↔
      x ∈ (localCompleteDVF F).valuation.valuationSubring
    rw [e.commutes]
    change x ∈
        A.comap
          (abstractFixedField K (SeparableClosure K) H.field).val.toRingHom ↔
      x ∈ (ValuativeRel.valuation F).valuationSubring
    rw [hcomap]
  let : (localCompleteDVF F).valuation.HasExtension B.valuation := hBext
  exact localSeparableValuationSubring_eq_of_hasExtension F B

/-- The residue field presented through the ambient separable closure is
canonically equivalent to the residue intermediate field attached to the
finite fixing subgroup, compatibly with their embeddings into the selected
residue field. -/
theorem exists_abstractFixedFieldResidueEquiv
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField (Gal(SeparableClosure K / K)))
    [FiniteDimensional K (finiteFixedField K H)]
    [NontriviallyNormedField (finiteFixedField K H)]
    [ValuativeRel (finiteFixedField K H)]
    [IsNonarchimedeanLocalField (finiteFixedField K H)]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation (finiteFixedField K H))]
    (e : SeparableClosure (finiteFixedField K H) ≃ₐ[
      finiteFixedField K H] SeparableClosure K) :
    ∃ tau :
        decompositionResidueField (finiteFixedField K H)
            (localSeparableValuationSubring K) ≃+*
          localAbstractFixedResidueIntermediateField K H.field,
      ∀ x : decompositionResidueField (finiteFixedField K H)
          (localSeparableValuationSubring K),
        algebraMap
            (decompositionResidueField (finiteFixedField K H)
              (localSeparableValuationSubring K))
            (selectedResidueField (localSeparableValuationSubring K)) x =
          algebraMap
            (localAbstractFixedResidueIntermediateField K H.field)
            (selectedResidueField (localSeparableValuationSubring K))
            (tau x) := by
  let F := abstractFixedField K (SeparableClosure K) H.field
  let A := localSeparableValuationSubring K
  let C := (ValuativeRel.valuation F).valuationSubring
  let V := (localCompleteDVF K).valuation.valuationSubring
  let kK := IsLocalRing.ResidueField V
  let kF := IsLocalRing.ResidueField C
  let k₀ := decompositionResidueField K A
  let kA := decompositionResidueField F A
  let Omega := selectedResidueField A
  let R := localAbstractFixedResidueIntermediateField K H.field
  let j : F →ₐ[K] SeparableClosure K :=
    (abstractFixedField K (SeparableClosure K) H.field).val
  let : (localCompleteDVF K).valuation.HasExtension C.valuation := by
    apply
      ValuationTheory.DiscreteValuationField.Valuation.hasExtension_valuation_of_valuationSubring_pullback
    intro x
    change ValuativeRel.valuation F (algebraMap K F x) ≤ 1 ↔
      (localCompleteDVF K).valuation x ≤ 1
    rw [_root_.Valuation.HasExtension.val_map_le_one_iff
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    rfl
  have hVC : V.valuation.HasExtension C.valuation := by
    apply
      ValuationTheory.DiscreteValuationField.Valuation.hasExtension_valuation_of_valuationSubring_pullback
    intro x
    simpa only [V, ValuationSubring.valuationSubring_valuation] using
      (ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_pullback_of_hasExtension_valuation
        (localCompleteDVF K).valuation C x)
  have hC : A.comap (algebraMap F (SeparableClosure K)) = C := by
    simpa only [
      RamificationTheory.ValuationSubring.restrictIntermediateField_eq_comap] using
      (ValuationSubring.restrictIntermediateField_eq_of_finite_separable
        (localCompleteDVF K) A
        (abstractFixedField K (SeparableClosure K) H.field) C)
  have htop : decompositionGroup F A = ⊤ :=
    localSeparableDecompositionGroup_eq_top_finiteExtensionEquiv
      K F j e
  let eK : kK ≃+* k₀ :=
    localBaseResidueEquivDecompositionResidue K
  let eA : kF ≃+* kA :=
    residueFieldEquivDecompositionResidueOfEqTop A C hC htop
  let i : V →+* C :=
    ValuationTheory.Valuations.valuationSubringMapOfHasExtension V C hVC
  let bar : kF →+* Omega :=
    (algebraMap kA Omega).comp eA.toRingHom
  let : Algebra kK kF := by
    change Algebra 𝓀[K] 𝓀[F]
    exact IsLocalRing.ResidueField.instAlgebra
  have hbar_base (x : kK) :
      bar (algebraMap kK kF x) =
        algebraMap k₀ Omega (eK x) := by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    have hres :
        algebraMap kK kF (IsLocalRing.residue V a) =
          IsLocalRing.residue C (i a) := by
      change algebraMap 𝓀[K] 𝓀[F]
          (IsLocalRing.residue 𝒪[K] a) =
        IsLocalRing.residue 𝒪[F] (algebraMap 𝒪[K] 𝒪[F] a)
      exact residueField_algebraMap_residue K F a
    rw [hres]
    change algebraMap kA Omega
        (eA (IsLocalRing.residue C (i a))) =
      algebraMap k₀ Omega
        (eK (IsLocalRing.residue V a))
    rw [residueFieldEquivDecompositionResidueOfEqTop_algebraMap]
    have hbase :=
      localBaseResidueEquivDecompositionResidue_algebraMap K a
    change algebraMap k₀ Omega
      (eK (IsLocalRing.residue V a)) = _ at hbase
    rw [hbase]
    congr 1
  let : Algebra k₀ kF :=
    ((algebraMap kK kF).comp eK.symm.toRingHom).toAlgebra
  let barAlg : kF →ₐ[k₀] Omega :=
    { bar with
      commutes' := fun z => by
        change bar (algebraMap kK kF (eK.symm z)) =
          algebraMap k₀ Omega z
        simpa using hbar_base (eK.symm z) }
  have hR : R = barAlg.fieldRange := by
    change IntermediateField.adjoin k₀
        (Set.range (algebraMap kA Omega)) = barAlg.fieldRange
    apply le_antisymm
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro y ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := eA.surjective z
      exact ⟨x, rfl⟩
    · rintro y ⟨x, rfl⟩
      apply IntermediateField.subset_adjoin
      exact ⟨eA x, rfl⟩
  let eRange : kF ≃+* barAlg.fieldRange :=
    (AlgEquiv.ofInjectiveField barAlg).toRingEquiv
  let eTop : kF ≃+* R :=
    eRange.trans
      (IntermediateField.equivOfEq hR.symm).toRingEquiv
  have heTop (x : kF) :
      algebraMap R Omega (eTop x) = bar x := by
    rfl
  let tau : kA ≃+* R := eA.symm.trans eTop
  refine ⟨tau, ?_⟩
  intro x
  change algebraMap kA Omega x =
    algebraMap R Omega (eTop (eA.symm x))
  rw [heTop]
  simp [bar]

theorem residueAbsoluteDegreeIn_eq_normalizedDegree_abstractFixedFieldEquiv
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField (Gal(SeparableClosure K / K)))
    [FiniteDimensional K (finiteFixedField K H)]
    [NontriviallyNormedField (finiteFixedField K H)]
    [ValuativeRel (finiteFixedField K H)]
    [IsNonarchimedeanLocalField (finiteFixedField K H)]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation (finiteFixedField K H))]
    [Fintype (decompositionResidueField (finiteFixedField K H)
      (localSeparableValuationSubring K))]
    (e : SeparableClosure (finiteFixedField K H) ≃ₐ[
      finiteFixedField K H] SeparableClosure K)
    (sigma : Gal(SeparableClosure (finiteFixedField K H) /
      finiteFixedField K H))
    (htop : decompositionGroup (finiteFixedField K H)
      (localSeparableValuationSubring K) = ⊤)
    (tau : decompositionResidueField (finiteFixedField K H)
        (localSeparableValuationSubring K) ≃+*
      localAbstractFixedResidueIntermediateField K H.field)
    (hTau : ∀ x : decompositionResidueField (finiteFixedField K H)
        (localSeparableValuationSubring K),
      algebraMap
          (decompositionResidueField (finiteFixedField K H)
            (localSeparableValuationSubring K))
          (selectedResidueField (localSeparableValuationSubring K)) x =
        algebraMap
          (localAbstractFixedResidueIntermediateField K H.field)
          (selectedResidueField (localSeparableValuationSubring K))
          (tau x)) :
    residueAbsoluteDegreeIn
        (decompositionResidueField (finiteFixedField K H)
          (localSeparableValuationSubring K))
        (selectedResidueField (localSeparableValuationSubring K))
        (residueAlgActionOfEqTop (finiteFixedField K H)
          (localSeparableValuationSubring K) htop
          (AlgEquiv.autCongr e sigma)) =
      (localResidueDatum K).normalizedDegree
        (H.toFiniteResidueAbstractField (localResidueDatum K))
        ((abstractSubgroupEquivGaloisGroup
          K (SeparableClosure K) H.field).symm
            (AlgEquiv.autCongr e sigma)) := by
  let F := finiteFixedField K H
  let : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  let A := localSeparableValuationSubring K
  let k₀ := decompositionResidueField K A
  let kA := decompositionResidueField F A
  let Omega := selectedResidueField A
  let R := localAbstractFixedResidueIntermediateField K H.field
  let eOmega : Omega ≃+* Omega := RingEquiv.refl Omega
  have heOmega (x : kA) :
      eOmega (algebraMap kA Omega x) =
        algebraMap R Omega (tau x) := by
    simpa [F, A, kA, Omega, R, eOmega] using hTau x
  let sigmaH : H.field.toSubgroup :=
    (abstractSubgroupEquivGaloisGroup
      K (SeparableClosure K) H.field).symm
        (AlgEquiv.autCongr e sigma)
  let rhoA : Omega ≃ₐ[kA] Omega :=
    residueAlgActionOfEqTop F A htop
      (AlgEquiv.autCongr e sigma)
  let rhoH : Omega ≃ₐ[R] Omega :=
    localAbstractFixedResidueActionOverIntermediateField
      K H.field sigmaH
  let conjugate : Omega ≃ₐ[R] Omega :=
    { eOmega.symm.trans (rhoA.toRingEquiv.trans eOmega) with
      commutes' :=
        semilinearConjugate_commutes
          tau eOmega heOmega rhoA }
  have hconjugate : conjugate = rhoH := by
    apply AlgEquiv.ext
    intro x
    change residueAlgActionOfEqTop F A htop
        (AlgEquiv.autCongr e sigma) x =
      localSeparableResidueAlgAction K sigmaH.1 x
    have hsigmaH :
        abstractSubgroupEquivGaloisGroup
            K (SeparableClosure K) H.field sigmaH =
          AlgEquiv.autCongr e sigma :=
      (abstractSubgroupEquivGaloisGroup
        K (SeparableClosure K) H.field).apply_symm_apply
          (AlgEquiv.autCongr e sigma)
    rw [localAbstractFixedResidueAction_apply K H.field sigmaH]
    rw [hsigmaH]
  let : Algebra k₀ R := R.algebra
  let : FiniteDimensional k₀ R :=
    localAbstractFixedResidueIntermediateField_finiteDimensional K H.field
  let : Finite R := Module.finite_of_finite k₀
  let : Fintype R := Fintype.ofFinite R
  rw [localResidueDatum_normalizedDegree_eq_residueAbsoluteDegreeIn]
  change residueAbsoluteDegreeIn kA Omega rhoA =
    residueAbsoluteDegreeIn R Omega rhoH
  rw [← hconjugate]
  exact
    (residueAbsoluteDegreeIn_semilinear_conjugation
      kA Omega tau eOmega heOmega rhoA).symm

/-- Changing from the canonical separable closure of a finite fixed field to
the original ambient separable closure identifies its intrinsic local
residue degree with the normalized degree on the corresponding abstract
field. -/
theorem localResidueDegree_eq_normalizedDegree_abstractFixedFieldEquiv
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField (Gal(SeparableClosure K / K)))
    (e : SeparableClosure (finiteFixedField K H) ≃ₐ[
          finiteFixedField K H] SeparableClosure K)
    (sigma : Gal(SeparableClosure (finiteFixedField K H) /
      finiteFixedField K H)) :
    letI : FiniteDimensional K
        (finiteFixedField K H) :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) H.field H.finite
    letI : NontriviallyNormedField
        (finiteFixedField K H) :=
      finiteExtensionSpectralNormedField K
        (finiteFixedField K H)
    letI : ValuativeRel
        (finiteFixedField K H) :=
      finiteExtensionSpectralValuativeRel K
        (finiteFixedField K H)
    letI : IsNonarchimedeanLocalField
        (finiteFixedField K H) :=
      finiteExtensionSpectralIsNonarchimedeanLocalField K
        (finiteFixedField K H)
    localResidueDegree (finiteFixedField K H) sigma =
        (localResidueDatum K).normalizedDegree
          (H.toFiniteResidueAbstractField (localResidueDatum K))
          ((abstractSubgroupEquivGaloisGroup
            K (SeparableClosure K) H.field).symm
              (AlgEquiv.autCongr e sigma)) := by
  let F := abstractFixedField K (SeparableClosure K) H.field
  let : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  let : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H.field H.finite
  let : NontriviallyNormedField F :=
    finiteExtensionSpectralNormedField K F
  let : ValuativeRel F :=
    finiteExtensionSpectralValuativeRel K F
  let : IsNonarchimedeanLocalField F :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K F
  let : Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation F) :=
    finiteExtensionSpectralValuation_hasExtension K F
  let A := localSeparableValuationSubring K
  let kA := decompositionResidueField F A
  let j : F →ₐ[K] SeparableClosure K :=
    (abstractFixedField K (SeparableClosure K) H.field).val
  have htop : decompositionGroup F A = ⊤ :=
    localSeparableDecompositionGroup_eq_top_finiteExtensionEquiv
      K F j e
  obtain ⟨tau, hTau⟩ := exists_abstractFixedFieldResidueEquiv K H e
  let : Fintype kA :=
    finiteExtensionDecompositionResidueFintype K F j e
  have hlocal :
      localResidueDegree F sigma =
        residueAbsoluteDegreeIn kA (selectedResidueField A)
          (residueAlgActionOfEqTop F A htop
            (AlgEquiv.autCongr e sigma)) :=
    localResidueDegree_eq_residueAbsoluteDegreeIn_finiteExtensionEquiv
      K F j e sigma
  rw [hlocal]
  exact
    residueAbsoluteDegreeIn_eq_normalizedDegree_abstractFixedFieldEquiv
      K H e sigma htop tau hTau

/-- The intrinsic residue degree of an arbitrary finite separable local
extension agrees with the normalized degree on the ambient fixing subgroup
cut out by an embedding into the base separable closure.  Thus the
fixed-field comparison does not require the extension field itself to be
definitionally a fixed-field subtype. -/
theorem
    localResidueDegree_eq_normalizedDegree_finiteExtensionEquiv
    (K F : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    (i : F →ₐ[K] SeparableClosure K) :
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (sigma : Gal(SeparableClosure F / F)),
      let H₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)
      letI hHabsolute : Finite
          ((baseField
            (Gal(SeparableClosure K / K))).toSubgroup ⧸
            extensionSubgroup
              (baseField (Gal(SeparableClosure K / K)))
              H₀ (le_baseField H₀)) := by
        let : FiniteDimensional K (AlgHom.fieldRange i) :=
          (AlgEquiv.ofInjectiveField i).toLinearEquiv.finiteDimensional
        let G := Gal(SeparableClosure K / K)
        let Bases := { B : ClosedSubgroup G //
          H₀.toSubgroup ≤ B.toSubgroup }
        let Bfix : Bases :=
          ⟨closedFixingSubgroup K (SeparableClosure K)
              (⊥ : IntermediateField K (SeparableClosure K)),
            fixingSubgroupLeBase K (SeparableClosure K)
              (AlgHom.fieldRange i)⟩
        let Bbase : Bases :=
          ⟨baseField G, le_baseField H₀⟩
        let Q : Bases → Type := fun B =>
          B.1.toSubgroup ⧸ extensionSubgroup B.1 H₀ B.2
        have hBase : Bfix = Bbase := by
          apply Subtype.ext
          exact closedFixingSubgroup_bot_eq_baseField
            K (SeparableClosure K)
        let : Finite (Q Bfix) := by
          change Finite
            ((closedFixingSubgroup K (SeparableClosure K)
                (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup ⧸
              extensionSubgroup
                (closedFixingSubgroup K (SeparableClosure K)
                  (⊥ : IntermediateField K (SeparableClosure K)))
                H₀
                (fixingSubgroupLeBase K (SeparableClosure K)
                  (AlgHom.fieldRange i)))
          infer_instance
        change Finite (Q Bbase)
        exact Finite.of_equiv (Q Bfix)
          (Equiv.cast (congrArg Q hBase))
      let H : FiniteAbstractField
          (Gal(SeparableClosure K / K)) :=
        ⟨H₀, hHabsolute⟩
      let F₀ :=
        abstractFixedField K (SeparableClosure K) H₀
      let hfixed :
          F₀ = AlgHom.fieldRange i :=
        InfiniteGalois.fixedField_fixingSubgroup
          (AlgHom.fieldRange i)
      let phi : F ≃+* F₀ :=
        ((i.equivFieldRange).trans
          (IntermediateField.equivOfEq hfixed.symm)).toRingEquiv
      let rho : Gal(SeparableClosure K / F₀) :=
        { e.symm.toRingEquiv.trans
            (sigma.toRingEquiv.trans e.toRingEquiv) with
          commutes' := fun x => by
            change e (sigma (e.symm
              (algebraMap F₀ (SeparableClosure K) x))) =
                algebraMap F₀ (SeparableClosure K) x
            have hpre :
                e.symm
                    (algebraMap F₀ (SeparableClosure K) x) =
                  algebraMap F (SeparableClosure F) (phi.symm x) := by
              apply e.injective
              rw [e.apply_symm_apply, e.commutes]
              change (x : SeparableClosure K) =
                i (phi.symm x)
              rw [← show
                ((phi (phi.symm x) : F₀) :
                    SeparableClosure K) =
                  i (phi.symm x) by rfl,
                phi.apply_symm_apply]
            rw [hpre, sigma.commutes, e.commutes]
            change i (phi.symm x) = (x : SeparableClosure K)
            rw [← show
              ((phi (phi.symm x) : F₀) :
                  SeparableClosure K) =
                i (phi.symm x) by rfl,
              phi.apply_symm_apply] }
      localResidueDegree F sigma =
        (localResidueDatum K).normalizedDegree
          (H.toFiniteResidueAbstractField
            (localResidueDatum K))
          ((abstractSubgroupEquivGaloisGroup
            K (SeparableClosure K) H₀).symm
              rho) := by
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e sigma
  dsimp only
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let hHabsolute : Finite
      ((baseField
        (Gal(SeparableClosure K / K))).toSubgroup ⧸
        extensionSubgroup
          (baseField (Gal(SeparableClosure K / K)))
          H₀ (le_baseField H₀)) := by
    let : FiniteDimensional K (AlgHom.fieldRange i) :=
      (AlgEquiv.ofInjectiveField i).toLinearEquiv.finiteDimensional
    let G := Gal(SeparableClosure K / K)
    let Bases := { B : ClosedSubgroup G //
      H₀.toSubgroup ≤ B.toSubgroup }
    let Bfix : Bases :=
      ⟨closedFixingSubgroup K (SeparableClosure K)
          (⊥ : IntermediateField K (SeparableClosure K)),
        fixingSubgroupLeBase K (SeparableClosure K)
          (AlgHom.fieldRange i)⟩
    let Bbase : Bases :=
      ⟨baseField G, le_baseField H₀⟩
    let Q : Bases → Type := fun B =>
      B.1.toSubgroup ⧸ extensionSubgroup B.1 H₀ B.2
    have hBase : Bfix = Bbase := by
      apply Subtype.ext
      exact closedFixingSubgroup_bot_eq_baseField
        K (SeparableClosure K)
    let : Finite (Q Bfix) := by
      change Finite
        ((closedFixingSubgroup K (SeparableClosure K)
            (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup ⧸
          extensionSubgroup
            (closedFixingSubgroup K (SeparableClosure K)
              (⊥ : IntermediateField K (SeparableClosure K)))
            H₀
            (fixingSubgroupLeBase K (SeparableClosure K)
              (AlgHom.fieldRange i)))
      infer_instance
    change Finite (Q Bbase)
    exact Finite.of_equiv (Q Bfix)
      (Equiv.cast (congrArg Q hBase))
  let H : FiniteAbstractField
      (Gal(SeparableClosure K / K)) :=
    ⟨H₀, hHabsolute⟩
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H₀
  let : FiniteDimensional K F₀ :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H₀ hHabsolute
  let : NontriviallyNormedField F₀ :=
    finiteExtensionSpectralNormedField K F₀
  let : ValuativeRel F₀ :=
    finiteExtensionSpectralValuativeRel K F₀
  let : IsNonarchimedeanLocalField F₀ :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K F₀
  let : Algebra.IsSeparable F₀ (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      K F₀ (SeparableClosure K)
  let : IsSepClosure F₀ (SeparableClosure K) :=
    ⟨inferInstance, inferInstance⟩
  let : Algebra F₀ (SeparableClosure F₀) :=
    (separableClosure F₀ (AlgebraicClosure F₀)).algebra
  let e₀ : SeparableClosure F₀ ≃ₐ[F₀] SeparableClosure K :=
    IsSepClosure.equiv F₀
      (SeparableClosure F₀) (SeparableClosure K)
  have hfixed :
      F₀ = AlgHom.fieldRange i :=
    InfiniteGalois.fixedField_fixingSubgroup
      (AlgHom.fieldRange i)
  let phiAlg : F ≃ₐ[K] F₀ :=
    (i.equivFieldRange).trans
      (IntermediateField.equivOfEq hfixed.symm)
  let phi : F ≃+* F₀ := phiAlg.toRingEquiv
  let c : SeparableClosure F ≃+* SeparableClosure F₀ :=
    e.toRingEquiv.trans e₀.symm.toRingEquiv
  have hc (x : F) :
      c (algebraMap F (SeparableClosure F) x) =
        algebraMap F₀ (SeparableClosure F₀) (phi x) := by
    change e₀.symm
        (e (algebraMap F (SeparableClosure F) x)) =
      algebraMap F₀ (SeparableClosure F₀) (phi x)
    apply e₀.injective
    rw [e₀.apply_symm_apply, e.commutes, e₀.commutes]
    rfl
  have hvaluation :
      localSeparableValuationSubring F =
        (localSeparableValuationSubring F₀).comap
          c.toRingHom := by
    have hF :=
      localSeparableValuationSubring_eq_comap_finiteExtensionEquiv
        K F i e
    have hF₀ :=
      localSeparableValuationSubring_eq_comap_abstractFixedFieldEquiv
        K H e₀
    rw [hF, hF₀]
    ext x
    change
      e x ∈ localSeparableValuationSubring K ↔
        e₀ (c x) ∈ localSeparableValuationSubring K
    change
      e x ∈ localSeparableValuationSubring K ↔
        e₀ (e₀.symm (e x)) ∈ localSeparableValuationSubring K
    rw [e₀.apply_symm_apply]
  let sigma₀ : Gal(SeparableClosure F₀ / F₀) :=
    { c.symm.trans (sigma.toRingEquiv.trans c) with
      commutes' := fun x => by
        change c (sigma (c.symm
          (algebraMap F₀ (SeparableClosure F₀) x))) =
            algebraMap F₀ (SeparableClosure F₀) x
        have hc' :
            c.symm
                (algebraMap F₀ (SeparableClosure F₀) x) =
              algebraMap F (SeparableClosure F) (phi.symm x) := by
          apply c.injective
          rw [c.apply_symm_apply, hc, phi.apply_symm_apply]
        rw [hc', sigma.commutes, hc, phi.apply_symm_apply] }
  let rho : Gal(SeparableClosure K / F₀) :=
    { e.symm.toRingEquiv.trans
        (sigma.toRingEquiv.trans e.toRingEquiv) with
      commutes' := fun x => by
        change e (sigma (e.symm
          (algebraMap F₀ (SeparableClosure K) x))) =
            algebraMap F₀ (SeparableClosure K) x
        have hpre :
            e.symm
                (algebraMap F₀ (SeparableClosure K) x) =
              algebraMap F (SeparableClosure F) (phi.symm x) := by
          apply e.injective
          rw [e.apply_symm_apply, e.commutes]
          change (x : SeparableClosure K) =
            i (phi.symm x)
          rw [← show
            ((phi (phi.symm x) : F₀) :
                SeparableClosure K) =
              i (phi.symm x) by rfl,
            phi.apply_symm_apply]
        rw [hpre, sigma.commutes, e.commutes]
        change i (phi.symm x) = (x : SeparableClosure K)
        rw [← show
          ((phi (phi.symm x) : F₀) :
              SeparableClosure K) =
            i (phi.symm x) by rfl,
          phi.apply_symm_apply] }
  have hrho :
      AlgEquiv.autCongr e₀ sigma₀ = rho := by
    apply AlgEquiv.ext
    intro x
    simp only [AlgEquiv.autCongr_apply]
    change
      e₀
          (c (sigma (c.symm (e₀.symm x)))) =
        e (sigma (e.symm x))
    rw [show c.symm (e₀.symm x) = e.symm x by
      apply c.injective
      rw [c.apply_symm_apply]
      change e₀.symm x = e₀.symm (e (e.symm x))
      rw [e.apply_symm_apply]]
    change e₀ (e₀.symm (e (sigma (e.symm x)))) =
      e (sigma (e.symm x))
    rw [e₀.apply_symm_apply]
  have hdegree :
      localResidueDegree F₀ sigma₀ =
        localResidueDegree F sigma := by
    simpa only [sigma₀] using
      localResidueDegree_semilinear_conjugation
        F F₀ phi c hc hvaluation sigma
  have hfixedDegree :
      localResidueDegree F₀ sigma₀ =
        (localResidueDatum K).normalizedDegree
          (H.toFiniteResidueAbstractField
            (localResidueDatum K))
          ((abstractSubgroupEquivGaloisGroup
            K (SeparableClosure K) H₀).symm
              (AlgEquiv.autCongr e₀ sigma₀)) := by
    exact
      localResidueDegree_eq_normalizedDegree_abstractFixedFieldEquiv
        K H e₀ sigma₀
  rw [hrho] at hfixedDegree
  change
    localResidueDegree F sigma =
      (localResidueDatum K).normalizedDegree
        (H.toFiniteResidueAbstractField
          (localResidueDatum K))
        ((abstractSubgroupEquivGaloisGroup
          K (SeparableClosure K) H₀).symm rho)
  exact hdegree.symm.trans hfixedDegree


end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_BaseComparison_IntrinsicBaseEquivalence
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.ClassFormation.instIsAddTorsionFreeZHat _root_.ClassFormation.instIsMulTorsionFreeMultiplicativeZHat _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeEquiv_unramifiedFrobenius _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeHom_mk _root_.ClassFormation.DegreeData.finiteUnramifiedRestriction_frobenius _root_.ClassFormation.DegreeData.finiteUnramifiedRestriction_mk _root_.ClassFormation.DegreeData.maximalUnramifiedExtensionRestriction_mk _root_.ClassFormation.DegreeData.maximalUnramifiedFrobeniusPower_one _root_.ClassFormation.DegreeData.maximalUnramifiedRestriction_frobenius _root_.ClassFormation.ValuationData.maximalUnramifiedNormResidue_degree _root_.ClassFormation.toZModPow_zHatToPadicInt _root_.ClassFormation.zHatReductionRingHom_apply _root_.ClassFormation.zHatRingEquivProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToPadicInt_intCast _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_apply _root_.ClassFormation.zHatToProfiniteIntegerPrimeProduct_intCast _root_.ClassFormation.zHatUnitsContinuousMulEquivPrimeProduct_coe_apply _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.KummerTheory.torsionQuotientEquivOfZHatMulDecomposition_mk _root_.KummerTheory.zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Intrinsic-to-ambient base equivalences

This module compares the intrinsic absolute Galois base of a finite extension with its realization as a fixing subgroup in an ambient separable closure.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- The fixing subgroup of the image of a finite extension embedded in
`SeparableClosure K` has finite index in the ambient base-field subgroup. -/
theorem ambientEmbeddedAbsoluteQuotientFinite
    (K F : Type) [Field K] [Field F]
    [Algebra K F] [FiniteDimensional K F]
    (i : F →ₐ[K] SeparableClosure K) :
    let H₀ :=
      closedFixingSubgroup K (SeparableClosure K)
        (AlgHom.fieldRange i)
    Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := by
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let : FiniteDimensional K (AlgHom.fieldRange i) :=
    (AlgEquiv.ofInjectiveField i).toLinearEquiv.finiteDimensional
  let G := Gal(SeparableClosure K / K)
  let Bases := { B : ClosedSubgroup G //
    H₀.toSubgroup ≤ B.toSubgroup }
  let Bfix : Bases :=
    ⟨closedFixingSubgroup K (SeparableClosure K)
        (⊥ : IntermediateField K (SeparableClosure K)),
      fixingSubgroupLeBase K (SeparableClosure K)
        (AlgHom.fieldRange i)⟩
  let Bbase : Bases :=
    ⟨baseField G, le_baseField H₀⟩
  let Q : Bases → Type := fun B =>
    B.1.toSubgroup ⧸ extensionSubgroup B.1 H₀ B.2
  have hBase : Bfix = Bbase := by
    apply Subtype.ext
    exact closedFixingSubgroup_bot_eq_baseField
      K (SeparableClosure K)
  let : Finite (Q Bfix) := by
    change Finite
      ((closedFixingSubgroup K (SeparableClosure K)
          (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup ⧸
        extensionSubgroup
          (closedFixingSubgroup K (SeparableClosure K)
            (⊥ : IntermediateField K (SeparableClosure K)))
          H₀
          (fixingSubgroupLeBase K (SeparableClosure K)
            (AlgHom.fieldRange i)))
    infer_instance
  change Finite (Q Bbase)
  exact Finite.of_equiv (Q Bfix)
    (Equiv.cast (congrArg Q hBase))

/-- On the intrinsic base, the normalized degree from the local residue datum
agrees with the local residue degree of the underlying automorphism. -/
theorem intrinsicBase_normalizedDegree_eq_localResidueDegree
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (τ : (intrinsicAbstractBase F).toSubgroup) :
    (localResidueDatum F).normalizedDegree
        ((intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
          (localResidueDatum F)) τ =
      localResidueDegree F τ.1 := by
  apply Multiplicative.ext
  have h :=
    (localResidueDatum F).residueDegree_nsmul_normalizedDegree
      ((intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
        (localResidueDatum F)) τ
  rw [show
      (((intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
        (localResidueDatum F)).residueDegree : ℕ) = 1 by
    exact intrinsicFiniteAbstractBase_residueDegree_eq_one F] at h
  simpa [localResidueDatum] using h

/-- For an embedded finite separable extension, transport through a
separable-closure equivalence identifies its intrinsic base subgroup with the
ambient subgroup fixing the embedding's field range. -/
noncomputable def
    intrinsicBaseEquivAmbientEmbeddedField
    (K F : Type) [Field K] [Field F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (i : F →ₐ[K] SeparableClosure K) :
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    (e : SeparableClosure F ≃ₐ[F] SeparableClosure K) →
      (intrinsicAbstractBase F).toSubgroup ≃*
        (closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)).toSubgroup := by
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  letI hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨H₀, hHabsolute⟩
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H₀
  letI : FiniteDimensional K F₀ :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H₀ hHabsolute
  letI : Algebra.IsSeparable F₀ (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      K F₀ (SeparableClosure K)
  letI : IsSepClosure F₀ (SeparableClosure K) :=
    ⟨inferInstance, inferInstance⟩
  letI : Algebra F₀ (SeparableClosure F₀) :=
    (separableClosure F₀ (AlgebraicClosure F₀)).algebra
  let e₀ : SeparableClosure F₀ ≃ₐ[F₀] SeparableClosure K :=
    IsSepClosure.equiv F₀
      (SeparableClosure F₀) (SeparableClosure K)
  have hfixed :
      F₀ = AlgHom.fieldRange i :=
    InfiniteGalois.fixedField_fixingSubgroup
      (AlgHom.fieldRange i)
  let phiAlg : F ≃ₐ[K] F₀ :=
    (i.equivFieldRange).trans
      (IntermediateField.equivOfEq hfixed.symm)
  let phi : F ≃+* F₀ := phiAlg.toRingEquiv
  let c : SeparableClosure F ≃+* SeparableClosure F₀ :=
    e.toRingEquiv.trans e₀.symm.toRingEquiv
  have hc (x : F) :
      c (algebraMap F (SeparableClosure F) x) =
        algebraMap F₀ (SeparableClosure F₀) (phi x) := by
    change e₀.symm
        (e (algebraMap F (SeparableClosure F) x)) =
      algebraMap F₀ (SeparableClosure F₀) (phi x)
    apply e₀.injective
    rw [e₀.apply_symm_apply, e.commutes, e₀.commutes]
    rfl
  let theta :
      Gal(SeparableClosure F / F) ≃*
        Gal(SeparableClosure F₀ / F₀) := {
    toFun := fun sigma =>
      { c.symm.trans (sigma.toRingEquiv.trans c) with
        commutes' := fun x => by
          change c (sigma (c.symm
            (algebraMap F₀ (SeparableClosure F₀) x))) =
              algebraMap F₀ (SeparableClosure F₀) x
          have hpre :
              c.symm
                  (algebraMap F₀ (SeparableClosure F₀) x) =
                algebraMap F (SeparableClosure F) (phi.symm x) := by
            apply c.injective
            rw [c.apply_symm_apply, hc, phi.apply_symm_apply]
          rw [hpre, sigma.commutes, hc, phi.apply_symm_apply] }
    invFun := fun tau =>
      { c.trans (tau.toRingEquiv.trans c.symm) with
        commutes' := fun x => by
          change c.symm (tau (c
            (algebraMap F (SeparableClosure F) x))) =
              algebraMap F (SeparableClosure F) x
          rw [hc, tau.commutes]
          apply c.injective
          rw [c.apply_symm_apply, hc] }
    left_inv := fun sigma => by
      apply AlgEquiv.ext
      intro x
      change c.symm
          (c (sigma (c.symm (c x)))) = sigma x
      rw [c.symm_apply_apply, c.symm_apply_apply]
    right_inv := fun tau => by
      apply AlgEquiv.ext
      intro x
      change c
          (c.symm (tau (c (c.symm x)))) = tau x
      rw [c.apply_symm_apply, c.apply_symm_apply]
    map_mul' := fun sigma tau => by
      apply AlgEquiv.ext
      intro x
      change c (sigma (tau (c.symm x))) =
        c (sigma (c.symm (c (tau (c.symm x)))))
      rw [c.symm_apply_apply] }
  let psi₀ :=
    intrinsicBaseEquivAmbientFixedField K H e₀
  exact
    (intrinsicAbstractBaseEquivAbsolute F).trans
      (theta.trans
        ((intrinsicAbstractBaseEquivAbsolute F₀).symm.trans psi₀))

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_EmbeddedFrobeniusTransport
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Embedded Frobenius transport

This module transports inertia, Frobenius elements, and fixed fields across an explicit equivalence of separable closures.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- The intrinsic absolute Galois equivalence induced by an embedding into the
ambient separable closure is continuous. -/
theorem
    intrinsicBaseEquivAmbientEmbeddedField_continuous
    (K F : Type) [Field K] [Field F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (i : F →ₐ[K] SeparableClosure K) :
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      Continuous
        (intrinsicBaseEquivAmbientEmbeddedField K F i e) := by
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨H₀, ambientEmbeddedAbsoluteQuotientFinite K F i⟩
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H₀
  let : FiniteDimensional K F₀ :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H₀ hHabsolute
  let : Algebra.IsSeparable F₀ (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      K F₀ (SeparableClosure K)
  let : IsSepClosure F₀ (SeparableClosure K) :=
    ⟨inferInstance, inferInstance⟩
  let : Algebra F₀ (SeparableClosure F₀) :=
    (separableClosure F₀ (AlgebraicClosure F₀)).algebra
  let e₀ : SeparableClosure F₀ ≃ₐ[F₀] SeparableClosure K :=
    IsSepClosure.equiv F₀
      (SeparableClosure F₀) (SeparableClosure K)
  have hfixed :
      F₀ = AlgHom.fieldRange i :=
    InfiniteGalois.fixedField_fixingSubgroup
      (AlgHom.fieldRange i)
  let phiAlg : F ≃ₐ[K] F₀ :=
    (i.equivFieldRange).trans
      (IntermediateField.equivOfEq hfixed.symm)
  let phi : F ≃+* F₀ := phiAlg.toRingEquiv
  let c : SeparableClosure F ≃+* SeparableClosure F₀ :=
    e.toRingEquiv.trans e₀.symm.toRingEquiv
  have hc (x : F) :
      c (algebraMap F (SeparableClosure F) x) =
        algebraMap F₀ (SeparableClosure F₀) (phi x) := by
    change e₀.symm
        (e (algebraMap F (SeparableClosure F) x)) =
      algebraMap F₀ (SeparableClosure F₀) (phi x)
    apply e₀.injective
    rw [e₀.apply_symm_apply, e.commutes, e₀.commutes]
    rfl
  let theta :
      Gal(SeparableClosure F / F) ≃*
        Gal(SeparableClosure F₀ / F₀) := {
    toFun := fun sigma =>
      { c.symm.trans (sigma.toRingEquiv.trans c) with
        commutes' := fun x => by
          change c (sigma (c.symm
            (algebraMap F₀ (SeparableClosure F₀) x))) =
              algebraMap F₀ (SeparableClosure F₀) x
          have hpre :
              c.symm
                  (algebraMap F₀ (SeparableClosure F₀) x) =
                algebraMap F (SeparableClosure F) (phi.symm x) := by
            apply c.injective
            rw [c.apply_symm_apply, hc, phi.apply_symm_apply]
          rw [hpre, sigma.commutes, hc, phi.apply_symm_apply] }
    invFun := fun tau =>
      { c.trans (tau.toRingEquiv.trans c.symm) with
        commutes' := fun x => by
          change c.symm (tau (c
            (algebraMap F (SeparableClosure F) x))) =
              algebraMap F (SeparableClosure F) x
          rw [hc, tau.commutes]
          apply c.injective
          rw [c.apply_symm_apply, hc] }
    left_inv := fun sigma => by
      apply AlgEquiv.ext
      intro x
      change c.symm
          (c (sigma (c.symm (c x)))) = sigma x
      rw [c.symm_apply_apply, c.symm_apply_apply]
    right_inv := fun tau => by
      apply AlgEquiv.ext
      intro x
      change c
          (c.symm (tau (c (c.symm x)))) = tau x
      rw [c.apply_symm_apply, c.apply_symm_apply]
    map_mul' := fun sigma tau => by
      apply AlgEquiv.ext
      intro x
      change c (sigma (tau (c.symm x))) =
        c (sigma (c.symm (c (tau (c.symm x)))))
      rw [c.symm_apply_apply] }
  have htheta : Continuous theta := by
    apply
      RamificationTheory.Field.absoluteGaloisGroup.semilinear_conjugation_continuous
        phi c hc theta.toMonoidHom
    intro sigma
    rfl
  let psi₀ :=
    intrinsicBaseEquivAmbientFixedField K H e₀
  have hpsi₀ : Continuous psi₀ :=
    intrinsicBaseEquivAmbientFixedField_continuous K H e₀
  have hlift : Continuous
      (fun sigma : Gal(SeparableClosure F₀ / F₀) =>
        (⟨sigma, by
          rw [intrinsicAbstractBase,
            closedFixingSubgroup_bot_eq_baseField]
          trivial⟩ :
          (intrinsicAbstractBase F₀).toSubgroup)) := by
    apply continuous_induced_rng.mpr
    exact continuous_id
  change Continuous
    (fun tau : (intrinsicAbstractBase F).toSubgroup =>
      psi₀
        ⟨theta tau.1, by
          rw [intrinsicAbstractBase,
            closedFixingSubgroup_bot_eq_baseField]
          trivial⟩)
  exact hpsi₀.comp
    (hlift.comp (htheta.comp continuous_subtype_val))

/-- Bundles the intrinsic-to-ambient absolute Galois equivalence as a continuous
multiplicative equivalence. -/
noncomputable def
    intrinsicBaseContinuousEquivAmbientEmbeddedField
    (K F : Type) [Field K] [Field F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (i : F →ₐ[K] SeparableClosure K) :
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    (e : SeparableClosure F ≃ₐ[F] SeparableClosure K) →
      (intrinsicAbstractBase F).toSubgroup ≃ₜ*
        (closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)).toSubgroup := by
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e
  let psi :=
    intrinsicBaseEquivAmbientEmbeddedField K F i e
  have hpsi : Continuous psi :=
    intrinsicBaseEquivAmbientEmbeddedField_continuous
      K F i e
  letI : CompactSpace (intrinsicAbstractBase F).toSubgroup :=
    isCompact_iff_compactSpace.mp
      ((intrinsicAbstractBase F).isClosed'.isCompact)
  exact
    { toMulEquiv := psi
      continuous_toFun := hpsi
      continuous_invFun :=
        hpsi.continuous_symm_of_equiv_compact_to_t2 }

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientPrimeNormTransport
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.realComplexNormQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Valuation-one units and abstract prime norm-residue transport

This module transports valuation-one units and norm classes through
compatible field equivalences, and evaluates abstract fixed-field
norm-residue symbols on transported prime norms.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- Compatible ring equivalences between finite extensions preserve
valuation-subring membership when their separable-closure transport preserves
the local valuation subrings. -/
theorem valuationSubring_mem_iff_of_separableClosureRingEquiv
    (F K L M : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [Algebra F L]
    [FiniteDimensional F L] [Algebra.IsSeparable F L]
    [Valuation.HasExtension
      (ValuativeRel.valuation F) (ValuativeRel.valuation L)]
    [Field M] [ValuativeRel M] [Algebra K M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation M)]
    (jL : L →ₐ[F] SeparableClosure F)
    (jM : M →ₐ[K] SeparableClosure K)
    (psi : SeparableClosure F ≃+* SeparableClosure K)
    (hpsi :
      localSeparableValuationSubring F =
        (localSeparableValuationSubring K).comap psi.toRingHom)
    (phi : L ≃+* M)
    (hphi : ∀ x : L, jM (phi x) = psi (jL x))
    (x : L) :
    x ∈ (ValuativeRel.valuation L).valuationSubring ↔
      phi x ∈ (ValuativeRel.valuation M).valuationSubring := by
  have hsourceRing :
      (localSeparableValuationSubring F).comap jL.toRingHom =
        (ValuativeRel.valuation L).valuationSubring :=
    localSeparableValuationSubring_comap_embedding F L jL
  have htargetRing :
      (localSeparableValuationSubring K).comap jM.toRingHom =
        (ValuativeRel.valuation M).valuationSubring :=
    localSeparableValuationSubring_comap_embedding K M jM
  rw [← hsourceRing, ← htargetRing]
  change
    jL x ∈ localSeparableValuationSubring F ↔
      jM (phi x) ∈ localSeparableValuationSubring K
  rw [hphi x, hpsi]
  rfl

/-- Compatible ring equivalences preserve equality of unit norm classes. -/
theorem normClass_mapEquiv
    (F E F₀ E₀ : Type)
    [Field F] [Field E] [Field F₀] [Field E₀]
    [Algebra F E] [Algebra F₀ E₀]
    (phiF : F ≃+* F₀) (phiE : E ≃+* E₀)
    (hcomm :
      RingHom.comp (algebraMap F₀ E₀) phiF.toRingHom =
        RingHom.comp phiE.toRingHom (algebraMap F E))
    (a x : Fˣ)
    (h : normClass F E a = normClass F E x) :
    normClass F₀ E₀ (Units.mapEquiv phiF.toMulEquiv a) =
      normClass F₀ E₀
        (Units.mapEquiv phiF.toMulEquiv x) := by
  rw [normClass_eq_iff_exists_norm_div] at h ⊢
  rcases h with ⟨y, hy⟩
  refine ⟨Units.mapEquiv phiE.toMulEquiv y, ?_⟩
  have hnorm :=
    normUnits_mapEquiv F E F₀ E₀ phiF phiE hcomm y
  rw [← map_div, hy]
  exact hnorm.symm

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_IntermediateFieldNormResidueNaturality
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.realComplexNormQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Restriction naturality for the concrete local norm-residue symbol

The abstract class formation supplies restriction naturality.  This file
constructs the field-facing restriction map for two finite Galois intermediate
fields in the fixed separable closure and transports the naturality identity
to the concrete local norm-residue symbol.

The intermediate-field restriction is packaged here so callers do not have
to install the auxiliary `Algebra E F` and scalar-tower instances attached
to an inclusion `E ≤ F`.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation LocalClassFieldTheory
open scoped IsMulCommutative

universe u v

variable {K : Type u} {Omega : Type v}
  [Field K] [Field Omega] [Algebra K Omega]

section AbstractToConcrete

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The finite abstract norm class represented by a base-field unit in an
explicit separable-closure realization. -/
def embeddedBaseNormClass
    (i : L →ₐ[K] SeparableClosure K) (a : Kˣ) :
    FiniteNormQuotient (absoluteUnits K) (abstractBase_p0 K)
      (finiteGaloisAbstractExtensionOfEmbedding K L i).field
      (finiteGaloisAbstractExtensionOfEmbedding K L i).below :=
  finiteNormClass (absoluteUnits K) (abstractBase_p0 K)
    (finiteGaloisAbstractExtensionOfEmbedding K L i).field
    (finiteGaloisAbstractExtensionOfEmbedding K L i).below
    (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
      (Additive.ofMul a))

/-- Before specializing the local datum, the concrete norm-residue symbol is
the abstract norm-residue class transported through the canonical quotient
equivalence.  This pointwise transport formula expresses abstract
restriction naturality as a statement about actual field automorphisms. -/
theorem concreteNormResidueSymbolOfEmbedding_eq_abstract
    (i : L →ₐ[K] SeparableClosure K)
    (D : DegreeData (absoluteGalois_p0 K))
    (v : ValuationData D (absoluteUnits K))
    (hcf : SatisfiesClassFieldAxiom (absoluteUnits K)) (a : Kˣ) :
    concreteNormResidueSymbolOfEmbedding K L i D v hcf a =
      (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
        K L i).abelianizationCongr
        (Additive.toMul
          (D.normResidueSymbol (absoluteUnits K) v hcf (intrinsicFiniteAbstractBase K)
            (finiteGaloisAbstractExtensionOfEmbedding K L i)
            (embeddedBaseNormClass K L i a))) := by
  let Eabs := finiteGaloisAbstractExtensionOfEmbedding K L i
  let q := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
  let xabs := embeddedBaseNormClass K L i a
  let z := D.normResidueSymbol (absoluteUnits K) v hcf
    (intrinsicFiniteAbstractBase K) Eabs xabs
  have hnorm :
      finiteNormQuotientEquivEmbeddedNormQuotient
          K (SeparableClosure K) L i xabs =
        Additive.ofMul
          (normClass K L a) := by
    convert
      finiteNormQuotientEquivEmbeddedNormQuotient_finiteNormClass_baseUnit
        K L i a using 1 <;> rfl
  have hsource :
      MulEquiv.toAdditive q.abelianizationCongr.symm
          (Additive.ofMul (q.abelianizationCongr (Additive.toMul z))) = z := by
    apply Additive.toMul.injective
    exact q.abelianizationCongr.symm_apply_apply (Additive.toMul z)
  have hforward :
      concreteReciprocityAddEquivOfEmbedding K L i D v hcf
          (Additive.ofMul (q.abelianizationCongr (Additive.toMul z))) =
        Additive.ofMul
          (normClass K L a) := by
    change finiteNormQuotientEquivEmbeddedNormQuotient
        K (SeparableClosure K) L i
        (D.abstractReciprocityEquiv (absoluteUnits K) v hcf (intrinsicFiniteAbstractBase K) Eabs
          (MulEquiv.toAdditive q.abelianizationCongr.symm
            (Additive.ofMul
              (q.abelianizationCongr (Additive.toMul z))))) = _
    rw [hsource]
    change finiteNormQuotientEquivEmbeddedNormQuotient
        K (SeparableClosure K) L i
        (D.abstractReciprocityEquiv (absoluteUnits K) v hcf (intrinsicFiniteAbstractBase K) Eabs
          ((D.abstractReciprocityEquiv
            (absoluteUnits K) v hcf (intrinsicFiniteAbstractBase K) Eabs).symm xabs)) = _
    rw [(D.abstractReciprocityEquiv
      (absoluteUnits K) v hcf (intrinsicFiniteAbstractBase K) Eabs).apply_symm_apply,
      hnorm]
  change (concreteReciprocityEquivOfEmbedding K L i D v hcf).symm
      (normClass K L a) =
    q.abelianizationCongr (Additive.toMul z)
  apply (concreteReciprocityEquivOfEmbedding K L i D v hcf).injective
  rw [(concreteReciprocityEquivOfEmbedding
    K L i D v hcf).apply_symm_apply]
  exact (congrArg Additive.toMul hforward).symm

end AbstractToConcrete

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_GeneralTowerNaturality
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Restriction naturality in an arbitrary finite abelian tower

The fixed-separable-closure form of finite local reciprocity naturality is
transported here to an arbitrary tower `K ⊂ E ⊂ L`.  The two extensions are
realized compatibly in the chosen separable closure by first embedding `L`
and then restricting that embedding to `E`.  Abstract norm--residue
naturality then becomes the actual restriction homomorphism
`Gal(L/K) → Gal(E/K)`.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation LocalClassFieldTheory
open scoped IsMulCommutative

def towerEmbeddedBaseNormClass
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (i : L →ₐ[K] SeparableClosure K) (a : Kˣ) :
    FiniteNormQuotient (towerAbsoluteUnits K) (towerAbstractBase K)
      (finiteGaloisAbstractExtensionOfEmbedding K L i).field
      (finiteGaloisAbstractExtensionOfEmbedding K L i).below :=
  finiteNormClass (towerAbsoluteUnits K) (towerAbstractBase K)
    (finiteGaloisAbstractExtensionOfEmbedding K L i).field
    (finiteGaloisAbstractExtensionOfEmbedding K L i).below
    (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
      (Additive.ofMul a))

theorem towerEmbeddedAbstractExtension_field_le
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [IsGalois K E] [IsGalois K L]
    (iL : L →ₐ[K] SeparableClosure K) :
    (finiteGaloisAbstractExtensionOfEmbedding K L iL).field.toSubgroup ≤
      (finiteGaloisAbstractExtensionOfEmbedding K E
        (towerLowerEmbedding K E L iL)).field.toSubgroup := by
  change
    (closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange iL)).toSubgroup ≤
    (closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange (towerLowerEmbedding K E L iL))).toSubgroup
  change
    (AlgHom.fieldRange iL).fixingSubgroup ≤
      (AlgHom.fieldRange (towerLowerEmbedding K E L iL)).fixingSubgroup
  exact
    (AlgHom.fieldRange (towerLowerEmbedding K E L iL)).fixingSubgroup_le
      (towerEmbeddedFieldRange_le K E L iL)

theorem towerRestrict_abstractQuotient_mk
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [IsGalois K E] [IsGalois K L]
    (iL : L →ₐ[K] SeparableClosure K)
    (sigma : (towerAbstractBase K).toSubgroup) :
    AlgEquiv.restrictNormalHom E
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          K L iL (QuotientGroup.mk sigma)) =
      finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
        K E (towerLowerEmbedding K E L iL)
        (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma)) := by
  let iE := towerLowerEmbedding K E L iL
  apply AlgEquiv.ext
  intro x
  apply iE.injective
  calc
    iE ((AlgEquiv.restrictNormalHom E
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          K L iL (QuotientGroup.mk sigma))) x) =
        iL ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          K L iL (QuotientGroup.mk sigma)) (algebraMap E L x)) := by
      change
        iL (algebraMap E L
          ((AlgEquiv.restrictNormalHom E
            (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
              K L iL (QuotientGroup.mk sigma))) x)) =
          iL ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
            K L iL (QuotientGroup.mk sigma)) (algebraMap E L x))
      exact congrArg iL
        (AlgEquiv.restrictNormal_commutes
          (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
            K L iL (QuotientGroup.mk sigma)) E x)
    _ = sigma.1 (iL (algebraMap E L x)) := by
      exact
        finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
          K L iL sigma (algebraMap E L x)
    _ = sigma.1 (iE x) := rfl
    _ = iE
        ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          K E iE
          (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma))) x) := by
      exact
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
          K E iE (Subgroup.inclusion le_rfl sigma) x).symm

theorem towerRestrict_abstractAbelianization
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [IsAbelianGalois K E] [IsAbelianGalois K L]
    (iL : L →ₐ[K] SeparableClosure K)
    (z : Abelianization
      (finiteGaloisAbstractExtensionOfEmbedding K L iL).extensionQuotient) :
    AlgEquiv.restrictNormalHom E
        ((Abelianization.equivOfComm (H := Gal(L / K))).symm
          ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
            K L iL).abelianizationCongr z)) =
      (Abelianization.equivOfComm (H := Gal(E / K))).symm
        ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          K E (towerLowerEmbedding K E L iL)).abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            (towerAbstractBase K) (towerAbstractBase K)
            (finiteGaloisAbstractExtensionOfEmbedding
              K E (towerLowerEmbedding K E L iL)).field
            (finiteGaloisAbstractExtensionOfEmbedding K L iL).field
            (finiteGaloisAbstractExtensionOfEmbedding
              K E (towerLowerEmbedding K E L iL)).below
            (finiteGaloisAbstractExtensionOfEmbedding K L iL).below
            le_rfl (towerEmbeddedAbstractExtension_field_le K E L iL) z)) := by
  let B := towerAbstractBase K
  let EE :=
    finiteGaloisAbstractExtensionOfEmbedding K E
      (towerLowerEmbedding K E L iL)
  let EL := finiteGaloisAbstractExtensionOfEmbedding K L iL
  let qE :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
      K E (towerLowerEmbedding K E L iL)
  let qL :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L iL
  let : (extensionSubgroup B EE.field EE.below).Normal := EE.normal
  let : (extensionSubgroup B EL.field EL.below).Normal := EL.normal
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨sigma, rfl⟩ := QuotientGroup.mk_surjective q
  change
    AlgEquiv.restrictNormalHom E
        ((Abelianization.equivOfComm (H := Gal(L / K))).symm
          (qL.abelianizationCongr
            (Abelianization.of (QuotientGroup.mk sigma)))) =
      (Abelianization.equivOfComm (H := Gal(E / K))).symm
        (qE.abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            B B EE.field EL.field EE.below EL.below le_rfl
            (towerEmbeddedAbstractExtension_field_le K E L iL)
            (Abelianization.of (QuotientGroup.mk sigma))))
  rw [abelianizationCongr_of]
  change
    AlgEquiv.restrictNormalHom E
        (qL (QuotientGroup.mk sigma)) =
      (Abelianization.equivOfComm (H := Gal(E / K))).symm
        (qE.abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            B B EE.field EL.field EE.below EL.below le_rfl
            (towerEmbeddedAbstractExtension_field_le K E L iL)
            (Abelianization.of (QuotientGroup.mk sigma))))
  rw [normResidueNaturalityAbelianizedRestriction_of_mk]
  change
    AlgEquiv.restrictNormalHom E
        (qL (QuotientGroup.mk sigma)) =
      (Abelianization.equivOfComm (H := Gal(E / K))).symm
        (qE.abelianizationCongr
          (Abelianization.of
            (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma))))
  rw [abelianizationCongr_of]
  change
    AlgEquiv.restrictNormalHom E
        (qL (QuotientGroup.mk sigma)) =
      qE (QuotientGroup.mk (Subgroup.inclusion le_rfl sigma))
  exact towerRestrict_abstractQuotient_mk K E L iL sigma

/-- Before specializing the local class-formation structures, compatible
embeddings of an arbitrary finite abelian tower identify abstract
norm--residue restriction with the actual Galois restriction map. -/
theorem concreteNormResidueAutomorphism_restrict_tower
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional K L]
    [IsAbelianGalois K E] [IsAbelianGalois K L]
    (iL : L →ₐ[K] SeparableClosure K)
    (D : DegreeData (towerAbsoluteGalois K))
    (v : ValuationData D (towerAbsoluteUnits K))
    (hcf : SatisfiesClassFieldAxiom (towerAbsoluteUnits K))
    (a : Kˣ) :
    AlgEquiv.restrictNormalHom E
        ((Abelianization.equivOfComm (H := Gal(L / K))).symm
          (concreteNormResidueSymbolOfEmbedding
            K L iL D v hcf a)) =
      (Abelianization.equivOfComm (H := Gal(E / K))).symm
        (concreteNormResidueSymbolOfEmbedding
          K E (towerLowerEmbedding K E L iL) D v hcf a) := by
  let B := towerAbstractBase K
  let BF := intrinsicFiniteAbstractBase K
  let EE :=
    finiteGaloisAbstractExtensionOfEmbedding K E
      (towerLowerEmbedding K E L iL)
  let EL := finiteGaloisAbstractExtensionOfEmbedding K L iL
  let qE :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
      K E (towerLowerEmbedding K E L iL)
  let qL :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L iL
  let xE :=
    towerEmbeddedBaseNormClass K E
      (towerLowerEmbedding K E L iL) a
  let xL := towerEmbeddedBaseNormClass K L iL a
  have hLE : EL.field.toSubgroup ≤ EE.field.toSubgroup :=
    towerEmbeddedAbstractExtension_field_le K E L iL
  let hEENormal : (extensionSubgroup B EE.field EE.below).Normal :=
    EE.normal
  let hELNormal : (extensionSubgroup B EL.field EL.below).Normal :=
    EL.normal
  let hEEFinite : Finite
      (B.toSubgroup ⧸ extensionSubgroup B EE.field EE.below) :=
    EE.finite
  let hELFinite : Finite
      (B.toSubgroup ⧸ extensionSubgroup B EL.field EL.below) :=
    EL.finite
  let hBBFinite : Finite
      (B.toSubgroup ⧸ extensionSubgroup B B le_rfl) := by
    have htop : extensionSubgroup B B le_rfl = ⊤ := by
      ext sigma
      constructor
      · intro _
        trivial
      · intro _
        exact sigma.2
    rw [htop]
    infer_instance
  let T : FiniteAbstractFieldExtension (towerAbsoluteGalois K) := {
    field := BF
    base := BF
    below := le_rfl
    finiteQuotient := hBBFinite }
  let : (extensionSubgroup T.base.field EE.field EE.below).Normal := by
    change (extensionSubgroup B EE.field EE.below).Normal
    exact hEENormal
  let : (extensionSubgroup T.field.field EL.field EL.below).Normal := by
    change (extensionSubgroup B EL.field EL.below).Normal
    exact hELNormal
  let : Finite
      (T.base.field.toSubgroup ⧸
        extensionSubgroup T.base.field EE.field EE.below) := by
    change Finite (B.toSubgroup ⧸ extensionSubgroup B EE.field EE.below)
    exact hEEFinite
  let : Finite
      (T.field.field.toSubgroup ⧸
        extensionSubgroup T.field.field EL.field EL.below) := by
    change Finite (B.toSubgroup ⧸ extensionSubgroup B EL.field EL.below)
    exact hELFinite
  have hnorm : finiteReciprocityNaturalityNormMap (towerAbsoluteUnits K)
        B B EE.field EL.field EE.below EL.below le_rfl hLE xL = xE := by
    dsimp only [xL, xE, towerEmbeddedBaseNormClass]
    rw [finiteReciprocityNaturalityNormMap_finiteNormClass,
      relativeNorm_self]
  have hraw := D.normResidueNaturality_norm_restriction
    (towerAbsoluteUnits K) v hcf
    T EE.field EL.field EE.below EL.below hLE
  have hrawa := DFunLike.congr_fun hraw xL
  change _ =
    D.normResidueSymbol (towerAbsoluteUnits K) v hcf BF EE
      (finiteReciprocityNaturalityNormMap (towerAbsoluteUnits K)
        B B EE.field EL.field EE.below EL.below le_rfl hLE xL) at hrawa
  rw [hnorm] at hrawa
  let zL :=
    D.normResidueSymbol (towerAbsoluteUnits K) v hcf BF EL xL
  let zE :=
    D.normResidueSymbol (towerAbsoluteUnits K) v hcf BF EE xE
  have hz : normResidueNaturalityAbelianizedRestriction
        B B EE.field EL.field EE.below EL.below le_rfl hLE
        (Additive.toMul zL) = Additive.toMul zE := by
    exact congrArg Additive.toMul hrawa
  rw [concreteNormResidueSymbolOfEmbedding_eq_abstract
      K L iL D v hcf a,
    concreteNormResidueSymbolOfEmbedding_eq_abstract
      K E (towerLowerEmbedding K E L iL) D v hcf a]
  change
    AlgEquiv.restrictNormalHom E
        ((Abelianization.equivOfComm (H := Gal(L / K))).symm
          (qL.abelianizationCongr (Additive.toMul zL))) =
      (Abelianization.equivOfComm (H := Gal(E / K))).symm
        (qE.abelianizationCongr (Additive.toMul zE))
  calc
    AlgEquiv.restrictNormalHom E
        ((Abelianization.equivOfComm (H := Gal(L / K))).symm
          (qL.abelianizationCongr (Additive.toMul zL))) =
      (Abelianization.equivOfComm (H := Gal(E / K))).symm
        (qE.abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction
            B B EE.field EL.field EE.below EL.below le_rfl hLE
            (Additive.toMul zL))) :=
      towerRestrict_abstractAbelianization
        K E L iL (Additive.toMul zL)
    _ = (Abelianization.equivOfComm (H := Gal(E / K))).symm
        (qE.abelianizationCongr (Additive.toMul zE)) :=
      congrArg
        (fun w => (Abelianization.equivOfComm (H := Gal(E / K))).symm
          (qE.abelianizationCongr w)) hz

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalField_DiscreteValuationField_PadicValuationComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseIsNonarchimedeanLocalField _root_.chosenFinitePlaceBaseValuativeRel _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Comparison of the chosen and canonical valuations on the p-adic field

The concrete local-field package on `ℚ_[p]` uses the DVR valuation obtained
from `ℤ_[p]`, whereas mathlib's nonarchimedean-local-field API uses
`ValuativeRel.valuation ℚ_[p]`.  This file proves that these are equivalent
valuations and makes the comparison usable when transporting valuation
extensions.
-/

noncomputable section

open scoped ValuativeRel

namespace LocalFieldTheory
namespace DiscreteValuationField
namespace Examples
namespace Qp

universe u v

/-- The chosen valuation in `padicLocalField p` is equivalent to the
canonical complete-DVF valuation supplied by the topology-first local-field
structure on `ℚ_[p]`. -/
theorem padicLocalField_valuation_isEquiv_localCompleteDVF
    (p : ℕ) [Fact p.Prime] :
    (padicLocalField p).toCompleteDVF.valuation.IsEquiv
      (LocalFieldTheory.localCompleteDVF ℚ_[p]).valuation := by
  rw [LocalFieldTheory.localCompleteDVF_valuation_eq]
  exact padicLocalField_valuation_isEquiv_valuativeRelValuation p

/-- Symmetric comparison, oriented for transporting canonical local-field
valuation extensions to the chosen p-adic DVR valuation. -/
theorem localCompleteDVF_valuation_isEquiv_padicLocalField
    (p : ℕ) [Fact p.Prime] :
    (LocalFieldTheory.localCompleteDVF ℚ_[p]).valuation.IsEquiv
      (padicLocalField p).toCompleteDVF.valuation :=
  (padicLocalField_valuation_isEquiv_localCompleteDVF p).symm

end Qp
end Examples
end DiscreteValuationField
end LocalFieldTheory
end
end


