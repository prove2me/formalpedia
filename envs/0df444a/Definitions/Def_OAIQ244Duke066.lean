-- Prove2me | Definitions.Def_OAIQ244Duke066
-- name    : OAIQ244Duke066
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T22:28:10.107501+00:00
-- url     : https://prove2.me/theorems/37845d90-cd41-4ede-8e07-8cef5d2f89c4
-- title:
--   Definitions bundle OAIQ244Duke066 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 37 declarations of OpenAI's Lean: 16 definitions and 21 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.finitePlaceArtinLocalizedCompletionBaseRingHom`, `GlobalClassFieldTheory.Reciprocity.finitePlaceArtinLocalizedCompletionRingHom`, `GlobalClassFieldTheory.Reciprocity.finitePlaceCrossLocalRestrictionMonoidHom`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinCompletionAlgebra`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinExtension`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinExtensionAlgebra`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinExtensionSMul`, `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedField`, `GlobalClassFieldTheory.Reciprocity.restrictFinitePlaceExtension`, `LocalClassFieldTheory.abstractFixedFieldAbelianizedRestriction`, `LocalClassFieldTheory.abstractFixedFieldCosetEquivAlgHom`, `LocalClassFieldTheory.abstractFixedFieldCosetToAlgHom`, `LocalClassFieldTheory.abstractFixedFieldNormResidueSymbol`, `LocalClassFieldTheory.abstractFixedFieldNormUnits`, `LocalClassFieldTheory.chosenValuationOneUnitOfRingEquiv`, `LocalClassFieldTheory.intrinsicBaseEquivAmbientFixedField`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_CrossLocalRestriction`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_TowerRestriction`, `GlobalClassFieldTheory_Reciprocity_InfinitePlaceArtin`, `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientPrimeNormTransport`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_BaseComparison_IntrinsicBaseEquivalence`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_EmbeddedFrobeniusTransport`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldNormResidueNaturality`, `LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldRelativeNorm`, `LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedComparison`, `LubinTate_Padic_ChangedUniformizerCoefficient`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke053`, `OAIQ244Duke054`, `OAIQ244Duke055`, `OAIQ244Duke056`, `OAIQ244Duke059` and `OAIQ244Duke060` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ244Duke070`, `OAIQ244Duke072`, `OAIQ244Duke073` and `OAIQ244Duke113`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.Action.Basic
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
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Finset.Max
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
import Mathlib.Data.ZMod.Units
import Mathlib.Dynamics.BirkhoffSum.Basic
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
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.Discriminant
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
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
import Mathlib.Topology.Homeomorph.TransferInstance
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Mathlib.Topology.WithTopology
import Definitions.Def_OAIQ244Duke053
import Definitions.Def_OAIQ244Duke054
import Definitions.Def_OAIQ244Duke055
import Definitions.Def_OAIQ244Duke056
import Definitions.Def_OAIQ244Duke059
import Definitions.Def_OAIQ244Duke060

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_TowerRestriction
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xT2Space _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceExtensionCompletionAlgebra _root_.chosenFinitePlaceExtensionCompletionSMul _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsUltrametricDist _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Restriction in a finite-place Artin tower

This module restricts finite-place extensions through an intermediate field and proves restriction naturality for the corresponding global Artin homomorphisms.
-/

open scoped Classical IsMulCommutative NNReal NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- Restrict an extension of a finite place through an intermediate
field in a scalar tower. -/
def restrictFinitePlaceExtension
    {E : Type}
    [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) E where
  val :=
    w.1.comp (f := algebraMap E L)
      (algebraMap E L).injective
  property x := by
    change
      w.1 (algebraMap E L (algebraMap K E x)) =
        NumberField.HeightOneSpectrum.adicAbv K v x
    rw [← IsScalarTower.algebraMap_apply K E L]
    exact w.2 x

omit [NumberField K] [FiniteDimensional K L]
    [IsAbelianGalois K L] in
/-- Completion maps compose along a scalar tower when the three
absolute values extend one another. -/
theorem absoluteValueCompletionMap_comp_of_isScalarTower
    {E : Type}
    [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    (vK : AbsoluteValue K ℝ)
    (vE : AbsoluteValue E ℝ)
    (vL : AbsoluteValue L ℝ)
    (hKE : AbsoluteValue.Extends vK vE)
    (hEL : AbsoluteValue.Extends vE vL)
    (hKL : AbsoluteValue.Extends vK vL) :
    (AbsoluteValue.completionMap vE vL hEL).comp
        (AbsoluteValue.completionMap vK vE hKE) =
      AbsoluteValue.completionMap vK vL hKL := by
  ext x
  refine
    UniformSpace.Completion.induction_on
      (α := WithAbs vK) x ?_ ?_
  · exact isClosed_eq
      ((AbsoluteValue.completionMap_isometry
          vE vL hEL).continuous.comp
        (AbsoluteValue.completionMap_isometry
          vK vE hKE).continuous)
      (AbsoluteValue.completionMap_isometry
        vK vL hKL).continuous
  · intro a
    have ha : (a : vK.Completion) =
        algebraMap K vK.Completion
          (WithAbs.equiv vK a) := by
      change (a : vK.Completion) =
        (((WithAbs.equiv vK).symm
          (WithAbs.equiv vK a) : WithAbs vK) :
            vK.Completion)
      exact congrArg
        (fun z : WithAbs vK => (z : vK.Completion))
        ((WithAbs.equiv vK).symm_apply_apply a).symm
    rw [ha]
    change
      AbsoluteValue.completionMap vE vL hEL
          (AbsoluteValue.completionMap vK vE hKE
            (algebraMap K vK.Completion
              (WithAbs.equiv vK a))) =
        AbsoluteValue.completionMap vK vL hKL
          (algebraMap K vK.Completion
            (WithAbs.equiv vK a))
    rw [AbsoluteValue.completionMap_coe,
      AbsoluteValue.toCompletion_eq_algebraMap,
      AbsoluteValue.completionMap_coe,
      AbsoluteValue.completionMap_coe,
      IsScalarTower.algebraMap_apply K E L]

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceArtin_CrossLocalRestriction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicCompletionAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLocalizedCompletionIsAlgebraic _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceBaseValued _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionContinuousSMul _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceCompletionLocallyCompactSpace _root_.chosenFinitePlaceExtensionCompletionAlgebra _root_.chosenFinitePlaceExtensionCompletionSMul _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.chosenFinitePlaceLocalizedIsIntegralClosure _root_.chosenFinitePlaceLocalizedIsNonarchimedeanLocalField _root_.chosenFinitePlaceLocalizedIsUltrametricDist _root_.chosenFinitePlaceLocalizedIsValuativeTopology _root_.chosenFinitePlaceLocalizedLocallyCompactSpace _root_.chosenFinitePlaceLocalizedValuationCompatible _root_.chosenFinitePlaceLocalizedValuationHasExtension _root_.chosenFinitePlaceLocalizedValuationIsNontrivial _root_.chosenFinitePlaceLocalizedValuativeRel _root_.chosenFinitePlaceLocalizedValuativeRelIsNontrivial _root_.chosenFinitePlaceLocalizedValued
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# Cross-base restriction of finite-place Artin homomorphisms

This module compares localized completions in a square of number fields with different base fields and transports restriction through the corresponding decomposition groups.
-/

open scoped Classical IsMulCommutative NNReal NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

theorem finitePlaceArtinLocalizedCompletion_algebraMap
    {F M : Type}
    [Field F] [NumberField F]
    [Field M] [NumberField M]
    [Algebra F M] [FiniteDimensional F M]
    (v : HeightOneSpectrum (𝓞 F))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv F v) M)
    (x : (NumberField.HeightOneSpectrum.adicAbv F v).Completion) :
    let vF := NumberField.HeightOneSpectrum.adicAbv F v
    let hvF : vF.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    letI hMF :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := F) w.1
    letI : SMul F w.1.Completion := hMF.toSMul
    letI : Algebra vF.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vF w.1 w.2
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vF w
    let U := finitePlaceExtensionEquivAbove
      (K := F) (L := M) v w
    let eF :
        vF.Completion ≃+* v.adicCompletion F :=
      (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
    let eE :
        E ≃+* U.1.adicCompletion M :=
      (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
          vF hvF w).toRingEquiv.trans
        (finitePlaceExtensionAdicCompletionRingEquiv
          (K := F) (L := M) v w)
    eE (algebraMap vF.Completion E x) =
      finitePlaceAdicCompletionMap
        F M v U (eF x) := by
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  let hvF : vF.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hMF :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := F) w.1
  let : SMul F w.1.Completion := hMF.toSMul
  let : Algebra vF.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vF w.1 w.2
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vF w
  let U := finitePlaceExtensionEquivAbove
    (K := F) (L := M) v w
  let eF :
      vF.Completion ≃+* v.adicCompletion F :=
    (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
  let eE :
      E ≃+* U.1.adicCompletion M :=
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
        vF hvF w).toRingEquiv.trans
      (finitePlaceExtensionAdicCompletionRingEquiv
        (K := F) (L := M) v w)
  change
    finitePlaceExtensionAdicCompletionRingEquiv
        (K := F) (L := M) v w
        (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
          vF hvF w (algebraMap vF.Completion E x)) =
      finitePlaceAdicCompletionMap
        F M v U
          (relativeFinitePlaceCompletionAlgEquiv v x)
  rw [
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
      vF hvF w).commutes]
  rw [←
    finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap
      F M v w]
  change
    finitePlaceExtensionAdicCompletionRingEquiv
        (K := F) (L := M) v w
        (algebraMap vF.Completion w.1.Completion x) =
      finitePlaceExtensionAdicCompletionRingEquiv
        (K := F) (L := M) v w
        (AbsoluteValue.completionMap vF w.1 w.2
          ((relativeFinitePlaceCompletionAlgEquiv v).symm
            (relativeFinitePlaceCompletionAlgEquiv v x)))
  rw [
    (relativeFinitePlaceCompletionAlgEquiv v).symm_apply_apply,
    AbsoluteValue.completionAlgebra_algebraMap]

/-- The canonical map from the base completion into the localized completion,
with its construction tower confined to the definition body. -/
noncomputable def finitePlaceArtinLocalizedCompletionBaseRingHom
    (F M : Type) [Field F] [NumberField F]
    [Field M] [NumberField M] [Algebra F M]
    (v : HeightOneSpectrum (𝓞 F))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv F v) M) :
    (NumberField.HeightOneSpectrum.adicAbv F v).Completion →+*
      finitePlaceArtinLocalizedCompletion F M v w := by
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  letI hwF :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := F) w.1
  letI : SMul F w.1.Completion := hwF.toSMul
  letI : Algebra vF.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vF w.1 w.2
  exact algebraMap vF.Completion
    (AlgebraicNumberTheory.Valuations.LocalizedCompletion vF w)

/-- The ring homomorphism between localized completions in a finite-place scalar tower. -/
noncomputable def finitePlaceArtinLocalizedCompletionRingHom
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [NumberField L]
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (w' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K' W) L')
    (hcentres :
      finitePlaceBelow (K := L)
          (finitePlaceExtensionCentre
            (K := K') (L := L') W w') =
        finitePlaceExtensionCentre
          (K := K) (L := L) v w) :
    finitePlaceArtinLocalizedCompletion K L v w →+*
      finitePlaceArtinLocalizedCompletion K' L' W w' := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let vK' := NumberField.HeightOneSpectrum.adicAbv K' W
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hvK' : vK'.IsNontrivial :=
    RayClass.adicAbv_isNontrivial W
  letI hwK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  letI : SMul K w.1.Completion := hwK.toSMul
  letI : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  letI hwK' :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K') w'.1
  letI : SMul K' w'.1.Completion := hwK'.toSMul
  letI : Algebra vK'.Completion w'.1.Completion :=
    AbsoluteValue.completionAlgebra vK' w'.1 w'.2
  let U :=
    finitePlaceExtensionEquivAbove
      (K := K) (L := L) v w
  let U' :=
    finitePlaceExtensionEquivAbove
      (K := K') (L := L') W w'
  have hU'L : finitePlaceBelow (K := L) U'.1 = U.1 := by
    simpa only [
      U, U',
      finitePlaceExtensionEquivAbove_coe
    ] using hcentres
  let eE :
      AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w ≃+*
        U.1.adicCompletion L :=
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
        vK hvK w).toRingEquiv.trans
      (finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) v w)
  let eE' :
      AlgebraicNumberTheory.Valuations.LocalizedCompletion vK' w' ≃+*
        U'.1.adicCompletion L' :=
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
        vK' hvK' w').toRingEquiv.trans
      (finitePlaceExtensionAdicCompletionRingEquiv
        (K := K') (L := L') W w')
  exact
    eE'.symm.toRingHom.comp
      ((finitePlaceAdicCompletionMap
        L L' U.1 ⟨U'.1, hU'L⟩).comp eE.toRingHom)

omit [IsAbelianGalois K L] in
/-- The localized-completion map agrees with the scalar-tower embedding on global elements. -/
theorem finitePlaceArtinLocalizedCompletion_towerPoint
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [NumberField L]
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (hW : finitePlaceBelow (K := K) W = v)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (w' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K' W) L')
    (hcentres :
      finitePlaceBelow (K := L)
          (finitePlaceExtensionCentre
            (K := K') (L := L') W w') =
        finitePlaceExtensionCentre
          (K := K) (L := L) v w)
    (x : (NumberField.HeightOneSpectrum.adicAbv K v).Completion) :
    finitePlaceArtinLocalizedCompletionBaseRingHom K' L' W w'
        (finitePlaceArtinRelativeCompletionRingHom
          (K := K) (K' := K') v W hW x) =
      finitePlaceArtinLocalizedCompletionRingHom
        (K := K) (L := L) (K' := K') (L' := L')
        v W w w' hcentres
        (finitePlaceArtinLocalizedCompletionBaseRingHom K L v w x) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let vK' := NumberField.HeightOneSpectrum.adicAbv K' W
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hvK' : vK'.IsNontrivial :=
    RayClass.adicAbv_isNontrivial W
  let hwK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hwK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let :=
    LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK w
  let hwK' :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K') w'.1
  let : SMul K' w'.1.Completion := hwK'.toSMul
  let : Algebra vK'.Completion w'.1.Completion :=
    AbsoluteValue.completionAlgebra vK' w'.1 w'.2
  let :=
    LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK' w'
  let C := vK.Completion
  let D := vK'.Completion
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let E' := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK' w'
  let : Algebra C D :=
    (finitePlaceArtinRelativeCompletionRingHom
      (K := K) (K' := K') v W hW).toAlgebra
  let : Algebra E E' :=
    (finitePlaceArtinLocalizedCompletionRingHom
      (K := K) (L := L) (K' := K') (L' := L')
      v W w w' hcentres).toAlgebra
  let : Algebra C E' :=
    ((algebraMap D E').comp (algebraMap C D)).toAlgebra
  change algebraMap C E' x =
    algebraMap E E' (algebraMap C E x)
  let U :=
    finitePlaceExtensionEquivAbove
      (K := K) (L := L) v w
  let U' :=
    finitePlaceExtensionEquivAbove
      (K := K') (L := L') W w'
  have hU'L : finitePlaceBelow (K := L) U'.1 = U.1 := by
    simpa only [
      U, U',
      finitePlaceExtensionEquivAbove_coe
    ] using hcentres
  have hU'K :
      finitePlaceBelow (K := K) U'.1 = v := by
    calc
      finitePlaceBelow (K := K) U'.1 =
          finitePlaceBelow (K := K)
            (finitePlaceBelow (K := K') U'.1) := by
        rw [finitePlaceBelow_finitePlaceBelow]
      _ = finitePlaceBelow (K := K) W := by
        rw [U'.2]
      _ = v := hW
  let eC :
      C ≃+* v.adicCompletion K :=
    (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
  let eD :
      D ≃+* W.adicCompletion K' :=
    (relativeFinitePlaceCompletionAlgEquiv W).toRingEquiv
  let eE :
      E ≃+* U.1.adicCompletion L :=
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
        vK hvK w).toRingEquiv.trans
      (finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) v w)
  let eE' :
      E' ≃+* U'.1.adicCompletion L' :=
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
        vK' hvK' w').toRingEquiv.trans
      (finitePlaceExtensionAdicCompletionRingEquiv
        (K := K') (L := L') W w')
  have hLowerBase (y : C) :
      eE (algebraMap C E y) =
        finitePlaceAdicCompletionMap
          K L v U (eC y) :=
    finitePlaceArtinLocalizedCompletion_algebraMap
      (F := K) (M := L) v w y
  have hUpperBase (y : D) :
      eE' (algebraMap D E' y) =
        finitePlaceAdicCompletionMap
          K' L' W U' (eD y) :=
    finitePlaceArtinLocalizedCompletion_algebraMap
      (F := K') (M := L') W w' y
  have hBaseMap (y : C) :
      eD (algebraMap C D y) =
        finitePlaceAdicCompletionMap
          K K' v ⟨W, hW⟩ (eC y) := by
    change
      eD (eD.symm
        (finitePlaceAdicCompletionMap
          K K' v ⟨W, hW⟩ (eC y))) =
        finitePlaceAdicCompletionMap
          K K' v ⟨W, hW⟩ (eC y)
    rw [eD.apply_symm_apply]
  apply eE'.injective
  calc
    eE' (algebraMap C E' x) =
        finitePlaceAdicCompletionMap
          K' L' W U'
          (finitePlaceAdicCompletionMap
            K K' v ⟨W, hW⟩ (eC x)) := by
      change eE' (algebraMap D E' (algebraMap C D x)) = _
      rw [hUpperBase, hBaseMap]
    _ =
        finitePlaceAdicCompletionMap
          K L' v ⟨U'.1, hU'K⟩ (eC x) :=
      finitePlaceAdicCompletionMap_comp
        K L' (M := K') v W U'.1 hW U'.2 hU'K (eC x)
    _ =
        finitePlaceAdicCompletionMap
          L L' U.1 ⟨U'.1, hU'L⟩
          (finitePlaceAdicCompletionMap
            K L v U (eC x)) := by
      symm
      exact
        finitePlaceAdicCompletionMap_comp
          K L' (M := L) v U.1 U'.1 U.2 hU'L hU'K (eC x)
    _ = eE' (algebraMap E E' (algebraMap C E x)) := by
      change
        _ =
          eE'
            (eE'.symm
              (finitePlaceAdicCompletionMap
                L L' U.1 ⟨U'.1, hU'L⟩
                (eE (algebraMap C E x))))
      rw [eE'.apply_symm_apply, hLowerBase]

omit [IsAbelianGalois K L] in
theorem finitePlaceArtinLocalizedCompletion_globalEmbedding
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [NumberField L]
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (w' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K' W) L')
    (hcentres :
      finitePlaceBelow (K := L)
          (finitePlaceExtensionCentre
            (K := K') (L := L') W w') =
        finitePlaceExtensionCentre
          (K := K) (L := L) v w)
    (x : L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let vK' := NumberField.HeightOneSpectrum.adicAbv K' W
    letI hwK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) w.1
    letI : SMul K w.1.Completion := hwK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI hwK' :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K') w'.1
    letI : SMul K' w'.1.Completion := hwK'.toSMul
    letI : Algebra vK'.Completion w'.1.Completion :=
      AbsoluteValue.completionAlgebra vK' w'.1 w'.2
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let E' := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK' w'
    letI : Algebra E E' :=
      (finitePlaceArtinLocalizedCompletionRingHom
        (K := K) (L := L) (K' := K') (L' := L')
        v W w w' hcentres).toAlgebra
    algebraMap E E'
        (AbsoluteValue.toAlgebraicLocalization
          vK w.1 w.2 x) =
      AbsoluteValue.toAlgebraicLocalization
        vK' w'.1 w'.2 (algebraMap L L' x) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let vK' := NumberField.HeightOneSpectrum.adicAbv K' W
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let hvK' : vK'.IsNontrivial :=
    RayClass.adicAbv_isNontrivial W
  let hwK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hwK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let hwK' :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K') w'.1
  let : SMul K' w'.1.Completion := hwK'.toSMul
  let : Algebra vK'.Completion w'.1.Completion :=
    AbsoluteValue.completionAlgebra vK' w'.1 w'.2
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let E' := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK' w'
  let : Algebra E E' :=
    (finitePlaceArtinLocalizedCompletionRingHom
      (K := K) (L := L) (K' := K') (L' := L')
      v W w w' hcentres).toAlgebra
  let U :=
    finitePlaceExtensionEquivAbove
      (K := K) (L := L) v w
  let U' :=
    finitePlaceExtensionEquivAbove
      (K := K') (L := L') W w'
  have hU'L : finitePlaceBelow (K := L) U'.1 = U.1 := by
    simpa only [
      U, U',
      finitePlaceExtensionEquivAbove_coe
    ] using hcentres
  let eE :
      E ≃+* U.1.adicCompletion L :=
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
        vK hvK w).toRingEquiv.trans
      (finitePlaceExtensionAdicCompletionRingEquiv
        (K := K) (L := L) v w)
  let eE' :
      E' ≃+* U'.1.adicCompletion L' :=
    (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
        vK' hvK' w').toRingEquiv.trans
      (finitePlaceExtensionAdicCompletionRingEquiv
        (K := K') (L := L') W w')
  have hLowerConcrete :
      eE
          (AbsoluteValue.toAlgebraicLocalization
            vK w.1 w.2 x) =
        FinitePlace.embedding U.1 x := by
    change
      finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) v w
          (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
            vK hvK w
            (AbsoluteValue.toAlgebraicLocalization
              vK w.1 w.2 x)) =
        FinitePlace.embedding U.1 x
    rw [
      AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion_coe]
    change
      finitePlaceExtensionAdicCompletionRingEquiv
          (K := K) (L := L) v w
          (AbsoluteValue.toCompletion w.1 x) =
        FinitePlace.embedding
          (finitePlaceExtensionCentre
            (K := K) (L := L) v w) x
    exact
      finitePlaceExtensionAdicCompletionRingEquiv_toCompletion
        (K := K) (L := L) v w x
  have hUpperConcrete :
      eE'
          (AbsoluteValue.toAlgebraicLocalization
            vK' w'.1 w'.2 (algebraMap L L' x)) =
        FinitePlace.embedding U'.1 (algebraMap L L' x) := by
    change
      finitePlaceExtensionAdicCompletionRingEquiv
          (K := K') (L := L') W w'
          (AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
            vK' hvK' w'
            (AbsoluteValue.toAlgebraicLocalization
              vK' w'.1 w'.2 (algebraMap L L' x))) =
        FinitePlace.embedding U'.1 (algebraMap L L' x)
    rw [
      AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion_coe]
    change
      finitePlaceExtensionAdicCompletionRingEquiv
          (K := K') (L := L') W w'
          (AbsoluteValue.toCompletion w'.1 (algebraMap L L' x)) =
        FinitePlace.embedding
          (finitePlaceExtensionCentre
            (K := K') (L := L') W w')
          (algebraMap L L' x)
    exact
      finitePlaceExtensionAdicCompletionRingEquiv_toCompletion
        (K := K') (L := L') W w' (algebraMap L L' x)
  apply eE'.injective
  change
    eE'
        (eE'.symm
          (finitePlaceAdicCompletionMap
            L L' U.1 ⟨U'.1, hU'L⟩
            (eE
              (AbsoluteValue.toAlgebraicLocalization
                vK w.1 w.2 x)))) =
      eE'
        (AbsoluteValue.toAlgebraicLocalization
          vK' w'.1 w'.2 (algebraMap L L' x))
  rw [eE'.apply_symm_apply, hLowerConcrete, hUpperConcrete]
  change
    finitePlaceAdicCompletionMap
        L L' U.1 ⟨U'.1, hU'L⟩
        (x : U.1.adicCompletion L) =
      (algebraMap L L' x : U'.1.adicCompletion L')
  exact
    finitePlaceAdicCompletionMap_coe
      L L' U.1 ⟨U'.1, hU'L⟩ x

/-- Restriction of localized automorphisms across a finite-place square with
different base fields. -/
noncomputable def finitePlaceCrossLocalRestrictionMonoidHom
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [NumberField L]
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (hW : finitePlaceBelow (K := K) W = v)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (w' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K' W) L')
    (hcentres :
      finitePlaceBelow (K := L)
          (finitePlaceExtensionCentre
            (K := K') (L := L') W w') =
        finitePlaceExtensionCentre
          (K := K) (L := L) v w) :
    finitePlaceArtinLocalizedAutomorphism K' L' W w' →*
      finitePlaceArtinLocalizedAutomorphism K L v w := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let vK' := NumberField.HeightOneSpectrum.adicAbv K' W
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let C := vK.Completion
  let D := vK'.Completion
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let E' := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK' w'
  letI : Algebra C E :=
    finitePlaceLocalArtinLocalizedAlgebra (K := K) (L := L) v w
  letI : Algebra D E' :=
    finitePlaceLocalArtinLocalizedAlgebra (K := K') (L := L') W w'
  let lowerGlobalAlgebra : Algebra K E :=
    LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK w
  let upperGlobalAlgebra : Algebra K' E' :=
    LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK' w'
  letI : Algebra C D :=
    (finitePlaceArtinRelativeCompletionRingHom
      (K := K) (K' := K') v W hW).toAlgebra
  let derivedStructures :
      PProd (Algebra E E') (Normal C E) := by
    letI : Algebra K E := lowerGlobalAlgebra
    letI : Algebra K' E' := upperGlobalAlgebra
    let upperAlgebra : Algebra E E' :=
      (finitePlaceArtinLocalizedCompletionRingHom
        (K := K) (L := L) (K' := K') (L' := L')
        v W w w' hcentres).toAlgebra
    letI : FiniteDimensional C E :=
      finitePlaceLocalArtinFiniteDimensional (K := K) (L := L) v w
    letI : IsAbelianGalois C E :=
      finitePlaceLocalArtinIsAbelianGalois (K := K) (L := L) v w
        (inferInstance : FiniteDimensional K L)
    letI hGaloisE : IsGalois C E :=
      (inferInstance : IsAbelianGalois C E).toIsGalois
    exact ⟨upperAlgebra, hGaloisE.to_normal⟩
  letI : Algebra E E' := derivedStructures.fst
  letI : Algebra C E' :=
    ((algebraMap D E').comp (algebraMap C D)).toAlgebra
  letI : IsScalarTower C D E' :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower C E E' :=
    IsScalarTower.of_algebraMap_eq' <| by
      apply RingHom.ext
      intro x
      exact
        finitePlaceArtinLocalizedCompletion_towerPoint
          (K := K) (L := L) (K' := K') (L' := L')
          v W hW w w' hcentres x
  letI : Normal C E := derivedStructures.snd
  exact
    (AlgEquiv.restrictNormalHom E).comp
      (AlgEquiv.restrictScalarsHom C)

theorem finitePlaceDecompositionEquiv_symm_action
    {F M : Type}
    [Field F] [Field M] [Algebra F M] [IsGalois F M]
    (vF : AbsoluteValue F ℝ)
    (hvF : vF.IsNontrivial)
    (wF : AbsoluteValueExtension vF M)
    (tau :
      letI hwF :=
        AbsoluteValue.extensionCompletionAlgebra
          (K := F) wF.1
      letI : SMul F wF.1.Completion := hwF.toSMul
      letI : Algebra vF.Completion wF.1.Completion :=
        AbsoluteValue.completionAlgebra vF wF.1 wF.2
      let E :=
        AlgebraicNumberTheory.Valuations.LocalizedCompletion vF wF
      E ≃ₐ[vF.Completion] E)
    (z : M) :
    letI hwF :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := F) wF.1
    letI : SMul F wF.1.Completion := hwF.toSMul
    letI : Algebra vF.Completion wF.1.Completion :=
      AbsoluteValue.completionAlgebra vF wF.1 wF.2
    let E :=
      AlgebraicNumberTheory.Valuations.LocalizedCompletion vF wF
    let e :
        absoluteValueDecompositionGroup F wF.1 ≃*
          (E ≃ₐ[vF.Completion] E) :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vF hvF wF
    let embedding : M →+* E :=
      AbsoluteValue.toAlgebraicLocalization vF wF.1 wF.2
    embedding (((e.symm tau).1 : M ≃ₐ[F] M) z) =
      tau (embedding z) := by
  let hwF :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := F) wF.1
  let : SMul F wF.1.Completion := hwF.toSMul
  let : Algebra vF.Completion wF.1.Completion :=
    AbsoluteValue.completionAlgebra vF wF.1 wF.2
  let E :=
    AlgebraicNumberTheory.Valuations.LocalizedCompletion vF wF
  let e :
      absoluteValueDecompositionGroup F wF.1 ≃*
        (E ≃ₐ[vF.Completion] E) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vF hvF wF
  let embedding : M →+* E :=
    AbsoluteValue.toAlgebraicLocalization vF wF.1 wF.2
  calc
    embedding (((e.symm tau).1 : M ≃ₐ[F] M) z) =
        e (e.symm tau) (embedding z) := by
      rw [
        localizationRamificationGroups_decompositionGroupEquiv_toLocalization]
    _ = tau (embedding z) := by
      rw [e.apply_symm_apply]

/-- Restriction through the completed local square agrees with restriction of
the corresponding global decomposition-group automorphisms. -/
theorem finitePlaceCrossDecompositionTransport
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [NumberField L]
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (v : HeightOneSpectrum (𝓞 K))
    (W : HeightOneSpectrum (𝓞 K'))
    (hW : finitePlaceBelow (K := K) W = v)
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (w' : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K' W) L')
    (hcentres :
      finitePlaceBelow (K := L)
          (finitePlaceExtensionCentre
            (K := K') (L := L') W w') =
        finitePlaceExtensionCentre
          (K := K) (L := L) v w)
    (tauUpper : finitePlaceArtinLocalizedAutomorphism K' L' W w') :
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K))
        (finitePlaceLocalToGlobalMonoidHom
          (K := K') (L := L') W w' tauUpper) =
      finitePlaceLocalToGlobalMonoidHom
        (K := K) (L := L) v w
        (finitePlaceCrossLocalRestrictionMonoidHom
          (K := K) (L := L) (K' := K') (L' := L')
          v W hW w w' hcentres tauUpper) := by
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let vK' := NumberField.HeightOneSpectrum.adicAbv K' W
    let hvK : vK.IsNontrivial :=
      RayClass.adicAbv_isNontrivial v
    let hvK' : vK'.IsNontrivial :=
      RayClass.adicAbv_isNontrivial W
    let C := vK.Completion
    let D := vK'.Completion
    let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
    let E' := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK' w'
    let : Algebra C E :=
      finitePlaceLocalArtinLocalizedAlgebra (K := K) (L := L) v w
    let : Algebra D E' :=
      finitePlaceLocalArtinLocalizedAlgebra (K := K') (L := L') W w'
    let : Algebra K E :=
      LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK w
    let : Algebra K' E' :=
      LocalClassFieldTheory.localizedCompletionGlobalAlgebra vK' w'
    let : Algebra C D :=
      (finitePlaceArtinRelativeCompletionRingHom
        (K := K) (K' := K') v W hW).toAlgebra
    let : Algebra E E' :=
      (finitePlaceArtinLocalizedCompletionRingHom
        (K := K) (L := L) (K' := K') (L' := L')
        v W w w' hcentres).toAlgebra
    let : Algebra C E' :=
      ((algebraMap D E').comp (algebraMap C D)).toAlgebra
    let : IsScalarTower C D E' :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower C E E' :=
      IsScalarTower.of_algebraMap_eq' <| by
        apply RingHom.ext
        intro x
        exact
          finitePlaceArtinLocalizedCompletion_towerPoint
            (K := K) (L := L) (K' := K') (L' := L')
            v W hW w w' hcentres x
    let : FiniteDimensional C E :=
      finitePlaceLocalArtinFiniteDimensional (K := K) (L := L) v w
    let : IsAbelianGalois C E :=
      finitePlaceLocalArtinIsAbelianGalois (K := K) (L := L) v w
        (inferInstance : FiniteDimensional K L)
    let hGaloisE : IsGalois C E :=
      (inferInstance : IsAbelianGalois C E).toIsGalois
    let : Normal C E := hGaloisE.to_normal
    let eLower :
        absoluteValueDecompositionGroup K w.1 ≃*
          (E ≃ₐ[C] E) :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK w
    let eUpper :
        absoluteValueDecompositionGroup K' w'.1 ≃*
          (E' ≃ₐ[D] E') :=
      decompositionGroupEquivAlgebraicLocalizationAut
        vK' hvK' w'
    let lowerEmbedding : L →+* E :=
      AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
    let upperEmbedding : L' →+* E' :=
      AbsoluteValue.toAlgebraicLocalization vK' w'.1 w'.2
    have hEmbedding (x : L) :
        algebraMap E E' (lowerEmbedding x) =
          upperEmbedding (algebraMap L L' x) := by
      exact
        finitePlaceArtinLocalizedCompletion_globalEmbedding
          (K := K) (L := L) (K' := K') (L' := L')
          v W w w' hcentres x
    have hUpperAction
        (tau : E' ≃ₐ[D] E') (z : L') :
        upperEmbedding
            (((eUpper.symm tau).1 : L' ≃ₐ[K'] L') z) =
          tau (upperEmbedding z) := by
      exact
        finitePlaceDecompositionEquiv_symm_action
          vK' hvK' w' tau z
    have hLowerAction
        (tau : E ≃ₐ[C] E) (z : L) :
        tau (lowerEmbedding z) =
          lowerEmbedding
            (((eLower.symm tau).1 : L ≃ₐ[K] L) z) := by
      exact
        (finitePlaceDecompositionEquiv_symm_action
          vK hvK w tau z).symm
    change
      ((AlgEquiv.restrictNormalHom L)
        ((AlgEquiv.restrictScalarsHom K)
          ((eUpper.symm tauUpper).1 : L' ≃ₐ[K'] L'))) =
        ((eLower.symm
          (AlgEquiv.restrictNormalHom E
            ((AlgEquiv.restrictScalarsHom C) tauUpper))).1 :
          L ≃ₐ[K] L)
    exact
      finitePlaceCrossDecompositionTransport_core
        (fun tau => ((eLower.symm tau).1 : L ≃ₐ[K] L))
        (fun tau => ((eUpper.symm tau).1 : L' ≃ₐ[K'] L'))
        lowerEmbedding upperEmbedding hEmbedding
        hUpperAction hLowerAction tauUpper

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_InfinitePlaceArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIsGalois
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

section AbelianTower

variable [IsAbelianGalois K L]

omit [NumberField L] in
/-- In an actual number-field diamond `K ⊂ K'`, `L ⊂ L'`, the
archimedean local Artin factor commutes with the ordinary completion
norm and with the standard restriction composite supplied by mathlib. -/
theorem chosenInfinitePlaceArtinMonoidHom_norm_restriction
    {K' L' : Type}
    [Field K'] [NumberField K']
    [Field L'] [NumberField L']
    [Algebra K K'] [Algebra K' L'] [Algebra K L']
    [IsScalarTower K K' L']
    [Algebra L L'] [IsScalarTower K L L']
    [IsAbelianGalois K' L']
    (W : InfinitePlace K') :
    let v := infinitePlaceBelow (K := K) W
    letI : W.1.LiesOver v.1 := ⟨rfl⟩
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (chosenInfinitePlaceArtinMonoidHom
          (K := K') (L := L') W) =
      (chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v).comp
        (LocalFieldTheory.normUnits
          v.Completion W.Completion) := by
  let v := infinitePlaceBelow (K := K) W
  let w' :=
    chosenInfinitePlaceAbove
      (L := L') W
  let w := w'.comap (algebraMap L L')
  have hW :
      W.comap (algebraMap K K') = v := rfl
  have hw' :
      w'.comap (algebraMap K' L') = W :=
    chosenInfinitePlaceAbove_comap
      (L := L') W
  have hw :
      w.comap (algebraMap K L) = v := by
    dsimp only [w]
    rw [← InfinitePlace.comap_comp,
      ← IsScalarTower.algebraMap_eq K L L',
      IsScalarTower.algebraMap_eq K K' L',
      InfinitePlace.comap_comp, hw', hW]
  let : W.1.LiesOver v.1 := ⟨rfl⟩
  calc
    ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K)).comp
        (chosenInfinitePlaceArtinMonoidHom
          (K := K') (L := L') W) =
      (infinitePlaceArtinMonoidHomOfPlace
        (K := K) (L := L) v w hw).comp
          (LocalFieldTheory.normUnits
            v.Completion W.Completion) :=
      infinitePlaceArtinMonoidHomOfPlace_norm_restriction
        (K := K) (L := L) v W w' hW hw'
    _ =
      (chosenInfinitePlaceArtinMonoidHom
        (K := K) (L := L) v).comp
          (LocalFieldTheory.normUnits
            v.Completion W.Completion) := by
      rw [chosenInfinitePlaceArtinMonoidHom]
      rw [infinitePlaceArtinMonoidHomOfPlace_eq
        (K := K) (L := L) v w
        (chosenInfinitePlaceAbove
          (L := L) v)
        hw
        (chosenInfinitePlaceAbove_comap
          (L := L) v)]

end AbelianTower

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_UnramifiedComparison
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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


section BaseResidueDegree

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The intrinsic finite abstract base has residue degree one for the local
datum. -/
theorem intrinsicFiniteAbstractBase_residueDegree_eq_one :
    ((intrinsicFiniteAbstractBase K).residueDegree (localResidueDatum K) : ℕ) = 1 := by
  rw [intrinsicFiniteAbstractBase_eq_base,
    FiniteAbstractField.base_residueDegree]
  rfl

end BaseResidueDegree

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_BaseComparison_IntrinsicBaseEquivalence
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
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

/-- A separable-closure equivalence identifies the intrinsic base subgroup of a
finite fixed field with its defining subgroup in the ambient Galois group. -/
noncomputable def intrinsicBaseEquivAmbientFixedField
    (K : Type) [Field K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K)) :
    let F := abstractFixedField K (SeparableClosure K) H.field
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    (e : SeparableClosure F ≃ₐ[F] SeparableClosure K) →
      (intrinsicAbstractBase F).toSubgroup ≃*
        H.field.toSubgroup := by
  dsimp only
  let F := abstractFixedField K (SeparableClosure K) H.field
  letI : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  intro e
  let φ :
      Gal(SeparableClosure F / F) ≃*
        H.field.toSubgroup :=
    (AlgEquiv.autCongr e).trans
      (abstractSubgroupEquivGaloisGroup
        K (SeparableClosure K) H.field).symm
  exact (intrinsicAbstractBaseEquivAbsolute F).trans φ

/-- On underlying automorphisms, the intrinsic-to-ambient fixed-field
equivalence is conjugation followed by the standard fixed-field subgroup equivalence. -/
@[simp]
theorem intrinsicBaseEquivAmbientFixedField_apply_val
    (K : Type) [Field K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K)) :
    let F := abstractFixedField K (SeparableClosure K) H.field
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (τ : (intrinsicAbstractBase F).toSubgroup),
      (intrinsicBaseEquivAmbientFixedField K H e τ).1 =
        ((AlgEquiv.autCongr e).trans
          (abstractSubgroupEquivGaloisGroup
            K (SeparableClosure K) H.field).symm) τ.1 := by
  dsimp only
  rintro e τ
  rfl

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldRelativeNorm
attribute [-instance] _root_.ClassFormation.DegreeData.FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionFinite _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.baseRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.fieldRepresentedAbsoluteFinite _root_.ClassFormation.DegreeData.FrobeniusPowerFixedFieldTower.relativeRepresentedQuotientFinite _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteAbstractConjugate_normal _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteResidueConjugate_normal _root_.ClassFormation.DegreeData.frobeniusClosure_isTopologicalGroup _root_.ClassFormation.DegreeData.frobeniusElementsMul _root_.ClassFormation.DegreeData.frobeniusElementsSemigroup _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteGaloisSubextension.abelianIntermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.baseFixingExtensionQuotient_finite_of_isSeparable _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localDecompositionResidueFintype _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.ClassFormation.DegreeData.abstractReciprocityEquiv_apply_of _root_.ClassFormation.DegreeData.abstractReciprocityTotallyRamifiedLowerGenerator_inclusion_restriction _root_.ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift_exponent _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_apply _root_.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_toMonoidHom _root_.ClassFormation.DegreeData.extensionNormalizedDegree_frobenius_mul _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_apply _root_.ClassFormation.DegreeData.finiteReciprocityCandidate_zero _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusConjugationEquiv_mk _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusConjugationLift_coe _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusConjugationLift_exponent _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusTowerLift_coe _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusTowerLift_exponent _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusTowerMap_mk _root_.ClassFormation.DegreeData.finiteUnramifiedDegreeEquiv_unramifiedFrobenius _root_.ClassFormation.DegreeData.finiteUnramifiedRestriction_frobenius _root_.ClassFormation.DegreeData.fixedFieldNormalizedDegree_generator _root_.ClassFormation.DegreeData.frobeniusActionConjugate_coe _root_.ClassFormation.DegreeData.frobeniusClosureDegreeInMulNatRange_coe _root_.ClassFormation.DegreeData.frobeniusClosureDegree_generator _root_.ClassFormation.DegreeData.frobeniusExponent_actionConjugate _root_.ClassFormation.DegreeData.frobeniusExponent_chosenDegreeOneFrobeniusElement _root_.ClassFormation.DegreeData.frobeniusExponent_mul _root_.ClassFormation.DegreeData.frobeniusExponent_powerOfDegreeOne _root_.ClassFormation.DegreeData.frobeniusFixedFieldAction_coe _root_.ClassFormation.DegreeData.frobeniusFixedFieldQuotientEquiv_mk _root_.ClassFormation.DegreeData.frobeniusFixedFieldToClosure_apply _root_.ClassFormation.DegreeData.frobeniusFixedField_normalizedDegreeEquiv_apply _root_.ClassFormation.DegreeData.frobeniusLiftDifference_coe _root_.ClassFormation.DegreeData.frobeniusMul_coe _root_.ClassFormation.DegreeData.frobeniusPowerOfDegreeOne_coe _root_.ClassFormation.DegreeData.frobeniusPowerSum_coe _root_.ClassFormation.DegreeData.frobeniusQuotientAction_mk _root_.ClassFormation.DegreeData.frobeniusQuotientRepresentation_apply _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenDegreeOneFrobeniusLiftOfTotallyRamified _root_.ClassFormation.DegreeData.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift _root_.ClassFormation.DegreeData.frobeniusRestriction_mul _root_.ClassFormation.DegreeData.maximalUnramifiedRestriction_frobenius _root_.ClassFormation.DegreeData.mem_frobeniusFixedField_iff _root_.ClassFormation.DegreeData.mem_frobeniusFixedSubgroupWithin_iff _root_.ClassFormation.DegreeData.normResidueSymbol_finiteReciprocityHom _root_.ClassFormation.DegreeData.transferNormNaturalityAbelianizedReciprocity_of _root_.ClassFormation.DegreeData.transferNormNaturalityFrobeniusIntermediateEquiv_mk _root_.ClassFormation.DegreeData.transferNormNaturalityIntermediateToFrobeniusSubgroup_apply _root_.ClassFormation.DegreeData.transferNormNaturalityTransferFrobeniusLift_coe _root_.ClassFormation.DegreeData.transferNormNaturalityTransferNormOrbitEquiv_mk _root_.ClassFormation.FiniteAbelianSubextension.extensionQuotientMk_apply _root_.ClassFormation.FiniteGaloisSubextension.lowerInclusionHom_mk _root_.ClassFormation.FiniteGaloisSubextension.upperRestrictionHom_mk _root_.ClassFormation.ValuationData.unramifiedNormQuotientValuation_finiteNormClass _root_.ClassFormation.ValuationData.unramifiedReciprocityEquiv_apply _root_.ClassFormation.ValuationData.unramifiedReciprocity_equiv_of_generator_apply _root_.ClassFormation.abstractReciprocityInclusion_mk _root_.ClassFormation.abstractReciprocityNormMap_finiteNormClass _root_.ClassFormation.abstractReciprocityNormProjection_finiteNormClass _root_.ClassFormation.abstractReciprocityRestriction_mk _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.ClassFormation.cyclicNormClassHom_apply _root_.ClassFormation.finiteReciprocityNaturalityConjugationNormMap_finiteNormClass _root_.ClassFormation.finiteReciprocityNaturalityConjugation_mk _root_.ClassFormation.finiteReciprocityNaturalityNormMap_finiteNormClass _root_.ClassFormation.finiteReciprocityNaturalityRestriction_mk _root_.ClassFormation.normResidueNaturalityAbelianizedConjugation_of_mk _root_.ClassFormation.normResidueNaturalityAbelianizedRestriction_of_mk _root_.ClassFormation.relativeConjugateCosetEquiv_mk _root_.ClassFormation.transferNormNaturalityExtensionFixedEquiv_apply_coe _root_.ClassFormation.transferNormNaturalityExtensionFixedEquiv_symm_coe _root_.ClassFormation.transferNormNaturalityIntermediateAbsoluteEquiv_apply _root_.ClassFormation.transferNormNaturalityIntermediateInclusion_mk _root_.ClassFormation.transferNormNaturalityIntermediateQuotientEquiv_mk _root_.ClassFormation.transferNormNaturality_normQuotientInclusion_finiteNormClass _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.baseFixingCosetToAlgHom_mk _root_.LocalClassFieldTheory.intrinsicBaseEquivAmbientFixedField_apply_val _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.ClassFormation.DegreeData.inertiaConjugationCosetEquiv_mk _root_.ClassFormation.transferNormNaturalityRightCosetProductEquiv_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Relative norms on actual fixed fields

This file identifies the class-formation relative norm on ambient fixed units
with the ordinary field norm between two concrete fixed fields.  The
intermediate extension need not be normal: relative left cosets are
identified with field embeddings into the common separably closed ambient
field, and both norms are then the same product of conjugates.
-/

noncomputable section

open scoped BigOperators

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation LocalClassFieldTheory

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsSepClosed Ω]

/-- A left coset of the abstract fixing subgroup restricts to an embedding
of the upper concrete fixed field into the common ambient field. -/
def abstractFixedFieldCosetToAlgHom
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    (K.toSubgroup ⧸ extensionSubgroup K L hLK) →
      (abstractRelativeFixedField k Ω hLK →ₐ[
        abstractFixedField k Ω K] Ω) := fun q =>
  Quotient.liftOn' q
    (fun σ => (abstractSubgroupEquivGaloisGroup k Ω K σ).toAlgHom.comp
      (abstractRelativeFixedField k Ω hLK).val)
    (by
      intro σ τ hστ
      have hmem : σ⁻¹ * τ ∈ extensionSubgroup K L hLK :=
        QuotientGroup.leftRel_apply.mp hστ
      let η : L.toSubgroup := ⟨(σ⁻¹ * τ).1, hmem⟩
      have hτ : τ = σ * Subgroup.inclusion hLK η := by
        apply Subtype.ext
        change τ.1 = σ.1 * η.1
        simp [η]
      apply AlgHom.ext
      intro x
      have hηfix : η.1 (x : Ω) = (x : Ω) :=
        (IntermediateField.mem_fixedField_iff L.toSubgroup
          (x : Ω)).1 x.property η.1 η.2
      change σ.1 (x : Ω) = τ.1 (x : Ω)
      calc
        σ.1 (x : Ω) = σ.1 (η.1 (x : Ω)) :=
          congrArg σ.1 hηfix.symm
        _ = (σ.1 * η.1) (x : Ω) := rfl
        _ = τ.1 (x : Ω) := by
          have hτ' := congrArg Subtype.val hτ
          change τ.1 = σ.1 * η.1 at hτ'
          rw [hτ'])

omit [IsSepClosed Ω] in
/-- States the theorem `abstractFixedFieldCosetToAlgHom_mk`. -/
@[simp]
theorem abstractFixedFieldCosetToAlgHom_mk
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup) (σ : K.toSubgroup) :
    abstractFixedFieldCosetToAlgHom k Ω K L hLK
        (QuotientGroup.mk σ) =
      (abstractSubgroupEquivGaloisGroup k Ω K σ).toAlgHom.comp
        (abstractRelativeFixedField k Ω hLK).val :=
  rfl

theorem abstractFixedFieldCosetToAlgHom_surjective
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [FiniteDimensional (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK)] :
    Function.Surjective
      (abstractFixedFieldCosetToAlgHom k Ω K L hLK) := by
  intro f
  let : Algebra.IsSeparable (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) :=
    Algebra.isSeparable_tower_bot_of_isSeparable
      (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) Ω
  let : Algebra.IsSeparable (abstractRelativeFixedField k Ω hLK) Ω :=
    Algebra.isSeparable_tower_top_of_isSeparable
      (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) Ω
  obtain ⟨φ, hφ⟩ :=
    (IsSepClosed.surjective_domRestrict_of_isSeparable
      (K := abstractFixedField k Ω K)
      (L := abstractRelativeFixedField k Ω hLK)
      (M := Ω) (E := Ω)) f
  let σReal : Gal(Ω / abstractFixedField k Ω K) :=
    AlgEquiv.ofBijective φ
      (Normal.toIsAlgebraic.algHom_bijective₂
        φ (AlgHom.id (abstractFixedField k Ω K) Ω)).1
  let σ : K.toSubgroup :=
    (abstractSubgroupEquivGaloisGroup k Ω K).symm σReal
  refine ⟨QuotientGroup.mk σ, ?_⟩
  apply AlgHom.ext
  intro x
  have hx := congrArg
    (fun ψ : abstractRelativeFixedField k Ω hLK →ₐ[
      abstractFixedField k Ω K] Ω => ψ x) hφ
  change σReal (x : Ω) = f x
  change φ (x : Ω) = f x at hx
  exact hx

omit [IsSepClosed Ω] in
theorem abstractFixedFieldCosetToAlgHom_injective
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    Function.Injective
      (abstractFixedFieldCosetToAlgHom k Ω K L hLK) := by
  intro q r hqr
  rw [← Quotient.out_eq q, ← Quotient.out_eq r] at hqr ⊢
  apply Quotient.sound'
  apply QuotientGroup.leftRel_apply.mpr
  apply (mem_extensionSubgroup_iff K L hLK
    ((Quotient.out q)⁻¹ * Quotient.out r)).2
  have hfix : (Quotient.out q).1⁻¹ * (Quotient.out r).1 ∈
      (abstractFixedField k Ω L).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    let y : abstractRelativeFixedField k Ω hLK := ⟨x, hx⟩
    have hy := congrArg
      (fun ψ : abstractRelativeFixedField k Ω hLK →ₐ[
        abstractFixedField k Ω K] Ω => ψ y) hqr
    change (Quotient.out q).1 (y : Ω) =
      (Quotient.out r).1 (y : Ω) at hy
    change (Quotient.out q).1⁻¹ ((Quotient.out r).1 x) = x
    rw [← hy]
    simp [y]
  rw [InfiniteGalois.fixingSubgroup_fixedField L] at hfix
  change (Quotient.out q).1⁻¹ * (Quotient.out r).1 ∈ L.toSubgroup
  exact hfix

/-- Abstract relative left cosets are precisely the embeddings of the upper
concrete fixed field into the ambient separably closed field. -/
def abstractFixedFieldCosetEquivAlgHom
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [FiniteDimensional (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK)] :
    (K.toSubgroup ⧸ extensionSubgroup K L hLK) ≃
      (abstractRelativeFixedField k Ω hLK →ₐ[
        abstractFixedField k Ω K] Ω) :=
  Equiv.ofBijective (abstractFixedFieldCosetToAlgHom k Ω K L hLK)
    ⟨abstractFixedFieldCosetToAlgHom_injective k Ω K L hLK,
      abstractFixedFieldCosetToAlgHom_surjective k Ω K L hLK⟩

omit [IsSepClosed Ω] in
/-- States the theorem `relativeCosetAction_abstractFixedFieldUnit_val`. -/
theorem relativeCosetAction_abstractFixedFieldUnit_val
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (x : (abstractRelativeFixedField k Ω hLK)ˣ)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK) :
    ((Additive.toMul
      (relativeCosetAction (galoisAmbientUnitsRep k Ω)
        K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK (Additive.ofMul x)) q) : Ωˣ) : Ω) =
      abstractFixedFieldCosetToAlgHom k Ω K L hLK q
        (x : abstractRelativeFixedField k Ω hLK) := by
  refine Quotient.inductionOn' q ?_
  intro σ
  rfl

attribute [local instance] LocalClassFieldTheory.finiteSeparableAlgHomFintypeRelative
/-- The class-formation relative norm on fixed coefficients is the ordinary
field norm between the two concrete fixed fields, without a normality
assumption on the intermediate extension. -/
theorem relativeNorm_abstractFixedFieldUnit_eq_normUnits
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField Gal(Ω / k)).toSubgroup ⧸
        extensionSubgroup (baseField Gal(Ω / k)) K
          (le_baseField K))]
    (x : (abstractRelativeFixedField k Ω hLK)ˣ) :
    relativeNorm (galoisAmbientUnitsRep k Ω) K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK (Additive.ofMul x)) =
      abstractFixedFieldUnitsEquivGaloisFixed k Ω K
        (Additive.ofMul
          (normUnits (abstractFixedField k Ω K)
            (abstractRelativeFixedField k Ω hLK) x)) := by
  let : FiniteDimensional (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K L hLK hKabsolute hfinite
  let : Algebra.IsSeparable (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) :=
    Algebra.isSeparable_tower_bot_of_isSeparable
      (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) Ω
  apply Subtype.ext
  apply Additive.ext
  apply Units.ext
  let Q := K.toSubgroup ⧸ extensionSubgroup K L hLK
  let := Fintype.ofFinite Q
  change
    ((Additive.toMul
      (relativeNormValue (galoisAmbientUnitsRep k Ω)
        K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK (Additive.ofMul x))) : Ωˣ) : Ω) = _
  rw [relativeNormValue]
  change
    (↑(Additive.toMul (∑ q : Q,
      relativeCosetAction (galoisAmbientUnitsRep k Ω)
        K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK (Additive.ofMul x)) q) : Ωˣ) : Ω) = _

  change (Units.coeHom Ω) (∏ q : Q,
    Additive.toMul
      (relativeCosetAction (galoisAmbientUnitsRep k Ω)
        K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK (Additive.ofMul x)) q)) = _
  rw [map_prod]
  change
    (∏ q : Q,
      ((Additive.toMul
        (relativeCosetAction (galoisAmbientUnitsRep k Ω)
          K L hLK
          (abstractRelativeFixedFieldUnitsEquivGaloisFixed
            k Ω K L hLK (Additive.ofMul x)) q) : Ωˣ) : Ω)) = _
  calc
    _ = ∏ σ : abstractRelativeFixedField k Ω hLK →ₐ[
        abstractFixedField k Ω K] Ω,
        σ (x : abstractRelativeFixedField k Ω hLK) := by
      exact Fintype.prod_equiv
        (abstractFixedFieldCosetEquivAlgHom k Ω K L hLK)
        (fun q : Q =>
          ((Additive.toMul
            (relativeCosetAction (galoisAmbientUnitsRep k Ω)
              K L hLK
              (abstractRelativeFixedFieldUnitsEquivGaloisFixed
                k Ω K L hLK (Additive.ofMul x)) q) : Ωˣ) : Ω))
        (fun σ : abstractRelativeFixedField k Ω hLK →ₐ[
          abstractFixedField k Ω K] Ω =>
            σ (x : abstractRelativeFixedField k Ω hLK))
        (relativeCosetAction_abstractFixedFieldUnit_val
          k Ω K L hLK x)
    _ = algebraMap (abstractFixedField k Ω K) Ω
        (Algebra.norm (abstractFixedField k Ω K)
          (x : abstractRelativeFixedField k Ω hLK)) :=
      (algebraMap_norm_eq_prod_embeddings_of_isSepClosed
        (abstractFixedField k Ω K) Ω
        (abstractRelativeFixedField k Ω hLK)
        (x : abstractRelativeFixedField k Ω hLK)).symm

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldNormResidueNaturality
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.finite_finsupp_nsmulQuotient _root_.KummerTheory.finite_sUnit_nthPowerQuotient _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_finPi_nsmulQuotient _root_.LocalFieldTheory.DiscreteValuationField.finite_padicInt_pi_nsmulQuotient_of_coprime _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerQuotient _root_.LocalFieldTheory.finite_nsmulAddQuotient_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instT2SpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.RayClass.Modulus.congruenceSubgroup_normal _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.intrinsicAbsoluteGaloisT2 _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Naturality of fixed-field norm-residue symbols

This file transports norm-restriction and transfer-inclusion naturality
from the closed-subgroup class formation to actual fixed fields in a single
Galois ambient field.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation LocalClassFieldTheory

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- The norm-residue symbol on the actual units of a concrete fixed field,
obtained from the abstract class-formation symbol through the canonical
fixed-unit and relative-Galois identifications. -/
noncomputable def abstractFixedFieldNormResidueSymbol
    (D : DegreeData (Gal(Ω / k)))
    (v : ValuationData D (galoisAmbientUnitsRep k Ω))
    (hcf : SatisfiesClassFieldAxiom
      (galoisAmbientUnitsRep k Ω))
    (K L : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField (Gal(Ω / k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω / k))) K
          (le_baseField K))] :
    Additive (abstractFixedField k Ω K)ˣ →+
      Additive (Abelianization
        Gal(abstractRelativeFixedField k Ω hLK /
          abstractFixedField k Ω K)) := by
  let KF : FiniteAbstractField (Gal(Ω / k)) :=
    ⟨K, hKabsolute⟩
  let E : FiniteGaloisSubextension KF.field :=
    ⟨L, hLK, hnormal, hfinite⟩
  exact
    (MulEquiv.toAdditive
      (abstractExtensionQuotientEquivGaloisGroup
        k Ω K L hLK hnormal).abelianizationCongr).toAddMonoidHom.comp
      ((D.normResidueSymbol (galoisAmbientUnitsRep k Ω)
        v hcf KF E).toAddMonoidHom.comp
        ((finiteNormClassHom (galoisAmbientUnitsRep k Ω)
          K L hLK).comp
          (abstractFixedFieldUnitsEquivGaloisFixed
            k Ω K).toAddMonoidHom))

/-- The ordinary field norm on units between two concrete fixed fields. -/
def abstractFixedFieldNormUnits
    (K K' : ClosedSubgroup (Gal(Ω / k)))
    (hK'K : K'.toSubgroup ≤ K.toSubgroup) :
    Additive (abstractRelativeFixedField k Ω hK'K)ˣ →+
      Additive (abstractFixedField k Ω K)ˣ :=
  MonoidHom.toAdditive
    (normUnits (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hK'K))

/-- Restriction between the abelianized actual relative Galois groups in a
fixed-field square, transported through the canonical quotient/Galois
equivalences. -/
noncomputable def abstractFixedFieldAbelianizedRestriction
    (K K' L L' : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hL'normal : (extensionSubgroup K' L' hL'K').Normal] :
    Additive (Abelianization
        Gal(abstractRelativeFixedField k Ω hL'K' /
          abstractFixedField k Ω K')) →+
      Additive (Abelianization
        Gal(abstractRelativeFixedField k Ω hLK /
          abstractFixedField k Ω K)) :=
  MonoidHom.toAdditive
    ((abstractExtensionQuotientEquivGaloisGroup
      k Ω K L hLK hLnormal).abelianizationCongr.toMonoidHom.comp
      ((normResidueNaturalityAbelianizedRestriction K K' L L'
        hLK hL'K' hK'K hL'L).comp
        (abstractExtensionQuotientEquivGaloisGroup
          k Ω K' L' hL'K'
          hL'normal).abelianizationCongr.symm.toMonoidHom))

/-- Norm-restriction naturality for actual fixed fields.
Actual Galois restriction is compatible with the ordinary unit norm and
the unit-level norm-residue symbols.  No normality of the intermediate
extension `K'/K` is assumed. -/
theorem abstractFixedFieldNormResidueSymbol_norm_restriction
    [IsSepClosed Ω]
    (D : DegreeData (Gal(Ω / k)))
    (v : ValuationData D (galoisAmbientUnitsRep k Ω))
    (hcf : SatisfiesClassFieldAxiom
      (galoisAmbientUnitsRep k Ω))
    (K K' L L' : ClosedSubgroup (Gal(Ω / k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hL'normal : (extensionSubgroup K' L' hL'K').Normal]
    [hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hL'K'finite : Finite
      (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K')]
    [hK'Kfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K K' hK'K)]
    [hKabsolute : Finite
      ((baseField (Gal(Ω / k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω / k))) K
          (le_baseField K))] :
    letI : Finite ((baseField (Gal(Ω / k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω / k))) K'
          (le_baseField K')) :=
      relativeTowerQuotientFinite (baseField (Gal(Ω / k))) K K' hK'K
        (le_baseField K)
    (abstractFixedFieldAbelianizedRestriction
        k Ω K K' L L' hLK hL'K' hK'K hL'L).comp
      (abstractFixedFieldNormResidueSymbol
        k Ω D v hcf K' L' hL'K') =
      (abstractFixedFieldNormResidueSymbol
        k Ω D v hcf K L hLK).comp
        (abstractFixedFieldNormUnits k Ω K K' hK'K) := by
  let : Finite ((baseField (Gal(Ω / k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω / k))) K'
        (le_baseField K')) :=
    relativeTowerQuotientFinite (baseField (Gal(Ω / k))) K K' hK'K
      (le_baseField K)
  let KF : FiniteAbstractField (Gal(Ω / k)) :=
    ⟨K, hKabsolute⟩
  let K'F : FiniteAbstractField (Gal(Ω / k)) :=
    ⟨K', inferInstance⟩
  let T : FiniteAbstractFieldExtension (Gal(Ω / k)) :=
    { field := K'F
      base := KF
      below := hK'K
      finiteQuotient := hK'Kfinite }
  apply AddMonoidHom.ext
  intro x
  have h := DFunLike.congr_fun
    (D.normResidueNaturality_norm_restriction
      (galoisAmbientUnitsRep k Ω) v hcf
      T L L' hLK hL'K' hL'L)
    (finiteNormClass (galoisAmbientUnitsRep k Ω) K' L' hL'K'
      (abstractFixedFieldUnitsEquivGaloisFixed k Ω K' x))
  dsimp only [T, KF, K'F] at h
  let q := abstractExtensionQuotientEquivGaloisGroup
    k Ω K L hLK hLnormal
  let q' := abstractExtensionQuotientEquivGaloisGroup
    k Ω K' L' hL'K' hL'normal
  let E : FiniteGaloisSubextension KF.field :=
    ⟨L, hLK, hLnormal, hLKfinite⟩
  let E' : FiniteGaloisSubextension K'F.field :=
    ⟨L', hL'K', hL'normal, hL'K'finite⟩
  change Additive.ofMul
      (q.abelianizationCongr
        (normResidueNaturalityAbelianizedRestriction K K' L L'
          hLK hL'K' hK'K hL'L
          (q'.abelianizationCongr.symm
            (q'.abelianizationCongr
              (Additive.toMul
                (D.normResidueSymbol
                  (galoisAmbientUnitsRep k Ω) v hcf K'F E'
                  (finiteNormClass (galoisAmbientUnitsRep k Ω) K' L' hL'K'
                    (abstractFixedFieldUnitsEquivGaloisFixed
                      k Ω K' x)))))))) =
    Additive.ofMul
      (q.abelianizationCongr
        (Additive.toMul
          (D.normResidueSymbol
            (galoisAmbientUnitsRep k Ω) v hcf KF E
            (finiteNormClass (galoisAmbientUnitsRep k Ω) K L hLK
              (abstractFixedFieldUnitsEquivGaloisFixed k Ω K
                (abstractFixedFieldNormUnits
                  k Ω K K' hK'K x))))))
  apply Additive.toMul.injective
  change q.abelianizationCongr _ = q.abelianizationCongr _
  rw [q.abelianizationCongr.apply_eq_iff_eq]
  rw [q'.abelianizationCongr.symm_apply_apply]
  change _ =
    D.normResidueSymbol
      (galoisAmbientUnitsRep k Ω) v hcf KF E
        (finiteReciprocityNaturalityNormMap
          (galoisAmbientUnitsRep k Ω) K K' L L'
          hLK hL'K' hK'K hL'L
          (finiteNormClass (galoisAmbientUnitsRep k Ω) K' L' hL'K'
            (abstractFixedFieldUnitsEquivGaloisFixed k Ω K' x))) at h
  rw [finiteReciprocityNaturalityNormMap_finiteNormClass] at h
  have hxFixed :
      abstractFixedFieldUnitsEquivGaloisFixed k Ω K' x =
        abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K K' hK'K
            (Additive.ofMul (Additive.toMul x)) := by
    rfl
  rw [hxFixed] at h
  rw [relativeNorm_abstractFixedFieldUnit_eq_normUnits
    k Ω K K' hK'K (Additive.toMul x)] at h
  exact congrArg Additive.toMul h

/-! ## Canonical local-field specializations -/

open scoped ValuativeRel

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_EmbeddedFrobeniusTransport
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

/-- The equivalence on absolute Galois base subgroups induced by a fixed-field
separable-closure equivalence is continuous. -/
theorem intrinsicBaseEquivAmbientFixedField_continuous
    (K : Type) [Field K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K)) :
    let F := abstractFixedField K (SeparableClosure K) H.field
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K),
      Continuous (intrinsicBaseEquivAmbientFixedField K H e) := by
  dsimp only
  let F := abstractFixedField K (SeparableClosure K) H.field
  let : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  intro e
  let : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H.field H.finite
  apply continuous_induced_rng.mpr
  change Continuous fun τ :
      (intrinsicAbstractBase F).toSubgroup =>
    (AlgEquiv.autCongr e τ.1).restrictScalars K
  exact
    (Field.absoluteGaloisGroup.ofIntermediateFieldInExtension_continuous
      F).comp
      ((Field.absoluteGaloisGroup.algEquiv_autCongr_continuous e).comp
        continuous_subtype_val)

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_Finite_LocalReciprocity_FixedFieldIntrinsicReciprocity_AmbientPrimeNormTransport
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalClassFieldTheory.principalUnitsSuccQuotTraceOfUnramifiedValuation_apply _root_.LocalClassFieldTheory.valuationModDegreeMulHom_apply _root_.LocalClassFieldTheory.valuationModDegree_apply _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.infinitePlace_mult_smul
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

/-- A valuation-subring-preserving ring equivalence carries some unit of
valuation one to a unit of valuation one. -/
theorem exists_valuationOne_unit_of_ringEquiv
    (L M : Type)
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    (phi : L ≃+* M)
    (hmem : ∀ x : L,
      x ∈ (ValuativeRel.valuation L).valuationSubring ↔
        phi x ∈ (ValuativeRel.valuation M).valuationSubring) :
    ∃ p : Lˣ,
      IsNonarchimedeanLocalField.valuationMap L
          (Additive.ofMul p) = 1 ∧
        IsNonarchimedeanLocalField.valuationMap M
          (Additive.ofMul
            (Units.mapEquiv phi.toMulEquiv p)) = 1 := by
  let r : 𝒪[L] ≃+* 𝒪[M] := {
    toFun := fun x =>
      ⟨phi (x : L), (hmem (x : L)).1 x.property⟩
    invFun := fun y =>
      ⟨phi.symm (y : M), (hmem (phi.symm (y : M))).2 (by
        rw [phi.apply_symm_apply]
        exact y.property)⟩
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
  let piOL : 𝒪[L] :=
    chosenIntegerRingUniformizer L
  have hpiOL : Irreducible piOL :=
    chosenIntegerRingUniformizer_irreducible L
  let piOM : 𝒪[M] := r piOL
  have hpiOM : Irreducible piOM :=
    (MulEquiv.irreducible_iff r.toMulEquiv).2 hpiOL
  let uL : Lˣ :=
    integerRingUniformizerFieldUnit L
  let uM : Mˣ :=
    Units.mapEquiv phi.toMulEquiv uL
  let pL : Lˣ := uL⁻¹
  let pM : Mˣ :=
    Units.mapEquiv phi.toMulEquiv pL
  have huL :
      (uL : L) = ((piOL : 𝒪[L]) : L) := rfl
  have huM :
      (uM : M) = ((piOM : 𝒪[M]) : M) := rfl
  have hpM : pM = uM⁻¹ := by
    simp [pM, pL, uM]
  have hpLvalue :
      IsNonarchimedeanLocalField.valuationMap L
        (Additive.ofMul pL) = 1 := by
    exact
      v_integerRingIrreducibleFieldUnit_inv
        L piOL hpiOL uL huL
  have hpMvalue :
      IsNonarchimedeanLocalField.valuationMap M
        (Additive.ofMul pM) = 1 := by
    rw [hpM]
    exact
      v_integerRingIrreducibleFieldUnit_inv
        M piOM hpiOM uM huM
  exact ⟨pL, hpLvalue, hpMvalue⟩

/-- A chosen valuation-one unit whose image under a valuation-compatible
ring equivalence also has valuation one. -/
noncomputable def chosenValuationOneUnitOfRingEquiv
    (L M : Type)
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    (phi : L ≃+* M)
    (hmem : ∀ x : L,
      x ∈ (ValuativeRel.valuation L).valuationSubring ↔
        phi x ∈ (ValuativeRel.valuation M).valuationSubring) :
    Lˣ :=
  Classical.choose
    (exists_valuationOne_unit_of_ringEquiv L M phi hmem)

/-- The chosen transported unit has valuation one in its source field. -/
theorem chosenValuationOneUnitOfRingEquiv_source
    (L M : Type)
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    (phi : L ≃+* M)
    (hmem : ∀ x : L,
      x ∈ (ValuativeRel.valuation L).valuationSubring ↔
        phi x ∈ (ValuativeRel.valuation M).valuationSubring) :
    IsNonarchimedeanLocalField.valuationMap L
        (Additive.ofMul
          (chosenValuationOneUnitOfRingEquiv L M phi hmem)) = 1 :=
  (Classical.choose_spec
    (exists_valuationOne_unit_of_ringEquiv L M phi hmem)).1

/-- The image of the chosen transported unit has valuation one in the
target field. -/
theorem chosenValuationOneUnitOfRingEquiv_target
    (L M : Type)
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    (phi : L ≃+* M)
    (hmem : ∀ x : L,
      x ∈ (ValuativeRel.valuation L).valuationSubring ↔
        phi x ∈ (ValuativeRel.valuation M).valuationSubring) :
    IsNonarchimedeanLocalField.valuationMap M
        (Additive.ofMul
          (Units.mapEquiv phi.toMulEquiv
            (chosenValuationOneUnitOfRingEquiv L M phi hmem))) = 1 :=
  (Classical.choose_spec
    (exists_valuationOne_unit_of_ringEquiv L M phi hmem)).2

end LocalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_ChangedUniformizerCoefficient
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitInverseLimitCarrierPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrierPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.adicPrincipalUnitsPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.discretePrincipalUnitQuotientPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousAdd _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitContinuousSMul _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitProdiscreteLimitPadicModule _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextFieldAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextQPadic _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralLatticeContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFinite _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedMaximalIdealPowContextModuleFree _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFact _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextFiniteDimensional _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationExtension _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.standardLubinTateLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.standardLubinTateLevelField_galFinite _root_.LubinTate.standardLubinTateLevelField_isAbelianGalois _root_.LubinTate.standardLubinTateLevelField_isMulCommutative _root_.LubinTate.standardLubinTateUnitParameter_commGroup _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.Higher.lowerRamificationGroup.instNormal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupMulSemiringAction _root_.RamificationTheory.HilbertRamification.CompleteDVF.decompositionGroupResidueFieldMulSemiringAction _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The coefficient source for the p-adic changed-uniformizer intertwiner

Let `k` be an algebraic closure of `ZMod p`.  The Witt ring `W(k)` is the
integer ring of the completed maximal-unramified coefficient field used in
the changed-uniformizer construction. Mathlib's `WittVector.frobeniusRotation` supplies the
actual unit `ε ∈ W(k)ˣ` satisfying

`φ(ε) = ε u`

for every p-adic integer unit `u`.  This is precisely the linear-coefficient
equation for the semilinear changed-uniformizer intertwiner.

No second p-adic integer ring or Frobenius is introduced here: the base map
uses mathlib's equivalence `W(ZMod p) ≃+* ℤ_[p]`, and `φ` is
`WittVector.frobenius`.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

/-- Witt Frobenius fixes the chosen p-adic valuation-ring coefficients. -/
theorem padicValuationSubringToCompletedUnramifiedWittRing_frobenius
    (p : ℕ) [Fact p.Prime]
    (z : (padicLocalField p).valuationSubring) :
    WittVector.frobenius
        (padicValuationSubringToCompletedUnramifiedWittRing p z) =
      padicValuationSubringToCompletedUnramifiedWittRing p z := by
  change
    WittVector.frobenius
        (padicIntToCompletedUnramifiedWittRing p
          ((padicIntEquivValuationSubring p).symm z)) =
      padicIntToCompletedUnramifiedWittRing p
        ((padicIntEquivValuationSubring p).symm z)
  exact
    padicIntToCompletedUnramifiedWittRing_frobenius p
      ((padicIntEquivValuationSubring p).symm z)

theorem completedUnramifiedWittUnit_coeff_zero_ne_zero
    (p : ℕ) [Fact p.Prime]
    (u : (padicCompletedUnramifiedWittRing p)ˣ) :
    ((u : padicCompletedUnramifiedWittRing p).coeff 0) ≠ 0 := by
  have hu :
      IsUnit
        (WittVector.constantCoeff
          (u : padicCompletedUnramifiedWittRing p)) :=
    u.isUnit.map WittVector.constantCoeff
  simpa only [WittVector.constantCoeff_apply] using hu.ne_zero

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicField_hasEnoughRootsOfUnity _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isAbelianGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isIntegral _root_.KummerTheory.rationalCyclotomicTorsionFixedField_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite-place Artin symbols in rational cyclotomic levels

At a rational prime away from the cyclotomic level, the chosen completed
extension is unramified.  Its normalized local Artin map is therefore the
arithmetic Frobenius raised to the local valuation.  The genuine primitive
root in the localized cyclotomic level identifies the image of arithmetic
Frobenius under the global cyclotomic character with the residue prime.
-/

open scoped Classical NNReal NumberField ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open LubinTate

/-! Named compatibility witnesses used by the ramified-prime and ray-norm
modules.  They are not installed as a duplicate module-level instance family;
the canonical instances above already provide the same data. -/

attribute [local instance] GlobalClassFieldTheory.Reciprocity.instFactPrimeValNat_solutions_2
attribute [local instance] GlobalClassFieldTheory.Reciprocity.instNeZeroNatVal_solutions
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLevelFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLevelIsAbelianGalois
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseLocallyCompactSpace
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseIsUltrametricDist
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuationIsNontrivial
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuationCompatible
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuativeRelIsNontrivial
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceCompletionRatAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseNontriviallyNormedField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValued
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuativeRel
noncomputable local instance rationalFinitePlaceBaseIsValuativeTopology_ra3cf61_1
    (q : Nat.Primes) :
    IsValuativeTopology
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  isValuativeTopology_of_valued_ofValuation
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion ℝ≥0
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseIsNonarchimedeanLocalField
abbrev rationalCyclotomicArtinExtension
    (m : ℕ+) (q : Nat.Primes) :
    AbsoluteValueExtension
      (rationalCyclotomicArtinBaseAbv q)
      (rationalCyclotomicArtinLevel m) :=
  chosenFinitePlaceExtension
    (L := rationalCyclotomicArtinLevel m)
    (rationalCyclotomicArtinPlace q)

abbrev rationalCyclotomicArtinLocalizedField
    (m : ℕ+) (q : Nat.Primes) :=
  AlgebraicNumberTheory.Valuations.LocalizedCompletion
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)

@[reducible]
noncomputable local instance rationalCyclotomicArtinExtensionAlgebra
    (m : ℕ+) (q : Nat.Primes) :
    Algebra ℚ
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra
    (K := ℚ) (rationalCyclotomicArtinExtension m q).1

@[reducible]
noncomputable local instance rationalCyclotomicArtinExtensionSMul
    (m : ℕ+) (q : Nat.Primes) :
    SMul ℚ
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  (rationalCyclotomicArtinExtensionAlgebra m q).toSMul

@[reducible]
noncomputable local instance
    rationalCyclotomicArtinCompletionAlgebra
    (m : ℕ+) (q : Nat.Primes) :
    Algebra (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinExtension m q).1.Completion :=
  AbsoluteValue.completionAlgebra
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q).1
    (rationalCyclotomicArtinExtension m q).2

end Reciprocity
end GlobalClassFieldTheory
end
end


