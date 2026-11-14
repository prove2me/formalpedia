-- Prove2me | Definitions.Def_OAIQ244Duke095
-- name    : OAIQ244Duke095
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-14T01:59:55.881443+00:00
-- url     : https://prove2.me/theorems/ecbe2e76-bf7b-4aff-bd2c-ed2cc856b55b
-- title:
--   Definitions bundle OAIQ244Duke095 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 1 definition and 19 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalInput`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin`, `LocalClassFieldTheory_LubinTateApplication_PadicMultiplicativeArtinComparison`, `LubinTate_Padic_CompletedChangedStandardFrobenius`, `LubinTate_Padic_CompletedChangedStandardUnramified`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke092` and `OAIQ244Duke093` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ244Duke097`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Hom.Basic
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
import Definitions.Def_OAIQ244Duke092
import Definitions.Def_OAIQ244Duke093

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_CompletedChangedStandardUnramified
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceBaseFourthRootField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceEmbeddedExtensionField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.HilbertRamification.Dedekind.basePrime_liesOver _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_finiteDimensional _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedChangedUniformizerFixedField_isNonarchimedeanLocalField _root_.LubinTate.padicCompletedChangedUniformizerFixedField_nontriviallyNormedField _root_.LubinTate.padicCompletedChangedUniformizerFixedField_valuativeRel _root_.LubinTate.padicCompletedStandardChangedCompositum_finiteDimensional_over_changedField _root_.LubinTate.padicCompletedStandardChangedCompositum_integerRing_isIntegralClosure _root_.LubinTate.padicCompletedStandardChangedCompositum_isGalois_over_changedField _root_.LubinTate.padicCompletedStandardChangedCompositum_isNonarchimedeanLocalField _root_.LubinTate.padicCompletedStandardChangedCompositum_localCompleteDVFValuation_hasExtension _root_.LubinTate.padicCompletedStandardChangedCompositum_nontriviallyNormedField _root_.LubinTate.padicCompletedStandardChangedCompositum_valuationSubring_isIntegralClosure _root_.LubinTate.padicCompletedStandardChangedCompositum_valuation_hasExtension _root_.LubinTate.padicCompletedStandardChangedCompositum_valuativeRel _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedMaximalIdeal.instLiesOver _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseIsNonarchimedeanLocalField _root_.chosenFinitePlaceBaseValuationIsNontrivial _root_.chosenFinitePlaceBaseValuativeRel _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The completed standard/changed compositum is unramified over the changed field

The genuine changed-uniformizer theta point is a uniformizer of the ambient
completed Lubin--Tate level.  Uniqueness of finite separable extensions of
the p-adic valuation transports this fact to both the changed fixed field and
the finite standard/changed compositum.  Since the same element is a
uniformizer on both sides, their relative ramification index is one.
-/

noncomputable section

namespace LubinTate

open scoped ValuativeRel

open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

/-- The finite standard/changed compositum has relative ramification index
one over the changed fixed field. -/
theorem
    padicCompletedStandardChangedCompositum_ramificationIndex_eq_one
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let D := padicCompletedChangedUniformizerFixedField p u n
    let M := padicCompletedStandardChangedCompositum p u n
    letI : NontriviallyNormedField D :=
      finiteExtensionSpectralNormedField ℚ_[p] D
    letI : ValuativeRel D :=
      finiteExtensionSpectralValuativeRel ℚ_[p] D
    let : IsNonarchimedeanLocalField D :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
    letI : NontriviallyNormedField M :=
      finiteExtensionSpectralNormedField ℚ_[p] M
    letI : ValuativeRel M :=
      finiteExtensionSpectralValuativeRel ℚ_[p] M
    let : IsNonarchimedeanLocalField M :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
    let :
        Valuation.HasExtension (ValuativeRel.valuation D)
          (ValuativeRel.valuation M) :=
      finiteExtensionSpectralValuation_hasExtension_of_tower ℚ_[p] D M
    let :
        (localCompleteDVF D).valuation.HasExtension
          (localCompleteDVF M).valuation :=
      localCompleteDVFValuation_hasExtension D M
    ramificationIndex (localCompleteDVF D).toDVF
      (localCompleteDVF M).toDVF = 1 := by
  let D := padicCompletedChangedUniformizerFixedField p u n
  let M := padicCompletedStandardChangedCompositum p u n
  let : NontriviallyNormedField D :=
    finiteExtensionSpectralNormedField ℚ_[p] D
  let : ValuativeRel D :=
    finiteExtensionSpectralValuativeRel ℚ_[p] D
  let : IsNonarchimedeanLocalField D :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
  let : NontriviallyNormedField M :=
    finiteExtensionSpectralNormedField ℚ_[p] M
  let : ValuativeRel M :=
    finiteExtensionSpectralValuativeRel ℚ_[p] M
  let : IsNonarchimedeanLocalField M :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
  let :
      Valuation.HasExtension (ValuativeRel.valuation D)
        (ValuativeRel.valuation M) :=
    finiteExtensionSpectralValuation_hasExtension_of_tower ℚ_[p] D M
  let :
      (localCompleteDVF D).valuation.HasExtension
        (localCompleteDVF M).valuation :=
    localCompleteDVFValuation_hasExtension D M
  let base := localCompleteDVF D
  let target := localCompleteDVF M
  obtain ⟨hthetaD, hthetaM⟩ :=
    padicCompletedChangedUniformizerPrimeElement_isUniformizer_in_changedField_and_compositum
      p u n
  let thetaInteger : base.valuationSubring :=
    ⟨padicCompletedChangedUniformizerPrimeElement p u n,
      hthetaD.val_lt_one.le⟩
  have hthetaMap :
      target.valuation.IsUniformizer
        (((integerMap base.toDVF target.toDVF thetaInteger :
          target.valuationSubring) : M)) := by
    rw [integerMap_apply]
    exact hthetaM
  exact
    LocalFieldTheory.DiscreteValuationField.ValuedExtension.ramificationIndex_eq_one_of_integerMap_uniformizer
      base target thetaInteger
      (by simpa only [thetaInteger] using hthetaD)
      hthetaMap

/-- With the canonical p-adic spectral valuations, the finite
standard/changed compositum is an unramified valued extension of the changed
fixed field. -/
theorem
    padicCompletedStandardChangedCompositum_isUnramifiedValuedExtension
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let D := padicCompletedChangedUniformizerFixedField p u n
    let M := padicCompletedStandardChangedCompositum p u n
    let : FiniteDimensional D M :=
      FiniteDimensional.right ℚ_[p] D M
    let : Algebra.IsSeparable D M :=
      Algebra.isSeparable_tower_top_of_isSeparable
        (F := ℚ_[p]) (L := D) (E := M)
    letI : NontriviallyNormedField D :=
      finiteExtensionSpectralNormedField ℚ_[p] D
    letI : ValuativeRel D :=
      finiteExtensionSpectralValuativeRel ℚ_[p] D
    let : IsNonarchimedeanLocalField D :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
    letI : NontriviallyNormedField M :=
      finiteExtensionSpectralNormedField ℚ_[p] M
    letI : ValuativeRel M :=
      finiteExtensionSpectralValuativeRel ℚ_[p] M
    let : IsNonarchimedeanLocalField M :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
    let :
        Valuation.HasExtension (ValuativeRel.valuation D)
          (ValuativeRel.valuation M) :=
      finiteExtensionSpectralValuation_hasExtension_of_tower ℚ_[p] D M
    let :
        (localCompleteDVF D).valuation.HasExtension
          (localCompleteDVF M).valuation :=
      localCompleteDVFValuation_hasExtension D M
    let :
        IsScalarTower (localCompleteDVF D).valuationSubring
          (localCompleteDVF M).valuationSubring M :=
      IsScalarTower.of_algebraMap_eq' rfl
    let :
        Module.Finite (ValuativeRel.valuation D).integer
          (ValuativeRel.valuation M).integer := by
      change
        Module.Finite (localCompleteDVF D).valuationSubring
          (localCompleteDVF M).valuationSubring
      exact
        ValuationTheory.DiscreteValuationField.ValuedExtension.moduleFinite_target_valuationSubring_of_finite_separable
          (localCompleteDVF D) (localCompleteDVF M)
    LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
      D M := by
  let D := padicCompletedChangedUniformizerFixedField p u n
  let M := padicCompletedStandardChangedCompositum p u n
  let : FiniteDimensional D M :=
    FiniteDimensional.right ℚ_[p] D M
  let : Algebra.IsSeparable D M :=
    Algebra.isSeparable_tower_top_of_isSeparable
      (F := ℚ_[p]) (L := D) (E := M)
  let : NontriviallyNormedField D :=
    finiteExtensionSpectralNormedField ℚ_[p] D
  let : ValuativeRel D :=
    finiteExtensionSpectralValuativeRel ℚ_[p] D
  let : IsNonarchimedeanLocalField D :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
  let : NontriviallyNormedField M :=
    finiteExtensionSpectralNormedField ℚ_[p] M
  let : ValuativeRel M :=
    finiteExtensionSpectralValuativeRel ℚ_[p] M
  let : IsNonarchimedeanLocalField M :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
  let :
      Valuation.HasExtension (ValuativeRel.valuation D)
        (ValuativeRel.valuation M) :=
    finiteExtensionSpectralValuation_hasExtension_of_tower ℚ_[p] D M
  let :
      (localCompleteDVF D).valuation.HasExtension
        (localCompleteDVF M).valuation :=
    localCompleteDVFValuation_hasExtension D M
  let :
      IsScalarTower (localCompleteDVF D).valuationSubring
        (localCompleteDVF M).valuationSubring M :=
    IsScalarTower.of_algebraMap_eq' rfl
  let :
      Module.Finite (ValuativeRel.valuation D).integer
        (ValuativeRel.valuation M).integer := by
    change
      Module.Finite (localCompleteDVF D).valuationSubring
        (localCompleteDVF M).valuationSubring
    exact
      ValuationTheory.DiscreteValuationField.ValuedExtension.moduleFinite_target_valuationSubring_of_finite_separable
        (localCompleteDVF D) (localCompleteDVF M)
  let base := localCompleteDVF D
  let target := localCompleteDVF M
  let :
      Module.IsTorsionFree base.valuationSubring target.valuationSubring :=
    ValuationTheory.DiscreteValuationField.ValuedExtension.moduleIsTorsionFree_target_valuationSubring_of_finite_separable
      base target
  have hramification :
      ramificationIndex base.toDVF target.toDVF = 1 :=
    padicCompletedStandardChangedCompositum_ramificationIndex_eq_one
      p u n
  exact {
    maximalIdeal_ramificationIdx_eq_one := by
      change target.maximalIdeal.ramificationIdx base.valuationSubring = 1
      have hbaseMaximal_ne :
          (base.maximalIdeal : Ideal base.valuationSubring) ≠ ⊥ :=
        Ring.ne_bot_of_isMaximal_of_not_isField
          (IsLocalRing.maximalIdeal.isMaximal base.valuationSubring)
          (IsDiscreteValuationRing.not_isField base.valuationSubring)
      rw [← Ideal.ramificationIdx'_eq_ramificationIdx
        base.maximalIdeal target.maximalIdeal hbaseMaximal_ne]
      exact hramification
  }

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_CompletedChangedStandardFrobenius
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceBaseFourthRootField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceEmbeddedExtensionField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_finiteDimensional _root_.LocalClassFieldTheory.finiteGaloisFieldRangeOfEmbedding_isGalois _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalClassFieldTheory.localSeparableValuationHasExtension _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedSubring.instIsLocalRing _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.LocalClassFieldTheory.localAbsoluteValuationHasExtension _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseIsNonarchimedeanLocalField _root_.chosenFinitePlaceBaseValuativeRel _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Frobenius orientation in the completed standard/changed compositum

The finite standard/changed compositum is unramified over the completed
changed-uniformizer fixed field.  Its explicit relative Artin candidate is
the restriction of inverse completed coefficient Frobenius.

Both automorphisms can be compared faithfully on residue fields.  Completed
coefficient Frobenius and relative residue arithmetic Frobenius are the same
`p`-power map, so the explicit candidate is the inverse of the actual
arithmetic Frobenius of the finite unramified extension.
-/

noncomputable section

namespace LubinTate

open scoped ValuativeRel

open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

/-- The explicit changed-uniformizer relative Artin candidate is the
inverse of the actual arithmetic Frobenius of the unramified finite
standard/changed compositum. -/
theorem
    padicCompletedChangedUniformizerRelativeArtinCandidate_eq_inverseArithmeticFrobenius
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let D := padicCompletedChangedUniformizerFixedField p u n
    let M := padicCompletedStandardChangedCompositum p u n
    let : FiniteDimensional D M :=
      FiniteDimensional.right ℚ_[p] D M
    let : IsGalois D M :=
      IsGalois.tower_top_of_isGalois ℚ_[p] D M
    letI : NontriviallyNormedField D :=
      finiteExtensionSpectralNormedField ℚ_[p] D
    letI : ValuativeRel D :=
      finiteExtensionSpectralValuativeRel ℚ_[p] D
    let : IsNonarchimedeanLocalField D :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
    letI : NontriviallyNormedField M :=
      finiteExtensionSpectralNormedField ℚ_[p] M
    letI : ValuativeRel M :=
      finiteExtensionSpectralValuativeRel ℚ_[p] M
    let : IsNonarchimedeanLocalField M :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
    let :
        Valuation.HasExtension (ValuativeRel.valuation D)
          (ValuativeRel.valuation M) :=
      finiteExtensionSpectralValuation_hasExtension_of_tower
        ℚ_[p] D M
    let :
        Module.Finite
          (ValuativeRel.valuation D).integer
          (ValuativeRel.valuation M).integer :=
      integerRing_moduleFinite_of_finite_separable D M
    let :
        IsIntegralClosure
          (ValuativeRel.valuation M).integer
          (ValuativeRel.valuation D).integer M :=
      padicCompletedStandardChangedCompositum_integerRing_isIntegralClosure
        p u n
    let :
        IsNonarchimedeanLocalField.IsUnramifiedValuedExtension D M :=
      padicCompletedStandardChangedCompositum_isUnramifiedValuedExtension
        p u n
    padicCompletedChangedUniformizerRelativeArtinCandidate p u n =
      (arithmeticFrobeniusOfUnramifiedValuation D M)⁻¹ := by
  let D := padicCompletedChangedUniformizerFixedField p u n
  let M := padicCompletedStandardChangedCompositum p u n
  let : FiniteDimensional D M :=
    FiniteDimensional.right ℚ_[p] D M
  let : IsGalois D M :=
    IsGalois.tower_top_of_isGalois ℚ_[p] D M
  let : NontriviallyNormedField D :=
    finiteExtensionSpectralNormedField ℚ_[p] D
  let : ValuativeRel D :=
    finiteExtensionSpectralValuativeRel ℚ_[p] D
  let : IsNonarchimedeanLocalField D :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
  let : NontriviallyNormedField M :=
    finiteExtensionSpectralNormedField ℚ_[p] M
  let : ValuativeRel M :=
    finiteExtensionSpectralValuativeRel ℚ_[p] M
  let : IsNonarchimedeanLocalField M :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
  let :
      Valuation.HasExtension (ValuativeRel.valuation D)
        (ValuativeRel.valuation M) :=
    finiteExtensionSpectralValuation_hasExtension_of_tower
      ℚ_[p] D M
  let :
      Module.Finite
        (ValuativeRel.valuation D).integer
        (ValuativeRel.valuation M).integer :=
    integerRing_moduleFinite_of_finite_separable D M
  let :
      IsIntegralClosure
        (ValuativeRel.valuation M).integer
        (ValuativeRel.valuation D).integer M :=
    padicCompletedStandardChangedCompositum_integerRing_isIntegralClosure
      p u n
  let :
      IsNonarchimedeanLocalField.IsUnramifiedValuedExtension D M :=
    padicCompletedStandardChangedCompositum_isUnramifiedValuedExtension
      p u n
  have hM :
      IsLocalRing.ResidueField
          (localCompleteDVF M).valuation.valuationSubring =
        𝓀[M] := by
    rw [localCompleteDVF_valuation_eq M]
    rfl
  have hD :
      IsLocalRing.ResidueField
          (localCompleteDVF D).valuation.valuationSubring =
        𝓀[D] := by
    rw [localCompleteDVF_valuation_eq D]
    rfl
  cases hM
  cases hD
  apply
    galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation
      D M
  calc
    galoisGroupResidueAlgEquivHomOfIsIntegralClosure D M
        (padicCompletedChangedUniformizerRelativeArtinCandidate p u n) =
      (residueExtensionArithmeticFrobeniusOfValuationExtension D M)⁻¹ := by
        apply AlgEquiv.ext
        intro a
        rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_apply D M]
        let embedding :=
          padicCompletedStandardChangedCompositumResidueEmbedding p u n
        let completedFrobenius :=
          IsLocalRing.ResidueField.mapEquiv
            (padicCompletedUnitFrobeniusIntegerEquiv p n u⁻¹)
        let x :
            IsLocalRing.ResidueField
              (localCompleteDVF M).valuation.valuationSubring :=
          (residueExtensionArithmeticFrobeniusOfValuationExtension D M)⁻¹ a
        apply embedding.injective
        change
          embedding
              (galoisGroupResidueFieldEquivOfIsIntegralClosure
                D M
                (padicCompletedChangedUniformizerRelativeArtinCandidate
                  p u n) a) =
            embedding x
        rw [show
          embedding
              (galoisGroupResidueFieldEquivOfIsIntegralClosure
                D M
                (padicCompletedChangedUniformizerRelativeArtinCandidate
                  p u n) a) =
            IsLocalRing.ResidueField.mapEquiv
                (padicCompletedUnitFrobeniusIntegerEquiv p n u⁻¹).symm
              (embedding a) by
            simpa only [localCompleteDVF_valuation_eq] using
              padicCompletedStandardChangedCompositumResidueEmbedding_artinCandidate
                p u n a]
        apply completedFrobenius.symm_apply_eq.2
        symm
        calc
          completedFrobenius (embedding x) = embedding x ^ p := by
            exact
              padicCompletedUnitFrobeniusIntegerEquiv_residue_apply_eq_pow
                p n u⁻¹ (embedding x)
          _ = embedding (x ^ p) := (embedding.map_pow x p).symm
          _ =
              embedding
                (residueExtensionArithmeticFrobeniusOfValuationExtension D M x) := by
            congr 1
            exact
              (padicCompletedStandardChangedCompositum_residueArithmeticFrobenius_apply
                p u n x).symm
          _ = embedding a := by
            exact congrArg embedding
              ((residueExtensionArithmeticFrobeniusOfValuationExtension
                D M).apply_symm_apply a)
    _ =
        (galoisGroupResidueAlgEquivHomOfIsIntegralClosure D M
          (arithmeticFrobeniusOfUnramifiedValuation D M))⁻¹ := by
      apply congrArg (fun σ => σ⁻¹)
      simpa only [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_apply] using
        (galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius D M).symm

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.LocalClassFieldTheory_LubinTateApplication_PadicMultiplicativeArtinComparison
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceBaseFourthRootField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional_over_extension _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceEmbeddedExtensionField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_finiteDimensional_over_K _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_finiteDimensional_over_layer _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatFiniteLayerInCompositum_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RayClass.approximationCompletionTopologicalSpace _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseIsNonarchimedeanLocalField _root_.chosenFinitePlaceBaseIsValuativeTopology _root_.chosenFinitePlaceBaseNontriviallyNormedField _root_.chosenFinitePlaceBaseValuativeRel _root_.chosenFinitePlaceBaseValued _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerModuleFinite _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_isGalois _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup _root_.scaledRelativeIntegerLatticeQuotientFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The local Artin map on multiplicative p-adic Lubin--Tate levels

This file compares the actual finite local Artin map with the explicit
multiplicative Lubin--Tate action.  The first source-produced comparison is
on the deepest invisible principal-unit group: a unit in `U^(n + 1)` is an
actual norm from level `n`, while its finite Lubin--Tate parameter class is
trivial.  Consequently the two automorphisms agree there, and the resulting
action on the chosen primitive root is the explicit cyclotomic action.
-/

noncomputable section

open scoped ValuativeRel

namespace LocalClassFieldTheory

open LubinTate
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open LocalFieldTheory.DiscreteValuationField.ValuedExtension
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

/-- The field-unit norm of the negative changed prime is the actual
changed base uniformizer. -/
theorem padicCompletedChangedUniformizerNegativePrimeUnit_norm
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    normUnits ℚ_[p]
        (padicCompletedChangedUniformizerFixedField p u n)
        (padicCompletedChangedUniformizerNegativePrimeUnit p n u) =
      standardLubinTateChangedUniformizerUnit
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u := by
  apply Units.ext
  simpa only [normUnits_apply_coe,
    padicCompletedChangedUniformizerNegativePrimeUnit_coe] using
    (padicCompletedChangedUniformizer_norm_neg_primeElement p u n).trans
      (standardLubinTateChangedUniformizerUnit_coe
        (padicMultiplicativeLubinTateSeries_isUniformizer p) u).symm

/-- The negative changed prime has normalized additive value `-1` in its
completed fixed field. -/
theorem padicCompletedChangedUniformizerNegativePrimeUnit_valuationMap
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    let D := padicCompletedChangedUniformizerFixedField p u n
    letI : NontriviallyNormedField D :=
      finiteExtensionSpectralNormedField ℚ_[p] D
    letI : ValuativeRel D :=
      finiteExtensionSpectralValuativeRel ℚ_[p] D
    letI : IsNonarchimedeanLocalField D :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
    IsNonarchimedeanLocalField.valuationMap D
        (Additive.ofMul
          (padicCompletedChangedUniformizerNegativePrimeUnit p n u)) =
      -1 := by
  let D := padicCompletedChangedUniformizerFixedField p u n
  let M := padicCompletedStandardChangedCompositum p u n
  let : NontriviallyNormedField D :=
    finiteExtensionSpectralNormedField ℚ_[p] D
  let : ValuativeRel D :=
    finiteExtensionSpectralValuativeRel ℚ_[p] D
  let : IsNonarchimedeanLocalField D :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
  let : NontriviallyNormedField M :=
    finiteExtensionSpectralNormedField ℚ_[p] M
  let : ValuativeRel M :=
    finiteExtensionSpectralValuativeRel ℚ_[p] M
  let : IsNonarchimedeanLocalField M :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
  obtain ⟨htheta, _⟩ :=
    padicCompletedChangedUniformizerPrimeElement_isUniformizer_in_changedField_and_compositum
      p u n
  have hnegative :
      (localCompleteDVF D).valuation.IsUniformizer
        (-padicCompletedChangedUniformizerPrimeElement p u n : D) := by
    simpa only [Valuation.IsUniformizer.iff,
      (localCompleteDVF D).valuation.map_neg] using htheta
  let negativeInteger : (localCompleteDVF D).valuationSubring :=
    ⟨-padicCompletedChangedUniformizerPrimeElement p u n,
      hnegative.val_lt_one.le⟩
  have hunit :
      padicCompletedChangedUniformizerNegativePrimeUnit p n u =
        IsNonarchimedeanLocalField.uniformizerFieldUnit
          D negativeInteger hnegative := by
    apply Units.ext
    rfl
  rw [hunit]
  exact
    IsNonarchimedeanLocalField.valuationMap_uniformizerFieldUnit
      D negativeInteger hnegative

/-- The actual relative local Artin image of the negative changed prime is
the explicit inverse-coefficient-Frobenius candidate. -/
theorem
    padicCompletedChangedUniformizerRelativeArtin_negativePrime
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    let D := padicCompletedChangedUniformizerFixedField p u n
    let M := padicCompletedStandardChangedCompositum p u n
    letI : NontriviallyNormedField D :=
      finiteExtensionSpectralNormedField ℚ_[p] D
    letI : ValuativeRel D :=
      finiteExtensionSpectralValuativeRel ℚ_[p] D
    letI : IsNonarchimedeanLocalField D :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
    letI : NontriviallyNormedField M :=
      finiteExtensionSpectralNormedField ℚ_[p] M
    letI : ValuativeRel M :=
      finiteExtensionSpectralValuativeRel ℚ_[p] M
    letI : IsNonarchimedeanLocalField M :=
      finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
    letI :
        Valuation.HasExtension (ValuativeRel.valuation D)
          (ValuativeRel.valuation M) :=
      finiteExtensionSpectralValuation_hasExtension_of_tower ℚ_[p] D M
    letI :
        IsNonarchimedeanLocalField.IsUnramifiedValuedExtension D M :=
      padicCompletedStandardChangedCompositum_isUnramifiedValuedExtension
        p u n
    abelianLocalArtinMonoidHom D M
        (padicCompletedChangedUniformizerNegativePrimeUnit p n u) =
      padicCompletedChangedUniformizerRelativeArtinCandidate p u n := by
  let D := padicCompletedChangedUniformizerFixedField p u n
  let M := padicCompletedStandardChangedCompositum p u n
  let : NontriviallyNormedField D :=
    finiteExtensionSpectralNormedField ℚ_[p] D
  let : ValuativeRel D :=
    finiteExtensionSpectralValuativeRel ℚ_[p] D
  let : IsNonarchimedeanLocalField D :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
  let : NontriviallyNormedField M :=
    finiteExtensionSpectralNormedField ℚ_[p] M
  let : ValuativeRel M :=
    finiteExtensionSpectralValuativeRel ℚ_[p] M
  let : IsNonarchimedeanLocalField M :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
  let :
      Valuation.HasExtension (ValuativeRel.valuation D)
        (ValuativeRel.valuation M) :=
    finiteExtensionSpectralValuation_hasExtension_of_tower ℚ_[p] D M
  let :
      IsNonarchimedeanLocalField.IsUnramifiedValuedExtension D M :=
    padicCompletedStandardChangedCompositum_isUnramifiedValuedExtension
      p u n
  calc
    abelianLocalArtinMonoidHom D M
        (padicCompletedChangedUniformizerNegativePrimeUnit p n u) =
        (arithmeticFrobeniusOfUnramifiedValuation D M) ^
          IsNonarchimedeanLocalField.valuationMap D
            (Additive.ofMul
              (padicCompletedChangedUniformizerNegativePrimeUnit p n u)) :=
      abelianLocalArtinMonoidHom_eq_frobenius_zpow D M _
    _ = (arithmeticFrobeniusOfUnramifiedValuation D M) ^ (-1 : ℤ) := by
      rw [padicCompletedChangedUniformizerNegativePrimeUnit_valuationMap]
    _ = (arithmeticFrobeniusOfUnramifiedValuation D M)⁻¹ := by
      rw [zpow_neg_one]
    _ = padicCompletedChangedUniformizerRelativeArtinCandidate p u n :=
      (padicCompletedChangedUniformizerRelativeArtinCandidate_eq_inverseArithmeticFrobenius
        p u n).symm

section PadicStandardLevelRestriction

attribute [local instance] padicArtinStandardLevel_normal

/-- Restricting the relative changed-prime Artin candidate to the standard
multiplicative level gives the direct finite unit-parameter automorphism. -/
theorem
    padicCompletedChangedUniformizerRelativeArtinCandidate_restrict_standardLevel
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    let T := standardLubinTateLevelField hπ n
    let M := padicCompletedStandardChangedCompositum p u n
    letI : Algebra T M :=
      (padicStandardLevelToCompletedChangedCompositum
        p u n).toRingHom.toAlgebra
    letI : IsScalarTower ℚ_[p] T M :=
      IsScalarTower.of_algebraMap_eq'
        (padicStandardLevelToCompletedChangedCompositum p u n).comp_algebraMap.symm
    ((AlgEquiv.restrictNormalHom T).comp
        (AlgEquiv.restrictScalarsHom ℚ_[p]))
        (padicCompletedChangedUniformizerRelativeArtinCandidate
          p u n) =
      standardLubinTateUnitParameterEquivGal
        (padicLocalField p) hπ n
        (standardLubinTateUnitParameterClass
          (padicLocalField p) n u) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let T := standardLubinTateLevelField hπ n
  let M := padicCompletedStandardChangedCompositum p u n
  let : Algebra T M :=
    (padicStandardLevelToCompletedChangedCompositum
      p u n).toRingHom.toAlgebra
  let : IsScalarTower ℚ_[p] T M :=
    IsScalarTower.of_algebraMap_eq'
      (padicStandardLevelToCompletedChangedCompositum p u n).comp_algebraMap.symm
  apply AlgEquiv.ext
  intro x
  apply (algebraMap T M).injective
  rw [MonoidHom.comp_apply, AlgEquiv.restrictScalarsHom_apply]
  change
    algebraMap T M
        (AlgEquiv.restrictNormal
          ((AlgEquiv.restrictScalarsHom ℚ_[p])
            (padicCompletedChangedUniformizerRelativeArtinCandidate p u n)) T x) =
      algebraMap T M
        (standardLubinTateUnitParameterEquivGal
          (padicLocalField p) hπ n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u) x)
  rw [AlgEquiv.restrictNormal_commutes]
  change
    padicCompletedChangedUniformizerRelativeArtinCandidate p u n
        (padicStandardLevelToCompletedChangedCompositum p u n x) =
      padicStandardLevelToCompletedChangedCompositum p u n
        (standardLubinTateUnitParameterEquivGal
          (padicLocalField p) hπ n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u) x)
  rw [
    padicCompletedChangedUniformizerRelativeArtinCandidate_apply,
    padicCompletedChangedUniformizerArtinCandidate_standardLevel]
  exact congrArg
    (fun σ : Gal(T / ℚ_[p]) =>
      padicStandardLevelToCompletedChangedCompositum p u n (σ x))
    (standardLubinTateUnitParameterEquivGal_apply (padicLocalField p) hπ n
      (standardLubinTateUnitParameterClass (padicLocalField p) n u)).symm

end PadicStandardLevelRestriction

/-- The chosen p-adic Lubin--Tate uniformizer is an actual norm from every
finite multiplicative level, hence its actual local Artin image is trivial. -/
theorem padicMultiplicativeAbelianLocalArtin_baseUniformizer
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional ℚ_[p] L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois ℚ_[p] L :=
      standardLubinTateLevelField_isAbelianGalois
        (padicLocalField p) hπ n
    abelianLocalArtinMonoidHom ℚ_[p] L
        (standardLubinTateBaseUniformizerUnit hπ) =
      1 := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional ℚ_[p] L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois ℚ_[p] L :=
    standardLubinTateLevelField_isAbelianGalois
      (padicLocalField p) hπ n
  have hnorm :=
    standardLubinTateBaseUniformizerUnit_mem_normSubgroup hπ n
  change
    standardLubinTateBaseUniformizerUnit hπ ∈
      localNormSubgroup ℚ_[p] L at hnorm
  rw [← abelianLocalArtinMonoidHom_ker, MonoidHom.mem_ker] at hnorm
  exact hnorm

/-- The actual Artin value of an arbitrary p-adic field unit is already
determined by its valuation-zero part.  This is an equality of the actual
maps: the discarded uniformizer power is an explicit norm from the standard
Lubin--Tate level. -/
theorem padicMultiplicativeAbelianLocalArtin_eq_uniformizerUnitPart
    (p : ℕ) [Fact p.Prime] (n : ℕ) (x : ℚ_[p]ˣ) :
    let F := padicLocalField p
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional ℚ_[p] L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois ℚ_[p] L :=
      standardLubinTateLevelField_isAbelianGalois F hπ n
    abelianLocalArtinMonoidHom ℚ_[p] L x =
      abelianLocalArtinMonoidHom ℚ_[p] L
        (standardLubinTateUnitFactorFieldUnit F
          (CompleteDVF.higherPrincipalUnitGroup.fieldUnitUniformizerUnitPart
            F.toCompleteDVF hπ x)) := by
  let F := padicLocalField p
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let L := standardLubinTateLevelField hπ n
  let : FiniteDimensional ℚ_[p] L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois ℚ_[p] L :=
    standardLubinTateLevelField_isAbelianGalois F hπ n
  let φ := abelianLocalArtinMonoidHom ℚ_[p] L
  let ϖ : ℚ_[p]ˣ := standardLubinTateBaseUniformizerUnit hπ
  let u : F.valuationSubringˣ :=
    CompleteDVF.higherPrincipalUnitGroup.fieldUnitUniformizerUnitPart
      F.toCompleteDVF hπ x
  let e : ℤ :=
    CompleteDVF.uniformizerValueExponent F.toCompleteDVF hπ x
  have hϖone : φ ϖ = 1 := by
    simpa only [φ, ϖ] using
      padicMultiplicativeAbelianLocalArtin_baseUniformizer p n
  have huField :
      standardLubinTateUnitFactorFieldUnit F u =
        x * ϖ ^ (-e) := by
    apply Units.ext
    simpa only [
      u, e, ϖ,
      standardLubinTateUnitFactorFieldUnit_coe,
      CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply,
      CompleteDVF.higherPrincipalUnitGroup.coe_valuationSubringUnitFieldUnitHom_apply,
      standardLubinTateBaseUniformizerUnit] using
      congrArg (fun z : ℚ_[p]ˣ => (z : ℚ_[p]))
        (CompleteDVF.higherPrincipalUnitGroup.valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart
          F.toCompleteDVF hπ x)
  calc
    φ x = φ x * φ ϖ ^ (-e) := by
      rw [hϖone, one_zpow, mul_one]
    _ = φ (x * ϖ ^ (-e)) := by
      rw [map_mul, map_zpow]
    _ = φ (standardLubinTateUnitFactorFieldUnit F u) := by
      rw [huField]

/-- Multiplying the chosen uniformizer by a p-adic valuation-ring unit does
not change the actual local Artin value of the unit factor. -/
theorem padicMultiplicativeAbelianLocalArtin_changedUniformizer
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    let L := standardLubinTateLevelField hπ n
    letI : FiniteDimensional ℚ_[p] L :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois ℚ_[p] L :=
      standardLubinTateLevelField_isAbelianGalois
        (padicLocalField p) hπ n
    abelianLocalArtinMonoidHom ℚ_[p] L
        (standardLubinTateChangedUniformizerUnit hπ u) =
      abelianLocalArtinMonoidHom ℚ_[p] L
        (standardLubinTateUnitFactorFieldUnit (padicLocalField p) u) := by
  let F := padicLocalField p
  let π : F.valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let hπ : F.toCompleteDVF.valuation.IsUniformizer (π : ℚ_[p]) :=
    padicMultiplicativeLubinTateSeries_isUniformizer p
  let L := standardLubinTateLevelField (F := F) (π := π) hπ n
  let : FiniteDimensional ℚ_[p] L :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois ℚ_[p] L :=
    standardLubinTateLevelField_isAbelianGalois
      F hπ n
  have hchanged :
      standardLubinTateChangedUniformizerUnit hπ u =
        standardLubinTateUnitFactorFieldUnit F u *
          standardLubinTateBaseUniformizerUnit hπ :=
    standardLubinTateChangedUniformizerUnit_eq_unit_mul (F := F) hπ u
  calc
    abelianLocalArtinMonoidHom ℚ_[p] L
        (standardLubinTateChangedUniformizerUnit hπ u) =
        abelianLocalArtinMonoidHom ℚ_[p] L
          (standardLubinTateUnitFactorFieldUnit F u *
            standardLubinTateBaseUniformizerUnit hπ) :=
      congrArg (abelianLocalArtinMonoidHom ℚ_[p] L) hchanged
    _ = abelianLocalArtinMonoidHom ℚ_[p] L
          (standardLubinTateUnitFactorFieldUnit F u) := by
      rw [map_mul, padicMultiplicativeAbelianLocalArtin_baseUniformizer p n,
        mul_one]

/-- On every finite multiplicative Lubin--Tate level, the actual local
Artin image of a p-adic valuation-ring unit is the direct finite
unit-parameter automorphism.

This is obtained from the genuine changed-uniformizer extension: the
negative changed prime has norm `u p`, its relative Artin image is the
inverse arithmetic Frobenius, and norm--restriction carries that image to
the direct `u`-action on the standard level. -/
theorem padicMultiplicativeAbelianLocalArtin_eq_unitParameter
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    let T := standardLubinTateLevelField hπ n
    letI : FiniteDimensional ℚ_[p] T :=
      standardLubinTateLevelField_finiteDimensional hπ n
    letI : IsAbelianGalois ℚ_[p] T :=
      standardLubinTateLevelField_isAbelianGalois
        (padicLocalField p) hπ n
    abelianLocalArtinMonoidHom ℚ_[p] T
        (standardLubinTateUnitFactorFieldUnit (padicLocalField p) u) =
      standardLubinTateUnitParameterEquivGal
        (padicLocalField p) hπ n
        (standardLubinTateUnitParameterClass
          (padicLocalField p) n u) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let T := standardLubinTateLevelField hπ n
  let D := padicCompletedChangedUniformizerFixedField p u n
  let M := padicCompletedStandardChangedCompositum p u n
  let : FiniteDimensional ℚ_[p] T :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsAbelianGalois ℚ_[p] T :=
    standardLubinTateLevelField_isAbelianGalois
      (padicLocalField p) hπ n
  let : Algebra T M :=
    (padicStandardLevelToCompletedChangedCompositum
      p u n).toRingHom.toAlgebra
  let : IsScalarTower ℚ_[p] T M :=
    IsScalarTower.of_algebraMap_eq'
      (padicStandardLevelToCompletedChangedCompositum p u n).comp_algebraMap.symm
  let : FiniteDimensional D M :=
    FiniteDimensional.right ℚ_[p] D M
  let : NontriviallyNormedField D :=
    finiteExtensionSpectralNormedField ℚ_[p] D
  let : ValuativeRel D :=
    finiteExtensionSpectralValuativeRel ℚ_[p] D
  let : IsNonarchimedeanLocalField D :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] D
  let : NontriviallyNormedField M :=
    finiteExtensionSpectralNormedField ℚ_[p] M
  let : ValuativeRel M :=
    finiteExtensionSpectralValuativeRel ℚ_[p] M
  let : IsNonarchimedeanLocalField M :=
    finiteExtensionSpectralIsNonarchimedeanLocalField ℚ_[p] M
  let :
      Valuation.HasExtension (ValuativeRel.valuation ℚ_[p])
        (ValuativeRel.valuation D) :=
    finiteExtensionSpectralValuation_hasExtension ℚ_[p] D
  let :
      Valuation.HasExtension (ValuativeRel.valuation D)
        (ValuativeRel.valuation M) :=
    finiteExtensionSpectralValuation_hasExtension_of_tower
      ℚ_[p] D M
  let :
      IsNonarchimedeanLocalField.IsUnramifiedValuedExtension D M :=
    padicCompletedStandardChangedCompositum_isUnramifiedValuedExtension
      p u n
  have hnormRestriction :=
    DFunLike.congr_fun
      (abelianLocalArtinMonoidHom_norm_restriction
        ℚ_[p] D T M)
      (padicCompletedChangedUniformizerNegativePrimeUnit p n u)
  have hrelative :
      abelianLocalArtinMonoidHom D M
          (padicCompletedChangedUniformizerNegativePrimeUnit p n u) =
        padicCompletedChangedUniformizerRelativeArtinCandidate p u n :=
    padicCompletedChangedUniformizerRelativeArtin_negativePrime p n u
  have hrestrict :
      ((AlgEquiv.restrictNormalHom T).comp
          (AlgEquiv.restrictScalarsHom ℚ_[p]))
          (padicCompletedChangedUniformizerRelativeArtinCandidate p u n) =
        standardLubinTateUnitParameterEquivGal
          (padicLocalField p) hπ n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u) :=
    padicCompletedChangedUniformizerRelativeArtinCandidate_restrict_standardLevel
      p n u
  have hnorm :
      normUnits ℚ_[p] D
          (padicCompletedChangedUniformizerNegativePrimeUnit p n u) =
        standardLubinTateChangedUniformizerUnit hπ u :=
    padicCompletedChangedUniformizerNegativePrimeUnit_norm p n u
  have hchanged :
      abelianLocalArtinMonoidHom ℚ_[p] T
          (standardLubinTateChangedUniformizerUnit hπ u) =
        abelianLocalArtinMonoidHom ℚ_[p] T
          (standardLubinTateUnitFactorFieldUnit (padicLocalField p) u) :=
    padicMultiplicativeAbelianLocalArtin_changedUniformizer p n u
  have h :
      standardLubinTateUnitParameterEquivGal
          (padicLocalField p) hπ n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u) =
        abelianLocalArtinMonoidHom ℚ_[p] T
          (standardLubinTateUnitFactorFieldUnit (padicLocalField p) u) := by
    simpa only [MonoidHom.comp_apply, hrelative, hrestrict, hnorm, hchanged] using
      hnormRestriction
  exact h.symm

end LocalClassFieldTheory

end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_RationalCyclotomicFinitePlaceArtin
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_isCompleteDiscrete _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_rangeFiniteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_isCyclotomic _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceBaseFourthRootField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceEmbeddedExtensionField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_algebra _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatFiniteLayerInCompositum_numberField _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatIntersection_finiteDimensional _root_.GlobalClassFieldTheory.Reciprocity.numberFieldCyclotomicZHatIntersection_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_isCMField _root_.GlobalClassFieldTheory.Reciprocity.rationalComplexificationCyclotomicField_isCyclotomicFour _root_.GlobalClassFieldTheory.Reciprocity.rationalCyclotomicZHatField_isAbelianGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitSMul _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalTowerClassGroupMul _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicField_hasEnoughRootsOfUnity _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isAbelianGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isGalois _root_.KummerTheory.rationalCyclotomicTorsionFixedField_isIntegral _root_.KummerTheory.rationalCyclotomicTorsionFixedField_normal _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedWithZeroValuationContextIntegralAlgebra _root_.LocalFieldTheory.DiscreteValuationField.finite_principalUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_residueRootsOfUnityGroup _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerKernel _root_.LocalFieldTheory.DiscreteValuationField.finite_valuationSubringUnits_nthPowerQuotient _root_.LocalFieldTheory.Padic.padicDVR_residueField_finite _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.labelPrime_fact _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.instSMulAlgEquivRatSeparableClosureClassGroupSubtypeMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractTowerClassGroupMulOneClass _root_.relativeUnrestrictedSPlaceFactorCommGroup
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

section RationalCyclotomicPrincipalPrime

/-! ## Ramified prime-power transport

This section reuses the canonical finite-place Artin tower above.  In
particular, it introduces no parallel completion/localization instance tower. -/

attribute [local instance]
  rationalCyclotomicPrincipalPrimePadicLevelFiniteDimensional

/-! ## The ramified principal finite-place factor -/

attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceCompletionRatAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.instFactPrimeValNat_solutions_2
attribute [local instance] GlobalClassFieldTheory.Reciprocity.instNeZeroNatVal_solutions
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLevelFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLevelIsAbelianGalois
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseLocallyCompactSpace
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseIsUltrametricDist
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuativeRel
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuationIsNontrivial
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuationCompatible
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuativeRelIsNontrivial
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseNontriviallyNormedField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValued
noncomputable local instance rationalFinitePlaceBaseIsValuativeTopology_r631a4d_1
    (q : Nat.Primes) :
    IsValuativeTopology
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  isValuativeTopology_of_valued_ofValuation
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion ℝ≥0
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseIsNonarchimedeanLocalField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinExtensionAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinExtensionSMul
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinCompletionAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedGlobalAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedGlobalSMul
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedScalarTower
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIsAbelianGalois
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIsSeparable
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIsCyclotomic
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinExtensionFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinExtensionContinuousSMul
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinExtensionLocallyCompact
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedLocallyCompact
noncomputable local instance
    rationalCyclotomicArtinLocalizedIsUltrametricDist_r631a4d_1
    (m : ℕ+) (q : Nat.Primes) :
    IsUltrametricDist
      (rationalCyclotomicArtinLocalizedField m q) :=
  localizedCompletionIsUltrametricDist
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedValued
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedValuativeRel
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedValuationCompatible
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedValuationHasExtension
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedValuationIsNontrivial
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedValuativeRelIsNontrivial
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIsValuativeTopology
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIsNonarchimedeanLocalField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIntegerAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIsIntegralClosure
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIntegerModuleFinite
noncomputable local instance
    rationalCyclotomicPrincipalPrimeLevelIsCyclotomicExtension_r631a4d_1
    (p : Nat.Primes) (n : ℕ) :
    IsCyclotomicExtension {p.1 ^ (n + 1)} ℚ
      (KummerTheory.rationalCyclotomicLevel
        (rationalCyclotomicPrincipalPrimeModulus p n)) := by
  change
    IsCyclotomicExtension
      {(rationalCyclotomicPrincipalPrimeModulus p n : ℕ)} ℚ
      (KummerTheory.rationalCyclotomicLevel
        (rationalCyclotomicPrincipalPrimeModulus p n))
  exact
    KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
      (rationalCyclotomicPrincipalPrimeModulus p n)
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedPadicAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedPadicScalarTower
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicPrincipalPrimePadicLevelIsAbelianGalois
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalPrimeFactorCompletionPadicAlgebra
theorem finitePlaceLocalArtinMonoidHom_apply_semilinear
    {K L K' L' : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [hKLfinite : FiniteDimensional K L] [IsAbelianGalois K L]
    [Field K'] [ValuativeRel K'] [TopologicalSpace K']
    [IsNonarchimedeanLocalField K']
    [Field L'] [Algebra K' L']
    [FiniteDimensional K' L'] [IsAbelianGalois K' L']
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K v) L)
    (eK : (HeightOneSpectrum.adicAbv K v).Completion ≃+* K')
    (eL : LocalizedCompletion
      (HeightOneSpectrum.adicAbv K v) w ≃+* L')
    (hcomm : ∀ y : (HeightOneSpectrum.adicAbv K v).Completion,
      eL (@algebraMap
        (HeightOneSpectrum.adicAbv K v).Completion
        (LocalizedCompletion (HeightOneSpectrum.adicAbv K v) w)
        _ _ (finitePlaceLocalArtinLocalizedAlgebra v w) y) =
        algebraMap K' L' (eK y))
    (hExt : SemilinearValuationCompatible
      (HeightOneSpectrum.adicAbv K v).Completion K' eK)
    (x : (v.adicCompletion K)ˣ)
    (z : LocalizedCompletion (HeightOneSpectrum.adicAbv K v) w) :
    eL (finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w x z) =
      LocalClassFieldTheory.abelianLocalArtinMonoidHom K' L'
        (Units.map eK.toMonoidHom
          (finitePlaceLocalArtinInput v x)) (eL z) := by
  calc
    eL (finitePlaceLocalArtinMonoidHom
        (K := K) (L := L) v w x z) =
      eL ((@LocalClassFieldTheory.abelianLocalArtinMonoidHom
        (HeightOneSpectrum.adicAbv K v).Completion
        (LocalizedCompletion (HeightOneSpectrum.adicAbv K v) w)
        (inferInstance : Field
          (HeightOneSpectrum.adicAbv K v).Completion)
        (inferInstance : Field
          (LocalizedCompletion (HeightOneSpectrum.adicAbv K v) w))
        (finitePlaceLocalArtinLocalizedAlgebra v w)
        (finitePlaceLocalArtinCompletionValuativeRel v)
        (inferInstance : TopologicalSpace
          (HeightOneSpectrum.adicAbv K v).Completion)
        (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v)
        (finitePlaceLocalArtinFiniteDimensional v w)
        (finitePlaceLocalArtinIsAbelianGalois v w hKLfinite)
        (finitePlaceLocalArtinInput v x)) z) :=
      congrArg eL
        (finitePlaceLocalArtinMonoidHom_apply_normalized_at
          (K := K) (L := L) v w x z)
    _ = LocalClassFieldTheory.abelianLocalArtinMonoidHom K' L'
          (Units.map eK.toMonoidHom
            (finitePlaceLocalArtinInput v x)) (eL z) :=
      @abelianLocalArtinMonoidHom_semilinear_action
        (HeightOneSpectrum.adicAbv K v).Completion K'
        (LocalizedCompletion (HeightOneSpectrum.adicAbv K v) w) L'
        (inferInstance : Field
          (HeightOneSpectrum.adicAbv K v).Completion)
        (finitePlaceLocalArtinCompletionValuativeRel v)
        (inferInstance : TopologicalSpace
          (HeightOneSpectrum.adicAbv K v).Completion)
        (finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v)
        (inferInstance : Field K')
        (inferInstance : ValuativeRel K')
        (inferInstance : TopologicalSpace K')
        (inferInstance : IsNonarchimedeanLocalField K')
        (inferInstance : Field
          (LocalizedCompletion (HeightOneSpectrum.adicAbv K v) w))
        (inferInstance : Field L')
        (finitePlaceLocalArtinLocalizedAlgebra v w)
        (inferInstance : Algebra K' L')
        (finitePlaceLocalArtinFiniteDimensional v w)
        (finitePlaceLocalArtinIsAbelianGalois v w hKLfinite)
        (inferInstance : FiniteDimensional K' L')
        (inferInstance : IsAbelianGalois K' L')
        eK eL hcomm hExt (finitePlaceLocalArtinInput v x) z

theorem rationalCyclotomicPrincipalPrime_localizedBase_commutes
    (p : Nat.Primes) (n : ℕ)
    (y : (rationalCyclotomicArtinBaseAbv p).Completion) :
    rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
        (algebraMap (rationalCyclotomicArtinBaseAbv p).Completion
          (rationalCyclotomicArtinLocalizedField
            (rationalCyclotomicPrincipalPrimeModulus p n) p) y) =
      algebraMap ℚ_[p.1]
        (RationalCyclotomicPrincipalPrimePadicLevel p n)
        (rationalFinitePlaceCompletionRingEquivPadic p y) := by
  let m := rationalCyclotomicPrincipalPrimeModulus p n
  let E := rationalCyclotomicArtinLocalizedField m p
  let eL := rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
  have hy :
      algebraMap (rationalCyclotomicArtinBaseAbv p).Completion E y =
        algebraMap ℚ_[p.1] E
          (rationalFinitePlaceCompletionRingEquivPadic p y) := by
    change
      algebraMap (rationalCyclotomicArtinBaseAbv p).Completion E y =
        algebraMap (rationalCyclotomicArtinBaseAbv p).Completion E
          ((rationalFinitePlaceCompletionRingEquivPadic p).symm
            (rationalFinitePlaceCompletionRingEquivPadic p y))
    exact
      (congrArg
        (algebraMap (rationalCyclotomicArtinBaseAbv p).Completion E)
        ((rationalFinitePlaceCompletionRingEquivPadic p).symm_apply_apply y)).symm
  calc
    eL (algebraMap (rationalCyclotomicArtinBaseAbv p).Completion E y) =
        eL (algebraMap ℚ_[p.1] E
          (rationalFinitePlaceCompletionRingEquivPadic p y)) :=
      congrArg eL hy
    _ = algebraMap ℚ_[p.1]
        (RationalCyclotomicPrincipalPrimePadicLevel p n)
        (rationalFinitePlaceCompletionRingEquivPadic p y) :=
      eL.commutes (rationalFinitePlaceCompletionRingEquivPadic p y)

theorem
    padicMultiplicativePrimitiveRoot_rationalPrimeUnitParameterGaloisAction
    (p : Nat.Primes) (n : ℕ) (x : ℚˣ) :
    standardLubinTateUnitParameterEquivGal
        (padicLocalField p.1)
        (padicMultiplicativeLubinTateSeries_isUniformizer p.1) n
        (standardLubinTateUnitParameterClass
          (padicLocalField p.1) n
          (rationalPrimeUnitValuationSubringUnit x p))
        (padicMultiplicativePrimitiveRoot p.1 n) =
      padicMultiplicativePrimitiveRoot p.1 n ^
        (PadicInt.toZModPow (p := p.1) (n + 1)
          (padicIntUnitOfRat p
            (rationalPrimeUnit x p : ℚ)
            (rationalPrimeUnit x p).ne_zero
            (padicValRat_rationalPrimeUnit x p) : ℤ_[p.1])).val := by
  let uZ : ℤ_[p.1]ˣ :=
    padicIntUnitOfRat p
      (rationalPrimeUnit x p : ℚ)
      (rationalPrimeUnit x p).ne_zero
      (padicValRat_rationalPrimeUnit x p)
  let u : (padicLocalField p.1).valuationSubringˣ :=
    Units.map (padicIntEquivValuationSubring p.1).toMonoidHom uZ
  have huRational :
      rationalPrimeUnitValuationSubringUnit x p = u := by
    rfl
  have huPreimage :
      (padicIntEquivValuationSubring p.1).symm
          ((u : (padicLocalField p.1).valuationSubringˣ) :
            (padicLocalField p.1).valuationSubring) =
        (uZ : ℤ_[p.1]) := by
    change
      (padicIntEquivValuationSubring p.1).symm
          (padicIntEquivValuationSubring p.1 (uZ : ℤ_[p.1])) =
        (uZ : ℤ_[p.1])
    exact
      (padicIntEquivValuationSubring p.1).symm_apply_apply
        (uZ : ℤ_[p.1])
  have hAction :=
    padicMultiplicativePrimitiveRoot_unitParameterGaloisAction
      p.1 n u
  rw [huPreimage] at hAction
  rw [huRational]
  exact hAction

theorem
    rationalCyclotomicPrincipalPrime_padicTargetArtin_eq_unitParameter
    (p : Nat.Primes) (n : ℕ) (x : ℚˣ) :
    rationalCyclotomicPrincipalPrimePadicTargetArtin p n x =
      rationalCyclotomicPrincipalPrimePadicUnitParameterArtin p n x := by
  let T := RationalCyclotomicPrincipalPrimePadicLevel p n
  let eK := rationalFinitePlaceCompletionRingEquivPadic p
  let : FiniteDimensional ℚ_[p.1] T :=
    rationalCyclotomicPrincipalPrimePadicLevelFiniteDimensional p n
  let hpi := padicMultiplicativeLubinTateSeries_isUniformizer p.1
  let : IsAbelianGalois ℚ_[p.1] T :=
    standardLubinTateLevelField_isAbelianGalois
      (padicLocalField p.1) hpi n
  have hsource :
      Units.map eK.toMonoidHom (rationalPrincipalFinitePlaceInput x p) =
        Units.map (algebraMap ℚ ℚ_[p.1]).toMonoidHom x := by
    rw [rationalPrincipalFinitePlaceInput_eq_algebraMap]
    apply Units.ext
    exact rationalFinitePlaceCompletionRingEquivPadic_algebraMap p (x : ℚ)
  change
    LocalClassFieldTheory.abelianLocalArtinMonoidHom ℚ_[p.1] T
        (Units.map eK.toMonoidHom
          (rationalPrincipalFinitePlaceInput x p)) =
      standardLubinTateUnitParameterEquivGal
        (padicLocalField p.1) hpi n
        (standardLubinTateUnitParameterClass
          (padicLocalField p.1) n
          (rationalPrimeUnitValuationSubringUnit x p))
  rw [hsource]
  rw [
    padicMultiplicativeAbelianLocalArtin_eq_uniformizerUnitPart,
    rationalPadicFieldUnit_uniformizerUnitPart,
    padicMultiplicativeAbelianLocalArtin_eq_unitParameter]

theorem
    rationalCyclotomicPrincipalPrime_padicArtin_action_eq_unitParameter
    (p : Nat.Primes) (n : ℕ) (x : ℚˣ) :
    (@LocalClassFieldTheory.abelianLocalArtinMonoidHom
      ℚ_[p.1] (RationalCyclotomicPrincipalPrimePadicLevel p n)
      (inferInstance : Field ℚ_[p.1])
      (inferInstance : Field
        (RationalCyclotomicPrincipalPrimePadicLevel p n))
      (inferInstance : Algebra ℚ_[p.1]
        (RationalCyclotomicPrincipalPrimePadicLevel p n))
      (inferInstance : ValuativeRel ℚ_[p.1])
      (inferInstance : TopologicalSpace ℚ_[p.1])
      (inferInstance : IsNonarchimedeanLocalField ℚ_[p.1])
      (rationalCyclotomicPrincipalPrimePadicLevelFiniteDimensional p n)
      (standardLubinTateLevelField_isAbelianGalois
        (padicLocalField p.1)
        (padicMultiplicativeLubinTateSeries_isUniformizer p.1) n)
      (Units.map
        (rationalFinitePlaceCompletionRingEquivPadic p).toMonoidHom
        (finitePlaceLocalArtinInput
          (K := ℚ) (RayClass.rationalPrime p)
          (IdeleGroup.finiteComponent
            (RayClass.rationalPrime p)
            (IdeleGroup.principalIdele ℚ x)))))
        ((rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n).toRingEquiv
          (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)) =
      rationalCyclotomicPrincipalPrimePadicUnitParameterArtin p n x
        (rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
          (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)) := by
  let eK := rationalFinitePlaceCompletionRingEquivPadic p
  have hInput :
      finitePlaceLocalArtinInput
          (K := ℚ) (RayClass.rationalPrime p)
          (IdeleGroup.finiteComponent
            (RayClass.rationalPrime p)
            (IdeleGroup.principalIdele ℚ x)) =
        rationalPrincipalFinitePlaceInput x p := by
    rfl
  have hMapped :
      Units.map eK.toMonoidHom
          (finitePlaceLocalArtinInput
            (K := ℚ) (RayClass.rationalPrime p)
            (IdeleGroup.finiteComponent
              (RayClass.rationalPrime p)
              (IdeleGroup.principalIdele ℚ x))) =
        Units.map eK.toMonoidHom
          (rationalPrincipalFinitePlaceInput x p) :=
    congrArg (Units.map eK.toMonoidHom) hInput
  calc
    _ = rationalCyclotomicPrincipalPrimePadicTargetArtin p n x
          (rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
            (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)) := by
      exact congrArg
        (fun uQp =>
          (@LocalClassFieldTheory.abelianLocalArtinMonoidHom
            ℚ_[p.1] (RationalCyclotomicPrincipalPrimePadicLevel p n)
            (inferInstance : Field ℚ_[p.1])
            (inferInstance : Field
              (RationalCyclotomicPrincipalPrimePadicLevel p n))
            (inferInstance : Algebra ℚ_[p.1]
              (RationalCyclotomicPrincipalPrimePadicLevel p n))
            (inferInstance : ValuativeRel ℚ_[p.1])
            (inferInstance : TopologicalSpace ℚ_[p.1])
            (inferInstance : IsNonarchimedeanLocalField ℚ_[p.1])
            (rationalCyclotomicPrincipalPrimePadicLevelFiniteDimensional p n)
            (standardLubinTateLevelField_isAbelianGalois
              (padicLocalField p.1)
              (padicMultiplicativeLubinTateSeries_isUniformizer p.1) n)
            uQp)
              (rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
                (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)))
        hMapped
    _ = rationalCyclotomicPrincipalPrimePadicUnitParameterArtin p n x
          (rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
            (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)) :=
      congrArg
        (fun tau => tau
          (rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
            (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)))
        (rationalCyclotomicPrincipalPrime_padicTargetArtin_eq_unitParameter
          p n x)

theorem
    rationalCyclotomicPrincipalPrime_padicUnitParameterArtin_action
    (p : Nat.Primes) (n : ℕ) (x : ℚˣ) :
    rationalCyclotomicPrincipalPrimePadicUnitParameterArtin p n x
        (rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
          (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)) =
      (rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
        (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)) ^
        (rationalCyclotomicPrincipalPrimeResidueUnit p n x).val.val := by
  let m := rationalCyclotomicPrincipalPrimeModulus p n
  let E := rationalCyclotomicArtinLocalizedField m p
  let T := RationalCyclotomicPrincipalPrimePadicLevel p n
  let eL : E ≃ₐ[ℚ_[p.1]] T :=
    rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
  let zetaE : E := rationalCyclotomicPrincipalPrimeLocalizedRoot p n
  let tau : Gal(T / ℚ_[p.1]) :=
    rationalCyclotomicPrincipalPrimePadicUnitParameterArtin p n x
  let a := rationalCyclotomicPrincipalPrimeResidueUnit p n x
  let zetaT : T := padicMultiplicativePrimitiveRoot p.1 n
  have hzetaE : IsPrimitiveRoot zetaE (p.1 ^ (n + 1)) := by
    change
      IsPrimitiveRoot
        (rationalCyclotomicLocalizedPrimitiveRoot m
          (RayClass.rationalPrime p)) (m : ℕ)
    exact
      rationalCyclotomicLocalizedPrimitiveRoot_isPrimitiveRoot
        m (RayClass.rationalPrime p)
  have hrho : IsPrimitiveRoot (eL zetaE) (p.1 ^ (n + 1)) :=
    hzetaE.map_of_injective eL.injective
  have hzetaT : IsPrimitiveRoot zetaT (p.1 ^ (n + 1)) :=
    padicMultiplicativePrimitiveRoot_isPrimitiveRoot p.1 n
  have htauZetaT : tau zetaT = zetaT ^ a.val.val :=
    padicMultiplicativePrimitiveRoot_rationalPrimeUnitParameterGaloisAction
      p n x
  exact
    map_primitiveRoot_eq_pow_of_eq_pow
      tau.toMonoidHom zetaT (eL zetaE)
      (p.1 ^ (n + 1)) a.val.val hzetaT hrho htauZetaT

theorem rationalCyclotomicPrincipalPrime_localArtin_action
    (p : Nat.Primes) (n : ℕ) (x : ℚˣ) :
    finitePlaceLocalArtinMonoidHom
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel
          (rationalCyclotomicPrincipalPrimeModulus p n))
        (RayClass.rationalPrime p)
        (rationalCyclotomicChosenFinitePlaceExtension
          (rationalCyclotomicPrincipalPrimeModulus p n)
          (RayClass.rationalPrime p))
        (IdeleGroup.finiteComponent
          (RayClass.rationalPrime p)
          (IdeleGroup.principalIdele ℚ x))
        (rationalCyclotomicPrincipalPrimeLocalizedRoot p n) =
      (rationalCyclotomicPrincipalPrimeLocalizedRoot p n) ^
        (rationalCyclotomicPrincipalPrimeResidueUnit p n x).val.val := by
  let eL := rationalCyclotomicLocalizedCompletionPadicAlgEquiv p n
  apply eL.injective
  calc
    _ = _ :=
      finitePlaceLocalArtinMonoidHom_apply_semilinear
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel
          (rationalCyclotomicPrincipalPrimeModulus p n))
        (K' := ℚ_[p.1])
        (L' := RationalCyclotomicPrincipalPrimePadicLevel p n)
        (RayClass.rationalPrime p)
        (rationalCyclotomicChosenFinitePlaceExtension
          (rationalCyclotomicPrincipalPrimeModulus p n)
          (RayClass.rationalPrime p))
        (rationalFinitePlaceCompletionRingEquivPadic p)
        eL.toRingEquiv
        (rationalCyclotomicPrincipalPrime_localizedBase_commutes p n)
        (rationalFinitePlaceCompletionRingEquivPadic_semilinearValuationCompatible
          p)
        (IdeleGroup.finiteComponent
          (RayClass.rationalPrime p)
          (IdeleGroup.principalIdele ℚ x))
        (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)
    _ = rationalCyclotomicPrincipalPrimePadicUnitParameterArtin p n x
          (eL (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)) :=
      rationalCyclotomicPrincipalPrime_padicArtin_action_eq_unitParameter
        p n x
    _ = (eL (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)) ^
          (rationalCyclotomicPrincipalPrimeResidueUnit p n x).val.val :=
      rationalCyclotomicPrincipalPrime_padicUnitParameterArtin_action p n x
    _ = eL ((rationalCyclotomicPrincipalPrimeLocalizedRoot p n) ^
          (rationalCyclotomicPrincipalPrimeResidueUnit p n x).val.val) :=
      (map_pow eL (rationalCyclotomicPrincipalPrimeLocalizedRoot p n)
        (rationalCyclotomicPrincipalPrimeResidueUnit p n x).val.val).symm

/-- At the ramified prime, the cyclotomic character of the chosen finite-place
Artin symbol is the direct reduction of the rational `p`-adic unit. -/
theorem galEquivZMod_chosenFinitePlaceArtinMonoidHom_principal_at_prime
    (p : Nat.Primes) (n : ℕ) (x : ℚˣ) :
    IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ (n + 1))
        (KummerTheory.rationalCyclotomicLevel
          (rationalCyclotomicPrincipalPrimeModulus p n))
        (hK :=
          KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
            (rationalCyclotomicPrincipalPrimeModulus p n))
        (rationalCyclotomicPrincipalPrimeChosenArtin p n x) =
      Units.map
        (PadicInt.toZModPow (p := p.1) (n + 1)).toMonoidHom
        (padicIntUnitOfRat p
          (rationalPrimeUnit x p : ℚ)
          (rationalPrimeUnit x p).ne_zero
          (padicValRat_rationalPrimeUnit x p)) := by
  change _ = rationalCyclotomicPrincipalPrimeResidueUnit p n x
  apply rationalCyclotomicPrincipalPrime_galEquivZMod_eq_of_action p n
  simp only [rationalCyclotomicPrincipalPrimeChosenArtin]
  apply finitePlaceLocalToGlobalMonoidHom_apply_pow_of_localized_action
    (zLocal := rationalCyclotomicPrincipalPrimeLocalizedRoot p n)
  · rfl
  · exact rationalCyclotomicPrincipalPrime_localArtin_action p n x

end RationalCyclotomicPrincipalPrime

attribute [local instance] GlobalClassFieldTheory.Reciprocity.instFactPrimeValNat_solutions_2
attribute [local instance] GlobalClassFieldTheory.Reciprocity.instNeZeroNatVal_solutions
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLevelFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLevelIsAbelianGalois
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseNontriviallyNormedField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseLocallyCompactSpace
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseIsUltrametricDist
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValued
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuativeRel
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuationIsNontrivial
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuationCompatible
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseValuativeRelIsNontrivial
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceCompletionRatAlgebra
noncomputable local instance rationalFinitePlaceBaseIsValuativeTopology_r631a4d_2
    (q : Nat.Primes) :
    IsValuativeTopology
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  isValuativeTopology_of_valued_ofValuation
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion ℝ≥0
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalFinitePlaceBaseIsNonarchimedeanLocalField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinExtensionAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinExtensionSMul
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinCompletionAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedGlobalAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedGlobalSMul
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedScalarTower
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIsAbelianGalois
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIsSeparable
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIsCyclotomic
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinExtensionFiniteDimensional
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinExtensionContinuousSMul
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinExtensionLocallyCompact
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedLocallyCompact
noncomputable local instance
    rationalCyclotomicArtinLocalizedIsUltrametricDist_r631a4d_2
    (m : ℕ+) (q : Nat.Primes) :
    IsUltrametricDist
      (rationalCyclotomicArtinLocalizedField m q) :=
  localizedCompletionIsUltrametricDist
    (rationalCyclotomicArtinBaseAbv q)
    (rationalCyclotomicArtinExtension m q)
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (rationalCyclotomicArtinPlace q))
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedValued
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedValuativeRel
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedValuationCompatible
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedValuationHasExtension
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedValuationIsNontrivial
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedValuativeRelIsNontrivial
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIsValuativeTopology
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIsNonarchimedeanLocalField
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIntegerAlgebra
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIsIntegralClosure
attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalCyclotomicArtinLocalizedIntegerModuleFinite
noncomputable abbrev rationalCyclotomicArtinLocalInput
    (q : Nat.Primes)
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    (rationalCyclotomicArtinBaseAbv q).Completionˣ :=
  finitePlaceLocalArtinInput
    (K := ℚ) (rationalCyclotomicArtinPlace q) x

end Reciprocity
end GlobalClassFieldTheory
end
end


