-- Prove2me | Definitions.Def_OAIQ244Duke079
-- name    : OAIQ244Duke079
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T23:16:44.847325+00:00
-- url     : https://prove2.me/theorems/9924d1ed-c8e8-4f1c-92fb-1327627e628f
-- title:
--   Definitions bundle OAIQ244Duke079 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 1 definition, 7 instances and 8 theorems. The definitions and types are `GlobalClassFieldTheory.Reciprocity.rationalBaseFixingCosetEquivNormalClosure`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `AlgebraicNumberTheory_Idele_FinitePrime`, `GlobalClassFieldTheory_GlobalClassFields_BigHilbertClassField`, `GlobalClassFieldTheory_Reciprocity_FinitePlaceCyclotomicFrobeniusLift`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitCore`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtension`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtensionAction`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitFiniteLevelCore`, `GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitFixedPoints`, `LubinTate_Padic_CompletedUnramifiedField`.
--
--   **Imports.** It imports the bundles `OAIQ244Duke070`, `OAIQ244Duke071` and `OAIQ244Duke072` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ244Duke082`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Pi
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
import Mathlib.Data.ZMod.QuotientRing
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
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
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
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.LocalRing.Basic
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
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UniformSpace.AbsoluteValue
import Mathlib.Topology.WithTopology
import Definitions.Def_OAIQ244Duke070
import Definitions.Def_OAIQ244Duke071
import Definitions.Def_OAIQ244Duke072

section
-- module Solutions.OAIQ244_DUKE.AlgebraicNumberTheory_Idele_FinitePrime
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
attribute [-simp] _root_.GlobalClassFieldTheory.ClassFieldAxiom.actualPushoutNormQuotientMap_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.hasseNormDiagonal_mk _root_.GlobalClassFieldTheory.ClassFieldAxiom.sUnitEquivSupportedPrincipalIdeleSubgroup_coe _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.ideleClassQuotientEquivOfNarrowFiniteConductorsEqOfRayClassGroupCardsEqQuotientCards_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.mem_fullConductorInfinitePart_iff _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupEquivQuotientOfCardEq_mk _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorRayClassGroupToQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientEquivNarrowClassGroup_mk _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldQuotientToSmallHilbertClassFieldQuotient_mk _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToBigHilbertClassFieldQuotient_apply _root_.GlobalClassFieldTheory.GlobalClassFields.realSignToNarrowClassKernel_apply _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldQuotientEquivClassGroup_mk _root_.GlobalClassFieldTheory.IdealClassFieldTheory.smallHilbertClassFieldIdeleExtensionMap_mk' _root_.GlobalClassFieldTheory.Reciprocity.globalNormClassFromIdele_principalIdele _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceGlobalArtinMonoidHom_finitePlaceIdele _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateIdeleClassEquivGaloisFixed_coe _root_.IdeleClassGroup.normOneNorm_apply _root_.IdeleGroup.count_fractionalIdeal _root_.IdeleGroup.ideleNormContinuousMonoidHom_apply _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.RayClass.positiveRationalIdealGeneratorUnit_one _root_.RayClass.positiveRationalIdealGeneratorUnit_val _root_.RayClass.positiveRationalIdealGenerator_one _root_.RayClass.primeToIdealResidueHom_apply _root_.RayClass.primeToModulusIdealNorm_coe _root_.RayClass.primesEquiv_val_eq_natGenerator _root_.RayClass.signToNarrow_mk _root_.IdeleGroup.idealClass_classRepresentative _root_.finiteIdeleOfSPlaceFactors_apply_mem _root_.finiteIdeleOfSPlaceFactors_apply_notMem _root_.ideleSupportedAtEquivSPlaceFactors_infinite _root_.ideleSupportedAtEquivSPlaceFactors_inside _root_.ideleSupportedAtEquivSPlaceFactors_outside_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Normalized finite-prime ideles

This file defines the idele supported at one finite place with normalized
local order one, and computes its associated fractional ideal and ideal
class. These constructions are independent of class field theory.
-/

open scoped NumberField

noncomputable section

namespace IdeleGroup

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-- The fractional ideal of the normalized one-place prime idele is the
corresponding prime ideal. -/
@[simp]
theorem fractionalIdeal_finitePrimeIdele
    (v : HeightOneSpectrum (𝓞 K)) :
    fractionalIdeal (finitePrimeIdele v) =
      FractionalIdealGroup.prime v := by
  apply FractionalIdealGroup.ext_count
  intro w
  change
    FractionalIdeal.count K w
        ((FiniteIdeleGroup.fractionalIdeal
          (finitePrimeIdele v).2 :
            FractionalIdealGroup K) :
          FractionalIdeal
            (nonZeroDivisors (𝓞 K)) K) =
      FractionalIdeal.count K w
        ((FractionalIdealGroup.prime v :
            FractionalIdealGroup K) :
          FractionalIdeal
            (nonZeroDivisors (𝓞 K)) K)
  rw [FiniteIdeleGroup.fractionalIdeal]
  change
    FractionalIdeal.count K w
        (((FractionalIdealGroup.factorization
          (FiniteIdeleGroup.valuationVector
            (finitePrimeIdele v).2) :
              FractionalIdealGroup K) :
            FractionalIdeal
              (nonZeroDivisors (𝓞 K)) K)) =
      FractionalIdeal.count K w
        (v.asIdeal :
          FractionalIdeal
            (nonZeroDivisors (𝓞 K)) K)
  rw [FractionalIdealGroup.count_factorization,
    FiniteIdeleGroup.valuationVector_apply]
  by_cases hw : w = v
  · subst w
    rw [← finiteComponent_apply, finitePrimeIdele,
      finitePlaceIdele_finiteComponent_same,
      FiniteIdeleGroup.localOrder_chosenLocalOrderSection,
      FractionalIdeal.count_self]
  · rw [← finiteComponent_apply, finitePrimeIdele,
      finitePlaceIdele_finiteComponent_of_ne
        v w (FiniteIdeleGroup.chosenLocalOrderSection v 1) hw,
      map_one]
    change
      0 =
        FractionalIdeal.count K w
          (v.asIdeal :
            FractionalIdeal
              (nonZeroDivisors (𝓞 K)) K)
    rw [FractionalIdeal.count_maximal_coprime K w (Ne.symm hw)]

/-- The ordinary ideal class of the normalized one-place prime idele is the
class of the corresponding prime ideal. -/
@[simp]
theorem idealClass_finitePrimeIdele
    (v : HeightOneSpectrum (𝓞 K)) :
    idealClass (finitePrimeIdele v) =
      ClassGroup.mk K (FractionalIdealGroup.prime v) := by
  change
    ClassGroup.mk K (fractionalIdeal (finitePrimeIdele v)) =
      ClassGroup.mk K (FractionalIdealGroup.prime v)
  rw [fractionalIdeal_finitePrimeIdele]

end IdeleGroup
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_GlobalClassFields_BigHilbertClassField
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.ClassFormation.DegreeData.FrobeniusFixedFieldTower.extensionNormal _root_.ClassFormation.DegreeData.GaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteAbstractConjugate_normal _root_.ClassFormation.DegreeData.finiteReciprocityNaturalityFiniteResidueConjugate_normal _root_.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal _root_.ClassFormation.FiniteCyclicSubextension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.FiniteGaloisSubextension.abelianIntermediateField_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_over_intermediate_normalInstance _root_.ClassFormation.FiniteGaloisSubextension.intermediateField_normalInstance _root_.ClassFormation.FiniteIntermediateField.galoisRefinement_normal _root_.ClassFormation.FiniteUnramifiedCyclicExtension.instNormalSubtypeMemSubgroupFieldExtensionSubgroupField _root_.ClassFormation.conjugateExtension_normal _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.extensionSubgroupBase_normal _root_.LocalClassFieldTheory.finiteGaloisExtensionSubgroupOfEmbedding_normal _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroupInInertiaAut_normal _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

set_option autoImplicit false

/-!
# The big Hilbert class field

The big Hilbert class field is the ray class field of modulus one (the
zero finite modulus in the exponent-valued representation).  This file
identifies its defining norm quotient with the narrow class group.  The
maximal-unramified field statement follows from this input together with
the narrow finite conductor/ramification criterion.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- Among conductorial idèle-class subgroups, containing the big-Hilbert
norm subgroup is equivalent to having narrow finite conductor zero. -/
theorem
    bigHilbertClassFieldNormSubgroup_le_iff_narrowFiniteConductor_eq_zero
    (H : ConductorialSubgroup K) :
    bigHilbertClassFieldNormSubgroup (K := K) ≤ H.1 ↔
      H.narrowFiniteConductor = 0 := by
  constructor
  · intro hH
    have hdef :
        IsDefiningModulus H.1
          (RayClass.Modulus.narrowOfFinite
            (0 : RayClass.FiniteModulus K)) := by
      simpa only [IsDefiningModulus,
        bigHilbertClassFieldNormSubgroup] using hH
    apply le_antisymm
    · exact H.narrowFiniteConductor_le hdef
    · exact bot_le
  · intro hconductor
    have hdef := H.narrowFiniteConductor_isDefiningModulus
    rw [hconductor] at hdef
    simpa only [IsDefiningModulus,
      bigHilbertClassFieldNormSubgroup] using hdef

end GlobalClassFields
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.LubinTate_Padic_CompletedUnramifiedField
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelCompleteDVF_hasExtensionInstance _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The p-adic completed-unramified coefficient field

The coefficient ring used by the mixed-characteristic changed-uniformizer
construction is

`W(AlgebraicClosure (ZMod p))`.

Its fraction field is the completed maximal-unramified coefficient field.
This file equips that existing mathlib fraction field with its canonical
`ℚ_[p]`-algebra structure.  Mathlib's fraction-field Frobenius then becomes
an actual `ℚ_[p]`-algebra automorphism.  No second Witt ring, p-adic field,
or Frobenius is introduced.
-/

noncomputable section

namespace LubinTate

open Filter
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open scoped Topology Valued WithZero

/-- The valued-field structure induced by the canonical Witt DVR
valuation. -/
noncomputable instance padicCompletedUnramifiedFieldValued
    (p : ℕ) [Fact p.Prime] :
    Valued (padicCompletedUnramifiedField p) ℤᵐ⁰ :=
  Valued.mk' (padicCompletedUnramifiedValuation p)

end LubinTate

end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_FinitePlaceCyclotomicFrobeniusLift
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalIdeleClassDirectLimitMonoid _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.GlobalClassFieldTheory.Reciprocity.instMonoidClassGroupRatSubtypeSeparableClosureMemIntermediateField _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Decomposition-compatible cyclotomic Frobenius lifts

The finite-place reduction in the local--global compatibility theorem
uses automorphisms in a specified decomposition group, not arbitrary
lifts in the ambient absolute Galois group.

This file begins with the source map needed for that construction.
For a normal intermediate field, restriction maps the decomposition
group upstairs onto the decomposition group of the restricted
valuation.  The proof uses the actual valuation-conjugacy correction
in `absoluteValueDecompositionGroup_map_restrictNormalHom`.
-/

open AlgebraicNumberTheory.Valuations
open AlgebraicNumberTheory
open HilbertRamification
open ClassFormation
open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

local instance localInst_ra6565a_1 (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩
local instance rationalCyclotomicFrobeniusLiftPrimePowerNumberField_ra6565a_1
    (p : Nat.Primes) (k : ℕ) :
    NumberField (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  KummerTheory.rationalCyclotomicLevel_numberField
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩
local instance rationalCyclotomicFrobeniusLiftPrimePowerFiniteDimensional_ra6565a_1
    (p : Nat.Primes) (k : ℕ) :
    FiniteDimensional ℚ (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩
local instance rationalCyclotomicFrobeniusLiftPrimePowerIsAbelianGalois_ra6565a_1
    (p : Nat.Primes) (k : ℕ) :
    IsAbelianGalois ℚ (KummerTheory.rationalCyclotomicLevel
      ⟨p.1 ^ k, pow_pos p.2.pos k⟩) :=
  rationalCyclotomicLevelIsAbelianGalois
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩
noncomputable local instance
    rationalCyclotomicFrobeniusLiftLevelFiniteDimensional_ra6565a_1
    (m : ℕ+) :
    FiniteDimensional ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional m
noncomputable local instance
    rationalCyclotomicFrobeniusLiftLevelIsAbelianGalois_ra6565a_1
    (m : ℕ+) :
    IsAbelianGalois ℚ
      (KummerTheory.rationalCyclotomicLevel m) :=
  rationalCyclotomicLevelIsAbelianGalois m
variable
    {K L Ω : Type}
    [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω]
    [IsScalarTower K L Ω] [Normal K L]

/-- Restriction from a Galois overfield is surjective on the actual
decomposition groups of a nontrivial valuation.

The preimage is obtained by first extending the requested
automorphism and then correcting it by an automorphism fixing the
normal intermediate field.  Thus the resulting lift genuinely
stabilizes the specified valuation upstairs. -/
theorem absoluteValueDecompositionGroupRestrictionHom_surjective
    [IsGalois K Ω]
    (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial)
    (wΩ : AbsoluteValueExtension vK Ω) :
    Function.Surjective
      (absoluteValueDecompositionGroupRestrictionHom
        (K := K) (L := L) (Ω := Ω) wΩ.1) := by
  intro σ
  have hσ :
      σ.1 ∈
        (absoluteValueDecompositionGroup K wΩ.1).map
          (AlgEquiv.restrictNormalHom
            (F := K) (K₁ := Ω) L) := by
    rw [
      absoluteValueDecompositionGroup_map_restrictNormalHom
        (F := K) (E := Ω) (M := L) vK hvK wΩ]
    exact σ.2
  obtain ⟨τ, hτ, hτσ⟩ := hσ
  refine ⟨⟨τ, hτ⟩, ?_⟩
  apply Subtype.ext
  exact hτσ

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitCore
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The rational absolute idele-class direct limit

Finite Galois relative idele class groups over `ℚ`, their scalar-extension
maps, and the induced absolute Galois representation.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open CyclicCohomology

universe u

/-- The rational absolute Galois action on every finite-Galois
relative idele class group. -/
noncomputable instance rationalFiniteGaloisIdeleClassMulDistribMulAction
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)) :
    MulDistribMulAction
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
      (RelativeIdeleGroup.ClassGroup ℚ E) :=
  rationalAbsoluteGaloisIdeleClassAction E

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitFiniteLevelCore
private local instance q359TowerIdeleIsMulCommutative2.{w} (A B C : Type w) [Field A] [NumberField A]
    [Field B] [Field C] [Algebra A B] [Algebra B C] :
    IsMulCommutative (TowerRelativeIdeleGroup A B C) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseSmul _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_smul _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite levels of the rational idele-class direct limit

Normal closures, finite-level scalar extension, tower base change, and the
canonical embeddings into the rational idele-class direct limit.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open CyclicCohomology

attribute [local instance]
  relativeAdeleRingIntermediateAlgebra

attribute [local instance] GlobalClassFieldTheory.Reciprocity.rationalIntermediateNumberField
instance rationalTowerClassGroupCommGroup
    (K N : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ N]
    [Algebra K N] [IsScalarTower ℚ K N] [FiniteDimensional K N] :
    CommGroup (TowerRelativeIdeleGroup.ClassGroup ℚ K N) := by
  letI : CommGroup (TowerRelativeIdeleGroup ℚ K N) := inferInstance
  exact
    QuotientGroup.Quotient.commGroup
      (TowerRelativeIdeleGroup.principalSubgroup ℚ K N)

instance rationalTowerClassGroupMul
    (K N : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ N]
    [Algebra K N] [IsScalarTower ℚ K N] [FiniteDimensional K N] :
    Mul (TowerRelativeIdeleGroup.ClassGroup ℚ K N) := by
  letI : CommGroup (TowerRelativeIdeleGroup ℚ K N) := inferInstance
  exact
    (QuotientGroup.Quotient.commGroup
      (TowerRelativeIdeleGroup.principalSubgroup ℚ K N)).toMul

/-- Absolute left cosets fixing a finite rational intermediate field,
identified with its embeddings into the canonical normal closure. -/
noncomputable def
    rationalBaseFixingCosetEquivNormalClosure
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    ((RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (⊥ : IntermediateField ℚ (SeparableClosure ℚ))).toSubgroup ⧸
      extensionSubgroup
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (⊥ : IntermediateField ℚ (SeparableClosure ℚ)))
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K)
        (LocalClassFieldTheory.fixingSubgroupLeBase
          ℚ (SeparableClosure ℚ) K)) ≃
      (K →ₐ[ℚ] rationalNormalClosure K) :=
  (LocalClassFieldTheory.baseFixingCosetEquivAlgHom
      ℚ (SeparableClosure ℚ) K).trans
    (normalClosure.algHomEquiv
      (F := ℚ) (K := K) (L := SeparableClosure ℚ)).symm

theorem rationalRelativeIdeleClassEmbedding_commutativeSquare
    {F E N₁ N₂ : IntermediateField ℚ (SeparableClosure ℚ)}
    [NumberField F] [NumberField E] [NumberField N₁] [NumberField N₂]
    (hFE : F ≤ E) (hFN₁ : F ≤ N₁) (hEN₂ : E ≤ N₂) (hN₁N₂ : N₁ ≤ N₂)
    (c : RelativeIdeleGroup.ClassGroup ℚ F) :
    RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := N₂)
        (IntermediateField.inclusion hEN₂)
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := E)
          (IntermediateField.inclusion hFE) c) =
      RelativeIdeleGroup.classEmbedding (K := ℚ) (L := N₁) (M := N₂)
        (IntermediateField.inclusion hN₁N₂)
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := N₁)
          (IntermediateField.inclusion hFN₁) c) := by
  calc
    _ = RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := N₂)
        (IntermediateField.inclusion (hFE.trans hEN₂)) c :=
      rationalRelativeIdeleClassEmbedding_comp hFE hEN₂ c
    _ = RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := N₂)
        (IntermediateField.inclusion (hFN₁.trans hN₁N₂)) c := by
      rfl
    _ = _ :=
      (rationalRelativeIdeleClassEmbedding_comp hFN₁ hN₁N₂ c).symm

/-- The canonical maps from nested rational intermediate fields to the
idele-class direct limit agree after scalar extension. -/
theorem
    rationalIntermediateIdeleClassToDirectLimit_extension
    {F E : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ E]
    (hFE : F ≤ E)
    (c : RelativeIdeleGroup.ClassGroup ℚ F) :
    rationalIntermediateIdeleClassToDirectLimit E
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E)
          (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := E)
            (IntermediateField.inclusion hFE) c)) =
      rationalIntermediateIdeleClassToDirectLimit F
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := F) c) := by
  let hFN :
      F ≤ (rationalNormalClosure F :
        IntermediateField ℚ (SeparableClosure ℚ)) :=
    IntermediateField.le_normalClosure F
  let hEN :
      E ≤ (rationalNormalClosure E :
        IntermediateField ℚ (SeparableClosure ℚ)) :=
    IntermediateField.le_normalClosure E
  let hN : rationalNormalClosure F ≤ rationalNormalClosure E :=
    IntermediateField.normalClosure_mono F E hFE
  have hcomp :
      RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E)
          (M := rationalNormalClosure E) (IntermediateField.inclusion hEN)
          (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := E)
            (IntermediateField.inclusion hFE) c) =
        RelativeIdeleGroup.classEmbedding (K := ℚ)
          (L := rationalNormalClosure F) (M := rationalNormalClosure E)
          (IntermediateField.inclusion hN)
          (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F)
            (M := rationalNormalClosure F)
            (IntermediateField.inclusion hFN) c) := by
    exact rationalRelativeIdeleClassEmbedding_commutativeSquare
      hFE hFN hEN hN c
  calc
    _ = rationalRelativeIdeleClassToDirectLimit (rationalNormalClosure E)
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E)
          (M := rationalNormalClosure E) (IntermediateField.inclusion hEN)
          (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := E)
            (IntermediateField.inclusion hFE) c)) :=
      rationalIntermediateIdeleClassToDirectLimit_baseChange E
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := E)
          (IntermediateField.inclusion hFE) c)
    _ = rationalRelativeIdeleClassToDirectLimit (rationalNormalClosure E)
        (RelativeIdeleGroup.classEmbedding (K := ℚ)
          (L := rationalNormalClosure F) (M := rationalNormalClosure E)
          (IntermediateField.inclusion hN)
          (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F)
            (M := rationalNormalClosure F)
            (IntermediateField.inclusion hFN) c)) := by
      exact congrArg
        (rationalRelativeIdeleClassToDirectLimit (rationalNormalClosure E)) hcomp
    _ = rationalRelativeIdeleClassToDirectLimit (rationalNormalClosure F)
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F)
          (M := rationalNormalClosure F)
          (IntermediateField.inclusion hFN) c) :=
      rationalIdeleClassDirectLimit_mk_apply
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F)
          (M := rationalNormalClosure F)
          (IntermediateField.inclusion hFN) c)
        hN
    _ = _ :=
      (rationalIntermediateIdeleClassToDirectLimit_baseChange F c).symm


end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitFixedPoints
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.finiteIndex _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.GlobalClassFields.smallHilbertClassFieldNormSubgroupFiniteIndex _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_algebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_baseAlgebra _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseIsGalois _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringTower _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedQPadicContextValuationSubringTower _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedLevelField_isGalois _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_numberField _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.CyclicCohomology.instMulDistribMulActionBinaryCoefficientFamily _root_.GlobalClassFieldTheory.Reciprocity.instNumberFieldSubtypeSeparableClosureRatMemIntermediateFieldAbstractFixedFieldOfFiniteQuotientAlgEquivSubgroupBaseFieldExtensionSubgroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupCommGroup _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMul _root_.GlobalClassFieldTheory.Reciprocity.rationalAbstractRelativeClassGroupMulOneClass _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.chosenFinitePlaceLocalizedIntegerAlgebra _root_.chosenFinitePlaceLocalizedIsGalois _root_.cyclicPrimeDegreeIntermediate_isGalois _root_.cyclicPrimeSubextension_isGalois _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Fixed points of the rational idele-class direct limit

The actual idele class group of a finite rational intermediate field is
identified with the corresponding fixed subgroup of the direct limit.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

/-- The canonical direct-limit realization of idèle classes is natural
under an equivalence between two finite rational intermediate fields
which is induced by an automorphism of the rational separable closure. -/
theorem rationalIntermediateIdeleClassToDirectLimit_ambientAlgEquiv
    {E F : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ E] [FiniteDimensional ℚ F]
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (e : E ≃ₐ[ℚ] F)
    (hσe : ∀ x : E,
      ((e x : F) : SeparableClosure ℚ) =
        σ (x : SeparableClosure ℚ))
    (c : IdeleClassGroup E) :
    σ • rationalIntermediateIdeleClassToDirectLimit E c =
      rationalIntermediateIdeleClassToDirectLimit F
        (ideleClassCongr e c) := by
  let U :
      FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) :=
    rationalNormalClosure E ⊔ rationalNormalClosure F
  let hEU :
      E ≤ (U : IntermediateField ℚ (SeparableClosure ℚ)) :=
    (IntermediateField.le_normalClosure E).trans le_sup_left
  let hFU :
      F ≤ (U : IntermediateField ℚ (SeparableClosure ℚ)) :=
    (IntermediateField.le_normalClosure F).trans le_sup_right
  let cE : RelativeIdeleGroup.ClassGroup ℚ E :=
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := E)).symm c
  let cF : RelativeIdeleGroup.ClassGroup ℚ F :=
    relativeIdeleClassCongr (K := ℚ) e cE
  let : MulDistribMulAction
      (U ≃ₐ[ℚ] U)
      (RelativeIdeleGroup.ClassGroup ℚ U) :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction ℚ U
  let : SMul
      (U ≃ₐ[ℚ] U)
      (RelativeIdeleGroup.ClassGroup ℚ U) :=
    (RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction ℚ U).toSMul
  let : SMul
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
      (RelativeIdeleGroup.ClassGroup ℚ U) :=
    (rationalAbsoluteGaloisIdeleClassAction U).toSMul
  have hcF :
      _root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := F) cF =
        ideleClassCongr e c := by
    calc
      _root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := F) cF =
        ideleClassCongr e
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := E) cE) := by
        simpa only [cF] using
          (_root_.relativeIdeleClassBaseChangeMulEquiv_relativeIdeleClassCongr
            e cE)
      _ = ideleClassCongr e c := by
        simp only [cE,
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := E)).apply_symm_apply]
  have hE :
      rationalIntermediateIdeleClassToDirectLimit E c =
        rationalRelativeIdeleClassToDirectLimit U
          (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
            (IntermediateField.inclusion hEU) cE) := by
    calc
      rationalIntermediateIdeleClassToDirectLimit E c =
          rationalIntermediateIdeleClassToDirectLimit E
          (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := E) cE) := by
        simp only [cE,
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := E)).apply_symm_apply]
      _ =
          rationalIntermediateIdeleClassToDirectLimit
            (U : IntermediateField ℚ (SeparableClosure ℚ))
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := U)
              (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
                (IntermediateField.inclusion hEU) cE)) :=
        (rationalIntermediateIdeleClassToDirectLimit_extension
          hEU cE).symm
      _ =
          rationalRelativeIdeleClassToDirectLimit U
            (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
              (IntermediateField.inclusion hEU) cE) :=
        rationalFiniteGaloisIdeleClassToDirectLimit_baseChange
          U (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
            (IntermediateField.inclusion hEU) cE)
  have hF :
      rationalIntermediateIdeleClassToDirectLimit F
          (ideleClassCongr e c) =
        rationalRelativeIdeleClassToDirectLimit U
          (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := U)
            (IntermediateField.inclusion hFU) cF) := by
    calc
      rationalIntermediateIdeleClassToDirectLimit F
          (ideleClassCongr e c) =
          rationalIntermediateIdeleClassToDirectLimit F
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := F) cF) := by
        rw [hcF]
      _ =
          rationalIntermediateIdeleClassToDirectLimit
            (U : IntermediateField ℚ (SeparableClosure ℚ))
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := U)
              (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := U)
                (IntermediateField.inclusion hFU) cF)) :=
        (rationalIntermediateIdeleClassToDirectLimit_extension
          hFU cF).symm
      _ =
          rationalRelativeIdeleClassToDirectLimit U
            (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := U)
              (IntermediateField.inclusion hFU) cF) :=
        rationalFiniteGaloisIdeleClassToDirectLimit_baseChange
          U (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := U)
            (IntermediateField.inclusion hFU) cF)
  have hrestricted :
      (AlgEquiv.restrictNormalHom U σ) •
          RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
            (IntermediateField.inclusion hEU) cE =
        RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
          ((AlgEquiv.restrictNormalHom U σ).toAlgHom.comp
            (IntermediateField.inclusion hEU)) cE := by
    exact rationalRelativeIdeleClassEmbedding_smul_eq_classEmbedding hEU σ cE
  have hsmul :
      σ • RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
          (IntermediateField.inclusion hEU) cE =
        RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
          ((AlgEquiv.restrictNormalHom U σ).toAlgHom.comp
            (IntermediateField.inclusion hEU)) cE := by
    change (AlgEquiv.restrictNormalHom U σ) •
        RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
          (IntermediateField.inclusion hEU) cE =
      RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
        ((AlgEquiv.restrictNormalHom U σ).toAlgHom.comp
          (IntermediateField.inclusion hEU)) cE
    exact hrestricted
  have hclass' :
      σ • RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
          (IntermediateField.inclusion hEU) cE =
        RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := U)
          (IntermediateField.inclusion hFU)
          (relativeIdeleClassCongr (K := ℚ) e cE) := by
    calc
      σ • RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
          (IntermediateField.inclusion hEU) cE =
        RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
          ((AlgEquiv.restrictNormalHom U σ).toAlgHom.comp
            (IntermediateField.inclusion hEU)) cE :=
        hsmul
      _ = RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := U)
          (IntermediateField.inclusion hFU)
          (relativeIdeleClassCongr (K := ℚ) e cE) := by
        rw [RelativeIdeleGroup.classEmbedding_relativeIdeleClassCongr]
        apply congrArg
          (fun f : E →ₐ[ℚ] U =>
            RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U) f cE)
        apply AlgHom.ext
        intro x
        apply Subtype.ext
        calc
          (((AlgEquiv.restrictNormalHom U σ).toAlgHom.comp
                (IntermediateField.inclusion hEU)) x :
              SeparableClosure ℚ) =
              σ (x : SeparableClosure ℚ) := by
            exact
              AlgEquiv.restrictNormal_commutes σ U
                (IntermediateField.inclusion hEU x)
          _ = ((e x : F) : SeparableClosure ℚ) :=
            (hσe x).symm
          _ =
              (((IntermediateField.inclusion hFU).comp
                e.toAlgHom) x : U) :=
            rfl
  have hclass :
      σ • RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
          (IntermediateField.inclusion hEU) cE =
        RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := U)
          (IntermediateField.inclusion hFU) cF := by
    simpa only [cF] using hclass'
  have hlimit_smul :
      σ • rationalRelativeIdeleClassToDirectLimit U
          (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
            (IntermediateField.inclusion hEU) cE) =
        rationalRelativeIdeleClassToDirectLimit U
          (σ • RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
            (IntermediateField.inclusion hEU) cE) := by
    exact DirectLimit.smul_def _ _ _
  calc
    σ • rationalIntermediateIdeleClassToDirectLimit E c =
      σ • rationalRelativeIdeleClassToDirectLimit U
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
          (IntermediateField.inclusion hEU) cE) := by
      rw [hE]
    _ = rationalRelativeIdeleClassToDirectLimit U
        (σ • RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := U)
          (IntermediateField.inclusion hEU) cE) :=
      hlimit_smul
    _ = rationalRelativeIdeleClassToDirectLimit U
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := U)
          (IntermediateField.inclusion hFU) cF) :=
      congrArg (rationalRelativeIdeleClassToDirectLimit U) hclass
    _ = rationalIntermediateIdeleClassToDirectLimit F
        (ideleClassCongr e c) :=
      hF.symm

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtension
private local instance q359TowerIdeleIsMulCommutative3.{w} (A B C : Type w) [Field A] [NumberField A]
    [Field B] [Field C] [Algebra A B] [Algebra B C] :
    IsMulCommutative (TowerRelativeIdeleGroup A B C) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Finite extensions in the rational idele-class representation

The fixed representation of a finite abstract extension is compared with
the relative idele class group of its two actual fixed fields.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology

noncomputable instance
    rationalAbstractTowerClassGroupCommGroup
    (F E : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Algebra ℚ F] [Algebra F E] [Algebra ℚ E]
    [IsScalarTower ℚ F E]
    [FiniteDimensional ℚ F] [FiniteDimensional F E] :
    CommGroup (TowerRelativeIdeleGroup.ClassGroup ℚ F E) := by
  letI : CommGroup (TowerRelativeIdeleGroup ℚ F E) :=
    inferInstance
  exact
    QuotientGroup.Quotient.commGroup
      (TowerRelativeIdeleGroup.principalSubgroup ℚ F E)

noncomputable instance
    rationalAbstractTowerClassGroupMul
    (F E : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Algebra ℚ F] [Algebra F E] [Algebra ℚ E]
    [IsScalarTower ℚ F E]
    [FiniteDimensional ℚ F] [FiniteDimensional F E] :
    Mul (TowerRelativeIdeleGroup.ClassGroup ℚ F E) :=
  (rationalAbstractTowerClassGroupCommGroup F E).toMul

noncomputable instance
    rationalAbstractTowerClassGroupMulOneClass
    (F E : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Algebra ℚ F] [Algebra F E] [Algebra ℚ E]
    [IsScalarTower ℚ F E]
    [FiniteDimensional ℚ F] [FiniteDimensional F E] :
    MulOneClass (TowerRelativeIdeleGroup.ClassGroup ℚ F E) :=
  (rationalAbstractTowerClassGroupCommGroup F E).toMulOneClass

end Reciprocity
end GlobalClassFieldTheory
end
end

section
-- module Solutions.OAIQ244_DUKE.GlobalClassFieldTheory_Reciprocity_IdeleClassDirectLimitExtensionAction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldNormSubgroup_normal _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.LocalClassFieldTheory.finiteGaloisLocalField_integerRing_moduleFinite _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.residueFieldZModAlgebra _root_.LocalFieldTheory.DiscreteValuationField.LocalField.mixedIntegralAlgebraContextValuationSubringAlgebra _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.padicCompletedLevelField_algebra _root_.LubinTate.padicCompletedLevelField_finiteDimensional _root_.LubinTate.padicCompletedUnramifiedFieldAlgebra _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.LocalClassFieldTheory.normalizationIntegerRingIsIntegralClosure _root_.chosenFinitePlaceCompletionAlgebra _root_.chosenFinitePlaceCompletionFiniteDimensional _root_.chosenFinitePlaceLocalizedFiniteDimensional _root_.relativeUnrestrictedSPlaceFactorCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# Galois actions on rational fixed-field idele classes

Naturality of the fixed-field comparison for automorphisms and the
finite-extension Galois action.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology

theorem rationalTowerRelativeIdeleClassBaseChangeAddEquiv_smul
    (F E : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Algebra ℚ F] [Algebra F E] [Algebra ℚ E]
    [IsScalarTower ℚ F E]
    [FiniteDimensional ℚ F] [FiniteDimensional F E]
    (τ : E ≃ₐ[F] E)
    (c : Additive (RelativeIdeleGroup.ClassGroup ℚ E)) :
    let eTower :
        Additive (RelativeIdeleGroup.ClassGroup ℚ E) ≃+
          Additive (RelativeIdeleGroup.ClassGroup F E) :=
      (MulEquiv.toAdditive
        (TowerRelativeIdeleGroup.classGroupEquiv
          ℚ F E).symm).trans
        (MulEquiv.toAdditive
          (towerRelativeIdeleClassBaseChangeMulEquiv
            ℚ F E))
    eTower
        (Additive.ofMul
          ((τ.restrictScalars ℚ) • Additive.toMul c)) =
      Additive.ofMul
        (τ • Additive.toMul (eTower c)) := by
  let eTower :
      Additive (RelativeIdeleGroup.ClassGroup ℚ E) ≃+
        Additive (RelativeIdeleGroup.ClassGroup F E) :=
    (MulEquiv.toAdditive
      (TowerRelativeIdeleGroup.classGroupEquiv
        ℚ F E).symm).trans
      (MulEquiv.toAdditive
        (towerRelativeIdeleClassBaseChangeMulEquiv
          ℚ F E))
  apply Additive.toMul.injective
  change
    towerRelativeIdeleClassBaseChangeMulEquiv ℚ F E
        ((TowerRelativeIdeleGroup.classGroupEquiv ℚ F E).symm
          ((τ.restrictScalars ℚ) • Additive.toMul c)) =
      τ •
        towerRelativeIdeleClassBaseChangeMulEquiv ℚ F E
          ((TowerRelativeIdeleGroup.classGroupEquiv ℚ F E).symm
            (Additive.toMul c))
  exact
    towerRelativeIdeleClassBaseChangeMulEquiv_smul
      ℚ F E τ (Additive.toMul c)

end Reciprocity
end GlobalClassFieldTheory
end
end


